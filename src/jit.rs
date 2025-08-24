// src/jit.rs
//! jit.rs — Cranelift JIT for WIR (Cranelift 0.121.x compatible)

use hashbrown::HashMap;

use cranelift::prelude::*;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module as _};
use cranelift::codegen::ir::instructions::BlockArg;

use crate::wir::{
    Constant, Function as WirFunction, Inst, IntBinOp, Value as WirValue, ValueDef, ValueId, FuncId,
};

/// ABI: `unsafe extern "C" fn(argv: *const i64, argc: usize) -> i64`
pub type JitFnPtr = unsafe extern "C" fn(*const i64, usize) -> i64;

pub struct JIT {
    module: JITModule,
    fctx: FunctionBuilderContext,
    keep_alive: Vec<std::ffi::CString>, // keep CString storage alive for compiled code
}

impl Default for JIT {
    fn default() -> Self {
        let mut jb = cranelift_jit::JITBuilder::new(cranelift_module::default_libcall_names())
            .expect("JITBuilder::new");

        unsafe extern "C" {
            fn wir_print_i64(x: i64) -> i64;
            fn wir_print_str(p: *const std::os::raw::c_char) -> i64;
        }
        unsafe {
            jb.symbol(
                "wir_print_i64",
                wir_print_i64 as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_print_str",
                wir_print_str as *const extern "C" fn(*const std::os::raw::c_char) -> i64 as *const u8,
            );
        }

        let module = cranelift_jit::JITModule::new(jb);
        Self {
            module,
            fctx: cranelift_frontend::FunctionBuilderContext::new(),
            keep_alive: Vec::new(), // <-- add this field (see next step)
        }
    }
}

// Add this helper near the top of jit.rs (or as a small inner fn in compile)
fn find_make_closure(fun: &WirFunction, v: ValueId) -> Option<(crate::wir::FuncId, ValueId)> {
    use crate::wir::{Inst, ValueDef};
    let mut cur = v;
    loop {
        match &fun.values[cur.0 as usize].def {
            ValueDef::InstResult(inst, 0) => {
                match &fun.nodes[inst.0 as usize].kind {
                    Inst::MakeClosure { callee, env } => return Some((*callee, *env)),
                    Inst::Mov(src) => { cur = *src; }
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
}

impl JIT {
    pub fn compile(&mut self, fun: &WirFunction) -> Result<JitFnPtr, String> {
        use cranelift::prelude::*;
        use cranelift::prelude::{AbiParam, FunctionBuilder, FunctionBuilderContext};
        use cranelift::prelude::types;
        use cranelift::codegen::ir::{StackSlot, StackSlotData, StackSlotKind};
        use cranelift_module::{Linkage, Module};

        // ---- build cranelift context/signature: (argv_ptr, argc) -> i64
        let mut ctx = self.module.make_context();
        let ptr_ty = self.module.target_config().pointer_type();
        ctx.func.signature.params.push(AbiParam::new(ptr_ty));
        ctx.func.signature.params.push(AbiParam::new(types::I64));
        ctx.func.signature.returns.push(AbiParam::new(types::I64));

        eprintln!(
            "[JIT] compile wir_f_{}: {} nodes, {} values, {} params",
            fun.id.0,
            fun.nodes.len(),
            fun.values.len(),
            fun.sig.params.len()
        );

        // ---- IR builder
        let mut fb = FunctionBuilder::new(&mut ctx.func, &mut self.fctx);
        let entry = fb.create_block();
        fb.append_block_params_for_function_params(entry);
        fb.switch_to_block(entry);

        let (args_base, _argc_val) = {
            let p = fb.block_params(entry);
            (p[0], p[1])
        };

        let mut vmap = ValueMap::new();
        let mut terminated = false;
        let mut saw_any_return = false;

        // Track stack-allocated "arrays" so we can answer ArrayLen at JIT time.
        // Keyed by the WIR value produced by AllocArray.
        let mut array_info: HashMap<ValueId, (cranelift::codegen::ir::StackSlot, i64)> = HashMap::new();

        // Track closures we build: closure_value -> (callee FuncId, env ValueId)
        let mut closure_info: HashMap<ValueId, (crate::wir::FuncId, ValueId)> = HashMap::new();

        // For small const-sized arrays/envs we back them by stack slots.
        let mut arr_slots: HashMap<ValueId, StackSlot> = HashMap::new();
        let mut arr_sizes: HashMap<ValueId, i32> = HashMap::new();

        // Bind WIR params: load argv[i] as i64s.
        let param_count = fun.sig.params.len();
        for i in 0..param_count {
            let off = (i as i64) * 8;
            let addr = fb.ins().iadd_imm(args_base, off);
            let loaded = fb.ins().load(types::I64, MemFlags::trusted(), addr, 0);
            vmap.bind(ValueId(i as u32), loaded);
            eprintln!("[JIT] prebind param {} -> ValueId#{:?}", i, i);
        }

        // helpers
        let mut emit_const = |fb: &mut FunctionBuilder, c: &Constant| -> Value {
            match c {
                Constant::Int32(x) => fb.ins().iconst(types::I64, *x as i64),
                Constant::F64(f)   => fb.ins().iconst(types::I64, (*f).to_bits() as i64),
                Constant::Bool(b)  => fb.ins().iconst(types::I64, if *b { 1 } else { 0 }),
                Constant::Null     => fb.ins().iconst(types::I64, 0),
                Constant::Str(s)   => {
                    let cstr = std::ffi::CString::new(s.as_str()).unwrap();
                    let ptr = cstr.as_ptr() as i64;
                    self.keep_alive.push(cstr);
                    fb.ins().iconst(types::I64, ptr)
                }
            }
        };
        let const_i32_of = |id: ValueId| -> Option<i32> {
            match &fun.values[id.0 as usize].def {
                ValueDef::Const(Constant::Int32(x)) => Some(*x),
                _ => None,
            }
        };

        // Precreate one CLIF block per WIR block.
        let mut clif_of = Vec::with_capacity(fun.blocks.len());
        for blk in &fun.blocks {
            let ebb = if blk.id == fun.entry { entry } else { fb.create_block() };
            clif_of.push(ebb);
            if blk.id != fun.entry {
                for &vid in &blk.params {
                    let p = fb.append_block_param(ebb, types::I64);
                    vmap.bind(vid, p);
                }
            }
        }

        // ---- linear pass
        for (bid, block) in fun.blocks.iter().enumerate() {
            eprintln!("  [block] visiting block #{bid} with {} insts", block.insts.len());

            let cur_ebb = clif_of[bid];
            if bid != fun.entry.0 as usize {
                fb.switch_to_block(cur_ebb);
            }

            let mut block_terminated = false;

            for nid in &block.insts {
                if block_terminated || terminated { break; }

                eprintln!("  [nodes] processing nid={:?}", nid);
                let node = &fun.nodes[nid.0 as usize];
                let res_count = node.results.len();
                eprintln!(
                    "  [nodes] processing nid={:?} kind={:?} results={:?}",
                    nid, node.kind, node.results
                );

                match &node.kind {
                    Inst::Const(c) => {
                        let v = emit_const(&mut fb, c);
                        if res_count == 1 { vmap.bind(node.results[0], v); }
                    }

                    Inst::Mov(src) => {
                        let v = vmap.get_or_emit(*src, &mut fb, args_base, fun);
                        if res_count == 1 { vmap.bind(node.results[0], v); }
                    }

                    Inst::IntBin { op, a, b } => {
                        let a = vmap.get_or_emit(*a, &mut fb, args_base, fun);
                        let b = vmap.get_or_emit(*b, &mut fb, args_base, fun);
                        let v = match op {
                            IntBinOp::Add => fb.ins().iadd(a, b),
                            IntBinOp::Sub => fb.ins().isub(a, b),
                            IntBinOp::Mul => fb.ins().imul(a, b),
                            IntBinOp::DivS => fb.ins().sdiv(a, b),
                            IntBinOp::RemS => fb.ins().srem(a, b),
                            IntBinOp::And => fb.ins().band(a, b),
                            IntBinOp::Or  => fb.ins().bor(a, b),
                            IntBinOp::Xor => fb.ins().bxor(a, b),
                            IntBinOp::Shl => fb.ins().ishl(a, b),
                            IntBinOp::ShrU => fb.ins().ushr(a, b),
                            IntBinOp::Sar => fb.ins().sshr(a, b),
                        };
                        if res_count == 1 { vmap.bind(node.results[0], v); }
                    }

                    Inst::CmpInt { kind, a, b } => {
                        let a = vmap.get_or_emit(*a, &mut fb, args_base, fun);
                        let b = vmap.get_or_emit(*b, &mut fb, args_base, fun);
                        let cc = match kind {
                            crate::wir::CmpKind::Eq => IntCC::Equal,
                            crate::wir::CmpKind::Ne => IntCC::NotEqual,
                            crate::wir::CmpKind::Lt => IntCC::SignedLessThan,
                            crate::wir::CmpKind::Le => IntCC::SignedLessThanOrEqual,
                            crate::wir::CmpKind::Gt => IntCC::SignedGreaterThan,
                            crate::wir::CmpKind::Ge => IntCC::SignedGreaterThanOrEqual,
                        };
                        let cond = fb.ins().icmp(cc, a, b);
                        let one = fb.ins().iconst(types::I64, 1);
                        let zero = fb.ins().iconst(types::I64, 0);
                        let v = fb.ins().select(cond, one, zero);
                        if res_count == 1 { vmap.bind(node.results[0], v); }
                    }

                    // -------- Arrays (const-size, stack-backed) --------
                    Inst::AllocArray { elem_hint: _ /* ignored for JIT */, len } => {
                        // We only need this for closure envs (small, constant lengths).
                        // Try to get a constant length; if not, fall back to a minimal slot.
                        let len_v = vmap.get_or_emit(*len, &mut fb, args_base, fun);
                        // Best-effort constant fold (works for Int32/Bool/Null consts).
                        let len_const = match &fun.values[len.0 as usize].def {
                            ValueDef::Const(Constant::Int32(x)) => *x as i64,
                            ValueDef::Const(Constant::Bool(b))  => if *b { 1 } else { 0 },
                            ValueDef::Const(Constant::Null)     => 0,
                            _ => 0, // non-const: treat as 0; we still make a small slot
                        }.max(0);

                        // Allocate a sized stack slot. Use at least 8 bytes so address is valid.
                        let bytes: u32 = ((len_const as u32).saturating_mul(8)).max(8);
                        let slot = fb.create_sized_stack_slot(StackSlotData::new(
                            StackSlotKind::ExplicitSlot,
                            bytes,
                            3, // 8-byte alignment
                        ));
                        let addr = fb.ins().stack_addr(ptr_ty, slot, 0);
                        if res_count == 1 {
                            vmap.bind(node.results[0], addr);
                            array_info.insert(node.results[0], (slot, len_const));
                        }
                    }
                    Inst::LoadElem { arr, idx } => {
                        // addr = arr + idx * 8
                        let base = vmap.get_or_emit(*arr, &mut fb, args_base, fun);
                        let i    = vmap.get_or_emit(*idx, &mut fb, args_base, fun);
                        let eight = fb.ins().iconst(types::I64, 8);
                        let off   = fb.ins().imul(i, eight);
                        let addr  = fb.ins().iadd(base, off);
                        let v     = fb.ins().load(types::I64, MemFlags::trusted(), addr, 0);
                        if res_count == 1 {
                            vmap.bind(node.results[0], v);
                        }
                    }

                    Inst::StoreElem { arr, idx, val } => {
                        // addr = arr + idx * 8 ; store val
                        let base = vmap.get_or_emit(*arr, &mut fb, args_base, fun);
                        let i    = vmap.get_or_emit(*idx, &mut fb, args_base, fun);
                        let v    = vmap.get_or_emit(*val, &mut fb, args_base, fun);
                        let eight = fb.ins().iconst(types::I64, 8);
                        let off   = fb.ins().imul(i, eight);
                        let addr  = fb.ins().iadd(base, off);
                        fb.ins().store(MemFlags::trusted(), v, addr, 0);
                        // no SSA result to bind (res_count is usually 1 due to effect token in WIR; we already bind that elsewhere)
                    }

                    Inst::ArrayLen(arr) => {
                        // If we created this array in this function, return the known constant length.
                        let len_const = array_info.get(arr).map(|&(_, n)| n).unwrap_or(0);
                        let v = fb.ins().iconst(types::I64, len_const);
                        if res_count == 1 {
                            vmap.bind(node.results[0], v);
                        }
                    }

                    // -------- Closures --------
                    Inst::MakeClosure { callee, env } => {
                        // Record which callee/env this closure carries so CallClosure can recover it.
                        if res_count == 1 {
                            // Bind a harmless placeholder value (0) as the "closure object".
                            let zero = fb.ins().iconst(types::I64, 0);
                            vmap.bind(node.results[0], zero);

                            // Remember the logical payload of the closure.
                            closure_info.insert(node.results[0], (*callee, *env));
                        }
                    }

                    Inst::CallClosure { conv: _, fun: clos, args } => {
                        let clos_id = *clos;

                        // Recover (callee, env) for this closure; trap if we never saw its MakeClosure.
                        let (callee_fid, env_vid) = match closure_info.get(&clos_id) {
                            Some(&(fid, env_v)) => (fid, env_v),
                            None => {
                                let code = TrapCode::unwrap_user(0xE2);
                                fb.ins().trap(code);
                                // Dummy (unreached) values to satisfy the type checker
                                (crate::wir::FuncId(0), ValueId(u32::MAX))
                            }
                        };

                        // Build the imported callee signature: (argv_ptr, argc) -> i64  (same as CallDirect)
                        let mut sig = self.module.make_signature();
                        sig.params.push(AbiParam::new(ptr_ty));
                        sig.params.push(AbiParam::new(types::I64));
                        sig.returns.push(AbiParam::new(types::I64));

                        let sym = format!("wir_f_{}", callee_fid.0);
                        let func_id = self
                            .module
                            .declare_function(&sym, Linkage::Import, &sig)
                            .map_err(|e| e.to_string())?;
                        let callee_ref = self.module.declare_func_in_func(func_id, &mut fb.func);

                        // Pack argv = [env, args…]
                        let n = 1 + args.len();
                        let size_bytes: u32 = (n as u32) * 8;
                        let slot = fb.create_sized_stack_slot(StackSlotData::new(
                            StackSlotKind::ExplicitSlot, size_bytes, 3,
                        ));

                        // env first
                        let env_val = if env_vid.0 != u32::MAX {
                            vmap.get_or_emit(env_vid, &mut fb, args_base, fun) // <-- this `fun` is &WirFunction
                        } else {
                            fb.ins().iconst(types::I64, 0)
                        };
                        fb.ins().stack_store(env_val, slot, 0);

                        // positional args follow
                        for (i, a) in args.iter().enumerate() {
                            let v = vmap.get_or_emit(*a, &mut fb, args_base, fun);
                            fb.ins().stack_store(v, slot, ((i as i32) + 1) * 8);
                        }

                        // Call
                        let argv_ptr = fb.ins().stack_addr(ptr_ty, slot, 0);
                        let argc     = fb.ins().iconst(types::I64, n as i64);
                        let call     = fb.ins().call(callee_ref, &[argv_ptr, argc]);

                        if res_count >= 1 {
                            let r = fb.inst_results(call)[0];
                            vmap.bind(node.results[0], r);
                        }
                    }

                    // -------- Calls --------
                    Inst::CallDirect { callee, args, .. } => {
                        let mut sig = self.module.make_signature();
                        sig.params.push(AbiParam::new(ptr_ty));
                        sig.params.push(AbiParam::new(types::I64));
                        sig.returns.push(AbiParam::new(types::I64));

                        let sym = format!("wir_f_{}", callee.0);
                        let func_id = self
                            .module
                            .declare_function(&sym, Linkage::Import, &sig)
                            .map_err(|e| e.to_string())?;
                        let callee_ref = self.module.declare_func_in_func(func_id, &mut fb.func);

                        let n = args.len();
                        let size_bytes: u32 = (n as u32) * 8;
                        let slot = fb.create_sized_stack_slot(StackSlotData::new(
                            StackSlotKind::ExplicitSlot,
                            size_bytes,
                            3,
                        ));
                        for (i, a) in args.iter().enumerate() {
                            let v = vmap.get_or_emit(*a, &mut fb, args_base, fun);
                            fb.ins().stack_store(v, slot, (i as i32) * 8);
                        }
                        let argv_ptr = fb.ins().stack_addr(ptr_ty, slot, 0);
                        let argc = fb.ins().iconst(types::I64, n as i64);
                        let call = fb.ins().call(callee_ref, &[argv_ptr, argc]);
                        if res_count >= 1 {
                            let r = fb.inst_results(call)[0];
                            vmap.bind(node.results[0], r);
                        }
                    }

                    Inst::CallNative { name, args, .. } => {
                        let mut sig = self.module.make_signature();
                        for _ in 0..args.len() {
                            sig.params.push(AbiParam::new(types::I64));
                        }
                        sig.returns.push(AbiParam::new(types::I64));
                        let func_id = self
                            .module
                            .declare_function(name, Linkage::Import, &sig)
                            .map_err(|e| e.to_string())?;
                        let callee = self.module.declare_func_in_func(func_id, &mut fb.func);

                        let mut argv = Vec::with_capacity(args.len());
                        for a in args {
                            argv.push(vmap.get_or_emit(*a, &mut fb, args_base, fun));
                        }
                        let call = fb.ins().call(callee, &argv);
                        if res_count == 1 {
                            let res = fb.inst_results(call)[0];
                            vmap.bind(node.results[0], res);
                        }
                    }

                    // -------- Control flow (BlockArg!) --------
                    Inst::Jump(to, args) => {
                        let dst = clif_of[to.0 as usize];
                        let mut bargs: Vec<BlockArg> = Vec::with_capacity(args.len());
                        for &a in args {
                            let v = vmap.get_or_emit(a, &mut fb, args_base, fun);
                            bargs.push(BlockArg::from(v));
                        }
                        fb.ins().jump(dst, &bargs[..]); // &BlockArg slice
                        block_terminated = true;
                    }

                    Inst::Branch { cond, then_b, else_b } => {
                        let c = vmap.get_or_emit(*cond, &mut fb, args_base, fun);
                        fb.ins().brif(
                            c,
                            clif_of[then_b.0 as usize], &[] as &[BlockArg],
                            clif_of[else_b.0 as usize], &[] as &[BlockArg],
                        );
                        block_terminated = true;
                    }

                    Inst::Return(vals) => {
                        let ret = if vals.is_empty() {
                            fb.ins().iconst(types::I64, 0)
                        } else {
                            vmap.get_or_emit(vals[0], &mut fb, args_base, fun)
                        };
                        fb.ins().return_(&[ret]);
                        block_terminated = true;
                        saw_any_return = true;
                    }

                    // -------- Effects / markers --------
                    Inst::EffectEntry => {
                        let token = fb.ins().iconst(ptr_ty, 0);
                        if res_count == 1 { vmap.bind(node.results[0], token); }
                    }

                    Inst::Safepoint => { /* ignore for now */ }

                    Inst::GuardBounds { idx, len, .. } => {
                        // idx and len are i64 values in our JIT
                        let i = vmap.get_or_emit(*idx, &mut fb, args_base, fun);
                        let n = vmap.get_or_emit(*len, &mut fb, args_base, fun);

                        // Build constants separately to avoid multiple mutable borrows of `fb`.
                        let zero = fb.ins().iconst(types::I64, 0);

                        // idx >= 0 && idx < len
                        let ge0 = fb.ins().icmp(IntCC::SignedGreaterThanOrEqual, i, zero);
                        let lt  = fb.ins().icmp(IntCC::SignedLessThan, i, n);
                        let ok  = fb.ins().band(ge0, lt);

                        // If not ok → trap (user code OOB)
                        let cont = fb.create_block();
                        let bad  = fb.create_block();
                        fb.ins().brif(
                            ok,
                            cont, &[] as &[BlockArg],
                            bad,  &[] as &[BlockArg],
                        );

                        fb.switch_to_block(bad);
                        fb.ins().trap(TrapCode::unwrap_user(0xE1));

                        fb.switch_to_block(cont);

                        // Bind a dummy token result (so downstream users don’t crash)
                        if res_count == 1 {
                            let tok = fb.ins().iconst(self.module.target_config().pointer_type(), 0);
                            vmap.bind(node.results[0], tok);
                        }
                    }

                    _ => {
                        trap_unsupported(&mut fb, "unsupported");
                        terminated = true;
                    }
                }

                // Safety net: only bind zeros if block still open.
                if !(block_terminated || terminated) {
                    for &rid in &node.results {
                        if vmap.get(rid).is_none() {
                            let z = fb.ins().iconst(types::I64, 0);
                            vmap.bind(rid, z);
                        }
                    }
                }
            }
            if terminated { break; }
        }

        if !saw_any_return {
            let tail = fb.create_block();
            fb.switch_to_block(tail);
            let zero = fb.ins().iconst(types::I64, 0);
            fb.ins().return_(&[zero]);
        }

        fb.seal_all_blocks();
        fb.finalize();

        // ---- define current function with stable symbol (wir_f_<id>)
        let sym = format!("wir_f_{}", fun.id.0);
        let func_id = self
            .module
            .declare_function(&sym, Linkage::Local, &ctx.func.signature)
            .map_err(|e| e.to_string())?;
        self.module.define_function(func_id, &mut ctx).map_err(|e| e.to_string())?;
        self.module.clear_context(&mut ctx);
        self.module.finalize_definitions().map_err(|e| e.to_string())?;

        let code = self.module.get_finalized_function(func_id);
        let fptr: JitFnPtr = unsafe { std::mem::transmute(code) };
        Ok(fptr)
    }
}

/// Value binder: maps WIR ValueIds to CLIF Values, and lazily loads argv[idx] only for params.
struct ValueMap {
    map: HashMap<ValueId, Value>,
}

impl ValueMap {
    fn new() -> Self {
        Self { map: HashMap::new() }
    }
    fn bind(&mut self, id: ValueId, v: Value) {
        self.map.insert(id, v);
    }
    fn get(&self, id: ValueId) -> Option<Value> {
        self.map.get(&id).copied()
    }

    fn get_or_load(
        &mut self,
        id: ValueId,
        fb: &mut FunctionBuilder,
        args_base: Value,
        values: &Vec<WirValue>,
    ) -> Value {
        if let Some(v) = self.get(id) {
            return v;
        }

        if let Some(v) = synth_const(values, id, fb) {
            self.bind(id, v);
            return v;
        }

        // Log the *actual* defining site so we know what we missed.
        let vdef = &values[id.0 as usize].def;
        eprintln!(
            "[JIT][warn] get_or_load fallback -> 0 for {:?} (def={:?})",
            id, vdef
        );

        // Fallback to 0 so we can keep running and see the rest of the trace.
        let zero = fb.ins().iconst(cranelift::prelude::types::I64, 0);
        self.bind(id, zero);
        zero
    }

    fn get_or_emit(
        &mut self,
        id: ValueId,
        fb: &mut FunctionBuilder,
        args_base: Value,
        fun: &WirFunction,
    ) -> Value {
        if let Some(v) = self.get(id) { return v; }
        if let Some(v) = synth_const(&fun.values, id, fb) { self.bind(id, v); return v; }

        eprintln!("[JIT][warn] get_or_emit fallback -> 0 for {:?} (def={:?})", id, fun.values[id.0 as usize].def);

        let zero = fb.ins().iconst(cranelift::prelude::types::I64, 0);
        self.bind(id, zero);
        zero
    }
}

fn synth_const(values: &Vec<WirValue>, id: ValueId, fb: &mut FunctionBuilder) -> Option<Value> {
    match &values[id.0 as usize].def {
        ValueDef::Const(c) => match c {
            Constant::Int32(x) => Some(fb.ins().iconst(types::I64, *x as i64)),
            Constant::F64(f)   => Some(fb.ins().iconst(types::I64, f.to_bits() as i64)),
            Constant::Bool(b)  => Some(fb.ins().iconst(types::I64, if *b { 1 } else { 0 })),
            Constant::Null     => Some(fb.ins().iconst(types::I64, 0)),
            Constant::Str(_)   => None,
        },
        _ => None,
    }
}

fn trap_unsupported(fb: &mut FunctionBuilder, _what: &str) {
    // 'trap' is a terminator. Do NOT emit any further instructions in this block.
    let code = TrapCode::unwrap_user(0xE0);
    fb.ins().trap(code);
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_print_i64(x: i64) -> i64 {
    println!("{}", x);
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_print_str(p: *const std::os::raw::c_char) -> i64 {
    use std::ffi::CStr;
    if p.is_null() {
        println!("(null)");
        return 0;
    }
    unsafe {
        let s = CStr::from_ptr(p).to_string_lossy();
        println!("{}", s);
    }
    0
}


// --- DEBUG HELPERS (fixed) ---------------------------------------------------
fn dump_value_kind(values: &Vec<WirValue>, id: ValueId) -> &'static str {
    match &values[id.0 as usize].def {
        crate::wir::ValueDef::Const(_) => "Const",
        _ => "Other",
    }
}

fn dump_const(values: &Vec<WirValue>, id: ValueId) -> Option<i64> {
    use crate::wir::Constant::*;
    match &values[id.0 as usize].def {
        crate::wir::ValueDef::Const(Int32(x)) => Some(*x as i64),
        crate::wir::ValueDef::Const(Bool(b))  => Some(if *b { 1 } else { 0 }),
        crate::wir::ValueDef::Const(F64(f))   => Some((*f).to_bits() as i64),
        crate::wir::ValueDef::Const(Null)     => Some(0),
        _ => None,
    }
}
