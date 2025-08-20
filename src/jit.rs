// src/jit.rs
//! jit.rs — Cranelift JIT for WIR (Cranelift 0.121.x compatible)

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module as _};
use cranelift::codegen::ir::instructions::BlockArg;

use crate::wir::{
    Constant, Function as WirFunction, Inst, IntBinOp, Value as WirValue, ValueDef, ValueId,
};

/// ABI: `unsafe extern "C" fn(argv: *const i64, argc: usize) -> i64`
pub type JitFnPtr = unsafe extern "C" fn(*const i64, usize) -> i64;

pub struct JIT {
    module: JITModule,
    fctx: FunctionBuilderContext,
}

impl Default for JIT {
    fn default() -> Self {
        // JITBuilder::new returns Result in 0.121.x
        let mut jb = cranelift_jit::JITBuilder::new(cranelift_module::default_libcall_names())
            .expect("JITBuilder::new");

        // Register runtime symbols we can import and call.
        unsafe extern "C" {
            fn wir_print_i64(x: i64) -> i64;
        }
        unsafe {
            jb.symbol(
                "wir_print_i64",
                wir_print_i64 as *const extern "C" fn(i64) -> i64 as *const u8,
            );
        }

        let module = cranelift_jit::JITModule::new(jb);
        Self {
            module,
            fctx: cranelift_frontend::FunctionBuilderContext::new(),
        }
    }
}

impl JIT {
    pub fn compile(&mut self, fun: &WirFunction) -> Result<JitFnPtr, String> {
        use cranelift::prelude::*;
        use cranelift::prelude::{AbiParam, FunctionBuilder, FunctionBuilderContext};
        use cranelift::prelude::types;
        use cranelift::codegen::ir::{StackSlotData, StackSlotKind};
        use cranelift_module::{Linkage, Module};

        // ---- build cranelift context/signature: (argv_ptr, argc) -> i64
        let mut ctx = self.module.make_context();
        let ptr_ty = self.module.target_config().pointer_type();
        ctx.func.signature.params.push(AbiParam::new(ptr_ty));
        ctx.func.signature.params.push(AbiParam::new(types::I64));
        ctx.func.signature.returns.push(AbiParam::new(types::I64));

        // Dump a quick header about the function we’re compiling
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

        // Bind WIR params for this function to loads from argv[i].
        let param_count = fun.sig.params.len();
        for i in 0..param_count {
            let off = (i as i64) * 8;
            let addr = fb.ins().iadd_imm(args_base, off);
            let loaded = fb.ins().load(types::I64, MemFlags::trusted(), addr, 0);
            vmap.bind(ValueId(i as u32), loaded);

            eprintln!("[JIT] prebind param {} -> ValueId#{:?}", i, i);
        }

        // Helpers
        let mut emit_const = |fb: &mut FunctionBuilder, c: &Constant| -> Value {
            match c {
                Constant::Int32(x) => fb.ins().iconst(types::I64, *x as i64),
                Constant::F64(f)   => fb.ins().iconst(types::I64, (*f).to_bits() as i64),
                Constant::Bool(b)  => fb.ins().iconst(types::I64, if *b { 1 } else { 0 }),
                Constant::Null     => fb.ins().iconst(types::I64, 0),
                // Do NOT trap here; emitting after a trap would panic. Just stub to 0.
                Constant::Str(_)   => fb.ins().iconst(types::I64, 0),
            }
        };

        // --- Precreate one CLIF block per WIR block ---
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

        // ---- naïve linear pass over all blocks in order
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
                        eprintln!("[JIT] Const {:?}", c);

                        let v = emit_const(&mut fb, c);
                        if res_count == 1 { vmap.bind(node.results[0], v); }
                    }

                    Inst::Mov(src) => {
                        eprintln!("[JIT] Mov from {:?}", src);
                        eprintln!(
                            "  [nodes] Mov -> dst={:?} <- src={:?}",
                            node.results.get(0).cloned().unwrap_or(ValueId(u32::MAX)),
                            src
                        );
                        let v = vmap.get_or_emit(*src, &mut fb, args_base, fun);
                        if res_count == 1 {
                            vmap.bind(node.results[0], v);
                            eprintln!("           bind {:?} (Mov)", node.results[0]);
                        } else {
                            eprintln!("           (Mov) no results to bind (res_count={})", res_count);
                        }
                    }

                    Inst::IntBin { op, a, b } => {
                        eprintln!(
                            "[JIT] IntBin {:?} a={:?}({:?}) b={:?}({:?})",
                            op, a, dump_value_kind(&fun.values, *a),
                                b, dump_value_kind(&fun.values, *b)
                        );
                        eprintln!(
                            "           operands: a={:?}({:?}) b={:?}({:?})",
                            a, dump_value_kind(&fun.values, *a),
                            b, dump_value_kind(&fun.values, *b)
                        );

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
                        eprintln!(
                            "[JIT] CmpInt {:?} a={:?}({:?}) b={:?}({:?})",
                            kind, a, dump_value_kind(&fun.values, *a),
                                b, dump_value_kind(&fun.values, *b)
                        );
                        eprintln!(
                            "           operands: a={:?}({:?}) b={:?}({:?})",
                            a, dump_value_kind(&fun.values, *a),
                            b, dump_value_kind(&fun.values, *b)
                        );

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

                    Inst::CallDirect { callee, args, .. } => {
                        eprintln!("[JIT] CallDirect wir_f_{} argc={}", callee.0, args.len());
                        eprintln!(
                            "  [nodes] CallDirect callee=wir_f_{} argc={}  results={:?}",
                            callee.0, args.len(), node.results
                        );

                        // Callee ABI: (argv_ptr, argc) -> i64
                        let mut sig = self.module.make_signature();
                        sig.params.push(AbiParam::new(ptr_ty));
                        sig.params.push(AbiParam::new(types::I64));
                        sig.returns.push(AbiParam::new(types::I64));

                        // Stable symbol per FuncId so we can import it here
                        let sym = format!("wir_f_{}", callee.0);
                        let func_id = self
                            .module
                            .declare_function(&sym, Linkage::Import, &sig)
                            .map_err(|e| e.to_string())?;
                        let callee_ref = self.module.declare_func_in_func(func_id, &mut fb.func);

                        // Pack args into a stack array of i64s
                        let n = args.len();
                        let size_bytes: u32 = (n as u32) * 8;
                        let slot = fb.create_sized_stack_slot(StackSlotData::new(
                            StackSlotKind::ExplicitSlot,
                            size_bytes,
                            3, // 2^3 = 8-byte alignment
                        ));
                        for (i, a) in args.iter().enumerate() {
                            let v = vmap.get_or_emit(*a, &mut fb, args_base, fun);
                            fb.ins().stack_store(v, slot, (i as i32) * 8);
                            eprintln!("           arg[{}] <- {:?}", i, a);
                        }
                        let argv_ptr = fb.ins().stack_addr(ptr_ty, slot, 0);
                        let argc = fb.ins().iconst(types::I64, n as i64);

                        let call = fb.ins().call(callee_ref, &[argv_ptr, argc]);

                        // IMPORTANT: Bind the produced result if WIR says there is one.
                        if res_count >= 1 {
                            let r = fb.inst_results(call)[0];
                            vmap.bind(node.results[0], r);
                            eprintln!("           bind result {:?} from CallDirect", node.results[0]);
                        } else {
                            // If this ever triggers, the lowerer created a call without a result
                            // but later WIR tries to use it (like your ValueId#5). This log will prove it.
                            eprintln!("           WARNING: CallDirect had res_count=0; no value bound");
                        }
                    }

                    // Native call already supported elsewhere in your JIT:
                    Inst::CallNative { name, args, .. } => {
                        eprintln!("[JIT] CallNative {} argc={}", name, args.len());
                        eprintln!("           native: {}  args: {:?}", name, args);

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
                        let mut index = 0;
                        for a in args {
                            eprintln!(
                                "             arg[{}] = {:?} kind={} const={:?}",
                                index, a, dump_value_kind(&fun.values, *a), dump_const(&fun.values, *a)
                            );
                            index += 1;

                            argv.push(vmap.get_or_emit(*a, &mut fb, args_base, fun));
                        }
                        let call = fb.ins().call(callee, &argv);
                        if res_count == 1 {
                            let res = fb.inst_results(call)[0];
                            vmap.bind(node.results[0], res);
                        }
                    }

                    Inst::Jump(to, args) => {
                        let dst = clif_of[to.0 as usize];
                        // Build BlockArgs (BlockArg::from(Value))
                        let mut bargs: Vec<BlockArg> = Vec::with_capacity(args.len());
                        for &a in args {
                            let v = vmap.get_or_emit(a, &mut fb, args_base, fun);
                            bargs.push(BlockArg::from(v));
                        }
                        fb.ins().jump(dst, &bargs[..]); // expects &BlockArg, not &Value
                        block_terminated = true;
                    }

                    Inst::Branch { cond, then_b, else_b } => {
                        let c = vmap.get_or_emit(*cond, &mut fb, args_base, fun);
                        // Our booleans are 0/1; brif treats non-zero as true.
                        fb.ins().brif(c,
                            clif_of[then_b.0 as usize], &[] as &[BlockArg],
                            clif_of[else_b.0 as usize], &[] as &[BlockArg]);
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
                        saw_any_return = true;     // <-- add this
                    }

                    // benign markers
                    Inst::EffectEntry => {
                        // Create a dummy effect token value
                        let token = fb.ins().iconst(ptr_ty, 0);
                        if res_count == 1 {
                            vmap.bind(node.results[0], token);
                            eprintln!("           bind {:?} (EffectEntry)", node.results[0]);
                        }
                    }

                    Inst::Safepoint => {}

                    _ => {
                        trap_unsupported(&mut fb, "unsupported");
                        terminated = true;
                    }
                }

                // Safety net: if an instruction declares results but we didn’t bind them,
                // bind zeros so later users don’t crash.
                for &rid in &node.results {
                    if vmap.get(rid).is_none() {
                        eprintln!(
                            "[JIT][warn] result {:?} of kind {:?} not bound; zeroing",
                            rid, node.kind
                        );
                        let z = fb.ins().iconst(types::I64, 0);
                        vmap.bind(rid, z);
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

        // ---- declare/define current function with stable symbol (wir_f_<id>)
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
