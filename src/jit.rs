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
    heap_keep_alive: Vec<*mut u8>,
}

impl Default for JIT {
    fn default() -> Self {
        let mut jb = cranelift_jit::JITBuilder::new(cranelift_module::default_libcall_names())
            .expect("JITBuilder::new");

        unsafe extern "C" {
            fn wir_print_i64(x: i64) -> i64;
            fn wir_print_str(p: *const std::os::raw::c_char) -> i64;
            fn wir_make_closure(code_ptr: *const u8, env: i64) -> i64;
            fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64;
            fn wir_alloc_words(n: i64) -> *mut i64;
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
            jb.symbol(
                "wir_make_closure",
                wir_make_closure as *const extern "C" fn(*const u8, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_call_closure",
                wir_call_closure as *const extern "C" fn(i64, *const i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_alloc_words",
                wir_alloc_words as *const extern "C" fn(i64) -> *mut i64 as *const u8
            );
        }

        let module = cranelift_jit::JITModule::new(jb);
        Self {
            module,
            fctx: cranelift_frontend::FunctionBuilderContext::new(),
            keep_alive: Vec::new(),
            heap_keep_alive: Vec::new(),
        }
    }
}

impl JIT {
    pub fn compile(&mut self, fun: &WirFunction) -> Result<JitFnPtr, String> {
        use cranelift::prelude::*;
        use cranelift::prelude::{AbiParam, FunctionBuilder};
        use cranelift::prelude::types;
        use cranelift::codegen::ir::{StackSlotData, StackSlotKind};
        use cranelift_module::{Linkage, Module};

        // Small helpers for SMI encode/decode (do NOT capture &mut self)
        let mut dec_smi = |fb: &mut FunctionBuilder, v: Value| -> Value {
            // raw = v >> 1 (arithmetic)
            fb.ins().sshr_imm(v, 1)
        };
        let mut enc_smi = |fb: &mut FunctionBuilder, raw: Value| -> Value {
            // (raw << 1) | 1
            let sh = fb.ins().ishl_imm(raw, 1);
            fb.ins().iadd_imm(sh, 1)
        };

        // ---- build cranelift function context/signature: (argv_ptr, argc) -> i64
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

        // Take the shared FunctionBuilderContext out of `self` for this compile.
        // This avoids aliasing &mut self (used by emit_const/module calls) with &mut self.fctx held by `fb`.
        let mut fctx_local = std::mem::take(&mut self.fctx);

        // Do the whole build in a closure so we can early-return with `?`
        // and still restore `self.fctx` afterwards.
        let result = (|| -> Result<JitFnPtr, String> {
            // IR builder uses the LOCAL context (not self.fctx)
            let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fctx_local);
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

            // (Optional) future: track array sizes created in this function
            let mut array_info: HashMap<ValueId, (cranelift::codegen::ir::StackSlot, i64)> = HashMap::new();

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

            // Bind WIR params: load argv[i] as i64s.
            let param_count = fun.sig.params.len();
            for i in 0..param_count {
                let off = (i as i64) * 8;
                let addr = fb.ins().iadd_imm(args_base, off);
                let loaded = fb.ins().load(types::I64, MemFlags::trusted(), addr, 0);
                vmap.bind(ValueId(i as u32), loaded);
                eprintln!("[JIT] prebind param {} -> ValueId#{:?}", i, i);
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
                        // ---------------- Constants ----------------
                        Inst::Const(c) => {
                            let v = self.emit_const(&mut fb, c); // safe now: fb uses fctx_local
                            if res_count == 1 { vmap.bind(node.results[0], v); }
                        }

                        Inst::Mov(src) => {
                            let v = vmap.get_or_emit(*src, &mut fb, args_base, fun);
                            if res_count == 1 { vmap.bind(node.results[0], v); }
                        }

                        // ---------------- Int ops (on SMIs) ----------------
                        Inst::IntBin { op, a, b } => {
                            let a = vmap.get_or_emit(*a, &mut fb, args_base, fun);
                            let b = vmap.get_or_emit(*b, &mut fb, args_base, fun);
                            let ra = dec_smi(&mut fb, a);
                            let rb = dec_smi(&mut fb, b);

                            let raw_res = match op {
                                IntBinOp::Add => fb.ins().iadd(ra, rb),
                                IntBinOp::Sub => fb.ins().isub(ra, rb),
                                IntBinOp::Mul => fb.ins().imul(ra, rb),
                                IntBinOp::DivS => fb.ins().sdiv(ra, rb),
                                IntBinOp::RemS => fb.ins().srem(ra, rb),
                                IntBinOp::And  => fb.ins().band(ra, rb),
                                IntBinOp::Or   => fb.ins().bor(ra, rb),
                                IntBinOp::Xor  => fb.ins().bxor(ra, rb),
                                IntBinOp::Shl  => fb.ins().ishl(ra, rb),
                                IntBinOp::ShrU => fb.ins().ushr(ra, rb),
                                IntBinOp::Sar  => fb.ins().sshr(ra, rb),
                            };

                            let v = enc_smi(&mut fb, raw_res);
                            if res_count == 1 { vmap.bind(node.results[0], v); }
                        }

                        Inst::CmpInt { kind, a, b } => {
                            let a = vmap.get_or_emit(*a, &mut fb, args_base, fun);
                            let b = vmap.get_or_emit(*b, &mut fb, args_base, fun);
                            let ra = dec_smi(&mut fb, a);
                            let rb = dec_smi(&mut fb, b);

                            let cc = match kind {
                                crate::wir::CmpKind::Eq => IntCC::Equal,
                                crate::wir::CmpKind::Ne => IntCC::NotEqual,
                                crate::wir::CmpKind::Lt => IntCC::SignedLessThan,
                                crate::wir::CmpKind::Le => IntCC::SignedLessThanOrEqual,
                                crate::wir::CmpKind::Gt => IntCC::SignedGreaterThan,
                                crate::wir::CmpKind::Ge => IntCC::SignedGreaterThanOrEqual,
                            };
                            let cond = fb.ins().icmp(cc, ra, rb);

                            let one  = fb.ins().iconst(types::I64, 1);
                            let zero = fb.ins().iconst(types::I64, 0);
                            let v    = fb.ins().select(cond, one, zero);
                            if res_count == 1 { vmap.bind(node.results[0], v); }
                        }

                        // ---------------- Arrays (heap words via wir_alloc_words) ----------------
                        Inst::AllocArray { elem_hint: _, len } => {
                            let mut sig = self.module.make_signature();
                            sig.params.push(AbiParam::new(types::I64));
                            sig.returns.push(AbiParam::new(ptr_ty));
                            let fid = self.module
                                .declare_function("wir_alloc_words", Linkage::Import, &sig)
                                .map_err(|e| e.to_string())?;
                            let callee = self.module.declare_func_in_func(fid, &mut fb.func);

                            let len_v = vmap.get_or_emit(*len, &mut fb, args_base, fun);
                            let call  = fb.ins().call(callee, &[len_v]);
                            let ptr   = fb.inst_results(call)[0];

                            if res_count == 1 { vmap.bind(node.results[0], ptr); }
                        }

                        Inst::StoreElem { arr, idx, val } => {
                            let arr_v = vmap.get_or_emit(*arr, &mut fb, args_base, fun);
                            let idx_v = vmap.get_or_emit(*idx, &mut fb, args_base, fun);
                            let val_v = vmap.get_or_emit(*val, &mut fb, args_base, fun);

                            let sh   = fb.ins().iconst(types::I64, 3);
                            let off  = fb.ins().ishl(idx_v, sh);
                            let addr = fb.ins().iadd(arr_v, off);
                            fb.ins().store(MemFlags::trusted(), val_v, addr, 0);

                            if res_count == 1 {
                                let z = fb.ins().iconst(types::I64, 0);
                                vmap.bind(node.results[0], z);
                            }
                        }

                        Inst::LoadElem { arr, idx } => {
                            let arr_v = vmap.get_or_emit(*arr, &mut fb, args_base, fun);
                            let idx_v = vmap.get_or_emit(*idx, &mut fb, args_base, fun);
                            let sh    = fb.ins().iconst(types::I64, 3);
                            let off   = fb.ins().ishl(idx_v, sh);
                            let addr  = fb.ins().iadd(arr_v, off);
                            let v     = fb.ins().load(types::I64, MemFlags::trusted(), addr, 0);
                            if res_count == 1 { vmap.bind(node.results[0], v); }
                        }

                        Inst::ArrayLen(arr) => {
                            let len_const = array_info.get(arr).map(|&(_, n)| n).unwrap_or(0);
                            let v = fb.ins().iconst(types::I64, len_const);
                            if res_count == 1 { vmap.bind(node.results[0], v); }
                        }

                        // ---------------- Closures ----------------
                        Inst::MakeClosure { callee, env } => {
                            // Code pointer for wir_f_<id>
                            let mut sig = self.module.make_signature();
                            sig.params.push(AbiParam::new(ptr_ty));      // argv*
                            sig.params.push(AbiParam::new(types::I64));  // argc
                            sig.returns.push(AbiParam::new(types::I64)); // i64 result

                            let sym      = format!("wir_f_{}", callee.0);
                            let func_id  = self.module.declare_function(&sym, Linkage::Import, &sig)
                                .map_err(|e| e.to_string())?;
                            let func_ref = self.module.declare_func_in_func(func_id, &mut fb.func);
                            let code_ptr = fb.ins().func_addr(ptr_ty, func_ref);

                            let env_v = vmap.get_or_emit(*env, &mut fb, args_base, fun);

                            // wir_make_closure(code_ptr, env)
                            let mut csig = self.module.make_signature();
                            csig.params.push(AbiParam::new(ptr_ty));
                            csig.params.push(AbiParam::new(types::I64));
                            csig.returns.push(AbiParam::new(types::I64));
                            let make_id  = self.module
                                .declare_function("wir_make_closure", Linkage::Import, &csig)
                                .map_err(|e| e.to_string())?;
                            let make_ref = self.module.declare_func_in_func(make_id, &mut fb.func);
                            let call     = fb.ins().call(make_ref, &[code_ptr, env_v]);

                            if res_count == 1 {
                                vmap.bind(node.results[0], fb.inst_results(call)[0]);
                            }
                        }

                        Inst::CallClosure { fun: fun_val, args, .. } => {
                            // Pack user args (env is prepended by trampoline)
                            let n = args.len();
                            let size_bytes: u32 = (n as u32) * 8;
                            let slot = fb.create_sized_stack_slot(StackSlotData::new(
                                StackSlotKind::ExplicitSlot, size_bytes, 3,
                            ));
                            for (i, a) in args.iter().enumerate() {
                                let v = vmap.get_or_emit(*a, &mut fb, args_base, fun);
                                fb.ins().stack_store(v, slot, (i as i32) * 8);
                            }
                            let argv_ptr = fb.ins().stack_addr(ptr_ty, slot, 0);
                            let argc     = fb.ins().iconst(types::I64, n as i64);

                            let clo_v = vmap.get_or_emit(*fun_val, &mut fb, args_base, fun);

                            // wir_call_closure(clo_ptr, argv, argc)
                            let mut csig = self.module.make_signature();
                            csig.params.push(AbiParam::new(types::I64)); // closure (i64)
                            csig.params.push(AbiParam::new(ptr_ty));     // argv*
                            csig.params.push(AbiParam::new(types::I64)); // argc
                            csig.returns.push(AbiParam::new(types::I64));
                            let call_id  = self.module
                                .declare_function("wir_call_closure", Linkage::Import, &csig)
                                .map_err(|e| e.to_string())?;
                            let call_ref = self.module.declare_func_in_func(call_id, &mut fb.func);
                            let call     = fb.ins().call(call_ref, &[clo_v, argv_ptr, argc]);

                            if res_count >= 1 {
                                vmap.bind(node.results[0], fb.inst_results(call)[0]);
                            }
                        }

                        // ---------------- Direct calls ----------------
                        Inst::CallDirect { callee, args, .. } => {
                            let mut sig = self.module.make_signature();
                            sig.params.push(AbiParam::new(ptr_ty));      // argv*
                            sig.params.push(AbiParam::new(types::I64));  // argc
                            sig.returns.push(AbiParam::new(types::I64)); // ret

                            let sym = format!("wir_f_{}", callee.0);
                            let func_id = self
                                .module
                                .declare_function(&sym, Linkage::Import, &sig)
                                .map_err(|e| e.to_string())?;
                            let callee_ref = self.module.declare_func_in_func(func_id, &mut fb.func);

                            let n = args.len();
                            let size_bytes: u32 = (n as u32) * 8;
                            let slot = fb.create_sized_stack_slot(StackSlotData::new(
                                StackSlotKind::ExplicitSlot, size_bytes, 3,
                            ));
                            for (i, a) in args.iter().enumerate() {
                                let v = vmap.get_or_emit(*a, &mut fb, args_base, fun);
                                fb.ins().stack_store(v, slot, (i as i32) * 8);
                            }
                            let argv_ptr = fb.ins().stack_addr(ptr_ty, slot, 0);
                            let argc = fb.ins().iconst(types::I64, n as i64);
                            let call = fb.ins().call(callee_ref, &[argv_ptr, argc]);
                            if res_count >= 1 {
                                vmap.bind(node.results[0], fb.inst_results(call)[0]);
                            }
                        }

                        // ---------------- Native calls ----------------
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
                                vmap.bind(node.results[0], fb.inst_results(call)[0]);
                            }
                        }

                        // ---------------- Control flow ----------------
                        Inst::Jump(to, args) => {
                            let dst = clif_of[to.0 as usize];
                            let mut bargs: Vec<cranelift::codegen::ir::instructions::BlockArg> =
                                Vec::with_capacity(args.len());
                            for &a in args {
                                let v = vmap.get_or_emit(a, &mut fb, args_base, fun);
                                bargs.push(cranelift::codegen::ir::instructions::BlockArg::from(v));
                            }
                            fb.ins().jump(dst, &bargs[..]);
                            block_terminated = true;
                        }

                        Inst::Branch { cond, then_b, else_b } => {
                            let c = vmap.get_or_emit(*cond, &mut fb, args_base, fun);
                            fb.ins().brif(
                                c,
                                clif_of[then_b.0 as usize], &[] as &[cranelift::codegen::ir::instructions::BlockArg],
                                clif_of[else_b.0 as usize],  &[] as &[cranelift::codegen::ir::instructions::BlockArg],
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

                        // ---------------- Effects / markers ----------------
                        Inst::EffectEntry => {
                            let token = fb.ins().iconst(ptr_ty, 0);
                            if res_count == 1 { vmap.bind(node.results[0], token); }
                        }

                        Inst::Safepoint => { /* ignore for now */ }

                        Inst::GuardBounds { idx, len, .. } => {
                            let i = vmap.get_or_emit(*idx, &mut fb, args_base, fun);
                            let n = vmap.get_or_emit(*len, &mut fb, args_base, fun);
                            let zero = fb.ins().iconst(types::I64, 0);

                            // idx >= 0 && idx < len
                            let ge0 = fb.ins().icmp(IntCC::SignedGreaterThanOrEqual, i, zero);
                            let lt  = fb.ins().icmp(IntCC::SignedLessThan, i, n);
                            let ok  = fb.ins().band(ge0, lt);

                            // If not ok → trap
                            let cont = fb.create_block();
                            let bad  = fb.create_block();
                            fb.ins().brif(
                                ok,
                                cont, &[] as &[cranelift::codegen::ir::instructions::BlockArg],
                                bad,  &[] as &[cranelift::codegen::ir::instructions::BlockArg],
                            );

                            fb.switch_to_block(bad);
                            fb.ins().trap(TrapCode::unwrap_user(0xE1));

                            fb.switch_to_block(cont);

                            if res_count == 1 {
                                let tok = fb.ins().iconst(ptr_ty, 0);
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
        })();

        // Always restore the shared builder context
        self.fctx = fctx_local;

        result
    }

}

impl JIT {
    fn emit_const(&mut self, fb: &mut FunctionBuilder, c: &crate::wir::Constant) -> cranelift::prelude::Value {
        use cranelift::prelude::*;
        match c {
            // small ints as SMIs (odd)
            Constant::Int32(x) => fb.ins().iconst(types::I64, ((*x as i64) << 1) | 1),

            // bools as 0/1 (unchanged)
            Constant::Bool(b)  => fb.ins().iconst(types::I64, if *b { 1 } else { 0 }),

            // null as 0
            Constant::Null     => fb.ins().iconst(types::I64, 0),

            // strings -> stable C string pointer kept alive
            Constant::Str(s)   => {
                let cstr = std::ffi::CString::new(s.as_str()).unwrap();
                let ptr = cstr.as_ptr() as i64;
                self.keep_alive.push(cstr);
                fb.ins().iconst(types::I64, ptr)
            }

            // f64 -> heap-allocated BoxedF64
            Constant::F64(f)   => {
                let p = self.alloc_boxed_f64(*f);
                fb.ins().iconst(types::I64, p)
            }
        }
    }

    fn alloc_boxed_f64(&mut self, x: f64) -> i64 {
        use crate::value::{BoxedF64, ObjHeader, TAG_BOXED_F64};
        let obj = Box::new(BoxedF64 { hdr: ObjHeader { tag: TAG_BOXED_F64, aux: 0 }, val: x });
        let ptr = Box::into_raw(obj) as *mut u8;
        self.heap_keep_alive.push(ptr);       // leak (intentionally) until GC
        ptr as i64                             // even pointer => tagged “pointer”
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
            Constant::Int32(x) => {
                let raw = fb.ins().iconst(types::I64, *x as i64);
                let sh  = fb.ins().ishl_imm(raw, 1);
                let smi = fb.ins().iadd_imm(sh, 1);
                Some(smi)
            },
            Constant::F64(f) => {
                // We cannot call self here, so keep synth_const() as-is for Int/Bool/Null,
                // and let F64 fall back to None so the caller uses emit_const path.
                // (Simplest: return None for F64 here.)
                None
            },
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

#[repr(C)]
struct WirClosure {
    code: JitFnPtr, // unsafe extern "C" fn(*const i64, usize) -> i64
    env:  i64,      // opaque environment pointer (we treat env as i64)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_print_i64(v: i64) -> i64 {
    use crate::value::*;
    if is_imm(v) {
        // Treat all odd values as SMI for now.
        // (When we switch booleans to singletons, we can special-case them here.)
        println!("{}", smi_to_i64(v));
    } else {
        // 0 = null, other even = pointer (address for now)
        if v == NULL {
            println!("null");
        } else {
            // TODO: inspect header + pretty-print object
            println!("{:#x}", v as u64);
        }
    }
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

#[unsafe(no_mangle)]
pub extern "C" fn wir_make_closure(code_ptr: *const u8, env: i64) -> i64 {
    // Turn the code address into our JIT function type and box the pair.
    let f: JitFnPtr = unsafe { std::mem::transmute(code_ptr) };
    let b = Box::new(WirClosure { code: f, env });
    Box::into_raw(b) as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64 {
    if clo_ptr == 0 { return 0; }
    let clo = unsafe { &*(clo_ptr as *const WirClosure) };

    // Prepend env to the provided args: callee ABI is (env, args...) -> i64
    let mut args: Vec<i64> = Vec::with_capacity(argc as usize + 1);
    args.push(clo.env);
    for i in 0..(argc as isize) {
        unsafe { args.push(*argv.offset(i)); }
    }

    unsafe { (clo.code)(args.as_ptr(), args.len()) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_alloc_words(n: i64) -> *mut i64 {
    if n <= 0 { return std::ptr::null_mut(); }
    let mut v = Vec::<i64>::with_capacity(n as usize);
    v.resize(n as usize, 0);
    let p = v.as_mut_ptr();
    std::mem::forget(v); // leak: fine for JIT demo
    p
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
