// src/jit.rs
//! jit.rs — Cranelift JIT for WIR (Cranelift 0.121.x compatible)

use ahash::AHashMap as HashMap;

use cranelift::prelude::*;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITModule};
use cranelift_module::{Linkage, Module as _};
use cranelift::codegen::ir::instructions::BlockArg;
use cranelift::prelude::{types, InstBuilder};

use std::sync::atomic::{AtomicU64, Ordering};
use std::cell::Cell;

use crate::gc::NAPALM_GC;

use crate::wir::{
    Constant, Function as WirFunction, Inst, IntBinOp, Value as WirValue, ValueDef, ValueId, FuncId,
};
use crate::runtime::{
    wir_obj_new, wir_is_str, napalm_yieldpoint,
    wir_obj_get_field, wir_obj_set_field, wir_obj_has_field, wir_obj_del_field,
    wir_obj_get_str, wir_obj_set_str, wir_obj_has_str, wir_obj_del_str,
    wir_memo_get, wir_memo_put,
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
        let mut jb = cranelift_jit::JITBuilder::new(cranelift_module::default_libcall_names()).expect("JITBuilder::new");

        unsafe extern "C" {
            fn wir_print_i64(x: i64) -> i64;
            fn wir_print_str(p: *const std::os::raw::c_char) -> i64;
            fn wir_make_closure(code_ptr: *const u8, env: i64) -> i64;
            fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64;
            fn wir_alloc_words(n: i64) -> *mut i64;
            fn wir_alloc_array(n: i64) -> i64;

            fn wir_add_slow(a: i64, b: i64) -> i64;
            fn wir_sub_slow(a: i64, b: i64) -> i64;
            fn wir_mul_slow(a: i64, b: i64) -> i64;

            fn wir_cmp_eq_slow(a: i64, b: i64) -> i64;
            fn wir_cmp_ne_slow(a: i64, b: i64) -> i64;
            fn wir_cmp_lt_slow(a: i64, b: i64) -> i64;
            fn wir_cmp_le_slow(a: i64, b: i64) -> i64;
            fn wir_cmp_gt_slow(a: i64, b: i64) -> i64;
            fn wir_cmp_ge_slow(a: i64, b: i64) -> i64;

            // arrays
            fn wir_array_new(len: i64) -> i64;
            fn wir_array_len(arr: i64) -> i64;
            fn wir_array_get(arr: i64, idx: i64) -> i64;
            fn wir_array_set(arr: i64, idx: i64, val: i64) -> i64;
            fn wir_array_set_len(arr: i64, new_len: i64) -> i64;

            fn wir_array_push(arr: i64, val: i64) -> i64;
            fn wir_array_pop(arr: i64) -> i64;
            fn wir_array_shift(arr: i64) -> i64;
            fn wir_array_unshift(arr: i64, val: i64) -> i64;

            fn wir_array_slice(arr: i64, start: i64, end: i64) -> i64;
            fn wir_array_map(arr: i64, fun_ptr: i64) -> i64;
            fn wir_array_for_each(arr: i64, fun_ptr: i64) -> i64;
            fn wir_array_find(arr: i64, fun_ptr: i64) -> i64;
            fn wir_array_find_index(arr: i64, fun_ptr: i64) -> i64;
            fn wir_array_filter(arr: i64, fun_ptr: i64) -> i64;
            fn wir_array_reduce(arr: i64, fun_ptr: i64, has_init: i64, init: i64) -> i64;

            fn wir_array_fill(arr: i64, val: i64) -> i64;
            fn wir_array_copy(dst: i64, src: i64, len: i64) -> i64;

            fn wir_memo_get(fid: i64, key: i64, out_ptr: *mut i64) -> i64;
            fn wir_memo_put(fid: i64, key: i64, val: i64) -> i64;
        }

        // --- declare the object natives so we can take typed fn pointers ---
        unsafe extern "C" {
            fn wir_obj_new() -> i64;
            fn wir_is_str(v: i64) -> i64;

            fn napalm_yieldpoint() -> i64;

            fn wir_obj_get_field(obj: i64, field_id: i64) -> i64;
            fn wir_obj_set_field(obj: i64, field_id: i64, val: i64) -> i64;
            fn wir_obj_has_field(obj: i64, field_id: i64) -> i64;
            fn wir_obj_del_field(obj: i64, field_id: i64) -> i64;

            fn wir_obj_get_str(obj: i64, key: i64) -> i64;
            fn wir_obj_set_str(obj: i64, key: i64, val: i64) -> i64;
            fn wir_obj_has_str(obj: i64, key: i64) -> i64;
            fn wir_obj_del_str(obj: i64, key: i64) -> i64;
        }

        unsafe {
            jb.symbol("wir_print_i64", wir_print_i64 as *const extern "C" fn(i64) -> i64 as *const u8);
            jb.symbol("wir_print_str", wir_print_str as *const extern "C" fn(*const std::os::raw::c_char) -> i64 as *const u8);
            jb.symbol("wir_make_closure", wir_make_closure as *const extern "C" fn(*const u8, i64) -> i64 as *const u8);
            jb.symbol("wir_call_closure", wir_call_closure as *const extern "C" fn(i64, *const i64, i64) -> i64 as *const u8);
            jb.symbol("wir_alloc_words", wir_alloc_words as *const extern "C" fn(i64) -> *mut i64 as *const u8);
            jb.symbol("wir_alloc_array", wir_alloc_array as *const extern "C" fn(i64) -> i64 as *const u8);

            jb.symbol("wir_add_slow", wir_add_slow as *const extern "C" fn(i64,i64)->i64 as *const u8);
            jb.symbol("wir_sub_slow", wir_sub_slow as *const extern "C" fn(i64,i64)->i64 as *const u8);
            jb.symbol("wir_mul_slow", wir_mul_slow as *const extern "C" fn(i64,i64)->i64 as *const u8);

            jb.symbol("wir_cmp_eq_slow", wir_cmp_eq_slow as *const extern "C" fn(i64,i64)->i64 as *const u8);
            jb.symbol("wir_cmp_ne_slow", wir_cmp_ne_slow as *const extern "C" fn(i64,i64)->i64 as *const u8);
            jb.symbol("wir_cmp_lt_slow", wir_cmp_lt_slow as *const extern "C" fn(i64,i64)->i64 as *const u8);
            jb.symbol("wir_cmp_le_slow", wir_cmp_le_slow as *const extern "C" fn(i64,i64)->i64 as *const u8);
            jb.symbol("wir_cmp_gt_slow", wir_cmp_gt_slow as *const extern "C" fn(i64,i64)->i64 as *const u8);
            jb.symbol("wir_cmp_ge_slow", wir_cmp_ge_slow as *const extern "C" fn(i64,i64)->i64 as *const u8);

            jb.symbol("wir_array_new",       wir_array_new as *const extern "C" fn(i64) -> i64 as *const u8);
            jb.symbol("wir_array_len",       wir_array_len as *const extern "C" fn(i64) -> i64 as *const u8);
            jb.symbol("wir_array_get",       wir_array_get as *const extern "C" fn(i64, i64) -> i64 as *const u8);
            jb.symbol("wir_array_set",       wir_array_set as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8);
            jb.symbol("wir_array_set_len",   wir_array_set_len as *const extern "C" fn(i64, i64) -> i64 as *const u8);

            jb.symbol("wir_array_push",      wir_array_push as *const extern "C" fn(i64, i64) -> i64 as *const u8);
            jb.symbol("wir_array_pop",       wir_array_pop as *const extern "C" fn(i64) -> i64 as *const u8);
            jb.symbol("wir_array_shift",     wir_array_shift as *const extern "C" fn(i64) -> i64 as *const u8);
            jb.symbol("wir_array_unshift",   wir_array_unshift as *const extern "C" fn(i64, i64) -> i64 as *const u8);

            jb.symbol("wir_array_slice",     wir_array_slice as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8);
            jb.symbol("wir_array_map",       wir_array_map as *const extern "C" fn(i64, i64) -> i64 as *const u8);
            jb.symbol("wir_array_for_each",  wir_array_for_each as *const extern "C" fn(i64, i64) -> i64 as *const u8);
            jb.symbol("wir_array_find",      wir_array_find as *const extern "C" fn(i64, i64) -> i64 as *const u8);
            jb.symbol("wir_array_find_index",wir_array_find_index as *const extern "C" fn(i64, i64) -> i64 as *const u8);
            jb.symbol("wir_array_filter",    wir_array_filter as *const extern "C" fn(i64, i64) -> i64 as *const u8);
            jb.symbol("wir_array_reduce",    wir_array_reduce as *const extern "C" fn(i64, i64, i64, i64) -> i64 as *const u8);

            jb.symbol("wir_array_fill",      wir_array_fill as *const extern "C" fn(i64, i64) -> i64 as *const u8);
            jb.symbol("wir_array_copy",      wir_array_copy as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8);

            // ---- object natives: bind symbol names used by CallNative to real addresses ----
            jb.symbol(
                "wir_obj_new",
                wir_obj_new as *const extern "C" fn() -> i64 as *const u8,
            );
            jb.symbol("wir_is_str", wir_is_str as *const u8);

            jb.symbol(
                "wir_obj_get_field",
                wir_obj_get_field as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_obj_set_field",
                wir_obj_set_field as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_obj_has_field",
                wir_obj_has_field as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_obj_del_field",
                wir_obj_del_field as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );

            jb.symbol(
                "wir_obj_get_str",
                wir_obj_get_str as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_obj_set_str",
                wir_obj_set_str as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_obj_has_str",
                wir_obj_has_str as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_obj_del_str",
                wir_obj_del_str as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );

            jb.symbol(
                "napalm_yieldpoint",
                napalm_yieldpoint as *const extern "C" fn() -> i64 as *const u8,
            );

            jb.symbol("wir_memo_get", wir_memo_get as *const extern "C" fn(i64, i64, *mut i64) -> i64 as *const u8);
            jb.symbol("wir_memo_put", wir_memo_put as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8);
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
    /// Get an i64-typed code pointer for a compiled WIR function (`wir_f_<id>`).
    fn funptr_i64(&mut self, fb: &mut FunctionBuilder, fid: FuncId) -> cranelift::prelude::Value {
        use cranelift::prelude::*;

        let ptr_ty = self.module.target_config().pointer_type();

        // JIT-internal callee signature: (argv_ptr, argc) -> i64
        let mut sig = self.module.make_signature();
        sig.call_conv = self.module.isa().default_call_conv(); // IMPORTANT: native ABI
        sig.params.push(AbiParam::new(ptr_ty));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let sym = format!("wir_f_{}", fid.0);
        let func_id = self
            .module
            .declare_function(&sym, Linkage::Import, &sig)
            .expect("declare wir_f_*");
        let func_ref = self.module.declare_func_in_func(func_id, &mut fb.func);

        let addr = fb.ins().func_addr(ptr_ty, func_ref);

        // Normalize to i64 for our FFI.
        match ptr_ty {
            types::I64 => addr,
            types::I32 => fb.ins().uextend(types::I64, addr),
            _ => fb.ins().uextend(types::I64, addr),
        }
    }
}

impl JIT {
    #[inline(always)]
    fn ptr_ty(&self) -> types::Type {
        self.module.target_config().pointer_type()
    }

/// Indirect call to a JITed function by emitting `func_addr` and then `call_indirect`.
    pub fn call_funcref<'a>(
        &mut self,
        fb: &mut FunctionBuilder<'a>,
        func_id: cranelift_module::FuncId,
        set_sig: impl FnOnce(&mut Signature),
        args: &[Value],
    ) -> Result<Vec<Value>, String> {
        let ptr_ty = self.ptr_ty();

        // Get a FuncRef and materialize its absolute address at runtime.
        let func_ref = self.module.declare_func_in_func(func_id, &mut fb.func);
        let fnptr = fb.ins().func_addr(ptr_ty, func_ref);

        // Signature MUST match how wir_f_* were defined: native/default CC.
        let mut sig = self.module.make_signature();
        sig.call_conv = self.module.isa().default_call_conv();
        set_sig(&mut sig);
        let sigref = fb.import_signature(sig);

        let call = fb.ins().call_indirect(sigref, fnptr, args);
        Ok(fb.inst_results(call).to_vec())
    }
}

impl JIT {
    /// Call a host/imported function via an *indirect* call.
    fn call_import<'a>(
        &mut self,
        fb: &mut cranelift_frontend::FunctionBuilder<'a>,
        name: &str,
        build_sig: impl FnOnce(&mut cranelift::prelude::Signature),
        args: &[cranelift::prelude::Value],
    ) -> Result<cranelift::prelude::Value, String> {
        use cranelift::prelude::*;
        use cranelift_module::Linkage;

        let ptr_ty = self.module.target_config().pointer_type();

        // Build the callee signature and import it into the current function.
        let mut sig = self.module.make_signature();
        sig.call_conv = self.module.isa().default_call_conv(); // IMPORTANT
        build_sig(&mut sig);
        let sigref = fb.import_signature(sig.clone());

        // Declare the external symbol, get a FuncRef for this function body.
        let func_id = self
            .module
            .declare_function(name, Linkage::Import, &sig)
            .map_err(|e| e.to_string())?;
        let func_ref = self.module.declare_func_in_func(func_id, &mut fb.func);

        // Get a pointer to the callee, then *indirect* call through that pointer.
        let fptr = fb.ins().func_addr(ptr_ty, func_ref);
        let call = fb.ins().call_indirect(sigref, fptr, args);
        Ok(fb.inst_results(call)[0])
    }
}

impl JIT {
    pub fn compile(&mut self, fun: &WirFunction) -> Result<JitFnPtr, String> {
        use cranelift::prelude::*;
        use cranelift::prelude::{AbiParam, FunctionBuilder};
        use cranelift::prelude::types;
        use cranelift_module::{Linkage, Module};

        let fun_ir: &WirFunction = fun;

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

        ctx.func.signature.call_conv = self.module.isa().default_call_conv();

        #[cfg(debug_assertions)] {
            eprintln!(
                "[JIT] compile wir_f_{}: {} nodes, {} values, {} params",
                fun.id.0,
                fun.nodes.len(),
                fun.values.len(),
                fun.sig.params.len()
            );
        }

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

                #[cfg(debug_assertions)] {
                    eprintln!("[JIT] prebind param {} -> ValueId#{:?}", i, i);
                }
            }

            // ---- linear pass
            for (bid, block) in fun.blocks.iter().enumerate() {
                #[cfg(debug_assertions)] {
                    eprintln!("  [block] visiting block #{bid} with {} insts", block.insts.len());
                }

                let cur_ebb = clif_of[bid];
                if bid != fun.entry.0 as usize {
                    fb.switch_to_block(cur_ebb);
                }

                let mut block_terminated = false;

                for nid in &block.insts {
                    if block_terminated || terminated { break; }

                    #[cfg(debug_assertions)] {
                        eprintln!("  [nodes] processing nid={:?}", nid);
                    }

                    let node = &fun.nodes[nid.0 as usize];
                    let res_count = node.results.len();

                    #[cfg(debug_assertions)] {
                        eprintln!(
                            "  [nodes] processing nid={:?} kind={:?} results={:?}",
                            nid, node.kind, node.results
                        );
                    }

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
                            let a = vmap.get_or_emit(*a, &mut fb, args_base, fun_ir);
                            let b = vmap.get_or_emit(*b, &mut fb, args_base, fun_ir);

                            // decode SMIs -> raw i64
                            let ra = fb.ins().sshr_imm(a, 1);
                            let rb = fb.ins().sshr_imm(b, 1);

                            // arithmetic/bitwise on raw
                            let raw = match op {
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

                            // re-encode to SMI: (raw << 1) | 1
                            let sh  = fb.ins().ishl_imm(raw, 1);
                            let smi = fb.ins().iadd_imm(sh, 1);

                            if res_count == 1 { vmap.bind(node.results[0], smi); }
                        }

                        Inst::CmpInt { kind, a, b } => {
                            let a = vmap.get_or_emit(*a, &mut fb, args_base, fun_ir);
                            let b = vmap.get_or_emit(*b, &mut fb, args_base, fun_ir);

                            // decode SMIs
                            let ra = fb.ins().sshr_imm(a, 1);
                            let rb = fb.ins().sshr_imm(b, 1);

                            // raw compare → 0/1 (NOT SMI)
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
                            let fast_res = fb.ins().select(cond, one, zero);

                            if res_count == 1 { vmap.bind(node.results[0], fast_res); }
                        }

                        // ---------------- Arrays (host runtime) ----------------
                        Inst::AllocArray { elem_hint: _, len } => {
                            use cranelift::prelude::{AbiParam, types};
                            let len_v = vmap.get_or_emit(*len, &mut fb, args_base, fun_ir);
                            let out   = self.call_import(
                                &mut fb,
                                "wir_array_new",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // len
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[len_v],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArrayLen(arr) => {
                            use cranelift::prelude::{AbiParam, types};
                            let a   = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_len",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // arr
                                    s.returns.push(AbiParam::new(types::I64)); // len (SMI)
                                },
                                &[a],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::LoadElem { arr, idx } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a   = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let i   = vmap.get_or_emit(*idx, &mut fb, args_base, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_get",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // arr
                                    s.params.push(AbiParam::new(types::I64)); // idx (SMI)
                                    s.returns.push(AbiParam::new(types::I64)); // value
                                },
                                &[a, i],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::StoreElem { arr, idx, val } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a   = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let i   = vmap.get_or_emit(*idx, &mut fb, args_base, fun_ir);
                            let vv  = vmap.get_or_emit(*val, &mut fb, args_base, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_set",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // arr
                                    s.params.push(AbiParam::new(types::I64)); // idx
                                    s.params.push(AbiParam::new(types::I64)); // val
                                    s.returns.push(AbiParam::new(types::I64)); // status / 0
                                },
                                &[a, i, vv],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArraySetLen { arr, new_len } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a   = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let nl  = vmap.get_or_emit(*new_len, &mut fb, args_base, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_set_len",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // arr
                                    s.params.push(AbiParam::new(types::I64)); // new_len (SMI)
                                    s.returns.push(AbiParam::new(types::I64)); // 0
                                },
                                &[a, nl],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArraySlice { arr, start, end } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr,   &mut fb, args_base, fun_ir);
                            let s = vmap.get_or_emit(*start, &mut fb, args_base, fun_ir);
                            let e = vmap.get_or_emit(*end,   &mut fb, args_base, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_slice",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // arr
                                    s.params.push(AbiParam::new(types::I64)); // start (SMI)
                                    s.params.push(AbiParam::new(types::I64)); // end (SMI)
                                    s.returns.push(AbiParam::new(types::I64)); // new arr
                                },
                                &[a, s, e],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArrayPush { arr, val } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let v = vmap.get_or_emit(*val, &mut fb, args_base, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_push",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64)); // new len (SMI)
                                },
                                &[a, v],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArrayPop(arr) => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_pop",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64)); // popped value or 0
                                },
                                &[a],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArrayShift(arr) => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_shift",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64)); // shifted value or 0
                                },
                                &[a],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArrayUnshift { arr, val } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let v = vmap.get_or_emit(*val, &mut fb, args_base, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_unshift",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64)); // new len (SMI)
                                },
                                &[a, v],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        // ---------------- Arrays (host runtime; FuncId → closure with env=0) ----------------
                        Inst::ArrayMap { func, arr } => {
                            use cranelift::prelude::{AbiParam, types};
                            let ptr_ty   = self.ptr_ty();
                            let code_ptr = self.funptr_i64(&mut fb, *func);      // wir_f_<id> address (i64)
                            let zero     = fb.ins().iconst(types::I64, 0);       // empty env
                            let clo      = self.call_import(&mut fb, "wir_make_closure", |s| {
                                s.params.push(AbiParam::new(ptr_ty));            // code_ptr
                                s.params.push(AbiParam::new(types::I64));        // env
                                s.returns.push(AbiParam::new(types::I64));       // closure*
                            }, &[code_ptr, zero])?;

                            let a   = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let out = self.call_import(&mut fb, "wir_array_map", |s| {
                                s.params.push(AbiParam::new(types::I64));        // arr
                                s.params.push(AbiParam::new(types::I64));        // clo
                                s.returns.push(AbiParam::new(types::I64));       // new arr
                            }, &[a, clo])?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArrayForEach { func, arr } => {
                            use cranelift::prelude::{AbiParam, types};
                            let ptr_ty   = self.ptr_ty();
                            let code_ptr = self.funptr_i64(&mut fb, *func);
                            let zero     = fb.ins().iconst(types::I64, 0);
                            let clo      = self.call_import(&mut fb, "wir_make_closure", |s| {
                                s.params.push(AbiParam::new(ptr_ty));
                                s.params.push(AbiParam::new(types::I64));
                                s.returns.push(AbiParam::new(types::I64));
                            }, &[code_ptr, zero])?;

                            let a   = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let out = self.call_import(&mut fb, "wir_array_for_each", |s| {
                                s.params.push(AbiParam::new(types::I64));
                                s.params.push(AbiParam::new(types::I64));
                                s.returns.push(AbiParam::new(types::I64));       // 0
                            }, &[a, clo])?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArrayFind { func, arr } => {
                            use cranelift::prelude::{AbiParam, types};
                            let ptr_ty   = self.ptr_ty();
                            let code_ptr = self.funptr_i64(&mut fb, *func);
                            let zero     = fb.ins().iconst(types::I64, 0);
                            let clo      = self.call_import(&mut fb, "wir_make_closure", |s| {
                                s.params.push(AbiParam::new(ptr_ty));
                                s.params.push(AbiParam::new(types::I64));
                                s.returns.push(AbiParam::new(types::I64));
                            }, &[code_ptr, zero])?;

                            let a   = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let out = self.call_import(&mut fb, "wir_array_find", |s| {
                                s.params.push(AbiParam::new(types::I64));
                                s.params.push(AbiParam::new(types::I64));
                                s.returns.push(AbiParam::new(types::I64));       // value or 0
                            }, &[a, clo])?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArrayFindIndex { func, arr } => {
                            use cranelift::prelude::{AbiParam, types};
                            let ptr_ty   = self.ptr_ty();
                            let code_ptr = self.funptr_i64(&mut fb, *func);
                            let zero     = fb.ins().iconst(types::I64, 0);
                            let clo      = self.call_import(&mut fb, "wir_make_closure", |s| {
                                s.params.push(AbiParam::new(ptr_ty));
                                s.params.push(AbiParam::new(types::I64));
                                s.returns.push(AbiParam::new(types::I64));
                            }, &[code_ptr, zero])?;

                            let a   = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let out = self.call_import(&mut fb, "wir_array_find_index", |s| {
                                s.params.push(AbiParam::new(types::I64));
                                s.params.push(AbiParam::new(types::I64));
                                s.returns.push(AbiParam::new(types::I64));       // SMI index or smi(-1)
                            }, &[a, clo])?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArrayFilter { func, arr } => {
                            use cranelift::prelude::{AbiParam, types};
                            let ptr_ty   = self.ptr_ty();
                            let code_ptr = self.funptr_i64(&mut fb, *func);
                            let zero     = fb.ins().iconst(types::I64, 0);
                            let clo      = self.call_import(&mut fb, "wir_make_closure", |s| {
                                s.params.push(AbiParam::new(ptr_ty));
                                s.params.push(AbiParam::new(types::I64));
                                s.returns.push(AbiParam::new(types::I64));
                            }, &[code_ptr, zero])?;

                            let a   = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let out = self.call_import(&mut fb, "wir_array_filter", |s| {
                                s.params.push(AbiParam::new(types::I64));
                                s.params.push(AbiParam::new(types::I64));
                                s.returns.push(AbiParam::new(types::I64));       // new arr
                            }, &[a, clo])?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArrayReduce { func, init, arr } => {
                            use cranelift::prelude::{AbiParam, types, IntCC};
                            let ptr_ty   = self.ptr_ty();
                            let code_ptr = self.funptr_i64(&mut fb, *func);
                            let zero     = fb.ins().iconst(types::I64, 0);
                            let clo      = self.call_import(&mut fb, "wir_make_closure", |s| {
                                s.params.push(AbiParam::new(ptr_ty));
                                s.params.push(AbiParam::new(types::I64));
                                s.returns.push(AbiParam::new(types::I64));
                            }, &[code_ptr, zero])?;

                            let a       = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let init_v  = vmap.get_or_emit(*init, &mut fb, args_base, fun_ir);
                            let one     = fb.ins().iconst(types::I64, 1);
                            let z64     = fb.ins().iconst(types::I64, 0);
                            let has_init= {
                                let c = fb.ins().icmp(IntCC::NotEqual, init_v, z64);
                                fb.ins().select(c, one, z64)
                            };

                            let out = self.call_import(&mut fb, "wir_array_reduce", |s| {
                                s.params.push(AbiParam::new(types::I64));        // arr
                                s.params.push(AbiParam::new(types::I64));        // clo
                                s.params.push(AbiParam::new(types::I64));        // has_init
                                s.params.push(AbiParam::new(types::I64));        // init
                                s.returns.push(AbiParam::new(types::I64));       // result
                            }, &[a, clo, has_init, init_v])?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArrayFill { arr, val } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, args_base, fun_ir);
                            let v = vmap.get_or_emit(*val, &mut fb, args_base, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_fill",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // arr
                                    s.params.push(AbiParam::new(types::I64)); // val
                                    s.returns.push(AbiParam::new(types::I64)); // 0
                                },
                                &[a, v],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::ArrayCopy { dst, src, len } => {
                            use cranelift::prelude::{AbiParam, types};
                            let d = vmap.get_or_emit(*dst, &mut fb, args_base, fun_ir);
                            let s = vmap.get_or_emit(*src, &mut fb, args_base, fun_ir);
                            let n = vmap.get_or_emit(*len, &mut fb, args_base, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_copy",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // dst
                                    s.params.push(AbiParam::new(types::I64)); // src
                                    s.params.push(AbiParam::new(types::I64)); // len (SMI)
                                    s.returns.push(AbiParam::new(types::I64)); // 0
                                },
                                &[d, s, n],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        // ---------------- Closures (host trampoline calls) ----------------
                        Inst::MakeClosure { callee, env } => {
                            use cranelift::prelude::{AbiParam, types};

                            // JIT function code ptr for wir_f_<id> (direct within code heap).
                            let ptr_ty   = self.module.target_config().pointer_type();
                            let mut jsig = self.module.make_signature();
                            jsig.params.push(AbiParam::new(ptr_ty));
                            jsig.params.push(AbiParam::new(types::I64));
                            jsig.returns.push(AbiParam::new(types::I64));
                            let sym      = format!("wir_f_{}", callee.0);
                            let fid      = self.module.declare_function(&sym, cranelift_module::Linkage::Import, &jsig)
                                .map_err(|e| e.to_string())?;
                            let fref     = self.module.declare_func_in_func(fid, &mut fb.func);
                            let code_ptr = fb.ins().func_addr(ptr_ty, fref);

                            // env value
                            let env_v = vmap.get_or_emit(*env, &mut fb, args_base, fun_ir);

                            // wir_make_closure(code_ptr, env) — call by address
                            let out = self.call_import(
                                &mut fb,
                                "wir_make_closure",
                                |s| {
                                    s.params.push(AbiParam::new(ptr_ty));     // code_ptr
                                    s.params.push(AbiParam::new(types::I64)); // env
                                    s.returns.push(AbiParam::new(types::I64)); // closure ptr
                                },
                                &[code_ptr, env_v],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::CallClosure { fun: fun_val, args, .. } => {
                            use cranelift::prelude::{AbiParam, types};
                            use cranelift::codegen::ir::{StackSlotData, StackSlotKind};

                            // Pack args on stack (8-byte slots).
                            let n: u32 = args.len() as u32;
                            let slot = fb.create_sized_stack_slot(StackSlotData::new(
                                StackSlotKind::ExplicitSlot,
                                n * 8,
                                3,
                            ));
                            for (i, a) in args.iter().enumerate() {
                                let v = vmap.get_or_emit(*a, &mut fb, args_base, fun_ir);
                                fb.ins().stack_store(v, slot, (i as i32) * 8);
                            }
                            let ptr_ty  = self.module.target_config().pointer_type();
                            let argv    = fb.ins().stack_addr(ptr_ty, slot, 0);
                            let argc    = fb.ins().iconst(types::I64, n as i64);
                            let clo_ptr = vmap.get_or_emit(*fun_val, &mut fb, args_base, fun_ir);

                            // wir_call_closure(clo, argv, argc) — indirect
                            let out = self.call_import(
                                &mut fb,
                                "wir_call_closure",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // closure
                                    s.params.push(AbiParam::new(ptr_ty));     // argv*
                                    s.params.push(AbiParam::new(types::I64)); // argc
                                    s.returns.push(AbiParam::new(types::I64)); // result
                                },
                                &[clo_ptr, argv, argc],
                            )?;
                            if res_count >= 1 { vmap.bind(node.results[0], out); }
                        }

                        // ---------------- Native calls (host) ----------------
                        Inst::CallNative { name, args, .. } => {
                            use cranelift::prelude::{AbiParam, types};

                            // We route "wir_print_str" via wir_print_i64 (keeps all args i64).
                            let import_name: &str = if name == "wir_print_str" {
                                "wir_print_i64"
                            } else {
                                name
                            };

                            // Gather argv values first.
                            let mut argv = Vec::with_capacity(args.len());
                            for a in args {
                                argv.push(vmap.get_or_emit(*a, &mut fb, args_base, fun_ir));
                            }

                            // Build signature: (i64, i64, ...) -> i64
                            let out = self.call_import(
                                &mut fb,
                                import_name,
                                |s| {
                                    for _ in 0..argv.len() { s.params.push(AbiParam::new(types::I64)); }
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &argv,
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        // ---------------- Direct calls ----------------
                        Inst::CallDirect { callee, args, .. } => {
                            use cranelift::prelude::{AbiParam, types};
                            use cranelift::codegen::ir::{StackSlotData, StackSlotKind};

                            // Signature for wir_f_* must match how we define them (argv*, argc) -> i64
                            let mut sig = self.module.make_signature();
                            sig.call_conv = self.module.isa().default_call_conv();
                            sig.params.push(AbiParam::new(ptr_ty));     // argv*
                            sig.params.push(AbiParam::new(types::I64)); // argc
                            sig.returns.push(AbiParam::new(types::I64));

                            let sym = format!("wir_f_{}", callee.0);
                            let func_id = self
                                .module
                                .declare_function(&sym, Linkage::Import, &sig)
                                .map_err(|e| e.to_string())?;

                            // Marshal args into a stack argv buffer
                            let n = args.len();
                            let size_bytes: u32 = (n as u32) * 8;
                            let slot = fb.create_sized_stack_slot(StackSlotData::new(
                                StackSlotKind::ExplicitSlot, size_bytes, 0,
                            ));
                            for (i, a) in args.iter().enumerate() {
                                let v = vmap.get_or_emit(*a, &mut fb, args_base, fun_ir);
                                fb.ins().stack_store(v, slot, (i as i32) * 8);
                            }
                            let argv_ptr = fb.ins().stack_addr(ptr_ty, slot, 0);
                            let argc     = fb.ins().iconst(types::I64, n as i64);

                            // Indirect call through absolute address (avoids 26-bit range issue)
                            let outs = self.call_funcref(
                                &mut fb,
                                func_id,
                                |s| {
                                    // IMPORTANT: do not touch `self` here.
                                    // call_funcref itself already sets `s.call_conv = default_call_conv()`.
                                    s.params.push(AbiParam::new(ptr_ty));     // argv*
                                    s.params.push(AbiParam::new(types::I64)); // argc
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[argv_ptr, argc],
                            )?;

                            if res_count >= 1 {
                                vmap.bind(node.results[0], outs[0]);
                            }
                        }

                        // Engine has the ability to memoize functions, it is implemented natively
                        Inst::CallDirectMemoized { callee, args } => {
                            use cranelift::prelude::{AbiParam, types, IntCC};
                            use cranelift::codegen::ir::{StackSlotData, StackSlotKind};

                            let ptr_ty = self.ptr_ty();

                            // We only memoize 1-arg calls (design choice). If not 1, just fall back to a plain call.
                            if args.len() != 1 {
                                // === same lowering as CallDirect ===
                                let mut sig = self.module.make_signature();
                                sig.call_conv = self.module.isa().default_call_conv();
                                sig.params.push(AbiParam::new(ptr_ty));
                                sig.params.push(AbiParam::new(types::I64));
                                sig.returns.push(AbiParam::new(types::I64));

                                let sym = format!("wir_f_{}", callee.0);
                                let func_id = self.module.declare_function(&sym, Linkage::Import, &sig)
                                    .map_err(|e| e.to_string())?;

                                let n = args.len();
                                let size_bytes: u32 = (n as u32) * 8;
                                let slot = fb.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size_bytes, 0));
                                for (i, a) in args.iter().enumerate() {
                                    let v = vmap.get_or_emit(*a, &mut fb, args_base, fun_ir);
                                    fb.ins().stack_store(v, slot, (i as i32) * 8);
                                }
                                let argv_ptr = fb.ins().stack_addr(ptr_ty, slot, 0);
                                let argc     = fb.ins().iconst(types::I64, n as i64);

                                let outs = self.call_funcref(
                                    &mut fb,
                                    func_id,
                                    |s| {
                                        s.params.push(AbiParam::new(ptr_ty));
                                        s.params.push(AbiParam::new(types::I64));
                                        s.returns.push(AbiParam::new(types::I64));
                                    },
                                    &[argv_ptr, argc],
                                )?;
                                if res_count >= 1 { vmap.bind(node.results[0], outs[0]); }
                                continue;
                            }

                            // ----- Memoized 1-arg path -----
                            let key = vmap.get_or_emit(args[0], &mut fb, args_base, fun_ir);
                            let fid = fb.ins().iconst(types::I64, callee.0 as i64);

                            // out-slot to receive cached value
                            let out_slot = fb.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 8, 0));
                            let out_ptr  = fb.ins().stack_addr(self.ptr_ty(), out_slot, 0);

                            // hoist the pointer type out so the closure doesn't touch `self`
                            let ptr_ty_local = self.ptr_ty();

                            // call wir_memo_get(fid, key, &out)
                            let found = self.call_import(
                                &mut fb,
                                "wir_memo_get",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64));      // fid
                                    s.params.push(AbiParam::new(types::I64));      // key
                                    s.params.push(AbiParam::new(ptr_ty_local));    // out*
                                    s.returns.push(AbiParam::new(types::I64));     // 0/1
                                },
                                &[fid, key, out_ptr],
                            )?;

                            // Control-flow split: hit vs miss
                            let bb_hit  = fb.create_block();
                            let bb_miss = fb.create_block();
                            let bb_join = fb.create_block();

                            // Join block gets a single param: the call result
                            let res_phi = fb.append_block_param(bb_join, types::I64);

                            let zero = fb.ins().iconst(types::I64, 0);
                            let is_hit = fb.ins().icmp(IntCC::NotEqual, found, zero);
                            fb.ins().brif(is_hit, bb_hit, &[] as &[BlockArg], bb_miss, &[] as &[BlockArg]);

                            // ---- HIT: load cached value, jump join
                            fb.switch_to_block(bb_hit);
                            let cached = fb.ins().load(types::I64, MemFlags::trusted(), out_ptr, 0);
                            let mut hit_args = vec![BlockArg::from(cached)];
                            fb.ins().jump(bb_join, &hit_args[..]);

                            // ---- MISS: call callee, memo_put, jump join
                            fb.switch_to_block(bb_miss);
                            // marshal argv of length 1
                            let slot = fb.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 8, 0));
                            fb.ins().stack_store(key, slot, 0);
                            let argv_ptr = fb.ins().stack_addr(ptr_ty, slot, 0);
                            let argc     = fb.ins().iconst(types::I64, 1);

                            // signature like CallDirect
                            let mut sig = self.module.make_signature();
                            sig.call_conv = self.module.isa().default_call_conv();
                            sig.params.push(AbiParam::new(ptr_ty));
                            sig.params.push(AbiParam::new(types::I64));
                            sig.returns.push(AbiParam::new(types::I64));

                            let sym = format!("wir_f_{}", callee.0);
                            let func_id = self
                                .module
                                .declare_function(&sym, Linkage::Import, &sig)
                                .map_err(|e| e.to_string())?;

                            let outs = self.call_funcref(
                                &mut fb,
                                func_id,
                                |s| {
                                    s.params.push(AbiParam::new(ptr_ty));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[argv_ptr, argc],
                            )?;
                            let retv = outs[0];

                            // wir_memo_put(fid, key, retv)
                            let _ = self.call_import(
                                &mut fb,
                                "wir_memo_put",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // fid
                                    s.params.push(AbiParam::new(types::I64)); // key
                                    s.params.push(AbiParam::new(types::I64)); // val
                                    s.returns.push(AbiParam::new(types::I64)); // 0
                                },
                                &[fid, key, retv],
                            )?;

                            let mut miss_args = vec![BlockArg::from(retv)];
                            fb.ins().jump(bb_join, &miss_args[..]);

                            // ---- JOIN: bind result
                            fb.switch_to_block(bb_join);
                            if res_count >= 1 { vmap.bind(node.results[0], res_phi); }
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

                        Inst::LoadField { obj, field, .. } => {
                            use cranelift::prelude::{AbiParam, types};

                            let o = vmap.get_or_emit(*obj, &mut fb, args_base, fun_ir);

                            // field id -> SMI
                            let raw  = fb.ins().iconst(types::I64, field.0 as i64);
                            let sh   = fb.ins().ishl_imm(raw, 1);
                            let fid  = fb.ins().iadd_imm(sh, 1);

                            let out = self.call_import(
                                &mut fb,
                                "wir_obj_get_field",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // obj
                                    s.params.push(AbiParam::new(types::I64)); // field_id (SMI)
                                    s.returns.push(AbiParam::new(types::I64)); // value or 0
                                },
                                &[o, fid],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        Inst::StoreField { obj, field, val, .. } => {
                            use cranelift::prelude::{AbiParam, types};

                            let o = vmap.get_or_emit(*obj,  &mut fb, args_base, fun_ir);
                            let v = vmap.get_or_emit(*val,  &mut fb, args_base, fun_ir);

                            // field id -> SMI
                            let raw  = fb.ins().iconst(types::I64, field.0 as i64);
                            let sh   = fb.ins().ishl_imm(raw, 1);
                            let fid  = fb.ins().iadd_imm(sh, 1);

                            let out = self.call_import(
                                &mut fb,
                                "wir_obj_set_field",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // obj
                                    s.params.push(AbiParam::new(types::I64)); // field_id (SMI)
                                    s.params.push(AbiParam::new(types::I64)); // val
                                    s.returns.push(AbiParam::new(types::I64)); // status / 0 (ignored)
                                },
                                &[o, fid, v],
                            )?;
                            if res_count == 1 { vmap.bind(node.results[0], out); }
                        }

                        // ---------------- Effects / markers ----------------
                        Inst::EffectEntry => {
                            let token = fb.ins().iconst(ptr_ty, 0);
                            if res_count == 1 { vmap.bind(node.results[0], token); }
                        }

                        Inst::Safepoint => {
                            use cranelift::prelude::{AbiParam, types};
                            let _ = self.call_import(
                                &mut fb,
                                "napalm_yieldpoint",
                                |s| {
                                    // () -> i64 (ignored)
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[],
                            )?;
                        }

                        Inst::GuardBounds { idx, len, .. } => {
                            let i_smi = vmap.get_or_emit(*idx, &mut fb, args_base, fun_ir);
                            let n_smi = vmap.get_or_emit(*len, &mut fb, args_base, fun_ir);

                            let i = fb.ins().sshr_imm(i_smi, 1); // raw idx
                            let n = fb.ins().sshr_imm(n_smi, 1); // raw len

                            let zero = fb.ins().iconst(types::I64, 0);
                            let ge0  = fb.ins().icmp(IntCC::SignedGreaterThanOrEqual, i, zero);
                            let lt   = fb.ins().icmp(IntCC::SignedLessThan, i, n);
                            let ok   = fb.ins().band(ge0, lt);

                            let cont = fb.create_block();
                            let bad  = fb.create_block();
                            fb.ins().brif(ok, cont, &[] as &[BlockArg], bad, &[] as &[BlockArg]);

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
                let p = self.alloc_boxed_str(s);
                fb.ins().iconst(types::I64, p)
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

    fn alloc_boxed_str(&mut self, s: &str) -> i64 {
        use crate::value::{BoxedStr, ObjHeader, TAG_STRING};

        // Keep UTF-8 bytes alive using CString (or you can keep raw Vec<u8>).
        let c = std::ffi::CString::new(s).unwrap();
        let data = c.as_ptr() as *const u8;
        let len  = s.as_bytes().len();

        // Store the CString so its memory isn't freed.
        self.keep_alive.push(c);

        // Box the string object itself
        let obj = Box::new(BoxedStr {
            hdr: ObjHeader { tag: TAG_STRING, aux: 0 },
            len,
            data,
        });
        let ptr = Box::into_raw(obj) as *mut u8;

        // Keep the object alive (until GC arrives)
        self.heap_keep_alive.push(ptr);

        ptr as i64  // even pointer => “heap object”
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

        #[cfg(debug_assertions)] {
            eprintln!(
                "[JIT][warn] get_or_load fallback -> 0 for {:?} (def={:?})",
                id, vdef
            );
        }

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

        #[cfg(debug_assertions)] {
            eprintln!("[JIT][warn] get_or_emit fallback -> 0 for {:?} (def={:?})", id, fun.values[id.0 as usize].def);
        }

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
    use std::slice;

    if is_imm(v) {
        #[cfg(debug_assertions)] {
            eprintln!("{}", smi_to_i64(v));
        }
        return 0;
    }

    if v == NULL {
        #[cfg(debug_assertions)] {
            eprintln!("NULL");
        }
        return 0;
    }

    unsafe {
        let hdr = &*(v as *const ObjHeader);
        match hdr.tag {
            TAG_BOXED_F64 => {
                let b = &*(v as *const BoxedF64);
                println!("{}", b.val);
            }
            TAG_STRING => {
                let s = &*(v as *const BoxedStr);
                let bytes = slice::from_raw_parts(s.data, s.len);
                println!("{}", String::from_utf8_lossy(bytes));
            }
            _ => {
                // Unknown object type for now
                println!("{:#x}", v as u64);
            }
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

#[unsafe(no_mangle)]
pub extern "C" fn wir_alloc_array(n: i64) -> i64 {
    use std::ptr::{write_unaligned};
    use crate::value::{ObjHeader, TAG_ARRAY, ARRAY_LEN_OFFSET, ARRAY_DATA_OFFSET};

    if n <= 0 {
        return 0; // null for degenerate
    }

    let total = (ARRAY_DATA_OFFSET as usize) + (n as usize) * 8;
    // Zero-initialized backing memory; we’ll leak it (fine until GC arrives).
    let mut buf = vec![0u8; total];
    let p = buf.as_mut_ptr();
    std::mem::forget(buf);

    unsafe {
        // header
        let hdr_ptr = p as *mut ObjHeader;
        (*hdr_ptr).tag = TAG_ARRAY;
        (*hdr_ptr).aux = 0;

        // len
        let len_ptr = p.add(ARRAY_LEN_OFFSET as usize) as *mut i64;
        write_unaligned(len_ptr, n);

        // data is already zeroed
    }

    p as i64 // even pointer => “heap object”
}

// ----- SMI and boxed f64 handling -----

#[inline(always)]
fn smi_encode(x: i64) -> i64 { (x << 1) | 1 }

#[unsafe(no_mangle)]
pub extern "C" fn wir_box_f64_runtime(bits: u64) -> i64 {
    use crate::value::{BoxedF64, ObjHeader, TAG_BOXED_F64};
    let x = f64::from_bits(bits);
    let obj = Box::new(BoxedF64 { hdr: ObjHeader { tag: TAG_BOXED_F64, aux: 0 }, val: x });
    Box::into_raw(obj) as i64
}

#[inline(always)]
fn val_to_f64(v: i64) -> Result<f64, &'static str> {
    use crate::value::*;
    if is_imm(v) {
        Ok(smi_to_i64(v) as f64)
    } else {
        if v == NULL { return Err("null is not a number"); }
        unsafe {
            let hdr = &*(v as *const ObjHeader);
            if hdr.tag == TAG_BOXED_F64 {
                let bf = &*(v as *const BoxedF64);
                Ok(bf.val)
            } else {
                Err("not a number")
            }
        }
    }
}

#[inline(always)]
fn f64_to_val(x: f64) -> i64 {
    let xi = x as i64;
    if (xi as f64) == x {
        smi_encode(xi)
    } else {
        wir_box_f64_runtime(x.to_bits())
    }
}

// ----- arithmetic slow paths -----
#[unsafe(no_mangle)]
pub extern "C" fn wir_add_slow(a: i64, b: i64) -> i64 {
    let af = val_to_f64(a).expect("TypeError: add lhs not a number");
    let bf = val_to_f64(b).expect("TypeError: add rhs not a number");
    f64_to_val(af + bf)
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_sub_slow(a: i64, b: i64) -> i64 {
    let af = val_to_f64(a).expect("TypeError: sub lhs not a number");
    let bf = val_to_f64(b).expect("TypeError: sub rhs not a number");
    f64_to_val(af - bf)
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_mul_slow(a: i64, b: i64) -> i64 {
    let af = val_to_f64(a).expect("TypeError: mul lhs not a number");
    let bf = val_to_f64(b).expect("TypeError: mul rhs not a number");
    f64_to_val(af * bf)
}

// ----- comparison slow paths (return raw 0/1) -----
#[inline(always)] fn b2i(b: bool) -> i64 { if b { 1 } else { 0 } }

#[unsafe(no_mangle)]
pub extern "C" fn wir_cmp_eq_slow(a: i64, b: i64) -> i64 {
    let af = val_to_f64(a).expect("TypeError: == lhs");
    let bf = val_to_f64(b).expect("TypeError: == rhs");
    b2i(af == bf)
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_cmp_ne_slow(a: i64, b: i64) -> i64 {
    let af = val_to_f64(a).expect("TypeError: != lhs");
    let bf = val_to_f64(b).expect("TypeError: != rhs");
    b2i(af != bf)
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_cmp_lt_slow(a: i64, b: i64) -> i64 {
    let af = val_to_f64(a).expect("TypeError: < lhs");
    let bf = val_to_f64(b).expect("TypeError: < rhs");
    b2i(af < bf)
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_cmp_le_slow(a: i64, b: i64) -> i64 {
    let af = val_to_f64(a).expect("TypeError: <= lhs");
    let bf = val_to_f64(b).expect("TypeError: <= rhs");
    b2i(af <= bf)
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_cmp_gt_slow(a: i64, b: i64) -> i64 {
    let af = val_to_f64(a).expect("TypeError: > lhs");
    let bf = val_to_f64(b).expect("TypeError: > rhs");
    b2i(af > bf)
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_cmp_ge_slow(a: i64, b: i64) -> i64 {
    let af = val_to_f64(a).expect("TypeError: >= lhs");
    let bf = val_to_f64(b).expect("TypeError: >= rhs");
    b2i(af >= bf)
}

// ---------------------
// Naive Array Runtime
// ---------------------

#[repr(C)]
struct WirArray {
    buf: Vec<i64>,
}

fn smi(v: i64) -> i64 { (v << 1) | 1 }
fn smi_to_i64_wrapped(v: i64) -> i64 { v >> 1 } // arithmetic shift; matches earlier SMI scheme

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_new(len: i64) -> i64 {
    let n = smi_to_i64_wrapped(len).max(0) as usize;
    let arr = Box::new(WirArray { buf: vec![0; n] });
    Box::into_raw(arr) as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_len(arr: i64) -> i64 {
    if arr == 0 { return smi(0); }
    let a = unsafe { &*(arr as *const WirArray) };
    smi(a.buf.len() as i64)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_get(arr: i64, idx: i64) -> i64 {
    if arr == 0 { return 0; }
    let i = smi_to_i64_wrapped(idx);
    if i < 0 { return 0; }
    let a = unsafe { &*(arr as *const WirArray) };
    a.buf.get(i as usize).copied().unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_set(arr: i64, idx: i64, val: i64) -> i64 {
    if arr == 0 { return 0; }
    let i = smi_to_i64_wrapped(idx);
    if i < 0 { return 0; }
    let a = unsafe { &mut *(arr as *mut WirArray) };
    let iu = i as usize;
    if iu >= a.buf.len() {
        a.buf.resize(iu + 1, 0);
    }
    // slot ptr before write
    let slot = a.buf.as_mut_ptr().wrapping_add(iu);
    a.buf[iu] = val;
    unsafe { NAPALM_GC.post_write_barrier(arr as *mut u8, slot, val) };
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_set_len(arr: i64, new_len: i64) -> i64 {
    if arr == 0 { return 0; }
    let n = smi_to_i64_wrapped(new_len).max(0) as usize;
    let a = unsafe { &mut *(arr as *mut WirArray) };
    a.buf.resize(n, 0);
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_push(arr: i64, val: i64) -> i64 {
    if arr == 0 { return smi(0); }
    let a = unsafe { &mut *(arr as *mut WirArray) };
    a.buf.push(val);
    let last = a.buf.len() - 1;
    let slot = a.buf.as_mut_ptr().wrapping_add(last);
    unsafe { NAPALM_GC.post_write_barrier(arr as *mut u8, slot, val) };
    smi(a.buf.len() as i64)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_pop(arr: i64) -> i64 {
    if arr == 0 { return 0; }
    let a = unsafe { &mut *(arr as *mut WirArray) };
    a.buf.pop().unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_shift(arr: i64) -> i64 {
    if arr == 0 { return 0; }
    let a = unsafe { &mut *(arr as *mut WirArray) };
    if a.buf.is_empty() { return 0; }
    let v = a.buf.remove(0);
    v
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_unshift(arr: i64, val: i64) -> i64 {
    if arr == 0 { return smi(0); }
    let a = unsafe { &mut *(arr as *mut WirArray) };
    a.buf.insert(0, val);
    // new element lives at index 0
    let slot = a.buf.as_mut_ptr();
    unsafe { NAPALM_GC.post_write_barrier(arr as *mut u8, slot, val) };
    smi(a.buf.len() as i64)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_slice(arr: i64, start: i64, end: i64) -> i64 {
    if arr == 0 { return 0; }
    let a = unsafe { &*(arr as *const WirArray) };
    let n = a.buf.len() as i64;
    let s = smi_to_i64_wrapped(start).clamp(0, n) as usize;
    let e = smi_to_i64_wrapped(end).clamp(s as i64, n) as usize;
    let mut out = Vec::with_capacity(e - s);
    out.extend_from_slice(&a.buf[s..e]);
    let b = Box::new(WirArray { buf: out });
    Box::into_raw(b) as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_map(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 { return 0; }
    let a = unsafe { &*(arr as *const WirArray) };
    let mut out = Vec::with_capacity(a.buf.len());
    for &x in &a.buf {
        let args = [x];
        let y = wir_call_closure(clo_ptr, args.as_ptr(), 1);
        out.push(y);
        NAPALM_GC.maybe_safepoint();
    }
    let b = Box::new(WirArray { buf: out });
    Box::into_raw(b) as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_for_each(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 { return 0; }
    let a = unsafe { &*(arr as *const WirArray) };
    for &x in &a.buf {
        let args = [x];
        let _ = wir_call_closure(clo_ptr, args.as_ptr(), 1);
        NAPALM_GC.maybe_safepoint();
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_find(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 { return 0; }
    let a = unsafe { &*(arr as *const WirArray) };
    for &x in &a.buf {
        let args = [x];
        let ok = wir_call_closure(clo_ptr, args.as_ptr(), 1);
        if ok != 0 { return x; }
        NAPALM_GC.maybe_safepoint();
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_find_index(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 { return smi(-1); }
    let a = unsafe { &*(arr as *const WirArray) };
    for (i, &x) in a.buf.iter().enumerate() {
        let args = [x];
        let ok = wir_call_closure(clo_ptr, args.as_ptr(), 1);
        if ok != 0 { return smi(i as i64); }
        NAPALM_GC.maybe_safepoint();
    }
    smi(-1)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_filter(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 { return 0; }
    let a = unsafe { &*(arr as *const WirArray) };
    let mut out = Vec::new();
    for &x in &a.buf {
        let args = [x];
        let ok = wir_call_closure(clo_ptr, args.as_ptr(), 1);
        if ok != 0 { out.push(x); }
        NAPALM_GC.maybe_safepoint();
    }
    let b = Box::new(WirArray { buf: out });
    Box::into_raw(b) as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_reduce(arr: i64, clo_ptr: i64, has_init: i64, init: i64) -> i64 {
    if arr == 0 { return 0; }
    let a = unsafe { &*(arr as *const WirArray) };
    if a.buf.is_empty() {
        return if has_init != 0 { init } else { 0 };
    }
    let mut it = a.buf.iter().copied();
    let mut acc = if has_init != 0 { init } else { it.next().unwrap() };
    for x in it {
        let args = [acc, x];
        acc = wir_call_closure(clo_ptr, args.as_ptr(), 2);
        NAPALM_GC.maybe_safepoint();
    }
    acc
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_fill(arr: i64, val: i64) -> i64 {
    if arr == 0 { return 0; }
    let a = unsafe { &mut *(arr as *mut WirArray) };
    let base = a.buf.as_mut_ptr();
    for i in 0..a.buf.len() {
        unsafe {
            let slot = base.add(i);
            *slot = val;
            NAPALM_GC.post_write_barrier(arr as *mut u8, slot, val);
            NAPALM_GC.maybe_safepoint();
        }
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_copy(dst: i64, src: i64, len: i64) -> i64 {
    if dst == 0 || src == 0 { return 0; }
    let d = unsafe { &mut *(dst as *mut WirArray) };
    let s = unsafe { &*(src as *const WirArray) };
    let n = smi_to_i64_wrapped(len).max(0) as usize;

    if d.buf.len() < n { d.buf.resize(n, 0); }

    let nn = n.min(s.buf.len());
    let dptr = d.buf.as_mut_ptr();
    let sptr = s.buf.as_ptr();

    // element-wise so we can fire the barrier per write
    for i in 0..nn {
        unsafe {
            let v = *sptr.add(i);
            let slot = dptr.add(i);
            *slot = v;
            NAPALM_GC.post_write_barrier(dst as *mut u8, slot, v);
        }
    }
    // pad tail with 0s (no barrier needed, but harmless if called)
    for i in nn..n {
        unsafe { *dptr.add(i) = 0; }
    }
    0
}
