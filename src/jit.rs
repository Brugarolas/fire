// src/jit.rs
//! jit.rs — Cranelift JIT for WIR/Napalm (Cranelift 0.121.x compatible)
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_unsafe)]

use cranelift::codegen::ir::instructions::BlockArg;
use cranelift::prelude::*;
use cranelift::prelude::{InstBuilder, types};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::JITModule;
use cranelift_module::{Linkage, Module as _};

use ahash::AHashMap as HashMap;
use parking_lot::Mutex;
use std::cell::Cell;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

#[allow(unused_imports)]
use crate::gc::NAPALM_GC;

use crate::wir::{
    Constant, FuncId, Function as WirFunction, Inst, IntBinOp, Value as WirValue, ValueDef, ValueId,
};

use crate::http::{wir_server_add_route, wir_server_create, wir_server_listen};
#[allow(unused_imports)]
use crate::native_promises::{
    wir_await, wir_deferred_new, wir_deferred_reject, wir_deferred_resolve,
    wir_event_loop_pump_once, wir_promise_catch, wir_promise_new, wir_promise_reject,
    wir_promise_resolve, wir_promise_then,
};
#[allow(unused_imports)]
use crate::native_timers::{
    event_loop_yieldpoint, wir_clear_interval, wir_clear_timeout, wir_set_interval, wir_set_timeout,
};
#[allow(unused_imports)]
use crate::runtime::{
    napalm_yieldpoint, wir_is_str, wir_memo_get, wir_memo_put, wir_obj_assign, wir_obj_clone,
    wir_obj_del_field, wir_obj_del_str, wir_obj_get_field, wir_obj_get_field_deep,
    wir_obj_get_method, wir_obj_get_proto, wir_obj_get_str, wir_obj_get_str_deep,
    wir_obj_has_field, wir_obj_has_str, wir_obj_new, wir_obj_set_field, wir_obj_set_proto,
    wir_obj_set_str, wir_super_get_method,
};
#[allow(unused_imports)]
use crate::value::{
    BoxedArray, BoxedClosure, ObjHeader, TAG_ARRAY, closure_new, closure_set_env_slot,
    wir_array_copy, wir_array_fill, wir_array_filter, wir_array_find, wir_array_find_index,
    wir_array_for_each, wir_array_get, wir_array_len, wir_array_map, wir_array_new, wir_array_pop,
    wir_array_push, wir_array_reduce, wir_array_set, wir_array_set_len, wir_array_shift,
    wir_array_slice, wir_array_unshift,
};

impl JIT {
    pub fn predeclare(&mut self, funs: &[WirFunction]) -> Result<(), String> {
        use cranelift::prelude::{AbiParam, types};
        use cranelift_module::Linkage;

        for fun in funs {
            let fid_raw = fun.id.0 as u32;
            if self.fast_decls.contains_key(&fid_raw) {
                continue;
            }

            let mut sig = self.module.make_signature();
            sig.call_conv = self.module.isa().default_call_conv();
            for _ in 0..fun.sig.params.len() {
                sig.params.push(AbiParam::new(types::I64));
            }
            sig.returns.push(AbiParam::new(types::I64));

            let sym = format!("wir_rf_{}", fun.id.0);
            let func_id = self
                .module
                .declare_function(&sym, Linkage::Local, &sig)
                .map_err(|e| e.to_string())?;
            self.fast_decls.insert(fid_raw, func_id);
        }

        Ok(())
    }

    fn ensure_fast_decl(&mut self, fun: &WirFunction) -> Result<cranelift_module::FuncId, String> {
        if let Some(&id) = self.fast_decls.get(&(fun.id.0 as u32)) {
            return Ok(id);
        }

        use cranelift::prelude::{AbiParam, types};
        use cranelift_module::Linkage;

        let mut sig = self.module.make_signature();
        sig.call_conv = self.module.isa().default_call_conv();
        for _ in 0..fun.sig.params.len() {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let sym = format!("wir_rf_{}", fun.id.0);
        let func_id = self
            .module
            .declare_function(&sym, Linkage::Local, &sig)
            .map_err(|e| e.to_string())?;
        self.fast_decls.insert(fun.id.0 as u32, func_id);
        Ok(func_id)
    }

    fn ensure_stub_decl(&mut self, fun: &WirFunction) -> Result<cranelift_module::FuncId, String> {
        if let Some(&id) = self.stub_decls.get(&(fun.id.0 as u32)) {
            return Ok(id);
        }

        use cranelift::prelude::{AbiParam, types};
        use cranelift_module::Linkage;

        let mut sig = self.module.make_signature();
        sig.call_conv = self.module.isa().default_call_conv();
        sig.params.push(AbiParam::new(self.ptr_ty()));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let sym = format!("wir_f_{}", fun.id.0);
        let func_id = self
            .module
            .declare_function(&sym, Linkage::Local, &sig)
            .map_err(|e| e.to_string())?;
        self.stub_decls.insert(fun.id.0 as u32, func_id);
        Ok(func_id)
    }

    fn fast_decl_for(&self, fid: FuncId) -> Option<cranelift_module::FuncId> {
        self.fast_decls.get(&fid.0).copied()
    }

    fn ensure_fast_decl_for_call(
        &mut self,
        fid: FuncId,
        arity: usize,
    ) -> Result<cranelift_module::FuncId, String> {
        if let Some(&id) = self.fast_decls.get(&fid.0) {
            return Ok(id);
        }

        use cranelift::prelude::{AbiParam, types};
        use cranelift_module::Linkage;

        let mut sig = self.module.make_signature();
        sig.call_conv = self.module.isa().default_call_conv();
        for _ in 0..arity {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let sym = format!("wir_rf_{}", fid.0);
        let func_id = self
            .module
            .declare_function(&sym, Linkage::Local, &sig)
            .map_err(|e| e.to_string())?;
        self.fast_decls.insert(fid.0, func_id);
        Ok(func_id)
    }
}

/// ABI: `unsafe extern "C" fn(argv: *const i64, argc: usize) -> i64`
pub type JitFnPtr = unsafe extern "C" fn(*const i64, usize) -> i64;

static WIR_FUNPTRS: OnceLock<Mutex<HashMap<u32, usize>>> = OnceLock::new();

fn funptrs() -> &'static Mutex<HashMap<u32, usize>> {
    WIR_FUNPTRS.get_or_init(|| Mutex::new(HashMap::new()))
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_resolve_funptr(fid: i64) -> *const u8 {
    let m = funptrs().lock();
    let addr = m.get(&(fid as u32)).copied().unwrap_or(0usize);
    addr as *const u8
}

fn register_funptr(fid: u32, ptr: *const u8) {
    let mut m = funptrs().lock();
    m.insert(fid, ptr as usize);
}

// --- Live bindings (ESM) ----------------------------------------------------
static WIR_BINDINGS: OnceLock<Mutex<HashMap<u32, i64>>> = OnceLock::new();
fn bindings() -> &'static Mutex<HashMap<u32, i64>> {
    WIR_BINDINGS.get_or_init(|| Mutex::new(HashMap::new()))
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_binding_load(binding_id_smi: i64) -> i64 {
    // binding_id viene como SMI o raw? Aquí esperamos RAW (como en Store/MakeNamespace).
    // Para máxima compatibilidad, acepta ambos: si es impar, decodifica SMI.
    let raw = if (binding_id_smi & 1) == 1 {
        binding_id_smi >> 1
    } else {
        binding_id_smi
    };
    let id = raw as u32;
    let m = bindings().lock();
    *m.get(&id).unwrap_or(&0)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_binding_store(binding_id_smi: i64, val: i64) -> i64 {
    let raw = if (binding_id_smi & 1) == 1 {
        binding_id_smi >> 1
    } else {
        binding_id_smi
    };
    let id = raw as u32;
    let mut m = bindings().lock();
    m.insert(id, val);
    0
}

pub struct JIT {
    module: JITModule,
    fctx: FunctionBuilderContext,
    keep_alive: Vec<std::ffi::CString>, // keep CString storage alive for compiled code
    heap_keep_alive: Vec<*mut u8>,
    fast_decls: HashMap<u32, cranelift_module::FuncId>,
    stub_decls: HashMap<u32, cranelift_module::FuncId>,
}

impl Default for JIT {
    fn default() -> Self {
        let mut jb = cranelift_jit::JITBuilder::new(cranelift_module::default_libcall_names())
            .expect("JITBuilder::new");

        unsafe extern "C" {
            fn wir_resolve_funptr(fid: i64) -> *const u8;

            fn wir_print_i64(x: i64) -> i64;
            fn wir_print_any(v: i64) -> i64;
            fn wir_print_str(p: *const std::os::raw::c_char) -> i64;
            fn wir_method_trampoline(argv: *const i64, argc: usize) -> i64;
            fn wir_make_method_closure(fid_smi: i64) -> i64;
            fn wir_make_closure(code_ptr: *const u8, env: i64) -> i64;
            fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64;
            fn wir_alloc_words(n: i64) -> *mut i64;
            fn wir_free_words(p: *mut i64, n: i64) -> i64;

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

            fn wir_memo_get2(fid: i64, k0: i64, k1: i64, out_ptr: *mut i64) -> i64;
            fn wir_memo_put2(fid: i64, k0: i64, k1: i64, val: i64) -> i64;

            fn wir_memo_get3(fid: i64, k0: i64, k1: i64, k2: i64, out_ptr: *mut i64) -> i64;
            fn wir_memo_put3(fid: i64, k0: i64, k1: i64, k2: i64, val: i64) -> i64;

            fn wir_memo_get4(
                fid: i64,
                k0: i64,
                k1: i64,
                k2: i64,
                k3: i64,
                out_ptr: *mut i64,
            ) -> i64;
            fn wir_memo_put4(fid: i64, k0: i64, k1: i64, k2: i64, k3: i64, val: i64) -> i64;

            fn wir_obj_set_proto(obj: i64, proto: i64) -> i64;
            fn wir_obj_get_proto(obj: i64) -> i64;
            fn wir_obj_get_field_deep(obj: i64, field_id: i64) -> i64;
            fn wir_obj_get_str_deep(obj: i64, key: i64) -> i64;
            fn wir_obj_get_method(obj: i64, field_id_smi: i64) -> i64;
            fn wir_super_get_method(home_proto: i64, field_id_smi: i64) -> i64;
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
            fn wir_obj_assign(dst: i64, src: i64) -> i64;
            fn wir_obj_clone(obj: i64) -> i64;
        }

        unsafe extern "C" {
            fn wir_set_timeout(fun: i64, delay_ms: i64) -> i64;
            fn wir_set_interval(fun: i64, period_ms: i64) -> i64;
            fn wir_clear_timeout(id: i64) -> i64;
            fn wir_clear_interval(id: i64) -> i64;
            fn event_loop_yieldpoint() -> i64;
        }

        unsafe extern "C" {
            fn wir_promise_new(executor: i64) -> i64;
            fn wir_promise_then(priv_ptr: i64, on_f: i64, on_r: i64) -> i64;
            fn wir_promise_catch(priv_ptr: i64, on_r: i64) -> i64;
            fn wir_promise_resolve(priv_ptr: i64, val: i64) -> i64;
            fn wir_promise_reject(priv_ptr: i64, reason: i64) -> i64;

            fn wir_deferred_new() -> i64;
            fn wir_deferred_resolve(priv_ptr: i64, val: i64) -> i64;
            fn wir_deferred_reject(priv_ptr: i64, reason: i64) -> i64;

            fn wir_event_loop_pump_once() -> u32;
            fn wir_await(val: i64) -> i64;
        }

        unsafe extern "C" {
            fn wir_server_create(addr_ptr: i64) -> i64;
            fn wir_server_add_route(
                server_id: i64,
                method_ptr: i64,
                pattern_arr: i64,
                handler: i64,
            ) -> i64;
            fn wir_server_listen(server_id: i64) -> i64;
            fn wir_http_get(url_ptr: i64) -> i64;
            fn wir_http_get_json(url_ptr: i64) -> i64;
            fn wir_http_post(url_ptr: i64, body_ptr: i64, headers_arr: i64) -> i64;
            fn wir_http_request(
                method_ptr: i64,
                url_ptr: i64,
                body_ptr: i64,
                headers_arr: i64,
                as_json: i64,
            ) -> i64;
            fn wir_http_post_json(url_ptr: i64, json_str_ptr: i64, headers_arr: i64) -> i64;
            fn wir_http_start_stream(
                server_id_smi: i64,
                req_id_smi: i64,
                status_smi: i64,
                headers_arr: i64,
            ) -> i64;
            fn wir_http_stream_write(server_id_smi: i64, req_id_smi: i64, chunk_ptr: i64) -> i64;
            fn wir_http_stream_end(server_id_smi: i64, req_id_smi: i64) -> i64;
            fn wir_http_start_stream_from_req(
                req_obj: i64,
                status_smi: i64,
                headers_arr: i64,
            ) -> i64;
            fn wir_json_parse(str_ptr: i64) -> i64;
            fn wir_http_send_json(status_smi: i64, body_val: i64, headers_arr: i64) -> i64;
        }

        unsafe extern "C" {
            fn wir_binding_load(binding_id_smi: i64) -> i64;
            fn wir_binding_store(binding_id_smi: i64, val: i64) -> i64;
        }

        unsafe {
            jb.symbol(
                "wir_resolve_funptr",
                wir_resolve_funptr as *const extern "C" fn(i64) -> *const u8 as *const u8,
            );

            jb.symbol(
                "wir_print_i64",
                wir_print_i64 as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_print_any",
                wir_print_any as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_print_str",
                wir_print_str as *const extern "C" fn(*const std::os::raw::c_char) -> i64
                    as *const u8,
            );
            jb.symbol(
                "wir_method_trampoline",
                wir_method_trampoline as *const extern "C" fn(*const i64, usize) -> i64
                    as *const u8,
            );
            jb.symbol(
                "wir_make_method_closure",
                wir_make_method_closure as *const extern "C" fn(i64) -> i64 as *const u8,
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
                wir_alloc_words as *const extern "C" fn(i64) -> *mut i64 as *const u8,
            );
            jb.symbol(
                "wir_free_words",
                wir_free_words as *const extern "C" fn(*mut i64, i64) -> i64 as *const u8,
            );

            jb.symbol(
                "wir_add_slow",
                wir_add_slow as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_sub_slow",
                wir_sub_slow as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_mul_slow",
                wir_mul_slow as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );

            jb.symbol(
                "wir_cmp_eq_slow",
                wir_cmp_eq_slow as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_cmp_ne_slow",
                wir_cmp_ne_slow as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_cmp_lt_slow",
                wir_cmp_lt_slow as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_cmp_le_slow",
                wir_cmp_le_slow as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_cmp_gt_slow",
                wir_cmp_gt_slow as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_cmp_ge_slow",
                wir_cmp_ge_slow as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );

            jb.symbol(
                "wir_array_new",
                wir_array_new as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_len",
                wir_array_len as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_get",
                wir_array_get as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_set",
                wir_array_set as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_set_len",
                wir_array_set_len as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );

            jb.symbol(
                "wir_array_push",
                wir_array_push as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_pop",
                wir_array_pop as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_shift",
                wir_array_shift as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_unshift",
                wir_array_unshift as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );

            jb.symbol(
                "wir_array_slice",
                wir_array_slice as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_map",
                wir_array_map as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_for_each",
                wir_array_for_each as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_find",
                wir_array_find as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_find_index",
                wir_array_find_index as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_filter",
                wir_array_filter as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_reduce",
                wir_array_reduce as *const extern "C" fn(i64, i64, i64, i64) -> i64 as *const u8,
            );

            jb.symbol(
                "wir_array_fill",
                wir_array_fill as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_array_copy",
                wir_array_copy as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8,
            );

            // ---- object natives: bind symbol names used by CallNative to real addresses ----
            jb.symbol(
                "wir_obj_new",
                wir_obj_new as *const extern "C" fn() -> i64 as *const u8,
            );
            jb.symbol(
                "wir_is_str",
                wir_is_str as *const extern "C" fn(i64) -> i64 as *const u8,
            );

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
                "wir_obj_assign",
                wir_obj_assign as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_obj_clone",
                wir_obj_clone as *const extern "C" fn(i64) -> i64 as *const u8,
            );

            jb.symbol(
                "napalm_yieldpoint",
                napalm_yieldpoint as *const extern "C" fn() -> i64 as *const u8,
            );

            jb.symbol(
                "wir_memo_get",
                wir_memo_get as *const extern "C" fn(i64, i64, *mut i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_memo_put",
                wir_memo_put as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_memo_get2",
                wir_memo_get2 as *const extern "C" fn(i64, i64, i64, *mut i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_memo_put2",
                wir_memo_put2 as *const extern "C" fn(i64, i64, i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_memo_get3",
                wir_memo_get3 as *const extern "C" fn(i64, i64, i64, i64, *mut i64) -> i64
                    as *const u8,
            );
            jb.symbol(
                "wir_memo_put3",
                wir_memo_put3 as *const extern "C" fn(i64, i64, i64, i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_memo_get4",
                wir_memo_get4 as *const extern "C" fn(i64, i64, i64, i64, i64, *mut i64) -> i64
                    as *const u8,
            );
            jb.symbol(
                "wir_memo_put4",
                wir_memo_put4 as *const extern "C" fn(i64, i64, i64, i64, i64, i64) -> i64
                    as *const u8,
            );

            jb.symbol(
                "wir_set_timeout",
                wir_set_timeout as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_set_interval",
                wir_set_interval as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_clear_timeout",
                wir_clear_timeout as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_clear_interval",
                wir_clear_interval as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "event_loop_yieldpoint",
                event_loop_yieldpoint as *const extern "C" fn() -> i64 as *const u8,
            );

            jb.symbol(
                "wir_promise_new",
                wir_promise_new as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_promise_then",
                wir_promise_then as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_promise_catch",
                wir_promise_catch as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_promise_resolve",
                wir_promise_resolve as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_promise_reject",
                wir_promise_reject as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_deferred_new",
                wir_deferred_new as *const extern "C" fn() -> i64 as *const u8,
            );
            jb.symbol(
                "wir_deferred_resolve",
                wir_deferred_resolve as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_deferred_reject",
                wir_deferred_reject as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_event_loop_pump_once",
                wir_event_loop_pump_once as *const extern "C" fn() -> u32 as *const u8,
            );
            jb.symbol(
                "wir_await",
                wir_await as *const extern "C" fn(i64) -> i64 as *const u8,
            );

            jb.symbol(
                "wir_server_create",
                wir_server_create as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_server_add_route",
                wir_server_add_route as *const extern "C" fn(i64, i64, i64, i64) -> i64
                    as *const u8,
            );
            jb.symbol(
                "wir_server_listen",
                wir_server_listen as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_http_get",
                wir_http_get as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_http_get_json",
                wir_http_get_json as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_http_post",
                wir_http_post as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_http_request",
                wir_http_request as *const extern "C" fn(i64, i64, i64, i64, i64) -> i64
                    as *const u8,
            );
            jb.symbol(
                "wir_http_post_json",
                wir_http_post_json as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_http_start_stream",
                wir_http_start_stream as *const extern "C" fn(i64, i64, i64, i64) -> i64
                    as *const u8,
            );
            jb.symbol(
                "wir_http_stream_write",
                wir_http_stream_write as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_http_stream_end",
                wir_http_stream_end as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_http_start_stream_from_req",
                wir_http_start_stream_from_req as *const extern "C" fn(i64, i64, i64) -> i64
                    as *const u8,
            );
            jb.symbol(
                "wir_json_parse",
                wir_json_parse as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_http_send_json",
                wir_http_send_json as *const extern "C" fn(i64, i64, i64) -> i64 as *const u8,
            );

            jb.symbol(
                "wir_obj_set_proto",
                wir_obj_set_proto as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_obj_get_proto",
                wir_obj_get_proto as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_obj_get_field_deep",
                wir_obj_get_field_deep as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_obj_get_str_deep",
                wir_obj_get_str_deep as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_obj_get_method",
                wir_obj_get_method as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_super_get_method",
                wir_super_get_method as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );

            jb.symbol(
                "wir_binding_load",
                wir_binding_load as *const extern "C" fn(i64) -> i64 as *const u8,
            );
            jb.symbol(
                "wir_binding_store",
                wir_binding_store as *const extern "C" fn(i64, i64) -> i64 as *const u8,
            );
        }

        let module = cranelift_jit::JITModule::new(jb);
        Self {
            module,
            fctx: cranelift_frontend::FunctionBuilderContext::new(),
            keep_alive: Vec::new(),
            heap_keep_alive: Vec::new(),
            fast_decls: HashMap::new(),
            stub_decls: HashMap::new(),
        }
    }
}

impl JIT {
    /// Get an i64-typed code pointer for a compiled WIR function (`wir_f_<id>`).
    fn funptr_i64(&mut self, fb: &mut FunctionBuilder, fid: FuncId) -> Value {
        let ptr_ty = self.module.target_config().pointer_type();
        let mut sig = self.module.make_signature();
        sig.call_conv = self.module.isa().default_call_conv();

        // resolve at runtime: wir_resolve_funptr(fid) -> code_ptr
        let fid_v = fb.ins().iconst(types::I64, fid.0 as i64);
        let code_ptr = self
            .call_import(
                fb,
                "wir_resolve_funptr",
                |s| {
                    s.params.push(AbiParam::new(types::I64));
                    s.returns.push(AbiParam::new(ptr_ty));
                },
                &[fid_v],
            )
            .expect("resolve funptr");

        // Keep returning I64 for callers that expect it.
        match ptr_ty {
            types::I64 => code_ptr,
            types::I32 => fb.ins().uextend(types::I64, code_ptr),
            _ => fb.ins().uextend(types::I64, code_ptr),
        }
    }

    fn funptr_ptr(&mut self, fb: &mut FunctionBuilder, fid: FuncId) -> Value {
        use cranelift::prelude::*;
        let ptr_ty = self.ptr_ty();
        let fid_val = fb.ins().iconst(types::I64, fid.0 as i64);
        // call resolver: (i64 fid) -> ptr
        self.call_import(
            fb,
            "wir_resolve_funptr",
            |s| {
                s.params.push(AbiParam::new(types::I64));
                s.returns.push(AbiParam::new(ptr_ty));
            },
            &[fid_val],
        )
        .expect("resolve funptr")
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
        use cranelift::prelude::types;
        use cranelift::prelude::*;
        use cranelift::prelude::{AbiParam, FunctionBuilder};
        use cranelift_module::Module;

        let fun_ir: &WirFunction = fun;

        let fast_func_id = self.ensure_fast_decl(fun)?;
        let stub_func_id = self.ensure_stub_decl(fun)?;

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

        // ---- build cranelift function context/signature: (param0, param1, ...) -> i64
        let mut fast_ctx = self.module.make_context();
        let ptr_ty = self.module.target_config().pointer_type();
        fast_ctx.func.signature.call_conv = self.module.isa().default_call_conv();
        for _ in 0..fun.sig.params.len() {
            fast_ctx
                .func
                .signature
                .params
                .push(AbiParam::new(types::I64));
        }
        fast_ctx
            .func
            .signature
            .returns
            .push(AbiParam::new(types::I64));

        #[cfg(debug_assertions)]
        {
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
            let mut fb = FunctionBuilder::new(&mut fast_ctx.func, &mut fctx_local);
            let entry = fb.create_block();
            fb.append_block_params_for_function_params(entry);
            fb.switch_to_block(entry);

            let entry_params = fb.block_params(entry).to_vec();

            let mut vmap = ValueMap::new();
            let mut terminated = false;
            let mut saw_any_return = false;

            // Precreate one CLIF block per WIR block.
            let mut clif_of = Vec::with_capacity(fun.blocks.len());
            for blk in &fun.blocks {
                let ebb = if blk.id == fun.entry {
                    entry
                } else {
                    fb.create_block()
                };
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
                if let Some(&param_val) = entry_params.get(i) {
                    vmap.bind(ValueId(i as u32), param_val);

                    #[cfg(debug_assertions)]
                    {
                        eprintln!("[JIT] prebind param {} -> ValueId#{:?}", i, i);
                    }
                } else {
                    #[cfg(debug_assertions)]
                    {
                        eprintln!("[JIT][warn] missing entry param {} for ValueId#{:?}", i, i);
                    }
                }
            }

            // ---- linear pass
            for (bid, block) in fun.blocks.iter().enumerate() {
                #[cfg(debug_assertions)]
                {
                    eprintln!(
                        "  [block] visiting block #{bid} with {} insts",
                        block.insts.len()
                    );
                }

                let cur_ebb = clif_of[bid];
                if bid != fun.entry.0 as usize {
                    fb.switch_to_block(cur_ebb);
                }

                let mut block_terminated = false;

                for nid in &block.insts {
                    if block_terminated || terminated {
                        break;
                    }

                    #[cfg(debug_assertions)]
                    {
                        eprintln!("  [nodes] processing nid={:?}", nid);
                    }

                    let node = &fun.nodes[nid.0 as usize];
                    let res_count = node.results.len();

                    #[cfg(debug_assertions)]
                    {
                        eprintln!(
                            "  [nodes] processing nid={:?} kind={:?} results={:?}",
                            nid, node.kind, node.results
                        );
                    }

                    match &node.kind {
                        // ---------------- Constants ----------------
                        Inst::Const(c) => {
                            let v = self.emit_const(&mut fb, c); // safe now: fb uses fctx_local
                            if res_count == 1 {
                                vmap.bind(node.results[0], v);
                            }
                        }

                        Inst::Mov(src) => {
                            let v = vmap.get_or_emit(*src, &mut fb, fun);
                            if res_count == 1 {
                                vmap.bind(node.results[0], v);
                            }
                        }

                        // ---------------- Int ops (on SMIs) ----------------
                        Inst::IntBin { op, a, b } => {
                            let a = vmap.get_or_emit(*a, &mut fb, fun_ir);
                            let b = vmap.get_or_emit(*b, &mut fb, fun_ir);

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
                                IntBinOp::And => fb.ins().band(ra, rb),
                                IntBinOp::Or => fb.ins().bor(ra, rb),
                                IntBinOp::Xor => fb.ins().bxor(ra, rb),
                                IntBinOp::Shl => fb.ins().ishl(ra, rb),
                                IntBinOp::ShrU => fb.ins().ushr(ra, rb),
                                IntBinOp::Sar => fb.ins().sshr(ra, rb),
                            };

                            // re-encode to SMI: (raw << 1) | 1
                            let sh = fb.ins().ishl_imm(raw, 1);
                            let smi = fb.ins().iadd_imm(sh, 1);

                            if res_count == 1 {
                                vmap.bind(node.results[0], smi);
                            }
                        }

                        Inst::CmpInt { kind, a, b } => {
                            let a = vmap.get_or_emit(*a, &mut fb, fun_ir);
                            let b = vmap.get_or_emit(*b, &mut fb, fun_ir);

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
                            let one = fb.ins().iconst(types::I64, 1);
                            let zero = fb.ins().iconst(types::I64, 0);
                            let fast_res = fb.ins().select(cond, one, zero);

                            if res_count == 1 {
                                vmap.bind(node.results[0], fast_res);
                            }
                        }

                        // ---------------- Arrays (host runtime) ----------------
                        Inst::AllocArray { elem_hint: _, len } => {
                            use cranelift::prelude::{AbiParam, types};
                            let len_v = vmap.get_or_emit(*len, &mut fb, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_new",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // len
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[len_v],
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArrayLen(arr) => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_len",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // arr
                                    s.returns.push(AbiParam::new(types::I64)); // len (SMI)
                                },
                                &[a],
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::LoadElem { arr, idx } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let i = vmap.get_or_emit(*idx, &mut fb, fun_ir);
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
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::StoreElem { arr, idx, val } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let i = vmap.get_or_emit(*idx, &mut fb, fun_ir);
                            let vv = vmap.get_or_emit(*val, &mut fb, fun_ir);
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
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArraySetLen { arr, new_len } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let nl = vmap.get_or_emit(*new_len, &mut fb, fun_ir);
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
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArraySlice { arr, start, end } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let s = vmap.get_or_emit(*start, &mut fb, fun_ir);
                            let e = vmap.get_or_emit(*end, &mut fb, fun_ir);
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
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArrayPush { arr, val } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let v = vmap.get_or_emit(*val, &mut fb, fun_ir);
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
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArrayPop(arr) => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_pop",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64)); // popped value or 0
                                },
                                &[a],
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArrayShift(arr) => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_shift",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64)); // shifted value or 0
                                },
                                &[a],
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArrayUnshift { arr, val } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let v = vmap.get_or_emit(*val, &mut fb, fun_ir);
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
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        // ---------------- Arrays (host runtime; FuncId → closure with env=0) ----------------
                        Inst::ArrayMap { func, arr } => {
                            use cranelift::prelude::{AbiParam, types};
                            let ptr_ty = self.ptr_ty();
                            let code_ptr = self.funptr_ptr(&mut fb, *func); // wir_f_<id> address (i64)
                            let zero = fb.ins().iconst(types::I64, 0); // empty env
                            let clo = self.call_import(
                                &mut fb,
                                "wir_make_closure",
                                |s| {
                                    s.params.push(AbiParam::new(ptr_ty)); // code_ptr
                                    s.params.push(AbiParam::new(types::I64)); // env
                                    s.returns.push(AbiParam::new(types::I64)); // closure*
                                },
                                &[code_ptr, zero],
                            )?;

                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_map",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // arr
                                    s.params.push(AbiParam::new(types::I64)); // clo
                                    s.returns.push(AbiParam::new(types::I64)); // new arr
                                },
                                &[a, clo],
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArrayForEach { func, arr } => {
                            use cranelift::prelude::{AbiParam, types};
                            let ptr_ty = self.ptr_ty();
                            let code_ptr = self.funptr_ptr(&mut fb, *func);
                            let zero = fb.ins().iconst(types::I64, 0);
                            let clo = self.call_import(
                                &mut fb,
                                "wir_make_closure",
                                |s| {
                                    s.params.push(AbiParam::new(ptr_ty));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[code_ptr, zero],
                            )?;

                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_for_each",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64)); // 0
                                },
                                &[a, clo],
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArrayFind { func, arr } => {
                            use cranelift::prelude::{AbiParam, types};
                            let ptr_ty = self.ptr_ty();
                            let code_ptr = self.funptr_ptr(&mut fb, *func);
                            let zero = fb.ins().iconst(types::I64, 0);
                            let clo = self.call_import(
                                &mut fb,
                                "wir_make_closure",
                                |s| {
                                    s.params.push(AbiParam::new(ptr_ty));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[code_ptr, zero],
                            )?;

                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_find",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64)); // value or 0
                                },
                                &[a, clo],
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArrayFindIndex { func, arr } => {
                            use cranelift::prelude::{AbiParam, types};
                            let ptr_ty = self.ptr_ty();
                            let code_ptr = self.funptr_ptr(&mut fb, *func);
                            let zero = fb.ins().iconst(types::I64, 0);
                            let clo = self.call_import(
                                &mut fb,
                                "wir_make_closure",
                                |s| {
                                    s.params.push(AbiParam::new(ptr_ty));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[code_ptr, zero],
                            )?;

                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_find_index",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64)); // SMI index or smi(-1)
                                },
                                &[a, clo],
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArrayFilter { func, arr } => {
                            use cranelift::prelude::{AbiParam, types};
                            let ptr_ty = self.ptr_ty();
                            let code_ptr = self.funptr_ptr(&mut fb, *func);
                            let zero = fb.ins().iconst(types::I64, 0);
                            let clo = self.call_import(
                                &mut fb,
                                "wir_make_closure",
                                |s| {
                                    s.params.push(AbiParam::new(ptr_ty));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[code_ptr, zero],
                            )?;

                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let out = self.call_import(
                                &mut fb,
                                "wir_array_filter",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64)); // new arr
                                },
                                &[a, clo],
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArrayReduce { func, init, arr } => {
                            use cranelift::prelude::{AbiParam, IntCC, types};
                            let ptr_ty = self.ptr_ty();
                            let code_ptr = self.funptr_ptr(&mut fb, *func);
                            let zero = fb.ins().iconst(types::I64, 0);
                            let clo = self.call_import(
                                &mut fb,
                                "wir_make_closure",
                                |s| {
                                    s.params.push(AbiParam::new(ptr_ty));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[code_ptr, zero],
                            )?;

                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let init_v = vmap.get_or_emit(*init, &mut fb, fun_ir);
                            let one = fb.ins().iconst(types::I64, 1);
                            let z64 = fb.ins().iconst(types::I64, 0);
                            let has_init = {
                                let c = fb.ins().icmp(IntCC::NotEqual, init_v, z64);
                                fb.ins().select(c, one, z64)
                            };

                            let out = self.call_import(
                                &mut fb,
                                "wir_array_reduce",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // arr
                                    s.params.push(AbiParam::new(types::I64)); // clo
                                    s.params.push(AbiParam::new(types::I64)); // has_init
                                    s.params.push(AbiParam::new(types::I64)); // init
                                    s.returns.push(AbiParam::new(types::I64)); // result
                                },
                                &[a, clo, has_init, init_v],
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArrayFill { arr, val } => {
                            use cranelift::prelude::{AbiParam, types};
                            let a = vmap.get_or_emit(*arr, &mut fb, fun_ir);
                            let v = vmap.get_or_emit(*val, &mut fb, fun_ir);
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
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::ArrayCopy { dst, src, len } => {
                            use cranelift::prelude::{AbiParam, types};
                            let d = vmap.get_or_emit(*dst, &mut fb, fun_ir);
                            let s = vmap.get_or_emit(*src, &mut fb, fun_ir);
                            let n = vmap.get_or_emit(*len, &mut fb, fun_ir);
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
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        // ---------------- Closures (host trampoline calls) ----------------
                        Inst::MakeClosure { callee, env } => {
                            use cranelift::prelude::{AbiParam, types};

                            // JIT function code ptr for wir_f_<id> (direct within code heap).
                            let ptr_ty = self.module.target_config().pointer_type();
                            let mut jsig = self.module.make_signature();
                            jsig.call_conv = self.module.isa().default_call_conv();
                            jsig.params.push(AbiParam::new(ptr_ty));
                            jsig.params.push(AbiParam::new(types::I64));
                            jsig.returns.push(AbiParam::new(types::I64));

                            let sym = format!("wir_f_{}", callee.0);
                            let fid = self
                                .module
                                .declare_function(&sym, cranelift_module::Linkage::Local, &jsig)
                                .map_err(|e| e.to_string())?;
                            let fref = self.module.declare_func_in_func(fid, &mut fb.func);

                            let code_ptr = self.funptr_ptr(&mut fb, *callee);

                            // env value
                            let env_v = vmap.get_or_emit(*env, &mut fb, fun_ir);

                            // wir_make_closure(code_ptr, env) — call by address
                            let out = self.call_import(
                                &mut fb,
                                "wir_make_closure",
                                |s| {
                                    s.params.push(AbiParam::new(ptr_ty)); // code_ptr
                                    s.params.push(AbiParam::new(types::I64)); // env
                                    s.returns.push(AbiParam::new(types::I64)); // closure ptr
                                },
                                &[code_ptr, env_v],
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::CallClosure {
                            fun: fun_val, args, ..
                        } => {
                            use cranelift::prelude::{AbiParam, MemFlags, types};

                            let ptr_ty = self.ptr_ty();

                            // 1) Allocate argv on the heap so it's naturally 8-byte aligned for i64
                            let n_i64 = fb.ins().iconst(types::I64, args.len() as i64);
                            let argv = self.call_import(
                                &mut fb,
                                "wir_alloc_words",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // n
                                    s.returns.push(AbiParam::new(ptr_ty)); // *mut i64
                                },
                                &[n_i64],
                            )?;

                            // 2) Store each argument at argv + i*8
                            for (i, a) in args.iter().enumerate() {
                                let v = vmap.get_or_emit(*a, &mut fb, fun_ir);
                                let addr = fb.ins().iadd_imm(argv, (i as i64) * 8);
                                fb.ins().store(MemFlags::trusted(), v, addr, 0);
                            }

                            // 3) Call the runtime trampoline (it will prepend env internally)
                            let clo_ptr = vmap.get_or_emit(*fun_val, &mut fb, fun_ir);
                            let argc = n_i64; // same as args.len()

                            let out = self.call_import(
                                &mut fb,
                                "wir_call_closure",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // closure pointer (i64)
                                    s.params.push(AbiParam::new(ptr_ty)); // argv*
                                    s.params.push(AbiParam::new(types::I64)); // argc
                                    s.returns.push(AbiParam::new(types::I64)); // result
                                },
                                &[clo_ptr, argv, argc],
                            )?;

                            // Free argv (no-op under GC build; real free in non-GC build).
                            let _ = self.call_import(
                                &mut fb,
                                "wir_free_words",
                                |s| {
                                    s.params.push(AbiParam::new(ptr_ty));
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[argv, argc],
                            )?;

                            if res_count >= 1 {
                                vmap.bind(node.results[0], out);
                            }
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
                                argv.push(vmap.get_or_emit(*a, &mut fb, fun_ir));
                            }

                            // Build signature: (i64, i64, ...) -> i64
                            let out = self.call_import(
                                &mut fb,
                                import_name,
                                |s| {
                                    for _ in 0..argv.len() {
                                        s.params.push(AbiParam::new(types::I64));
                                    }
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &argv,
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        // ---------------- Direct calls ----------------
                        Inst::CallDirect { callee, args, .. } => {
                            let func_id = self.ensure_fast_decl_for_call(*callee, args.len())?;
                            let func_ref = self.module.declare_func_in_func(func_id, &mut fb.func);

                            let mut call_args = Vec::with_capacity(args.len());
                            for &a in args {
                                call_args.push(vmap.get_or_emit(a, &mut fb, fun_ir));
                            }

                            let call = fb.ins().call(func_ref, &call_args);
                            let outs = fb.inst_results(call).to_vec();

                            if res_count >= 1 {
                                vmap.bind(node.results[0], outs[0]);
                            }
                        }

                        // Engine has the ability to memoize functions, it is implemented natively
                        Inst::CallDirectMemoized { callee, args } => {
                            use cranelift::prelude::{AbiParam, IntCC, MemFlags, types};

                            let arity = args.len();
                            let ptr_ty = self.ptr_ty();

                            // Materialize args now (as i64 CLIF vals).
                            let mut keys = Vec::with_capacity(arity);
                            for &a in args {
                                keys.push(vmap.get_or_emit(a, &mut fb, fun_ir));
                            }

                            // ---- Lookup: out value lives in a 1-word HEAP buffer (aligned) ----
                            let one = fb.ins().iconst(types::I64, 1);
                            let zero = fb.ins().iconst(types::I64, 0);
                            let fid = fb.ins().iconst(types::I64, callee.0 as i64);

                            let out_ptr = self.call_import(
                                &mut fb,
                                "wir_alloc_words",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64));
                                    s.returns.push(AbiParam::new(ptr_ty));
                                },
                                &[one],
                            )?;

                            let found = match arity {
                                1 => {
                                    let args = [fid, keys[0], out_ptr];
                                    self.call_import(
                                        &mut fb,
                                        "wir_memo_get",
                                        |s| {
                                            s.params.push(AbiParam::new(types::I64)); // fid
                                            s.params.push(AbiParam::new(types::I64)); // k0
                                            s.params.push(AbiParam::new(ptr_ty)); // out*
                                            s.returns.push(AbiParam::new(types::I64)); // 0/1
                                        },
                                        &args,
                                    )?
                                }
                                2 => {
                                    let args = [fid, keys[0], keys[1], out_ptr];
                                    self.call_import(
                                        &mut fb,
                                        "wir_memo_get2",
                                        |s| {
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(ptr_ty));
                                            s.returns.push(AbiParam::new(types::I64));
                                        },
                                        &args,
                                    )?
                                }
                                3 => {
                                    let args = [fid, keys[0], keys[1], keys[2], out_ptr];
                                    self.call_import(
                                        &mut fb,
                                        "wir_memo_get3",
                                        |s| {
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(ptr_ty));
                                            s.returns.push(AbiParam::new(types::I64));
                                        },
                                        &args,
                                    )?
                                }
                                _ => {
                                    let args = [fid, keys[0], keys[1], keys[2], keys[3], out_ptr];
                                    self.call_import(
                                        &mut fb,
                                        "wir_memo_get4",
                                        |s| {
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(ptr_ty));
                                            s.returns.push(AbiParam::new(types::I64));
                                        },
                                        &args,
                                    )?
                                }
                            };

                            let bb_hit = fb.create_block();
                            let bb_miss = fb.create_block();
                            let bb_join = fb.create_block();
                            let res_phi = fb.append_block_param(bb_join, types::I64);

                            let is_hit = fb.ins().icmp(IntCC::NotEqual, found, zero);
                            use cranelift::codegen::ir::instructions::BlockArg;
                            fb.ins().brif(
                                is_hit,
                                bb_hit,
                                &[] as &[BlockArg],
                                bb_miss,
                                &[] as &[BlockArg],
                            );

                            // HIT: load cached, free temp buffer, jump join
                            fb.switch_to_block(bb_hit);
                            let cached = fb.ins().load(types::I64, MemFlags::trusted(), out_ptr, 0);
                            let _ = self.call_import(
                                &mut fb,
                                "wir_free_words",
                                |s| {
                                    s.params.push(AbiParam::new(ptr_ty));
                                    s.params.push(AbiParam::new(types::I64)); // n
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[out_ptr, one],
                            )?;
                            let hit_args = [BlockArg::from(cached)];
                            fb.ins().jump(bb_join, &hit_args);

                            // MISS: call callee, memoize, jump join
                            fb.switch_to_block(bb_miss);

                            let func_id = self.ensure_fast_decl_for_call(*callee, arity)?;
                            let func_ref = self.module.declare_func_in_func(func_id, &mut fb.func);
                            let call = fb.ins().call(func_ref, &keys[..]);
                            let retv = fb.inst_results(call)[0];

                            // memo put
                            let fid2 = fb.ins().iconst(types::I64, callee.0 as i64);
                            match arity {
                                1 => {
                                    let args = [fid2, keys[0], retv];
                                    let _ = self.call_import(
                                        &mut fb,
                                        "wir_memo_put",
                                        |s| {
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(types::I64));
                                            s.params.push(AbiParam::new(types::I64));
                                            s.returns.push(AbiParam::new(types::I64));
                                        },
                                        &args,
                                    )?;
                                }
                                2 => {
                                    let args = [fid2, keys[0], keys[1], retv];
                                    let _ = self.call_import(
                                        &mut fb,
                                        "wir_memo_put2",
                                        |s| {
                                            for _ in 0..4 {
                                                s.params.push(AbiParam::new(types::I64));
                                            }
                                            s.returns.push(AbiParam::new(types::I64));
                                        },
                                        &args,
                                    )?;
                                }
                                3 => {
                                    let args = [fid2, keys[0], keys[1], keys[2], retv];
                                    let _ = self.call_import(
                                        &mut fb,
                                        "wir_memo_put3",
                                        |s| {
                                            for _ in 0..5 {
                                                s.params.push(AbiParam::new(types::I64));
                                            }
                                            s.returns.push(AbiParam::new(types::I64));
                                        },
                                        &args,
                                    )?;
                                }
                                _ => {
                                    let args = [fid2, keys[0], keys[1], keys[2], keys[3], retv];
                                    let _ = self.call_import(
                                        &mut fb,
                                        "wir_memo_put4",
                                        |s| {
                                            for _ in 0..6 {
                                                s.params.push(AbiParam::new(types::I64));
                                            }
                                            s.returns.push(AbiParam::new(types::I64));
                                        },
                                        &args,
                                    )?;
                                }
                            }

                            // return path
                            let miss_args = [BlockArg::from(retv)];
                            fb.ins().jump(bb_join, &miss_args);

                            fb.switch_to_block(bb_join);
                            if res_count >= 1 {
                                vmap.bind(node.results[0], res_phi);
                            }
                        }

                        // ---------------- Control flow ----------------
                        Inst::Jump(to, args) => {
                            let dst = clif_of[to.0 as usize];
                            let mut bargs: Vec<cranelift::codegen::ir::instructions::BlockArg> =
                                Vec::with_capacity(args.len());
                            for &a in args {
                                let v = vmap.get_or_emit(a, &mut fb, fun);
                                bargs.push(cranelift::codegen::ir::instructions::BlockArg::from(v));
                            }
                            fb.ins().jump(dst, &bargs[..]);
                            block_terminated = true;
                        }

                        Inst::Branch {
                            cond,
                            then_b,
                            else_b,
                        } => {
                            use cranelift::prelude::{IntCC, types};
                            let ci64 = vmap.get_or_emit(*cond, &mut fb, fun);
                            let z = fb.ins().iconst(types::I64, 0);
                            let cb1 = fb.ins().icmp(IntCC::NotEqual, ci64, z);
                            use cranelift::codegen::ir::instructions::BlockArg;
                            fb.ins().brif(
                                cb1,
                                clif_of[then_b.0 as usize],
                                &[] as &[BlockArg],
                                clif_of[else_b.0 as usize],
                                &[] as &[BlockArg],
                            );
                            block_terminated = true;
                        }

                        Inst::Return(vals) => {
                            let ret = if vals.is_empty() {
                                fb.ins().iconst(types::I64, 0)
                            } else {
                                vmap.get_or_emit(vals[0], &mut fb, fun)
                            };
                            fb.ins().return_(&[ret]);
                            block_terminated = true;
                            saw_any_return = true;
                        }

                        Inst::LoadField { obj, field, .. } => {
                            use cranelift::prelude::{AbiParam, types};

                            let o = vmap.get_or_emit(*obj, &mut fb, fun_ir);

                            // field id -> SMI
                            let raw = fb.ins().iconst(types::I64, field.0 as i64);
                            let sh = fb.ins().ishl_imm(raw, 1);
                            let fid = fb.ins().iadd_imm(sh, 1);

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
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::StoreField {
                            obj, field, val, ..
                        } => {
                            use cranelift::prelude::{AbiParam, types};

                            let o = vmap.get_or_emit(*obj, &mut fb, fun_ir);
                            let v = vmap.get_or_emit(*val, &mut fb, fun_ir);

                            // field id -> SMI
                            let raw = fb.ins().iconst(types::I64, field.0 as i64);
                            let sh = fb.ins().ishl_imm(raw, 1);
                            let fid = fb.ins().iadd_imm(sh, 1);

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
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        // ---------------- ESM live bindings ----------------
                        Inst::LoadBinding { binding } => {
                            use cranelift::prelude::{AbiParam, types};
                            // binding id como RAW i64 (no SMI): emitimos constante con el id
                            let bid = fb.ins().iconst(types::I64, binding.0 as i64);
                            let out = self.call_import(
                                &mut fb,
                                "wir_binding_load",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // binding id
                                    s.returns.push(AbiParam::new(types::I64)); // valor
                                },
                                &[bid],
                            )?;
                            if res_count == 1 {
                                vmap.bind(node.results[0], out);
                            }
                        }

                        Inst::StoreBinding { binding, val } => {
                            use cranelift::prelude::{AbiParam, types};
                            let bid = fb.ins().iconst(types::I64, binding.0 as i64);
                            let vv = vmap.get_or_emit(*val, &mut fb, fun_ir);
                            let _ = self.call_import(
                                &mut fb,
                                "wir_binding_store",
                                |s| {
                                    s.params.push(AbiParam::new(types::I64)); // binding id
                                    s.params.push(AbiParam::new(types::I64)); // val
                                    s.returns.push(AbiParam::new(types::I64)); // 0
                                },
                                &[bid, vv],
                            )?;
                            // sin resultados
                        }

                        Inst::MakeNamespace { exports } => {
                            use cranelift::prelude::{AbiParam, MemFlags, types};

                            // MVP: construye un objeto normal y copia *snapshot* de los valores actuales
                            // de cada binding como campos por nombre (string). Más adelante podemos
                            // sustituir esto por getters enlazados a celdas.
                            let obj = self.call_import(
                                &mut fb,
                                "wir_obj_new",
                                |s| {
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[],
                            )?;

                            for (name, binding) in exports {
                                // Materializa el nombre como BoxedStr* (i64)
                                let name_ptr = self.alloc_boxed_str(name);
                                let name_val = fb.ins().iconst(types::I64, name_ptr);

                                // Carga valor de la celda
                                let bid = fb.ins().iconst(types::I64, binding.0 as i64);
                                let cur = self.call_import(
                                    &mut fb,
                                    "wir_binding_load",
                                    |s| {
                                        s.params.push(AbiParam::new(types::I64));
                                        s.returns.push(AbiParam::new(types::I64));
                                    },
                                    &[bid],
                                )?;

                                // obj[name] = cur
                                let _ = self.call_import(
                                    &mut fb,
                                    "wir_obj_set_str",
                                    |s| {
                                        s.params.push(AbiParam::new(types::I64)); // obj
                                        s.params.push(AbiParam::new(types::I64)); // key (boxed str*)
                                        s.params.push(AbiParam::new(types::I64)); // val
                                        s.returns.push(AbiParam::new(types::I64)); // 0
                                    },
                                    &[obj, name_val, cur],
                                )?;
                            }

                            if res_count == 1 {
                                vmap.bind(node.results[0], obj);
                            }
                        }

                        // ---------------- Effects / markers ----------------
                        Inst::EffectEntry => {
                            let token = fb.ins().iconst(ptr_ty, 0);
                            if res_count == 1 {
                                vmap.bind(node.results[0], token);
                            }
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
                            let _ = self.call_import(
                                &mut fb,
                                "event_loop_yieldpoint",
                                |s| {
                                    // () -> i64 (ignored)
                                    s.returns.push(AbiParam::new(types::I64));
                                },
                                &[],
                            )?;
                        }

                        Inst::GuardBounds { idx, len, .. } => {
                            let i_smi = vmap.get_or_emit(*idx, &mut fb, fun_ir);
                            let n_smi = vmap.get_or_emit(*len, &mut fb, fun_ir);

                            let i = fb.ins().sshr_imm(i_smi, 1); // raw idx
                            let n = fb.ins().sshr_imm(n_smi, 1); // raw len

                            let zero = fb.ins().iconst(types::I64, 0);
                            let ge0 = fb.ins().icmp(IntCC::SignedGreaterThanOrEqual, i, zero);
                            let lt = fb.ins().icmp(IntCC::SignedLessThan, i, n);
                            let ok = fb.ins().band(ge0, lt);

                            let cont = fb.create_block();
                            let bad = fb.create_block();
                            fb.ins()
                                .brif(ok, cont, &[] as &[BlockArg], bad, &[] as &[BlockArg]);

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
                if terminated {
                    break;
                }
            }

            if !saw_any_return {
                let tail = fb.create_block();
                fb.switch_to_block(tail);
                let zero = fb.ins().iconst(types::I64, 0);
                fb.ins().return_(&[zero]);
            }

            fb.seal_all_blocks();
            fb.finalize();

            // Materialize fast (register ABI) body.
            self.module
                .define_function(fast_func_id, &mut fast_ctx)
                .map_err(|e| e.to_string())?;
            self.module.clear_context(&mut fast_ctx);

            // Build stub that adapts (argv*, argc) -> fast(params...)
            let mut stub_ctx = self.module.make_context();
            stub_ctx.func.signature.call_conv = self.module.isa().default_call_conv();
            stub_ctx.func.signature.params.push(AbiParam::new(ptr_ty));
            stub_ctx
                .func
                .signature
                .params
                .push(AbiParam::new(types::I64));
            stub_ctx
                .func
                .signature
                .returns
                .push(AbiParam::new(types::I64));

            {
                use cranelift::prelude::MemFlags;
                let mut sb = FunctionBuilder::new(&mut stub_ctx.func, &mut fctx_local);
                let entry = sb.create_block();
                sb.append_block_params_for_function_params(entry);
                sb.switch_to_block(entry);

                let params = sb.block_params(entry);
                let argv_ptr = params[0];

                let mut call_args = Vec::with_capacity(fun.sig.params.len());
                for i in 0..fun.sig.params.len() {
                    let addr = sb.ins().iadd_imm(argv_ptr, (i as i64) * 8);
                    let v = sb.ins().load(types::I64, MemFlags::trusted(), addr, 0);
                    call_args.push(v);
                }

                let func_ref = self.module.declare_func_in_func(fast_func_id, &mut sb.func);
                let call = sb.ins().call(func_ref, &call_args);
                let res = sb.inst_results(call)[0];
                sb.ins().return_(&[res]);

                sb.seal_all_blocks();
                sb.finalize();
            }

            self.module
                .define_function(stub_func_id, &mut stub_ctx)
                .map_err(|e| e.to_string())?;
            self.module.clear_context(&mut stub_ctx);

            self.module
                .finalize_definitions()
                .map_err(|e| e.to_string())?;

            let code = self.module.get_finalized_function(stub_func_id);
            register_funptr(fun.id.0 as u32, code as *const u8);
            let fptr: JitFnPtr = unsafe { std::mem::transmute(code) };
            Ok(fptr)
        })();

        // Always restore the shared builder context
        self.fctx = fctx_local;

        result
    }
}

impl JIT {
    fn emit_const(
        &mut self,
        fb: &mut FunctionBuilder,
        c: &crate::wir::Constant,
    ) -> cranelift::prelude::Value {
        use cranelift::prelude::*;
        match c {
            // small ints as SMIs (odd)
            Constant::Int32(x) => fb.ins().iconst(types::I64, ((*x as i64) << 1) | 1),

            // bools as 0/1 (unchanged)
            Constant::Bool(b) => fb.ins().iconst(types::I64, if *b { 1 } else { 0 }),

            // null as 0
            Constant::Null => fb.ins().iconst(types::I64, 0),

            // strings -> stable C string pointer kept alive
            Constant::Str(s) => {
                let p = self.alloc_boxed_str(s);
                fb.ins().iconst(types::I64, p)
            }

            // f64 -> heap-allocated BoxedF64
            Constant::F64(f) => {
                let p = self.alloc_boxed_f64(*f);
                fb.ins().iconst(types::I64, p)
            }

            Constant::Undefined => {
                // We don't have a special undefined value, so use null (0).
                fb.ins().iconst(types::I64, 0)
            }
        }
    }

    fn alloc_boxed_f64(&mut self, x: f64) -> i64 {
        use crate::value::{BoxedF64, ObjHeader, TAG_BOXED_F64};
        let obj = Box::new(BoxedF64 {
            hdr: ObjHeader {
                tag: TAG_BOXED_F64,
                aux: 0,
            },
            val: x,
        });
        let ptr = Box::into_raw(obj) as *mut u8;
        self.heap_keep_alive.push(ptr); // leak (intentionally) until GC
        ptr as i64 // even pointer => tagged “pointer”
    }

    fn alloc_boxed_str(&mut self, s: &str) -> i64 {
        use crate::value::{BoxedStr, ObjHeader, TAG_STRING};
        use std::alloc::{Layout, alloc, handle_alloc_error};
        use std::ptr::copy_nonoverlapping;

        let len = s.as_bytes().len();
        // At least 1 byte, but force 8-byte alignment for ARM64 safety.
        let layout = Layout::from_size_align(len.max(1), 8).unwrap();

        unsafe {
            // Allocate an 8-byte aligned raw buffer and copy the bytes.
            let buf = alloc(layout);
            if buf.is_null() {
                handle_alloc_error(layout);
            }
            if len > 0 {
                copy_nonoverlapping(s.as_ptr(), buf, len);
            }
            // Keep the raw buffer alive (we leak like other boxed heap objs — until GC arrives).
            self.heap_keep_alive.push(buf);

            // Now box the metadata object that points to the aligned buffer.
            let obj = Box::new(BoxedStr {
                hdr: ObjHeader {
                    tag: TAG_STRING,
                    aux: 0,
                },
                len,
                data: buf as *const u8, // 8-byte aligned
            });
            let ptr = Box::into_raw(obj) as *mut u8;
            self.heap_keep_alive.push(ptr);

            ptr as i64 // even pointer => heap object
        }
    }
}
/// Value binder: maps WIR ValueIds to CLIF Values.
struct ValueMap {
    map: HashMap<ValueId, Value>,
}

impl ValueMap {
    fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
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

        #[cfg(debug_assertions)]
        {
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

    fn get_or_emit(&mut self, id: ValueId, fb: &mut FunctionBuilder, fun: &WirFunction) -> Value {
        if let Some(v) = self.get(id) {
            return v;
        }
        if let Some(v) = synth_const(&fun.values, id, fb) {
            self.bind(id, v);
            return v;
        }

        #[cfg(debug_assertions)]
        {
            eprintln!(
                "[JIT][warn] get_or_emit fallback -> 0 for {:?} (def={:?})",
                id, fun.values[id.0 as usize].def
            );
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
                let sh = fb.ins().ishl_imm(raw, 1);
                let smi = fb.ins().iadd_imm(sh, 1);
                Some(smi)
            }
            Constant::F64(f) => {
                // We cannot call self here, so keep synth_const() as-is for Int/Bool/Null,
                // and let F64 fall back to None so the caller uses emit_const path.
                // (Simplest: return None for F64 here.)
                None
            }
            Constant::Bool(b) => Some(fb.ins().iconst(types::I64, if *b { 1 } else { 0 })),
            Constant::Null => Some(fb.ins().iconst(types::I64, 0)),
            Constant::Str(_) => None,
            Constant::Undefined => Some(fb.ins().iconst(types::I64, 0)),
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
pub extern "C" fn wir_print_i64(v: i64) -> i64 {
    use crate::value::*;
    use std::slice;

    if is_imm(v) {
        #[cfg(debug_assertions)]
        {
            eprintln!("{}", smi_to_i64(v));
        }
        return 0;
    }

    if v == NULL {
        #[cfg(debug_assertions)]
        {
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
pub extern "C" fn wir_method_trampoline(argv: *const i64, argc: usize) -> i64 {
    // argv layout when called via wir_call_closure with env_len=1:
    //   argv[0] = env[0] = SMI(fid)
    //   argv[1] = this
    //   argv[2...] = user args
    if argv.is_null() || argc == 0 {
        panic!("method trampoline: empty argv");
    }
    if argv.is_null() || argc < 2 {
        panic!(
            "method trampoline: need at least env + this, got argc={}",
            argc
        );
    }

    unsafe {
        let fid_smi = *argv;
        // SMI decode: (x >> 1)
        let fid_raw = (fid_smi >> 1) as i64;
        let fptr = wir_resolve_funptr(fid_raw);
        if fptr.is_null() {
            panic!("method trampoline: unresolved fid={}", fid_raw);
        }
        let f: JitFnPtr = std::mem::transmute(fptr);
        // forward *without* the env word
        (f)(argv.add(1), argc - 1)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_make_method_closure(fid_smi: i64) -> i64 {
    unsafe extern "C" {
        fn wir_method_trampoline(argv: *const i64, argc: usize) -> i64;
    }
    let clo_val = closure_new(wir_method_trampoline as usize, 1);
    unsafe {
        closure_set_env_slot(clo_val, 0, fid_smi);
    }
    clo_val
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_make_closure(code_ptr: *const u8, env: i64) -> i64 {
    // If env == 0 (NULL), build a closure with no env slots,
    // so calls won't prepend an extra argument before `this`.
    let env_len = if env == 0 { 0 } else { 1 };
    let clo_val = closure_new(code_ptr as usize, env_len);
    if env_len == 1 {
        unsafe {
            closure_set_env_slot(clo_val, 0, env);
        }
    }
    clo_val
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64 {
    use crate::value::{NULL, ObjHeader, TAG_CLOSURE, is_imm};
    use core::ptr;

    // Basic checks (helpful messages instead of UB)
    if clo_ptr == NULL {
        panic!("CallClosure: null callee");
    }
    if ((argv as usize) & 7) != 0 {
        panic!("CallClosure: argv not 8-byte aligned: {:p}", argv);
    }

    // Path 1: callee is a SMI(FuncId). Call wir_f_<id>(argv, argc) directly.
    if is_imm(clo_ptr) {
        // SMI decode: raw id = v >> 1
        let fid = clo_ptr >> 1;
        let code = unsafe { wir_resolve_funptr(fid) };
        if code.is_null() {
            panic!("CallClosure: unresolved function id {}", fid);
        }
        let f: JitFnPtr = unsafe { core::mem::transmute(code) };
        return unsafe { (f)(argv, argc as usize) };
    }

    // Path 2: callee must be a real closure object
    unsafe {
        let hdr = &*(clo_ptr as *const ObjHeader);
        if hdr.tag != TAG_CLOSURE {
            panic!("CallClosure: value is not a closure (tag={})", hdr.tag);
        }

        let clo = &*(clo_ptr as *const BoxedClosure);
        let f: JitFnPtr = core::mem::transmute(clo.code_ptr as *const u8);

        // Build argv' = [env..., argv...]
        let env_len = clo.env.len();
        let arg_len = argc as usize;
        let total = env_len + arg_len;

        // Allocate a temporary vector to stitch env + args. (Aligned, safe.)
        let mut args: Vec<i64> = Vec::with_capacity(total);
        args.extend_from_slice(&clo.env);
        for i in 0..arg_len {
            args.push(*argv.add(i));
        }

        (f)(args.as_ptr(), args.len())
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_alloc_words(n: i64) -> *mut i64 {
    use std::alloc::{Layout, alloc_zeroed, handle_alloc_error};
    if n <= 0 {
        return core::ptr::null_mut();
    }

    let words = n as usize;
    let a = core::cmp::max(core::mem::align_of::<i64>(), core::mem::align_of::<usize>());
    let hdr = (core::mem::size_of::<usize>() + (a - 1)) & !(a - 1); // padded header
    let total = hdr + words * core::mem::size_of::<i64>();

    unsafe {
        let layout = Layout::from_size_align(total, a).unwrap();
        let base = alloc_zeroed(layout);
        if base.is_null() {
            handle_alloc_error(layout);
        }
        // store length at header
        *(base as *mut usize) = words;
        let ret = base.add(hdr) as *mut i64; // aligned *mut i64

        return ret;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_free_words(p: *mut i64, _n: i64) -> i64 {
    use std::alloc::{Layout, dealloc};
    if p.is_null() {
        return 0;
    }
    unsafe {
        let a = core::cmp::max(core::mem::align_of::<i64>(), core::mem::align_of::<usize>());
        let hdr = (core::mem::size_of::<usize>() + (a - 1)) & !(a - 1);
        let base = (p as *mut u8).sub(hdr);
        let words = *(base as *const usize);
        let total = hdr + words * core::mem::size_of::<i64>();
        let layout = Layout::from_size_align(total, a).unwrap();
        dealloc(base, layout);
    }
    0
}

// ----- SMI and boxed f64 handling -----

#[inline(always)]
fn smi_encode(x: i64) -> i64 {
    (x << 1) | 1
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_box_f64_runtime(bits: u64) -> i64 {
    use crate::value::{BoxedF64, ObjHeader, TAG_BOXED_F64};
    let x = f64::from_bits(bits);
    let obj = Box::new(BoxedF64 {
        hdr: ObjHeader {
            tag: TAG_BOXED_F64,
            aux: 0,
        },
        val: x,
    });
    Box::into_raw(obj) as i64
}

#[inline(always)]
fn val_to_f64(v: i64) -> Result<f64, &'static str> {
    use crate::value::*;
    if is_imm(v) {
        Ok(smi_to_i64(v) as f64)
    } else {
        if v == NULL {
            return Err("null is not a number");
        }
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
#[inline(always)]
fn b2i(b: bool) -> i64 {
    if b { 1 } else { 0 }
}

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
