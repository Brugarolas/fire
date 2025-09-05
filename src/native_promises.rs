// src/native_promises.rs

use crate::event_loop::EVENT_LOOP;
use crate::value::{ObjHeader, BoxedClosure, closure_new, closure_set_env_slot, TAG_STRING};
use crate::runtime::{wir_obj_new, wir_obj_set_str};
use std::slice;

#[derive(Copy, Clone, PartialEq, Eq)]
enum PState { Pending=0, Fulfilled=1, Rejected=2 }

#[repr(C)]
struct BoxedPromise {
    hdr: ObjHeader,     // use a dedicated tag if you have one; else reuse object-like tag ok if not exposed
    state: i32,         // PState as i32
    value: i64,         // fulfillment value or rejection reason
    // queued reactions (closures)
    on_fulfilled: Vec<i64>,
    on_rejected: Vec<i64>,
}

// Tiny helper: allocate a BoxedStr for a *static* &str key
fn static_str_value(s: &'static str) -> i64 {
    use crate::value::{BoxedStr, TAG_STRING};
    let obj = Box::new(BoxedStr {
        hdr: ObjHeader { tag: TAG_STRING, aux: 0 },
        len: s.as_bytes().len(),
        data: s.as_ptr(),
    });
    Box::into_raw(obj) as i64
}

// ---- core helpers ----

unsafe fn as_promise(p: i64) -> *mut BoxedPromise {
    p as *mut BoxedPromise
}

fn schedule_fulfill(fun: i64, arg: i64) {
    EVENT_LOOP.enqueue_microtask(fun, arg);
}

// Resolve / Reject primitives (no-ops if already settled)
#[unsafe(no_mangle)]
pub extern "C" fn wir_promise_resolve(priv_ptr: i64, val: i64) -> i64 {
    unsafe {
        let p = as_promise(priv_ptr);
        if (*p).state != PState::Pending as i32 { return 0; }
        (*p).state = PState::Fulfilled as i32;
        (*p).value = val;

        // schedule queued on_fulfilled
        let pending = std::mem::take(&mut (*p).on_fulfilled);
        for f in pending { schedule_fulfill(f, val); }
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_promise_reject(priv_ptr: i64, reason: i64) -> i64 {
    unsafe {
        let p = as_promise(priv_ptr);
        if (*p).state != PState::Pending as i32 { return 0; }
        (*p).state = PState::Rejected as i32;
        (*p).value = reason;

        let pending = std::mem::take(&mut (*p).on_rejected);
        for f in pending { schedule_fulfill(f, reason); } // same microtask path
    }
    0
}

// then(p, onFulfilled?, onRejected?) -> (returns same promise for now)
#[unsafe(no_mangle)]
pub extern "C" fn wir_promise_then(priv_ptr: i64, on_f: i64, on_r: i64) -> i64 {
    unsafe {
        let p = as_promise(priv_ptr);
        match (*p).state {
            x if x == PState::Pending as i32 => {
                if on_f != 0 { (*p).on_fulfilled.push(on_f); }
                if on_r != 0 { (*p).on_rejected.push(on_r); }
            }
            x if x == PState::Fulfilled as i32 => {
                if on_f != 0 { schedule_fulfill(on_f, (*p).value); }
            }
            _ => {
                if on_r != 0 { schedule_fulfill(on_r, (*p).value); }
            }
        }
    }
    // Minimal v1: return the *same* promise; (chainable version can return a new promise)
    priv_ptr
}

// catch(p, onRejected) sugar
#[unsafe(no_mangle)]
pub extern "C" fn wir_promise_catch(priv_ptr: i64, on_r: i64) -> i64 {
    wir_promise_then(priv_ptr, 0, on_r)
}

// ---- public API: Promise(executor) -> promise object with .then/.catch ----
// executor: closure(resolve, reject)
#[unsafe(no_mangle)]
pub extern "C" fn wir_promise_new(executor: i64) -> i64 {
    unsafe {
        // 1) private state
        let priv_p = {
            let p = BoxedPromise {
                hdr: ObjHeader { tag: 0, aux: 0 }, // not exposed to general object APIs
                state: PState::Pending as i32,
                value: 0,
                on_fulfilled: Vec::new(),
                on_rejected: Vec::new(),
            };
            Box::into_raw(Box::new(p)) as i64
        };

        // 2) resolve/reject closures with env[0] = priv_p
        extern "C" fn resolve_tramp(argv: *const i64, argc: usize) -> i64 {
            unsafe {
                let args = std::slice::from_raw_parts(argv, argc);
                let priv_p = *args.get(0).unwrap_or(&0);
                let val    = *args.get(1).unwrap_or(&0);
                wir_promise_resolve(priv_p, val)
            }
        }
        extern "C" fn reject_tramp(argv: *const i64, argc: usize) -> i64 {
            unsafe {
                let args = std::slice::from_raw_parts(argv, argc);
                let priv_p = *args.get(0).unwrap_or(&0);
                let reason = *args.get(1).unwrap_or(&0);
                wir_promise_reject(priv_p, reason)
            }
        }

        let res = closure_new(resolve_tramp as usize, 1);
        closure_set_env_slot(res, 0, priv_p);

        let rej = closure_new(reject_tramp as usize, 1);
        closure_set_env_slot(rej, 0, priv_p);

        // 3) call executor(resolve, reject)
        unsafe extern "C" { fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64; }
        let argv = [res, rej];
        let _ = wir_call_closure(executor, argv.as_ptr(), 2);

        // Public value is the private pointer; .then/.catch are lowered directly (see front.rs).
        priv_p
    }
}
