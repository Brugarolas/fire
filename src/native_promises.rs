// src/native_promises.rs
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_unsafe)]

use crate::event_loop::EVENT_LOOP;
use crate::runtime::{wir_obj_new, wir_obj_set_str};
use crate::value::{BoxedClosure, ObjHeader, closure_new, closure_set_env_slot};
use std::slice;

use once_cell::sync::Lazy;
use parking_lot::Mutex;

// Store promise pointers as integer handles so T: Send holds for the Mutex.
type PromiseHandle = usize;

static PROMISES: Lazy<Mutex<Vec<PromiseHandle>>> = Lazy::new(|| Mutex::new(Vec::new()));

fn register_promise(p: *mut BoxedPromise) {
    PROMISES.lock().push(p as usize);
}

fn unregister_promise(p: *mut BoxedPromise) {
    let h = p as usize;
    let mut v = PROMISES.lock();
    if let Some(i) = v.iter().position(|&q| q == h) {
        v.swap_remove(i);
    }
}

/// Let the GC visit the i64 slots stored inside BoxedPromise (callbacks & value).
pub fn promises_with_root_slots<F: FnMut(*mut i64)>(mut f: F) {
    let v = PROMISES.lock();
    for &h in v.iter() {
        unsafe {
            let p = &mut *(h as *mut BoxedPromise);
            for fun in p.on_fulfilled.iter_mut() {
                f(fun as *mut i64);
            }
            for fun in p.on_rejected.iter_mut() {
                f(fun as *mut i64);
            }
            f(&mut p.value as *mut i64);
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum PState {
    Pending = 0,
    Fulfilled = 1,
    Rejected = 2,
}

#[repr(C)]
struct BoxedPromise {
    hdr: ObjHeader, // use a dedicated tag if you have one; else reuse object-like tag ok if not exposed
    state: i32,     // PState as i32
    value: i64,     // fulfillment value or rejection reason
    // queued reactions (closures)
    on_fulfilled: Vec<i64>,
    on_rejected: Vec<i64>,
}

// Tiny helper: allocate a BoxedStr for a *static* &str key
// tiny helper (already present above, keep one copy)
fn static_str_value(s: &'static str) -> i64 {
    crate::value::intern_string(s)
}

// ---- core helpers ----

unsafe fn as_promise(p: i64) -> *mut BoxedPromise {
    p as *mut BoxedPromise
}

fn schedule_fulfill(fun: i64, arg: i64) {
    #[cfg(debug_assertions)]
    eprintln!(
        "[promise] schedule_fulfill(fun={}, arg={})",
        crate::value::dbg_addr(fun),
        crate::value::dbg_addr(arg)
    );

    EVENT_LOOP.enqueue_microtask(fun, arg);
}

// Resolve / Reject primitives (no-ops if already settled)
#[unsafe(no_mangle)]
pub extern "C" fn wir_promise_resolve(priv_ptr: i64, val: i64) -> i64 {
    unsafe {
        let p = as_promise(priv_ptr);
        if (*p).state != PState::Pending as i32 {
            return 0;
        }
        (*p).state = PState::Fulfilled as i32;
        (*p).value = val;

        // schedule queued on_fulfilled
        let pending = std::mem::take(&mut (*p).on_fulfilled);
        for f in pending {
            schedule_fulfill(f, val);
        }

        unregister_promise(p);
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_promise_reject(priv_ptr: i64, reason: i64) -> i64 {
    unsafe {
        let p = as_promise(priv_ptr);
        if (*p).state != PState::Pending as i32 {
            return 0;
        }
        (*p).state = PState::Rejected as i32;
        (*p).value = reason;

        let pending = std::mem::take(&mut (*p).on_rejected);
        for f in pending {
            schedule_fulfill(f, reason);
        } // same microtask path

        unregister_promise(p);
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
                if on_f != 0 {
                    (*p).on_fulfilled.push(on_f);
                }
                if on_r != 0 {
                    (*p).on_rejected.push(on_r);
                }
            }
            x if x == PState::Fulfilled as i32 => {
                if on_f != 0 {
                    schedule_fulfill(on_f, (*p).value);
                }
            }
            _ => {
                if on_r != 0 {
                    schedule_fulfill(on_r, (*p).value);
                }
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
                let val = *args.get(1).unwrap_or(&0);
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
        unsafe extern "C" {
            fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64;
        }
        let argv = [res, rej];
        let _ = wir_call_closure(executor, argv.as_ptr(), 2);

        register_promise(priv_p as *mut BoxedPromise);

        // Public value is the private pointer; .then/.catch are lowered directly (see front.rs).
        priv_p
    }
}

// ================= Deferreds ==================

#[unsafe(no_mangle)]
pub extern "C" fn wir_deferred_new() -> i64 {
    // allocate the same BoxedPromise as Promise uses, but don't run an executor
    let p = BoxedPromise {
        hdr: ObjHeader { tag: 0, aux: 0 },
        state: PState::Pending as i32,
        value: 0,
        on_fulfilled: Vec::new(),
        on_rejected: Vec::new(),
    };

    let p_raw = Box::into_raw(Box::new(p)) as i64;
    register_promise(p_raw as *mut BoxedPromise);
    p_raw
}

// Return-the-same-pointer wrappers so you can chain: d.resolve(v).then(...)
#[unsafe(no_mangle)]
pub extern "C" fn wir_deferred_resolve(priv_ptr: i64, val: i64) -> i64 {
    wir_promise_resolve(priv_ptr, val);
    priv_ptr
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_deferred_reject(priv_ptr: i64, reason: i64) -> i64 {
    wir_promise_reject(priv_ptr, reason);
    priv_ptr
}

// ================= Async/Await ==================

unsafe extern "C" {
    // You already used this above for executors
    fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64;

    // These exist and are used elsewhere in your lowering
    fn wir_obj_get_str(obj: i64, key: i64) -> i64;
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_event_loop_pump_once() -> i32 {
    unsafe extern "C" {
        fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64;
    }
    let ran = EVENT_LOOP.pump_once(
        // microtask: one arg
        |f, a| unsafe {
            let arg = [a];
            let _ = wir_call_closure(f, arg.as_ptr(), 1);
        },
        // timer: zero args
        |fun| unsafe {
            let _ = wir_call_closure(fun, core::ptr::null(), 0);
        },
    );
    ran as i32
}

// Blocking await: returns fulfillment value; rejection returns 0 for now
#[unsafe(no_mangle)]
pub extern "C" fn wir_await(val: i64) -> i64 {
    #[cfg(debug_assertions)]
    eprintln!(
        "[await] wir_await(val={} {})",
        crate::value::dbg_addr(val),
        crate::value::dbg_classify(val)
    );

    #[repr(C)]
    struct Cell {
        ready: bool,
        ok: bool,
        v: i64,
    }

    // Immediates (SMIs/booleans) and null resolve synchronously.
    if val == 0 || (val & 1) == 1 {
        return val;
    }

    extern "C" fn on_f(argv: *const i64, argc: usize) -> i64 {
        unsafe {
            let args = std::slice::from_raw_parts(argv, argc);
            let cell = args.get(0).copied().unwrap_or(0) as *mut Cell;
            let v = args.get(1).copied().unwrap_or(0);
            (*cell).v = v;
            (*cell).ok = true;
            (*cell).ready = true;
        }
        0
    }
    extern "C" fn on_r(argv: *const i64, argc: usize) -> i64 {
        unsafe {
            let args = std::slice::from_raw_parts(argv, argc);
            let cell = args.get(0).copied().unwrap_or(0) as *mut Cell;
            let v = args.get(1).copied().unwrap_or(0);
            (*cell).v = v;
            (*cell).ok = false;
            (*cell).ready = true;
        }
        0
    }

    let cell = Box::into_raw(Box::new(Cell {
        ready: false,
        ok: true,
        v: 0,
    }));

    unsafe {
        let onf = closure_new(on_f as usize, 1);
        closure_set_env_slot(onf, 0, cell as i64);
        let onr = closure_new(on_r as usize, 1);
        closure_set_env_slot(onr, 0, cell as i64);

        // IMPORTANT: do NOT call wir_obj_get_str here.
        // This is a private promise pointer, wire via the native API.
        let _ = wir_promise_then(val, onf, onr);

        #[cfg(debug_assertions)]
        eprintln!("[await] then attached to {}", crate::value::dbg_addr(val));
    }

    // Pump until settled.
    loop {
        unsafe {
            if (*cell).ready {
                break;
            }
        }
        let _ = wir_event_loop_pump_once();
    }

    let out = unsafe { (*cell).v };
    unsafe {
        drop(Box::from_raw(cell));
    }
    out
}
