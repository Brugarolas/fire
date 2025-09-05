// runtime/natives_timers.rs (new)

use crate::event_loop::{EVENT_LOOP, TimerKind};
use crate::jit::JitFnPtr;
use crate::jit::wir_call_closure;

// Helpers you already have for calling a closure value:
unsafe extern "C" {
    // Call a closure value (tagged i64) with zero/one args as your engine provides.
    // Adjust signature to your existing call trampoline:
    fn napalm_call_closure(fun: i64, arg0: i64) -> i64;
}

// setTimeout(fn, ms) -> id
#[unsafe(no_mangle)]
pub extern "C" fn wir_set_timeout(fun: i64, delay_ms: i64) -> i64 {
    EVENT_LOOP.schedule(fun, delay_ms, TimerKind::Timeout) as i64
}

// setInterval(fn, ms) -> id
#[unsafe(no_mangle)]
pub extern "C" fn wir_set_interval(fun: i64, period_ms: i64) -> i64 {
    EVENT_LOOP.schedule(fun, period_ms, TimerKind::Interval) as i64
}

// clearTimeout(id)
#[unsafe(no_mangle)]
pub extern "C" fn wir_clear_timeout(id: i64) -> i64 {
    EVENT_LOOP.clear(id as u64);
    0
}

// clearInterval(id)
#[unsafe(no_mangle)]
pub extern "C" fn wir_clear_interval(id: i64) -> i64 {
    EVENT_LOOP.clear(id as u64);
    0
}

/// Drain all due timers/intervals until the event loop is quiescent.
/// Call this **after** a top-level JIT invocation returns.
pub fn drain_event_loop_to_quiescence() {
    EVENT_LOOP.run_until_quiescent(|fun| unsafe {
        // Timers here are zero-arg closures; pass null argv/argc=0.
        let _ = wir_call_closure(fun, std::ptr::null(), 0);
    });
}

/// C-ABI helper if you want to pump from the embedding.
#[unsafe(no_mangle)]
pub extern "C" fn napalm_pump_to_quiescence() -> i64 {
    drain_event_loop_to_quiescence();
    0
}

pub fn invoke_and_pump(entry: JitFnPtr, args: &[i64]) -> i64 {
    let ret = unsafe { (entry)(args.as_ptr(), args.len()) };
    drain_event_loop_to_quiescence();
    ret
}

#[unsafe(no_mangle)]
pub extern "C" fn event_loop_yieldpoint() -> i64 {
    unsafe {
        unsafe extern "C" { fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64; }

        // Drain a chunk of microtasks FIRST
        let _ = EVENT_LOOP.run_microtasks(32, |f, a| {
            let arg = [a];
            let _ = wir_call_closure(f, arg.as_ptr(), 1);
        });

        // Then poll timers and run a few macrotasks
        EVENT_LOOP.poll_due_and_enqueue();
        // Run just a few ready closures; avoid full drain while inside JIT.
        let _ = EVENT_LOOP.run_ready(4, |fun| {
            let _ = wir_call_closure(fun, std::ptr::null(), 0);
        });
    }
    0
}