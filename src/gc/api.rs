// src/gc/api.rs
#![cfg(feature = "gc_mmtk")]

use core::ptr;
use mmtk::{
    memory_manager,
    util::{Address, ObjectReference},
    AllocationSemantics, Mutator,
};
use once_cell::sync::OnceCell;

use crate::gc::binding::NapalmVM;
use crate::gc::mmtk_globals::get_mmtk;

thread_local! {
    static TLS_MUTATOR: std::cell::RefCell<Option<Box<Mutator<NapalmVM>>>> =
        const { std::cell::RefCell::new(None) };
}

pub struct GcInit;
pub struct GcHandle;

/// Call once per process (e.g., early in main) to create the MMTk instance.
/// You still need to attach each mutator thread (see below).
impl GcInit {
    pub fn init() -> GcHandle {
        let _ = crate::gc::mmtk_globals::init_mmtk_for_stickyimmix();
        GcHandle
    }
}

/// Attach the current thread to MMTk and create a mutator.
/// Safe to call multiple times per thread (no-op if already attached).
pub fn attach_current_thread() {
    TLS_MUTATOR.with(|c| {
        if c.borrow().is_none() {
            let mmtk = get_mmtk();
            let mutator = memory_manager::bind_mutator::<NapalmVM>(mmtk);
            *c.borrow_mut() = Some(mutator);
        }
    });
}

/// Detach (optional for now; some bindings do this on thread exit).
pub fn detach_current_thread() {
    TLS_MUTATOR.with(|c| {
        let _ = c.borrow_mut().take();
    });
}

#[inline(always)]
fn with_mutator<R>(f: impl FnOnce(&mut Mutator<NapalmVM>) -> R) -> R {
    TLS_MUTATOR.with(|c| {
        let mut guard = c.borrow_mut();
        let m = guard
            .as_deref_mut()
            .expect("MMTk mutator not attached on this thread. Call gc::attach_current_thread().");
        f(m)
    })
}

/// Fast-path allocation. Returns null on failure so the caller can slow-path.
pub unsafe fn alloc_raw(bytes: usize, align: usize) -> *mut u8 {
    with_mutator(|mutator| {
        let addr = memory_manager::alloc::<NapalmVM>(
            mutator,
            bytes,
            align,
            /*offset=*/ 0,
            AllocationSemantics::Default,
        );
        if addr.is_zero() { ptr::null_mut() } else { addr.to_mut_ptr::<u8>() }
    })
}

/// Slow-path allocation (may trigger GC inside MMTk).
pub unsafe fn alloc_slow_path(bytes: usize, align: usize) -> *mut u8 {
    with_mutator(|mutator| {
        let addr = memory_manager::alloc_slow::<NapalmVM>(
            mutator,
            bytes,
            align,
            /*offset=*/ 0,
            AllocationSemantics::Default,
        );
        debug_assert!(!addr.is_zero());
        addr.to_mut_ptr::<u8>()
    })
}

/// Must be called *after* you wrote a valid header to `obj_ptr`
/// (tag + whatever your VM requires) and before you publish edges.
pub unsafe fn post_alloc_object(obj_ptr: *mut u8, bytes: usize) {
    with_mutator(|mutator| {
        let objref = ObjectReference::from_raw_address(Address::from_mut_ptr(obj_ptr));
        memory_manager::post_alloc::<NapalmVM>(
            mutator,
            objref,
            bytes,
            AllocationSemantics::Default,
        );
    });
}
