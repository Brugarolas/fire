// src/gc/api_nop.rs
use crate::value::ValueRepr;

pub struct GcInit;
pub struct GcHandle;

impl GcInit {
    #[inline] pub fn init() -> GcHandle { GcHandle }
}

#[inline] pub fn attach_current_thread() {}
#[inline] pub fn detach_current_thread() {}

/// Fast-path alloc (no GC): just use libc as a placeholder so callers compile.
/// Replace with your bump alloc if you have one outside MMTk.
pub unsafe fn alloc_raw(bytes: usize, align: usize) -> *mut u8 {
    // simple aligned alloc fallback
    std::alloc::alloc(std::alloc::Layout::from_size_align(bytes, align).unwrap())
}

pub unsafe fn alloc_slow_path(bytes: usize, align: usize) -> *mut u8 {
    std::alloc::alloc(std::alloc::Layout::from_size_align(bytes, align).unwrap())
}

#[inline] pub unsafe fn post_alloc_object(_obj_ptr: *mut u8, _bytes: usize) {}

#[inline(always)]
pub unsafe fn post_write_barrier(_object_base: *mut u8, _slot: *mut ValueRepr, _new_val: ValueRepr) {
    // no-op
}

#[inline(always)]
pub unsafe fn pre_write_barrier(_object_base: *mut u8, _slot: *mut ValueRepr) {
    // no-op
}
