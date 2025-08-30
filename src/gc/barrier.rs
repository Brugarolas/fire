// src/gc/barrier.rs
use crate::gc::api;
use crate::value::ValueRepr;

#[inline(always)]
pub unsafe fn post_write_barrier(object_base: *mut u8, slot: *mut ValueRepr, new_val: ValueRepr) {
    unsafe { api::post_write_barrier(object_base, slot, new_val) };
}

#[inline(always)]
pub unsafe fn pre_write_barrier(object_base: *mut u8, slot: *mut ValueRepr) {
    unsafe { api::pre_write_barrier(object_base, slot) };
}
