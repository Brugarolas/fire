#![cfg(feature = "gc_mmtk")]

use mmtk::memory_manager;
use mmtk::util::{Address, ObjectReference};
use crate::gc::binding::NapalmVM;
use crate::value::{ValueRepr, is_ptr, NULL};

#[inline]
pub unsafe fn post_write_barrier(object_base: *mut u8, slot: *mut ValueRepr, new_val: ValueRepr) {
    if is_ptr(new_val) && new_val != NULL {
        let objref = ObjectReference::from_raw_address(Address::from_ptr(object_base));
        let slot_addr = Address::from_ptr(slot.cast::<u8>());
        let target = ObjectReference::from_raw_address(Address::from_ptr(new_val as *mut u8));
        // StickyImmix relies on a remembered-set style post barrier.
        memory_manager::object_reference_write_post::<NapalmVM>(objref, slot_addr, target);
    }
}

#[inline]
pub unsafe fn pre_write_barrier(object_base: *mut u8, slot: *mut ValueRepr) {
    let objref = ObjectReference::from_raw_address(Address::from_ptr(object_base));
    let slot_addr = Address::from_ptr(slot.cast::<u8>());
    memory_manager::object_reference_write_pre::<NapalmVM>(objref, slot_addr);
}
