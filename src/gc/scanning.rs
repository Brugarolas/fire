/// Object scanning entry-points (called from the future MMTk binding).
/// Phase 1: stubs (so we can compile code that references them later).

#[inline]
pub fn scan_object_edges(_obj_addr: *mut u8, _cb_edge: &mut impl FnMut(*mut i64)) {
    // In Phase 4 we’ll:
    //  - read the ObjHeader to decide the tag
    //  - iterate BoxedArray.buf, BoxedObj.{by_id,by_str}, and closure env
    //  - for each &mut i64 slot that may hold a ref, call cb_edge(slot_ptr)
}

#[inline]
pub fn scan_vm_roots(_cb_edge: &mut impl FnMut(*mut i64)) {
    // In Phase 4 we’ll enumerate from gc::roots::with_roots(...)
}
