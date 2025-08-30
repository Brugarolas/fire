/// Post-write barrier hook.
/// Phase 1: no-op (we’ll call MMTk’s store buffer in Phase 5).
#[inline(always)]
pub fn post_write(_obj: i64, _slot_addr: *mut i64, _new_val: i64) {
    // no-op for now
}

/// Convenience: only call the barrier if `val` looks like a heap ref (even, non-zero).
#[inline(always)]
pub fn post_write_if_ptr(obj: i64, slot_addr: *mut i64, val: i64) {
    if (val & 1) == 0 && val != 0 {
        post_write(obj, slot_addr, val);
    }
}
