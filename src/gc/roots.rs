// src/gc/roots.rs
use std::cell::RefCell;

/// Shadow stack holds slices of GC-visible slots (ValueRepr = i64).
/// Phase 1: it’s inert, but the API is stable.
thread_local! {
    static SHADOW: RefCell<Vec<(*mut i64, usize)>> = RefCell::new(Vec::new());
}

#[inline]
pub unsafe fn push_range(base: *mut i64, slots: usize) {
    SHADOW.with(|s| s.borrow_mut().push((base, slots)));
}
#[inline]
pub fn pop_range() {
    SHADOW.with(|s| { s.borrow_mut().pop(); });
}

/// Iterate current roots (Phase 1: just exposes an iterator for future use)
pub fn with_roots<F: FnMut(*mut i64)>(mut f: F) {
    SHADOW.with(|s| {
        for (base, n) in s.borrow().iter().copied() {
            for i in 0..n {
                let slot = unsafe { base.add(i) };
                f(slot);
            }
        }
    });
}
