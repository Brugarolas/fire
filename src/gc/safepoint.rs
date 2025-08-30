/// src/gc/yieldpoint.
/// Phase 1: no-op. Phase 2+ will call into MMTk yieldpoint.
#[inline(always)]
pub fn yieldpoint() {
    // JIT or interpreter can call this at loop backedges / call sites.
    crate::gc::mmtk::yieldpoint();
}
