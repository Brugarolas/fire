/// Safepoint/yieldpoint.
/// Phase 1: no-op. Phase 2+ will call into MMTk yieldpoint.
#[inline]
pub fn yieldpoint() {}
