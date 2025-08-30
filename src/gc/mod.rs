// src/gc/mod.rs
pub mod api;
pub mod binding;
// pub mod barrier;
pub mod roots;
pub mod mmtk;
pub mod scanning;
pub mod object_model;

/// VM-facing hooks. These are no-ops unless `gc_mmtk` is enabled.
pub mod runtime {
    #[inline(always)]
    pub fn init() { crate::gc::mmtk::init(); }

    /// Bind the current thread as a mutator (safe to call multiple times).
    #[inline(always)]
    pub fn bind_current_thread() { crate::gc::mmtk::bind_current_thread(); }

    /// Optional shutdown (useful in tests).
    #[inline(always)]
    pub fn shutdown() { crate::gc::mmtk::shutdown(); }
}

pub use api::{GcInit, GcHandle, alloc_raw, alloc_slow_path};
pub use barrier::{post_write_barrier, pre_write_barrier};