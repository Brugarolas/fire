// src/gc/mod.rs
pub mod api;
pub mod api_nop;
pub mod binding;
pub mod object_model;
pub mod alloc;
pub mod barrier;
pub mod roots;
pub mod mmtk;
pub mod safepoint;
pub mod scanning;

/// VM-facing hooks. These are no-ops unless `gc_mmtk` is enabled.
pub mod runtime {
    #[inline]
    pub fn init() { crate::gc::mmtk::init(); }

    /// Bind the current thread as a mutator (safe to call multiple times).
    #[inline]
    pub fn bind_current_thread() { crate::gc::mmtk::bind_current_thread(); }

    /// Optional shutdown (useful in tests).
    #[inline]
    pub fn shutdown() { crate::gc::mmtk::shutdown(); }
}

pub use mmtk_globals::get_mmtk;
pub use api::{GcInit, GcHandle, alloc_raw, alloc_slow_path};
pub use barriers::{post_write_barrier, pre_write_barrier};