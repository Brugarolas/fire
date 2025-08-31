// File: src/gc/roots.rs
//! Global registry of live `ExecutionContext` frames.

use once_cell::sync::Lazy;
use parking_lot::RwLock;
use crate::vm::ExecutionContext;

/* ── ①  raw pointers are not Send/Sync → wrap them ───────── */
#[derive(Copy, Clone)]
struct CtxPtr(*const ExecutionContext);
unsafe impl Send for CtxPtr {}
unsafe impl Sync for CtxPtr {}

static FRAMES: Lazy<RwLock<Vec<CtxPtr>>> = Lazy::new(|| RwLock::new(Vec::new()));

#[inline(always)]
pub fn register(c: &ExecutionContext) {
    FRAMES.write().push(CtxPtr(c as *const _));
}
#[inline(always)]
pub fn unregister(c: &ExecutionContext) {
    let addr = c as *const _ as usize;
    let mut g = FRAMES.write();
    if let Some(i) = g.iter().position(|p| p.0 as usize == addr) {
        g.swap_remove(i);
    }
}

#[inline(always)]
pub fn iter<'a>() -> impl Iterator<Item = &'a ExecutionContext> + 'a {
    FRAMES.read()
        .clone()
        .into_iter()
        .map(|p| unsafe { &*p.0 })
}
