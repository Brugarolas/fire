// src/gc/mmtk_globals.rs
#![cfg(feature = "gc_mmtk")]

use once_cell::sync::OnceCell;
use mmtk::MMTK;
use mmtk::memory_manager;
use crate::gc::binding::NapalmVM;

static MMTK: OnceCell<MMTK<NapalmVM>> = OnceCell::new();

pub fn get_mmtk() -> &'static MMTK<NapalmVM> {
    MMTK.get().expect("MMTk not initialized")
}

pub fn init_mmtk_for_stickyimmix() -> &'static MMTK<NapalmVM> {
    // Prefer an explicit plan to avoid surprises.
    // If your mmtk-core exports the module as `stickyimmix`, change the import below accordingly.
    use mmtk::plan::sticky_immix::StickyImmix;

    let mmtk = mmtk::MMTKBuilder::new()
        .set_plan::<StickyImmix<NapalmVM>>()   // <- pick the plan here
        .build();

    let _ = MMTK.set(mmtk);
    get_mmtk()
}

/// Poll the GC at a safepoint/backedge.
/// Call this periodically in long-running loops and in runtime helpers.
#[inline(always)]
pub fn yieldpoint() {
    with_mutator(|m| {
        memory_manager::yieldpoint::<NapalmVM>(m);
    });
}
