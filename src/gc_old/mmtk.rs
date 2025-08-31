// src/gc/mmtk.rs
use once_cell::sync::OnceCell;
use mmtk::MMTK;
use mmtk::memory_manager;
use crate::gc::binding::NapalmVM;
use crate::gc::api::with_mutator;

static MMTK: OnceCell<MMTK<NapalmVM>> = OnceCell::new();

pub fn get_mmtk() -> &'static MMTK<NapalmVM> {
    MMTK.get().expect("MMTk not initialized")
}

pub fn init_mmtk_for_stickyimmix() -> &'static MMTK<NapalmVM> {
    use mmtk::plan::sticky_immix::StickyImmix;
    // mmtk::plan::STICKY_IMMIX_CONSTRAINTS
    let mmtk = mmtk::MMTKBuilder::new()
        .set_plan::<StickyImmix<NapalmVM>>()
        .build();
    let _ = MMTK.set(mmtk);
    get_mmtk()
}

#[inline(always)]
pub fn yieldpoint() {
    with_mutator(|mutator| {
        memory_manager::yieldpoint::<NapalmVM>(mutator);
    });
}
