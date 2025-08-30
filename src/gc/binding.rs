#![cfg(feature = "gc_mmtk")]

use mmtk::vm::{VMBinding};

pub enum NapalmVM {} // zero-sized marker for our binding

impl VMBinding for NapalmVM {
    type VMSupport = crate::gc::binding::support::Support;
    type VMObjectModel = crate::gc::object_model::NapalmObjectModel;
    type VMScanning    = crate::gc::scanning::NapalmScanning;
    type VMActivePlan  = crate::gc::binding::support::ActivePlan;
    type VMCollection  = crate::gc::binding::support::Collection;
    type VMReferenceGlue = crate::gc::binding::support::ReferenceGlue;
}

pub mod support {
    // We’ll fill these with minimal stubs first (no-ops), then real code.
    pub struct Support;
    pub struct ActivePlan;
    pub struct Collection;
    pub struct ReferenceGlue;
}
