#![cfg(feature = "gc_mmtk")]
use mmtk::vm::ObjectModel;

pub struct NapalmObjectModel;

impl<VM: mmtk::vm::VMBinding> ObjectModel<VM> for NapalmObjectModel {
    // We will fill in object size/align/offset helpers and ref iteration soon.
}