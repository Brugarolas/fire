// src/gc/scanning.rs
use mmtk::vm::scanning::{Scanning, SlotVisitor, RootsWorkFactory};
use mmtk::vm::VMWorkerThread;
use mmtk::util::ObjectReference;

use crate::gc::binding::NapalmVM;
use crate::gc::api::Slot;

pub enum NapalmScanning {}

impl Scanning<NapalmVM> for NapalmScanning {
    #[inline(always)]
    fn scan_object<SV: SlotVisitor<Slot>>(
        _tls: VMWorkerThread,
        _object: ObjectReference,
        _slot_visitor: &mut SV,
    ) {
        // stub: no interior edges reported yet
    }

    #[inline(always)] fn notify_initial_thread_scan_complete(_partial: bool, _tls: VMWorkerThread) {}

    #[inline(always)]
    fn scan_roots_in_mutator_thread(
        _tls: VMWorkerThread,
        _mutator: &'static mut mmtk::Mutator<NapalmVM>,
        _factory: impl RootsWorkFactory<Slot>,
    ) {
        // stub
    }

    #[inline(always)]
    fn scan_vm_specific_roots(
        _tls: VMWorkerThread,
        _factory: impl RootsWorkFactory<Slot>,
    ) {
        // stub
    }

    #[inline(always)] fn supports_return_barrier() -> bool { false }
    #[inline(always)] fn prepare_for_roots_re_scanning() {}
}
