// src/gc/object_model.rs
use mmtk::vm::object_model::ObjectModel;
use mmtk::vm::object_model::specs::*;
use mmtk::util::{Address, ObjectReference};
use mmtk::plan::CopySemantics;
use mmtk::util::copy::GCWorkerCopyContext;

use crate::gc::binding::NapalmVM;

pub enum NapalmObjectModel {}

impl ObjectModel<NapalmVM> for NapalmObjectModel {
    const GLOBAL_LOG_BIT_SPEC: VMGlobalLogBitSpec = VMGlobalLogBitSpec::side_first();
    const LOCAL_MARK_BIT_SPEC: VMLocalMarkBitSpec = VMLocalMarkBitSpec::side_first();
    const LOCAL_LOS_MARK_NURSERY_SPEC: VMLocalLOSMarkNurserySpec = VMLocalLOSMarkNurserySpec::side_after(Self::LOCAL_MARK_BIT_SPEC.as_spec());
    const LOCAL_PINNING_BIT_SPEC: VMLocalPinningBitSpec = VMLocalPinningBitSpec::side_after(Self::LOCAL_LOS_MARK_NURSERY_SPEC.as_spec());
    const LOCAL_FORWARDING_BITS_SPEC: VMLocalForwardingBitsSpec = VMLocalForwardingBitsSpec::side_after(Self::LOCAL_PINNING_BIT_SPEC.as_spec());
    const LOCAL_FORWARDING_POINTER_SPEC: VMLocalForwardingPointerSpec = VMLocalForwardingPointerSpec::side_after(Self::LOCAL_FORWARDING_BITS_SPEC.as_spec());

    const OBJECT_REF_OFFSET_LOWER_BOUND: isize = 0;

    #[inline(always)] fn ref_to_object_start(object: ObjectReference) -> Address { object.to_raw_address() }
    #[inline(always)] fn ref_to_header(object: ObjectReference) -> Address { object.to_raw_address() }

    // Minimal placeholders; we’ll wire sizes later.
    fn get_current_size(_object: ObjectReference) -> usize { 0 }
    fn get_size_when_copied(object: ObjectReference) -> usize { Self::get_current_size(object) }
    fn get_align_when_copied(_object: ObjectReference) -> usize { 8 }
    fn get_align_offset_when_copied(_object: ObjectReference) -> usize { 0 }

    fn get_type_descriptor(_reference: ObjectReference) -> &'static [i8] {
        &[] // not used yet
    }

    fn copy(
        from: ObjectReference,
        _semantics: CopySemantics,
        _copy_context: &mut GCWorkerCopyContext<NapalmVM>,
    ) -> ObjectReference {
        // We shouldn’t be copying with StickyImmix normally; leave a trap for now.
        panic!("copy not implemented")
    }

    fn copy_to(
        _from: ObjectReference,
        _to: ObjectReference,
        _region: Address,
    ) -> Address {
        panic!("copy_to not implemented")
    }

    fn get_reference_when_copied_to(_from: ObjectReference, _to: Address) -> ObjectReference {
        panic!("get_reference_when_copied_to not implemented")
    }

    fn dump_object(_object: ObjectReference) {}
}
