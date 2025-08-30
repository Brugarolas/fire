// src/gc/scanning.rs
use crate::value::*;
use crate::value::ValueRepr;

/// Visit mutable ValueRepr slots contained in `obj_v` and call `f(slot_ptr)` for each.
/// Safety: `obj_v` must be either NULL, an immediate, or a valid Napalm heap object.
pub unsafe fn visit_object_value_slots<F: FnMut(*mut ValueRepr)>(obj_v: ValueRepr, mut f: F) {
    if obj_v == NULL || is_imm(obj_v) { return; }

    let hdr = (obj_v as *mut ObjHeader).as_ref().unwrap();
    match hdr.tag {
        TAG_ARRAY => {
            // We walk the Vec<i64> form (BoxedArray).
            let a = &mut *(obj_v as *mut BoxedArray);
            let len = a.buf.len();
            let base = a.buf.as_mut_ptr();
            for i in 0..len {
                let slot = base.add(i);
                // Hand out the slot regardless of its current content
                f(slot);
            }
        }

        TAG_OBJECT => {
            let o = &mut *(obj_v as *mut BoxedObj);
            for v in o.by_id.values_mut()  { f(v as *mut ValueRepr); }
            for v in o.by_str.values_mut() { f(v as *mut ValueRepr); }
        }

        TAG_BOXED_F64 => { /* no interior refs */ }
        TAG_STRING    => { /* no interior refs */ }
        _ => { /* future tags go here */ }
    }
}

