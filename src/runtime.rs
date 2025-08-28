use crate::value::{ValueRepr, make_smi, as_obj_mut, TAG_STRING, BoxedStr, ObjHeader};

use ahash::AHashMap as HashMap;

// Simple object storage: fast slots by FieldId (u32) + string-key map.
#[repr(C)]
struct WirObj {
    by_id:  HashMap<u32, i64>,
    by_str: HashMap<String, i64>,
}

#[inline] fn smi_to_i64(v: i64) -> i64 { v >> 1 }
#[inline] fn decode_field_smi(v: i64) -> u32 { smi_to_i64(v) as u32 }

#[inline]
unsafe fn boxedstr_to_string(p: i64) -> Option<String> {
    if p == 0 { return None; }
    let s = &*(p as *const BoxedStr);
    let bytes = std::slice::from_raw_parts(s.data, s.len);
    Some(String::from_utf8_lossy(bytes).into_owned())
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_new() -> i64 {
    let o = Box::new(WirObj { by_id: HashMap::new(), by_str: HashMap::new() });
    Box::into_raw(o) as i64
}

// -------- fast-slot path (field id is a SMI) --------

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_field(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 { return 0; }
    let id = decode_field_smi(field_id_smi);
    let o = unsafe { &*(obj as *const WirObj) };
    o.by_id.get(&id).copied().unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_set_field(obj: i64, field_id_smi: i64, val: i64) -> i64 {
    if obj == 0 { return 0; }
    let id = decode_field_smi(field_id_smi);
    let o = unsafe { &mut *(obj as *mut WirObj) };
    o.by_id.insert(id, val);
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_has_field(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 { return 0; }
    let id = decode_field_smi(field_id_smi);
    let o = unsafe { &*(obj as *const WirObj) };
    if o.by_id.contains_key(&id) { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_del_field(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 { return 0; }
    let id = decode_field_smi(field_id_smi);
    let o = unsafe { &mut *(obj as *mut WirObj) };
    if o.by_id.remove(&id).is_some() { 1 } else { 0 }
}

// -------- string-key path (key is a BoxedStr pointer) --------

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_str(obj: i64, key_ptr: i64) -> i64 {
    if obj == 0 { return 0; }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else { return 0; };
    let o = unsafe { &*(obj as *const WirObj) };
    o.by_str.get(&k).copied().unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_set_str(obj: i64, key_ptr: i64, val: i64) -> i64 {
    if obj == 0 { return 0; }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else { return 0; };
    let o = unsafe { &mut *(obj as *mut WirObj) };
    o.by_str.insert(k, val);
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_has_str(obj: i64, key_ptr: i64) -> i64 {
    if obj == 0 { return 0; }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else { return 0; };
    let o = unsafe { &*(obj as *const WirObj) };
    if o.by_str.contains_key(&k) { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_del_str(obj: i64, key_ptr: i64) -> i64 {
    if obj == 0 { return 0; }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else { return 0; };
    let o = unsafe { &mut *(obj as *mut WirObj) };
    if o.by_str.remove(&k).is_some() { 1 } else { 0 }
}