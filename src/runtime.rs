#![allow(unsafe_op_in_unsafe_fn)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_unsafe)]

use crate::jit::wir_make_method_closure;
use crate::value::{TAG_STRING, BoxedStr, ObjHeader, TAG_OBJECT, is_imm, NULL, obj_set_proto, obj_get_proto, obj_get_field_deep, obj_get_str_deep};
use crate::value as v;
use crate::gc::NAPALM_GC;

use ahash::AHashMap as HashMap;
use std::sync::OnceLock;
use parking_lot::Mutex;

// Simple object storage: fast slots by FieldId (u32) + string-key map.
#[repr(C)]
struct WirObj {
    by_id:  HashMap<u32, i64>,
    by_str: HashMap<String, i64>,
}

#[inline(always)] fn smi_to_i64(v: i64) -> i64 { v >> 1 }
#[inline(always)] fn decode_field_smi(v: i64) -> u32 { smi_to_i64(v) as u32 }

#[inline(always)]
unsafe fn boxedstr_to_string(p: i64) -> Option<String> {
    if p == 0 { return None; }
    let s = &*(p as *const BoxedStr);
    let bytes = std::slice::from_raw_parts(s.data, s.len);
    Some(String::from_utf8_lossy(bytes).into_owned())
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_new() -> i64 {
    v::obj_new()
}

#[unsafe(no_mangle)] // or #[unsafe(no_mangle)] if you're using that everywhere else
pub extern "C" fn wir_is_str(v: i64) -> i64 {
    // Immediates (SMIs) and null are not strings
    if v == 0 || (v & 1) == 1 {
        return 0;
    }
    // v is an even (pointer) ValueRepr. Read its header tag.
    unsafe {
        let hdr = &*(v as *const ObjHeader);
        if hdr.tag == TAG_STRING { 1 } else { 0 }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn napalm_yieldpoint() -> i64 {
    #[cfg(feature = "gc")]
    unsafe { NAPALM_GC.yieldpoint(); }

    0
}

// -------- fast-slot path (field id is a SMI) --------

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_field(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 { return 0; }
    let id = decode_field_smi(field_id_smi);
    unsafe { v::obj_get_field(obj, id) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_set_field(obj: i64, field_id_smi: i64, val: i64) -> i64 {
    if obj == 0 { return 0; }
    let id = decode_field_smi(field_id_smi);
    unsafe { v::obj_set_field(obj, id, val); }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_has_field(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 { return 0; }
    let id = decode_field_smi(field_id_smi);
    unsafe { v::obj_has_field(obj, id) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_del_field(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 { return 0; }
    let id = decode_field_smi(field_id_smi);
    unsafe { v::obj_del_field(obj, id) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_set_proto(obj: i64, proto: i64) -> i64 {
    if obj == 0 { return 0; }
    unsafe { obj_set_proto(obj, proto) }
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_proto(obj: i64) -> i64 {
    if obj == 0 { return 0; }
    unsafe { obj_get_proto(obj) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_field_deep(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 { return 0; }
    unsafe { obj_get_field_deep(obj, decode_field_smi(field_id_smi)) }
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_str_deep(obj: i64, key_ptr: i64) -> i64 {
    if obj == 0 { return 0; }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else { return 0; };
    unsafe { obj_get_str_deep(obj, &k) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_method(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 { return 0; }
    let fid_smi_or_val = unsafe { obj_get_field_deep(obj, decode_field_smi(field_id_smi)) };
    if fid_smi_or_val == 0 { return 0; }

    // If it’s an SMI(FuncId), bind it via method trampoline.
    if (fid_smi_or_val & 1) == 1 {
        return unsafe { wir_make_method_closure(fid_smi_or_val) };
    }
    // Otherwise (already-closure or data), return as-is.
    fid_smi_or_val
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_super_get_method(home_proto: i64, field_id_smi: i64) -> i64 {
    let super_proto = wir_obj_get_proto(home_proto);
    if super_proto == 0 { return 0; }
    let fid = unsafe { obj_get_field_deep(super_proto, decode_field_smi(field_id_smi)) };
    if (fid & 1) == 1 { (unsafe { wir_make_method_closure(fid) }) } else { fid } // same binding rule
}

// -------- string-key path (key is a BoxedStr pointer) --------

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_str(obj: i64, key_ptr: i64) -> i64 {
    if obj == 0 { return 0; }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else { return 0; };
    unsafe { v::obj_get_str(obj, &k) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_set_str(obj: i64, key_ptr: i64, val: i64) -> i64 {
    if obj == 0 { return 0; }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else { return 0; };
    unsafe { v::obj_set_str(obj, &k, val); }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_has_str(obj: i64, key_ptr: i64) -> i64 {
    if obj == 0 { return 0; }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else { return 0; };
    unsafe { v::obj_has_str(obj, &k) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_del_str(obj: i64, key_ptr: i64) -> i64 {
    if obj == 0 { return 0; }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else { return 0; };
    unsafe { v::obj_del_str(obj, &k) }
}

// Global: func_id -> (key -> value)
static MEMO_TABLE: OnceLock<Mutex<HashMap<u32, HashMap<i64, i64>>>> = OnceLock::new();

fn memo_lock() -> &'static Mutex<HashMap<u32, HashMap<i64, i64>>> {
    MEMO_TABLE.get_or_init(|| Mutex::new(HashMap::new()))
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Key2(i64, i64);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Key3(i64, i64, i64);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Key4(i64, i64, i64, i64);

static MEMO1: OnceLock<Mutex<HashMap<u32, HashMap<i64, i64>>>>     = OnceLock::new();
static MEMO2: OnceLock<Mutex<HashMap<u32, HashMap<Key2, i64>>>>    = OnceLock::new();
static MEMO3: OnceLock<Mutex<HashMap<u32, HashMap<Key3, i64>>>>    = OnceLock::new();
static MEMO4: OnceLock<Mutex<HashMap<u32, HashMap<Key4, i64>>>>    = OnceLock::new();

fn memo1() -> &'static Mutex<HashMap<u32, HashMap<i64, i64>>> { MEMO1.get_or_init(|| Mutex::new(HashMap::new())) }
fn memo2() -> &'static Mutex<HashMap<u32, HashMap<Key2, i64>>> { MEMO2.get_or_init(|| Mutex::new(HashMap::new())) }
fn memo3() -> &'static Mutex<HashMap<u32, HashMap<Key3, i64>>> { MEMO3.get_or_init(|| Mutex::new(HashMap::new())) }
fn memo4() -> &'static Mutex<HashMap<u32, HashMap<Key4, i64>>> { MEMO4.get_or_init(|| Mutex::new(HashMap::new())) }

#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_get(fid: i64, key: i64, out_ptr: *mut i64) -> i64 {
    let fid_u = fid as u32;
    let guard = memo_lock().lock();
    if let Some(map) = guard.get(&fid_u) {
        if let Some(&val) = map.get(&key) {
            unsafe {
                if !out_ptr.is_null() { *out_ptr = val; }
            }
            return 1; // found
        }
    }
    0 // miss
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_put(fid: i64, key: i64, val: i64) -> i64 {
    let fid_u = fid as u32;
    let mut guard = memo_lock().lock();
    let entry = guard.entry(fid_u).or_insert_with(HashMap::new);
    entry.insert(key, val);
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_get2(fid: i64, k0: i64, k1: i64, out_ptr: *mut i64) -> i64 {
    let fid_u = fid as u32;
    let guard = memo2().lock();
    if let Some(map) = guard.get(&fid_u) {
        if let Some(&val) = map.get(&Key2(k0,k1)) {
            unsafe { if !out_ptr.is_null() { *out_ptr = val; } }
            return 1;
        }
    }
    0
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_put2(fid: i64, k0: i64, k1: i64, val: i64) -> i64 {
    let fid_u = fid as u32;
    let mut guard = memo2().lock();
    let entry = guard.entry(fid_u).or_insert_with(HashMap::new);
    entry.insert(Key2(k0,k1), val);
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_get3(fid: i64, k0: i64, k1: i64, k2: i64, out_ptr: *mut i64) -> i64 {
    let fid_u = fid as u32;
    let guard = memo3().lock();
    if let Some(map) = guard.get(&fid_u) {
        if let Some(&val) = map.get(&Key3(k0,k1,k2)) {
            unsafe { if !out_ptr.is_null() { *out_ptr = val; } }
            return 1;
        }
    }
    0
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_put3(fid: i64, k0: i64, k1: i64, k2: i64, val: i64) -> i64 {
    let fid_u = fid as u32;
    let mut guard = memo3().lock();
    let entry = guard.entry(fid_u).or_insert_with(HashMap::new);
    entry.insert(Key3(k0,k1,k2), val);
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_get4(fid: i64, k0: i64, k1: i64, k2: i64, k3: i64, out_ptr: *mut i64) -> i64 {
    let fid_u = fid as u32;
    let guard = memo4().lock();
    if let Some(map) = guard.get(&fid_u) {
        if let Some(&val) = map.get(&Key4(k0,k1,k2,k3)) {
            unsafe { if !out_ptr.is_null() { *out_ptr = val; } }
            return 1;
        }
    }
    0
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_put4(fid: i64, k0: i64, k1: i64, k2: i64, k3: i64, val: i64) -> i64 {
    let fid_u = fid as u32;
    let mut guard = memo4().lock();
    let entry = guard.entry(fid_u).or_insert_with(HashMap::new);
    entry.insert(Key4(k0,k1,k2,k3), val);
    0
}


#[inline(always)]
unsafe fn as_wirobj_const(obj: i64) -> Option<*const WirObj> {
    if obj == 0 || (obj & 1) == 1 { return None; }        // null or SMI
    let base = obj as *const u8;

    // Read a possible header tag without creating a typed reference.
    let tag = core::ptr::read_unaligned(base as *const u32);
    if tag == TAG_OBJECT {
        // BoxedObj { ObjHeader, by_id, by_str } → skip header
        Some(base.add(core::mem::size_of::<ObjHeader>()) as *const WirObj)
    } else {
        // Header-less WirObj starts at base
        Some(base as *const WirObj)
    }
}
#[inline(always)]
unsafe fn as_wirobj_mut(obj: i64) -> Option<*mut WirObj> {
    as_wirobj_const(obj).map(|p| p as *mut WirObj)
}
