#![allow(unsafe_op_in_unsafe_fn)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::value::{TAG_STRING, BoxedStr, ObjHeader, is_imm, NULL};
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
    let o = Box::new(WirObj { by_id: HashMap::new(), by_str: HashMap::new() });
    Box::into_raw(o) as i64
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
    let o = unsafe { &*(obj as *const WirObj) };
    o.by_id.get(&id).copied().unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_set_field(obj: i64, field_id_smi: i64, val: i64) -> i64 {
    #[cfg(debug_assertions)] {
        eprintln!("[dbg] wir_obj_set_field called");
    }

    if obj == 0 { return 0; }
    let id = decode_field_smi(field_id_smi);
    let o = unsafe { &mut *(obj as *mut WirObj) };

    let cell = o.by_id.entry(id).or_insert(0);
    let slot: *mut i64 = cell as *mut i64;
    *cell = val;

    #[cfg(feature = "gc")]
    unsafe { NAPALM_GC.post_write_barrier(obj as *mut u8, slot, val) };

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

type StrKey = Vec<u8>; // own the bytes; alignment no longer matters

static STR_PROPS: OnceLock<Mutex<HashMap<usize, HashMap<StrKey, i64>>>> = OnceLock::new();
fn str_props() -> &'static Mutex<HashMap<usize, HashMap<StrKey, i64>>> {
    STR_PROPS.get_or_init(|| Mutex::new(HashMap::new()))
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_str(obj: i64, key: i64) -> i64 {
    if obj == NULL || is_imm(obj) || key == NULL || is_imm(key) {
        return 0;
    }
    unsafe {
        let hdr = &*(key as *const ObjHeader);
        if hdr.tag != TAG_STRING { return 0; }
        let bs = &*(key as *const BoxedStr);
        let bytes = std::slice::from_raw_parts(bs.data, bs.len);

        let top = str_props().lock();
        if let Some(map) = top.get(&(obj as usize)) {
            if let Some(&v) = map.get(bytes) {
                return v;
            }
        }
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_set_str(obj: i64, key: i64, val: i64) -> i64 {
    // Defensive checks
    if obj == NULL || is_imm(obj) || key == NULL || is_imm(key) {
        // Not a heap object or not a boxed string → treat as no-op
        return 0;
    }
    unsafe {
        // Decode boxed string
        let hdr = &*(key as *const ObjHeader);
        if hdr.tag != TAG_STRING {
            return 0; // not a string key
        }
        let bs = &*(key as *const BoxedStr);
        let bytes = std::slice::from_raw_parts(bs.data, bs.len);

        let mut top = str_props().lock();
        let map = top.entry(obj as usize).or_insert_with(HashMap::new);
        map.insert(bytes.to_vec(), val);
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_has_str(obj: i64, key: i64) -> i64 {
    if obj == NULL || is_imm(obj) || key == NULL || is_imm(key) {
        return 0;
    }
    unsafe {
        let hdr = &*(key as *const ObjHeader);
        if hdr.tag != TAG_STRING { return 0; }
        let bs = &*(key as *const BoxedStr);
        let bytes = std::slice::from_raw_parts(bs.data, bs.len);

        let top = str_props().lock();
        let has = top
            .get(&(obj as usize))
            .map(|m| m.contains_key(bytes))
            .unwrap_or(false);
        if has { 1 } else { 0 } // raw 0/1 (not SMI) is what your WIR Bool expects
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_del_str(obj: i64, key: i64) -> i64 {
    if obj == NULL || is_imm(obj) || key == NULL || is_imm(key) {
        return 0;
    }
    unsafe {
        let hdr = &*(key as *const ObjHeader);
        if hdr.tag != TAG_STRING { return 0; }
        let bs = &*(key as *const BoxedStr);
        let bytes = std::slice::from_raw_parts(bs.data, bs.len);

        let mut top = str_props().lock();
        if let Some(map) = top.get_mut(&(obj as usize)) {
            if map.remove(bytes).is_some() {
                return 1;
            }
        }
    }
    0
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