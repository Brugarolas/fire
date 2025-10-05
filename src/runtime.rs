#![allow(unsafe_op_in_unsafe_fn)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_unsafe)]

use crate::gc::NAPALM_GC;
use crate::jit::wir_make_method_closure;
use crate::value as v;
use crate::value::{
    BoxedArray, BoxedClosure, BoxedF64, BoxedMap, BoxedObj, BoxedSet, BoxedStr, Value,
    NULL, ObjHeader, TAG_ARRAY, TAG_BOXED_F64, TAG_CLOSURE, TAG_MAP, TAG_OBJECT, TAG_SET,
    TAG_STRING, bool_to_value, is_imm, map_new, obj_assign, obj_clone_shallow,
    obj_get_field_deep, obj_get_proto, obj_get_str_deep, obj_set_proto, set_new, value_to_bool,
};

use crate::helpers::collections::{ConcurrentHashMap, HashMap, HashSet};
use core::cmp::min;
use parking_lot::Mutex;
use std::slice;
use std::sync::OnceLock;

// Simple object storage: fast slots by FieldId (u32) + string-key map.
#[repr(C)]
struct WirObj {
    by_id: HashMap<u32, i64>,
    by_str: HashMap<String, i64>,
}

#[inline(always)]
fn smi_to_i64(v: i64) -> i64 {
    v >> 1
}
#[inline(always)]
fn decode_field_smi(v: i64) -> u32 {
    smi_to_i64(v) as u32
}

#[inline(always)]
fn is_heap_ptr(v: i64) -> bool {
    v::is_ptr(v)
}

#[inline(always)]
fn heap_tag(v: i64) -> Option<u32> {
    if is_heap_ptr(v) {
        unsafe { (v as *const ObjHeader).as_ref().map(|h| h.tag) }
    } else {
        None
    }
}

#[inline(always)]
fn is_closure_value(v: i64) -> bool {
    matches!(heap_tag(v), Some(TAG_CLOSURE))
}

#[inline(always)]
unsafe fn boxedstr_to_string(p: i64) -> Option<String> {
    if p == 0 {
        return None;
    }
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
    if v == NULL || is_imm(v) || v::is_bool(v) {
        return bool_to_value(false);
    }
    // v is an even (pointer) ValueRepr. Read its header tag.
    unsafe {
        let hdr = &*(v as *const ObjHeader);
        bool_to_value(hdr.tag == TAG_STRING)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn napalm_yieldpoint() -> i64 {
    #[cfg(feature = "gc")]
    unsafe {
        NAPALM_GC.yieldpoint();
    }

    0
}

// -------- fast-slot path (field id is a SMI) --------

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_field(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 {
        return 0;
    }
    let id = decode_field_smi(field_id_smi);
    unsafe { v::obj_get_field(obj, id) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_set_field(obj: i64, field_id_smi: i64, val: i64) -> i64 {
    if obj == 0 {
        return 0;
    }
    let id = decode_field_smi(field_id_smi);
    unsafe {
        v::obj_set_field(obj, id, val);
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_has_field(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 {
        return bool_to_value(false);
    }
    let id = decode_field_smi(field_id_smi);
    unsafe { v::obj_has_field(obj, id) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_del_field(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 {
        return bool_to_value(false);
    }
    let id = decode_field_smi(field_id_smi);
    unsafe { v::obj_del_field(obj, id) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_set_proto(obj: i64, proto: i64) -> i64 {
    if obj == 0 {
        return 0;
    }
    unsafe { obj_set_proto(obj, proto) }
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_proto(obj: i64) -> i64 {
    if obj == 0 {
        return 0;
    }
    unsafe { obj_get_proto(obj) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_field_deep(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 {
        return 0;
    }
    unsafe { obj_get_field_deep(obj, decode_field_smi(field_id_smi)) }
}
#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_str_deep(obj: i64, key_ptr: i64) -> i64 {
    if obj == 0 {
        return 0;
    }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else {
        return 0;
    };
    unsafe { obj_get_str_deep(obj, &k) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_method(obj: i64, field_id_smi: i64) -> i64 {
    if obj == 0 {
        return 0;
    }
    let fid_smi_or_val = unsafe { obj_get_field_deep(obj, decode_field_smi(field_id_smi)) };
    if fid_smi_or_val == 0 {
        return 0;
    }

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
    if super_proto == 0 {
        return 0;
    }
    let fid = unsafe { obj_get_field_deep(super_proto, decode_field_smi(field_id_smi)) };
    if (fid & 1) == 1 {
        (unsafe { wir_make_method_closure(fid) })
    } else {
        fid
    } // same binding rule
}

// -------- string-key path (key is a BoxedStr pointer) --------

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_get_str(obj: i64, key_ptr: i64) -> i64 {
    if obj == 0 {
        return 0;
    }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else {
        return 0;
    };
    unsafe { v::obj_get_str(obj, &k) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_set_str(obj: i64, key_ptr: i64, val: i64) -> i64 {
    if obj == 0 {
        return 0;
    }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else {
        return 0;
    };
    unsafe {
        v::obj_set_str(obj, &k, val);
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_has_str(obj: i64, key_ptr: i64) -> i64 {
    if obj == 0 {
        return bool_to_value(false);
    }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else {
        return bool_to_value(false);
    };
    unsafe { v::obj_has_str(obj, &k) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_del_str(obj: i64, key_ptr: i64) -> i64 {
    if obj == 0 {
        return bool_to_value(false);
    }
    let Some(k) = (unsafe { boxedstr_to_string(key_ptr) }) else {
        return bool_to_value(false);
    };
    unsafe { v::obj_del_str(obj, &k) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_equals(s1_val: i64, s2_val: i64) -> i64 {
    // Fast path: if the values are identical (e.g., two SMIs, two pointers to the
    // same object, or both null), they are equal.
    if s1_val == s2_val {
        return bool_to_value(true);
    }

    if !is_heap_ptr(s1_val) || !is_heap_ptr(s2_val) {
        return bool_to_value(false);
    }

    if heap_tag(s1_val) != Some(TAG_STRING) || heap_tag(s2_val) != Some(TAG_STRING) {
        return bool_to_value(false);
    }

    let s1 = &*(s1_val as *const BoxedStr);
    let s2 = &*(s2_val as *const BoxedStr);

    if s1.len != s2.len {
        return bool_to_value(false);
    }

    if s1.len == 0 {
        return bool_to_value(true);
    }

    let slice1 = std::slice::from_raw_parts(s1.data, s1.len);
    let slice2 = std::slice::from_raw_parts(s2.data, s2.len);
    bool_to_value(slice1 == slice2)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_assign(dst: i64, src: i64) -> i64 {
    unsafe { obj_assign(dst, src) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_is_nullish(v: i64) -> i64 {
    bool_to_value(v == NULL)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_obj_clone(obj: i64) -> i64 {
    unsafe { obj_clone_shallow(obj) }
}

// --- Definiciones de claves para funciones de 2, 3 y 4 argumentos ---
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Key2(i64, i64);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Key3(i64, i64, i64);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Key4(i64, i64, i64, i64);

// --- Tablas de memoización globales, lock-free y con el hasher AES ---
static MEMO1: OnceLock<ConcurrentHashMap<(u32, i64), i64>> = OnceLock::new();
static MEMO2: OnceLock<ConcurrentHashMap<(u32, Key2), i64>> = OnceLock::new();
static MEMO3: OnceLock<ConcurrentHashMap<(u32, Key3), i64>> = OnceLock::new();
static MEMO4: OnceLock<ConcurrentHashMap<(u32, Key4), i64>> = OnceLock::new();

// --- Inicializadores para las tablas de memoización ---
fn memo1() -> &'static ConcurrentHashMap<(u32, i64), i64> {
    MEMO1.get_or_init(|| ConcurrentHashMap::new())
}
fn memo2() -> &'static ConcurrentHashMap<(u32, Key2), i64> {
    MEMO2.get_or_init(|| ConcurrentHashMap::new())
}
fn memo3() -> &'static ConcurrentHashMap<(u32, Key3), i64> {
    MEMO3.get_or_init(|| ConcurrentHashMap::new())
}
fn memo4() -> &'static ConcurrentHashMap<(u32, Key4), i64> {
    MEMO4.get_or_init(|| ConcurrentHashMap::new())
}

// --- API C para el Runtime de Napalm ---

// -- Funciones para 1 argumento --
#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_get(fid: i64, key: i64, out_ptr: *mut i64) -> i64 {
    let fid_u = fid as u32;
    let guard = &mut memo1().guard();

    if let Some(val) = memo1().get(&(fid_u, key), guard) {
        unsafe {
            if !out_ptr.is_null() {
                *out_ptr = *val;
            }
        }
        return bool_to_value(true);
    }
    bool_to_value(false)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_put(fid: i64, key: i64, val: i64) -> i64 {
    let fid_u = fid as u32;
    let guard = &mut memo1().guard();

    memo1().insert((fid_u, key), val, guard);
    0
}

// -- Funciones para 2 argumentos --
#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_get2(fid: i64, k0: i64, k1: i64, out_ptr: *mut i64) -> i64 {
    let fid_u = fid as u32;
    let guard = &mut memo2().guard();

    if let Some(val) = memo2().get(&(fid_u, Key2(k0, k1)), guard) {
        unsafe {
            if !out_ptr.is_null() {
                *out_ptr = *val;
            }
        }
        return bool_to_value(true);
    }
    bool_to_value(false)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_put2(fid: i64, k0: i64, k1: i64, val: i64) -> i64 {
    let fid_u = fid as u32;
    let guard = &mut memo2().guard();

    memo2().insert((fid_u, Key2(k0, k1)), val, guard);
    0
}

// -- Funciones para 3 argumentos --
#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_get3(fid: i64, k0: i64, k1: i64, k2: i64, out_ptr: *mut i64) -> i64 {
    let fid_u = fid as u32;
    let guard = &mut memo3().guard();

    if let Some(val) = memo3().get(&(fid_u, Key3(k0, k1, k2)), guard) {
        unsafe {
            if !out_ptr.is_null() {
                *out_ptr = *val;
            }
        }
        return bool_to_value(true);
    }
    bool_to_value(false)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_put3(fid: i64, k0: i64, k1: i64, k2: i64, val: i64) -> i64 {
    let fid_u = fid as u32;
    let guard = &mut memo3().guard();

    memo3().insert((fid_u, Key3(k0, k1, k2)), val, guard);
    0
}

// -- Funciones para 4 argumentos --
#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_get4(fid: i64, k0: i64, k1: i64, k2: i64, k3: i64, out_ptr: *mut i64) -> i64 {
    let fid_u = fid as u32;
    let guard = &mut memo4().guard();

    if let Some(val) = memo4().get(&(fid_u, Key4(k0, k1, k2, k3)), guard) {
        unsafe {
            if !out_ptr.is_null() {
                *out_ptr = *val;
            }
        }
        return bool_to_value(true);
    }
    bool_to_value(false)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_memo_put4(fid: i64, k0: i64, k1: i64, k2: i64, k3: i64, val: i64) -> i64 {
    let fid_u = fid as u32;
    let guard = &mut memo4().guard();

    memo4().insert((fid_u, Key4(k0, k1, k2, k3)), val, guard);
    0
}

#[inline(always)]
unsafe fn as_wirobj_const(obj: i64) -> Option<*const WirObj> {
    if obj == 0 || (obj & 1) == 1 {
        return None;
    } // null or SMI
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

// -----------------------------------------------------------------------------
// Pretty printer (safe for cycles; bounded depth/width)
// -----------------------------------------------------------------------------

const PP_MAX_DEPTH: usize = 3;
const PP_MAX_ELEMS: usize = 50;

pub fn fmt_value(v: i64) -> String {
    let mut seen: HashSet<u64> = HashSet::new();
    pp(v, 0, PP_MAX_DEPTH, PP_MAX_ELEMS, &mut seen)
}

fn pp(v: i64, depth: usize, max_depth: usize, max_elems: usize, seen: &mut HashSet<u64>) -> String {
    if let Some(b) = value_to_bool(v) {
        return if b { "true".to_string() } else { "false".to_string() };
    }

    // Small ints (SMI)
    if is_imm(v) {
        return smi_to_i64(v).to_string();
    }

    // Null
    if v == NULL {
        return "null".to_string();
    }

    // Heap objects: guard cycles
    let addr = v as u64;
    if !seen.insert(addr) {
        return "<cycle>".to_string();
    }

    let out = unsafe {
        let hdr = (v as *const ObjHeader).as_ref();
        if let Some(h) = hdr {
            match h.tag {
                TAG_BOXED_F64 => {
                    let f = &*(v as *const BoxedF64);
                    format!("{}", f.val)
                }

                TAG_STRING => {
                    // "{:?}" gives us quoted + escaped output
                    let s = &*(v as *const BoxedStr);
                    let bytes: &[u8] = if s.data.is_null() || s.len == 0 {
                        &[]
                    } else {
                        slice::from_raw_parts(s.data, s.len)
                    };
                    format!("{:?}", String::from_utf8_lossy(bytes))
                }

                TAG_ARRAY => {
                    if depth >= max_depth {
                        "[]".to_string()
                    } else {
                        let a = &*(v as *const BoxedArray);
                        let mut s = String::from("[");
                        let n = min(a.buf.len(), max_elems);
                        for i in 0..n {
                            if i > 0 {
                                s.push_str(", ");
                            }
                            s.push_str(&pp(a.buf[i], depth + 1, max_depth, max_elems, seen));
                        }
                        if a.buf.len() > n {
                            s.push_str(", …");
                        }
                        s.push(']');
                        s
                    }
                }

                TAG_OBJECT => {
                    if depth >= max_depth {
                        "{}".to_string()
                    } else {
                        let o = &*(v as *const BoxedObj);
                        let mut s = String::from("{");
                        let mut wrote = 0usize;
                        let mut first = true;

                        // Print string-keyed props first (sorted for stability)
                        let mut skeys: Vec<&String> = o.by_str.keys().collect();
                        skeys.sort_unstable();
                        let is_class_instance = skeys
                            .iter()
                            .any(|k| k.starts_with("__get__") || k.starts_with("__set__"));
                        for k in skeys {
                            if wrote >= max_elems {
                                break;
                            }
                            let key_str = k.as_str();
                            if key_str.starts_with("__get__") || key_str.starts_with("__set__") {
                                continue;
                            }
                            let val = o.by_str.get(k).copied().unwrap_or(NULL);
                            if is_class_instance && is_closure_value(val) {
                                continue;
                            }
                            if !first {
                                s.push_str(", ");
                            } else {
                                first = false;
                            }
                            s.push_str(&format!(
                                "{:?}: {}",
                                k,
                                pp(val, depth + 1, max_depth, max_elems, seen)
                            ));
                            wrote += 1;
                        }

                        // Then FieldId (u32) props (also sorted)
                        if wrote < max_elems && !is_class_instance {
                            let mut fids: Vec<u32> = o.by_id.keys().copied().collect();
                            fids.sort_unstable();
                            for id in fids {
                                if wrote >= max_elems {
                                    break;
                                }
                                if !first {
                                    s.push_str(", ");
                                } else {
                                    first = false;
                                }
                                let val = o.by_id.get(&id).copied().unwrap_or(NULL);
                                s.push_str(&format!(
                                    "f{}: {}",
                                    id,
                                    pp(val, depth + 1, max_depth, max_elems, seen)
                                ));
                                wrote += 1;
                            }
                        }

                        // Optionally show proto (kept last)
                        if wrote < max_elems && o.proto != NULL {
                            if !first {
                                s.push_str(", ");
                            }
                            s.push_str(&format!(
                                "__proto__: {}",
                                pp(o.proto, depth + 1, max_depth, max_elems, seen)
                            ));
                        }

                        if wrote >= max_elems {
                            s.push_str(", …");
                        }
                        s.push('}');
                        s
                    }
                }

                TAG_CLOSURE => {
                    let c = &*(v as *const BoxedClosure);
                    let mut s = format!("<closure code=0x{:x} env=[", c.code_ptr as u64);
                    let n = min(c.env.len(), max_elems);
                    for i in 0..n {
                        if i > 0 {
                            s.push_str(", ");
                        }
                        s.push_str(&pp(c.env[i], depth + 1, max_depth, max_elems, seen));
                    }
                    if c.env.len() > n {
                        s.push_str(", …");
                    }
                    s.push_str("]>");
                    s
                }

                _ => format!("<tag={} @ 0x{:x}>", h.tag, addr),
            }
        } else {
            // Corrupt or invalid pointer
            format!("0x{:x}", addr)
        }
    };

    // allow other branches to render this address again elsewhere
    seen.remove(&addr);
    out
}

// -----------------------------------------------------------------------------
// Map & Set
// -----------------------------------------------------------------------------

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_is_map(v: i64) -> i64 {
    if !is_heap_ptr(v) { return bool_to_value(false); }
    let hdr = &*(v as *const ObjHeader);
    bool_to_value(hdr.tag == TAG_MAP)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_is_set(v: i64) -> i64 {
    if !is_heap_ptr(v) { return bool_to_value(false); }
    let hdr = &*(v as *const ObjHeader);
    bool_to_value(hdr.tag == TAG_SET)
}

// A global list of all live Map and Set objects, storing their addresses as `usize`.
// `usize` is Send + Sync, making it safe to use in a static Mutex.
static LIVE_COLLECTIONS: OnceLock<Mutex<HashSet<usize>>> = OnceLock::new();
fn live_collections() -> &'static Mutex<HashSet<usize>> {
    LIVE_COLLECTIONS.get_or_init(|| Mutex::new(HashSet::new()))
}

pub fn collections_with_root_slots<F: FnMut(*mut i64)>(mut f: F) {
    let guard = live_collections().lock();
    for &addr in guard.iter() {
        if addr == 0 { continue; }
        let ptr = addr as *const u8;
        unsafe {
            let hdr = &*(ptr as *const ObjHeader);
            if hdr.tag == TAG_MAP {
                let map = &mut *(ptr as *mut BoxedMap);
                for (k, v) in map.map.iter_mut() {
                    // The `k` is a `&Value` and the `v` is a `&mut Value`.
                    // The pointer cast `as *const _ as *mut _` is necessary because the GC needs a mutable pointer.
                    f(&k.0 as *const i64 as *mut i64);
                    f(&mut v.0 as *mut i64);
                }
            } else if hdr.tag == TAG_SET {
                let set = &mut *(ptr as *mut BoxedSet);
                for v in set.set.iter() {
                    f(&v.0 as *const i64 as *mut i64);
                }
            }
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_map_new() -> i64 {
    let map_val = map_new();
    // Register the new map's address as a `usize`.
    live_collections().lock().insert(map_val as usize);
    map_val
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_map_get(map_val: i64, key: i64) -> i64 {
    if !is_heap_ptr(map_val) { return NULL; }
    let map = &* (map_val as *const BoxedMap);
    map.map.get(&Value(key)).map_or(NULL, |v| v.0)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_map_set(map_val: i64, key: i64, val: i64) -> i64 {
    if !is_heap_ptr(map_val) { return map_val; }
    let map = &mut * (map_val as *mut BoxedMap);
    map.map.insert(Value(key), Value(val));
    map_val
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_map_has(map_val: i64, key: i64) -> i64 {
    if !is_heap_ptr(map_val) { return bool_to_value(false); }
    match heap_tag(map_val) {
        Some(TAG_MAP) => {
            let map = &*(map_val as *const BoxedMap);
            bool_to_value(map.map.contains_key(&Value(key)))
        }
        Some(TAG_SET) => wir_set_has(map_val, key),
        _ => bool_to_value(false),
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_map_delete(map_val: i64, key: i64) -> i64 {
    if !is_heap_ptr(map_val) { return bool_to_value(false); }
    match heap_tag(map_val) {
        Some(TAG_MAP) => {
            let map = &mut *(map_val as *mut BoxedMap);
            bool_to_value(map.map.remove(&Value(key)).is_some())
        }
        Some(TAG_SET) => wir_set_delete(map_val, key),
        _ => bool_to_value(false),
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_map_clear(map_val: i64) {
    if !is_heap_ptr(map_val) { return; }
    match heap_tag(map_val) {
        Some(TAG_MAP) => {
            let map = &mut *(map_val as *mut BoxedMap);
            map.map.clear();
        }
        Some(TAG_SET) => wir_set_clear(map_val),
        _ => {}
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_map_size(map_val: i64) -> i64 {
    if !is_heap_ptr(map_val) { return v::make_smi(0); }
    match heap_tag(map_val) {
        Some(TAG_MAP) => {
            let map = &*(map_val as *const BoxedMap);
            v::make_smi(map.map.len() as i64)
        }
        Some(TAG_SET) => wir_set_size(map_val),
        _ => v::make_smi(0),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_set_new() -> i64 {
    let set_val = set_new();
    // Register the new set's address as a `usize`.
    live_collections().lock().insert(set_val as usize);
    set_val
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_set_add(set_val: i64, val: i64) -> i64 {
    if !is_heap_ptr(set_val) { return set_val; }
    let set = &mut * (set_val as *mut BoxedSet);
    set.set.insert(Value(val));
    set_val
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_set_has(set_val: i64, val: i64) -> i64 {
    if !is_heap_ptr(set_val) { return bool_to_value(false); }
    let set = &* (set_val as *const BoxedSet);
    bool_to_value(set.set.contains(&Value(val)))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_set_delete(set_val: i64, val: i64) -> i64 {
    if !is_heap_ptr(set_val) { return bool_to_value(false); }
    let set = &mut * (set_val as *mut BoxedSet);
    bool_to_value(set.set.remove(&Value(val)))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_set_clear(set_val: i64) {
    if !is_heap_ptr(set_val) { return; }
    let set = &mut * (set_val as *mut BoxedSet);
    set.set.clear();
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_set_size(set_val: i64) -> i64 {
    if !is_heap_ptr(set_val) { return v::make_smi(0); }
    let set = &* (set_val as *const BoxedSet);
    v::make_smi(set.set.len() as i64)
}

// -----------------------------------------------------------------------------
// Optional: a single native that prints *any* value using fmt_value
// -----------------------------------------------------------------------------
#[unsafe(no_mangle)]
pub extern "C" fn wir_print_any(v: i64) -> i64 {
    use std::io::Write;
    let s = fmt_value(v);
    let _ = std::io::stdout().write_all(s.as_bytes());
    let _ = std::io::stdout().write_all(b"\n");
    0
}
