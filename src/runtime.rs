#![allow(unsafe_op_in_unsafe_fn)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_unsafe)]

use crate::jit::wir_make_method_closure;
use crate::value::{
    TAG_STRING, BoxedStr, ObjHeader, TAG_OBJECT, is_imm, NULL,
    obj_set_proto, obj_get_proto, obj_get_field_deep, obj_get_str_deep,
    is_bool, to_bool,
    TAG_BOXED_F64, BoxedF64,
    TAG_ARRAY, BoxedArray,
    BoxedObj, TAG_CLOSURE, BoxedClosure,
};
use crate::value as v;
use crate::gc::NAPALM_GC;

use ahash::{AHashMap as HashMap, AHashSet as HashSet};
use std::sync::OnceLock;
use parking_lot::Mutex;
use core::cmp::min;
use std::slice;

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
    // Booleans are raw 0/1 in this runtime
    if is_bool(v) {
        return if to_bool(v) { "1".to_string() } else { "0".to_string() };
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
                            if i > 0 { s.push_str(", "); }
                            s.push_str(&pp(a.buf[i], depth + 1, max_depth, max_elems, seen));
                        }
                        if a.buf.len() > n { s.push_str(", …"); }
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
                        for k in skeys {
                            if wrote >= max_elems { break; }
                            if !first { s.push_str(", "); } else { first = false; }
                            let val = o.by_str.get(k).copied().unwrap_or(NULL);
                            s.push_str(&format!("{:?}: {}", k, pp(val, depth + 1, max_depth, max_elems, seen)));
                            wrote += 1;
                        }

                        // Then FieldId (u32) props (also sorted)
                        if wrote < max_elems {
                            let mut fids: Vec<u32> = o.by_id.keys().copied().collect();
                            fids.sort_unstable();
                            for id in fids {
                                if wrote >= max_elems { break; }
                                if !first { s.push_str(", "); } else { first = false; }
                                let val = o.by_id.get(&id).copied().unwrap_or(NULL);
                                s.push_str(&format!("f{}: {}", id, pp(val, depth + 1, max_depth, max_elems, seen)));
                                wrote += 1;
                            }
                        }

                        // Optionally show proto (kept last)
                        if wrote < max_elems && o.proto != NULL {
                            if !first { s.push_str(", "); }
                            s.push_str(&format!("__proto__: {}", pp(o.proto, depth + 1, max_depth, max_elems, seen)));
                        }

                        if wrote >= max_elems { s.push_str(", …"); }
                        s.push('}');
                        s
                    }
                }

                TAG_CLOSURE => {
                    let c = &*(v as *const BoxedClosure);
                    let mut s = format!("<closure code=0x{:x} env=[", c.code_ptr as u64);
                    let n = min(c.env.len(), max_elems);
                    for i in 0..n {
                        if i > 0 { s.push_str(", "); }
                        s.push_str(&pp(c.env[i], depth + 1, max_depth, max_elems, seen));
                    }
                    if c.env.len() > n { s.push_str(", …"); }
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
