#![allow(dead_code)]

use ahash::AHashMap as HashMap;

// ============================================================================
// Value representation
// ============================================================================

pub type ValueRepr = i64;

// ---- Pointer / immediate tests ----
#[inline] pub fn is_ptr(v: ValueRepr) -> bool { (v & 1) == 0 }
#[inline] pub fn is_imm(v: ValueRepr) -> bool { (v & 1) == 1 }

// ---- Small Int (SMI) encoding ----
#[inline] pub fn make_smi(n: i64) -> ValueRepr { (n << 1) | 1 }
#[inline] pub fn smi_to_i64(v: ValueRepr) -> i64 { v >> 1 } // arithmetic shift

// ---- Null (boxed-null) ----
pub const NULL: ValueRepr = 0;

// ---- Booleans: raw 0/1 (not SMIs) ----
// (Kept for now to match your lowerer’s behavior)
#[inline] pub fn is_bool(v: i64) -> bool          { v == 0 || v == 1 }
#[inline] pub fn to_bool(v: i64) -> bool          { v != 0 }

// ============================================================================
// Object headers & tags
// ============================================================================

#[repr(C)]
#[derive(Copy, Clone)]
pub struct ObjHeader {
    pub tag: u32,
    pub aux: u32, // size, hash, flags, etc (free for now)
}

// Object tags (grow as we add types)
pub const TAG_BOXED_F64: u32 = 1;
pub const TAG_STRING:   u32 = 2;
pub const TAG_ARRAY:    u32 = 3;
pub const TAG_CLOSURE:  u32 = 4;
pub const TAG_OBJECT:   u32 = 5;

// ============================================================================
// Boxed f64
// ============================================================================

#[repr(C)]
pub struct BoxedF64 {
    pub hdr: ObjHeader,
    pub val: f64,
}

#[inline]
pub fn box_f64(x: f64) -> ValueRepr {
    let b = Box::new(BoxedF64 { hdr: ObjHeader { tag: TAG_BOXED_F64, aux: 0 }, val: x });
    Box::into_raw(b) as ValueRepr
}

#[inline]
pub unsafe fn unbox_f64(v: ValueRepr) -> f64 {
    debug_assert!(is_ptr(v));
    let p = v as *const BoxedF64;
    (*p).val
}

// ============================================================================
// Flat “Array” layout (JIT may poke with offsets)
// ============================================================================

#[repr(C)]
pub struct Array {
    pub hdr: ObjHeader, // tag = TAG_ARRAY
    pub len: i64,       // number of elements
    // followed in memory by `len` i64 elements (8 bytes each)
}

// Offsets used by the JIT (all bytes)
pub const ARRAY_HDR_SIZE:    i32 = core::mem::size_of::<ObjHeader>() as i32; // 8
pub const ARRAY_LEN_OFFSET:  i32 = ARRAY_HDR_SIZE;                           // 8
pub const ARRAY_DATA_OFFSET: i32 = ARRAY_HDR_SIZE + core::mem::size_of::<i64>() as i32; // 16

// A safe, Vec-backed array form used by the interpreter/native helpers.
// (You can keep both forms; choose based on where you create it.)
#[repr(C)]
pub struct BoxedArray {
    pub hdr: ObjHeader,
    pub buf: Vec<i64>,
}

impl BoxedArray {
    #[inline] pub fn len(&self) -> usize { self.buf.len() }
    #[inline] pub fn cap(&self) -> usize { self.buf.capacity() }
}

#[inline]
pub fn box_array_with_len(len: usize) -> ValueRepr {
    let mut buf = Vec::<i64>::with_capacity(len);
    unsafe { buf.set_len(len); } // initialized to garbage; runtime usually fills in
    let b = Box::new(BoxedArray { hdr: ObjHeader { tag: TAG_ARRAY, aux: 0 }, buf });
    Box::into_raw(b) as ValueRepr
}

#[inline]
pub unsafe fn as_boxed_array_mut(v: ValueRepr) -> *mut BoxedArray {
    v as *mut BoxedArray
}

// ============================================================================
// Boxed string (placeholder wiring)
// ============================================================================

#[repr(C)]
pub struct BoxedStr {
    pub hdr: ObjHeader,
    pub len: usize,       // byte length (no trailing NUL)
    pub data: *const u8,  // points to UTF-8 bytes (NUL-terminated OK, not required)
}

#[inline]
pub fn box_str_borrowed(bytes: &[u8]) -> ValueRepr {
    let b = Box::new(BoxedStr {
        hdr: ObjHeader { tag: TAG_STRING, aux: 0 },
        len: bytes.len(),
        data: bytes.as_ptr(), // NOTE: lifetime! use owned if you need to keep beyond scope
    });
    Box::into_raw(b) as ValueRepr
}

// ============================================================================
// Boxed object (JS-like dictionary): the bit you asked for
// ============================================================================

#[repr(C)]
pub struct BoxedObj {
    pub hdr: ObjHeader,
    pub by_id:  HashMap<u32, ValueRepr>,   // FieldId fast path
    pub by_str: HashMap<String, ValueRepr> // string-key path
}

#[inline]
pub fn obj_new() -> ValueRepr {
    let b = Box::new(BoxedObj {
        hdr: ObjHeader { tag: TAG_OBJECT, aux: 0 },
        by_id:  HashMap::new(),
        by_str: HashMap::new(),
    });
    Box::into_raw(b) as ValueRepr
}

#[inline]
pub unsafe fn as_obj_mut(v: ValueRepr) -> *mut BoxedObj {
    v as *mut BoxedObj
}

// ---- FieldId-based (u32) helpers ----

#[inline]
pub unsafe fn obj_get_field(obj_v: ValueRepr, fid: u32) -> ValueRepr {
    let o = &*as_obj_mut(obj_v);
    o.by_id.get(&fid).cloned().unwrap_or(NULL)
}

#[inline]
pub unsafe fn obj_set_field(obj_v: ValueRepr, fid: u32, val: ValueRepr) -> ValueRepr {
    let o = &mut *as_obj_mut(obj_v);
    o.by_id.insert(fid, val);
    val
}

#[inline]
pub unsafe fn obj_has_field(obj_v: ValueRepr, fid: u32) -> ValueRepr {
    let o = &*as_obj_mut(obj_v);
    if o.by_id.contains_key(&fid) { 1 } else { 0 }
}

#[inline]
pub unsafe fn obj_del_field(obj_v: ValueRepr, fid: u32) -> ValueRepr {
    let o = &mut *as_obj_mut(obj_v);
    if o.by_id.remove(&fid).is_some() { 1 } else { 0 }
}

// ---- String-key helpers ----

#[inline]
pub unsafe fn obj_get_str(obj_v: ValueRepr, key: &str) -> ValueRepr {
    let o = &*as_obj_mut(obj_v);
    o.by_str.get(key).cloned().unwrap_or(NULL)
}

#[inline]
pub unsafe fn obj_set_str(obj_v: ValueRepr, key: &str, val: ValueRepr) -> ValueRepr {
    let o = &mut *as_obj_mut(obj_v);
    o.by_str.insert(key.to_string(), val);
    val
}

#[inline]
pub unsafe fn obj_has_str(obj_v: ValueRepr, key: &str) -> ValueRepr {
    let o = &*as_obj_mut(obj_v);
    if o.by_str.contains_key(key) { 1 } else { 0 }
}

#[inline]
pub unsafe fn obj_del_str(obj_v: ValueRepr, key: &str) -> ValueRepr {
    let o = &mut *as_obj_mut(obj_v);
    if o.by_str.remove(key).is_some() { 1 } else { 0 }
}

// ============================================================================
// Debug formatting
// ============================================================================

/// Try to pretty-print a runtime value according to our tags.
/// Keep this conservative; it’s only for `print` and debugging.
pub fn fmt_value(v: i64) -> String {
    // Booleans are raw 0/1
    if is_bool(v) {
        return if v != 0 { "1".to_string() } else { "0".to_string() };
    }

    // Small ints are odd (SMI)
    if is_imm(v) {
        return smi_to_i64(v).to_string();
    }

    // Even: either NULL or a pointer
    if v == NULL {
        return "null".to_string();
    }

    // Best-effort: read header and switch on tag
    unsafe {
        let hdr = (v as *const ObjHeader).as_ref();
        if let Some(h) = hdr {
            match h.tag {
                TAG_BOXED_F64 => {
                    let f = &*(v as *const BoxedF64);
                    return format!("{}", f.val);
                }
                TAG_STRING => {
                    return format!("<string@{:#x}>", v as u64);
                }
                TAG_ARRAY => {
                    return format!("<array@{:#x}>", v as u64);
                }
                TAG_OBJECT => {
                    return format!("<object@{:#x}>", v as u64);
                }
                _ => { /* fallthrough */ }
            }
        }
    }

    // Unknown object
    format!("{:#x}", v as u64)
}
