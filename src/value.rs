#![allow(dead_code)]
#![allow(unsafe_op_in_unsafe_fn)]

use core::mem;
use ahash::AHashMap as HashMap;
use std::ptr;
use crate::gc::NAPALM_GC;

//use crate::gc::api::{alloc_raw, alloc_slow_path, post_alloc_object};
//use crate::gc::post_write_barrier;

// ============================================================================
// Value representation
// ============================================================================

pub type ValueRepr = i64;

// ---- Pointer / immediate tests ----
#[inline(always)] pub fn is_ptr(v: ValueRepr) -> bool { (v & 1) == 0 }
#[inline(always)] pub fn is_imm(v: ValueRepr) -> bool { (v & 1) == 1 }

// ---- Small Int (SMI) encoding ----
#[inline(always)] pub fn make_smi(n: i64) -> ValueRepr { (n << 1) | 1 }
#[inline(always)] pub fn smi_to_i64(v: ValueRepr) -> i64 { v >> 1 } // arithmetic shift

// ---- Null (boxed-null) ----
pub const NULL: ValueRepr = 0;

// ---- Booleans: raw 0/1 (not SMIs) ----
// (Kept for now to match your lowerer’s behavior)
#[inline(always)] pub fn is_bool(v: i64) -> bool          { v == 0 || v == 1 }
#[inline(always)] pub fn to_bool(v: i64) -> bool          { v != 0 }

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

#[inline(always)]
pub fn box_f64(x: f64) -> ValueRepr {
    unsafe {
        let size = mem::size_of::<BoxedF64>();
        let align = mem::align_of::<BoxedF64>();

        #[cfg(feature = "gc")] {
            let mut p = NAPALM_GC.alloc_raw(size, align);
            if p.is_null() { p = NAPALM_GC.alloc_slow_path(size, align); }

            let obj = p as *mut BoxedF64;
            core::ptr::write(
                obj,
                BoxedF64 { hdr: ObjHeader { tag: TAG_BOXED_F64, aux: 0 }, val: x }
            );

            NAPALM_GC.post_alloc_object(p, size);

            return p as ValueRepr;
        }

        #[cfg(not(feature = "gc"))] {
            use std::alloc::{alloc, Layout};

            let layout = Layout::from_size_align_unchecked(size, align);

            let p = alloc(layout);
            if p.is_null() { std::process::abort(); }

            let obj = p as *mut BoxedF64;
            core::ptr::write(
                obj,
                BoxedF64 { hdr: ObjHeader { tag: TAG_BOXED_F64, aux: 0 }, val: x }
            );

            return p as ValueRepr;
        }
    }
}

#[inline(always)]
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
    #[inline(always)] pub fn len(&self) -> usize { self.buf.len() }
    #[inline(always)] pub fn cap(&self) -> usize { self.buf.capacity() }
}

#[inline]
pub fn box_array_with_len(len: usize) -> ValueRepr {
    unsafe {
        let size  = mem::size_of::<BoxedArray>();
        let align = mem::align_of::<BoxedArray>();

        #[cfg(feature = "gc")] {
            let mut p = NAPALM_GC.alloc_raw(size, align);
            if p.is_null() { p = NAPALM_GC.alloc_slow_path(size, align); }

            let obj = p as *mut BoxedArray;

            // Build Vec on the Rust heap (capacity=len, length=len), filled with uninitialized i64.
            let mut buf = Vec::<i64>::with_capacity(len);
            buf.set_len(len);

            core::ptr::write(
                obj,
                BoxedArray { hdr: ObjHeader { tag: TAG_ARRAY, aux: 0 }, buf }
            );

            NAPALM_GC.post_alloc_object(p, size);

            return p as ValueRepr;
        }

        #[cfg(not(feature = "gc"))] {
            use std::alloc::{alloc, Layout};

            let layout = Layout::from_size_align_unchecked(size, align);

            let p = alloc(layout);
            if p.is_null() { std::process::abort(); }

            let obj = p as *mut BoxedArray;

            // Build Vec on the Rust heap (capacity=len, length=len), filled with uninitialized i64.
            let mut buf = Vec::<i64>::with_capacity(len);
            buf.set_len(len);

            core::ptr::write(
                obj,
                BoxedArray { hdr: ObjHeader { tag: TAG_ARRAY, aux: 0 }, buf }
            );

            return p as ValueRepr;
        }
    }
}

#[inline(always)]
pub unsafe fn as_boxed_array_mut(v: ValueRepr) -> *mut BoxedArray {
    v as *mut BoxedArray
}

#[inline(always)]
pub unsafe fn array_set(arr_v: ValueRepr, idx: usize, val: ValueRepr) {
    // Vec-backed variant shown
    let a = &mut *as_boxed_array_mut(arr_v);
    let slot: *mut i64 = a.buf.as_mut_ptr().add(idx);
    *slot = val;

    #[cfg(feature = "gc")]
    NAPALM_GC.post_write_barrier(arr_v as *mut u8, slot, val);
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

#[inline(always)]
pub fn box_str_borrowed(bytes: &[u8]) -> ValueRepr {
    unsafe {
        let size  = mem::size_of::<BoxedStr>();
        let align = mem::align_of::<BoxedStr>();

        #[cfg(feature = "gc")] {
            let mut p = NAPALM_GC.alloc_raw(size, align);
            if p.is_null() { p = NAPALM_GC.alloc_slow_path(size, align); }

            let obj = p as *mut BoxedStr;
            core::ptr::write(
                obj,
                BoxedStr { hdr: ObjHeader { tag: TAG_STRING, aux: 0 }, len: bytes.len(), data: bytes.as_ptr() }
            );

            NAPALM_GC.post_alloc_object(p, size);

            return p as ValueRepr;
        }

        #[cfg(not(feature = "gc"))] {
            use std::alloc::{alloc, Layout};

            let layout = Layout::from_size_align_unchecked(size, align);

            let p = alloc(layout);
            if p.is_null() { std::process::abort(); }

            let obj = p as *mut BoxedStr;
            core::ptr::write(
                obj,
                BoxedStr { hdr: ObjHeader { tag: TAG_STRING, aux: 0 }, len: bytes.len(), data: bytes.as_ptr() }
            );

            return p as ValueRepr;
        }
    }
}

// ============================================================================
// Boxed closure (placeholder wiring)
// ============================================================================

#[repr(C)]
pub struct BoxedClosure {
    pub hdr: ObjHeader,     // tag = TAG_CLOSURE
    pub code_ptr: usize,    // or a function id/index if you prefer
    pub env: Vec<i64>,      // captured values
}

#[inline(always)]
pub fn closure_new(code_ptr: usize, env_len: usize) -> ValueRepr {
    unsafe {
        let size  = core::mem::size_of::<BoxedClosure>();
        let align = core::mem::align_of::<BoxedClosure>();

        #[cfg(feature = "gc")] {
            let mut p = NAPALM_GC.alloc_raw(size, align);
            if p.is_null() { p = NAPALM_GC.alloc_slow_path(size, align); }

            let clo = p as *mut BoxedClosure;

            // Build Vec on the Rust heap. Filled with uninitialized i64.
            let mut env = Vec::<i64>::with_capacity(env_len);
            env.set_len(env_len);

            core::ptr::write(
                clo,
                BoxedClosure { hdr: ObjHeader { tag: TAG_CLOSURE, aux: 0 }, code_ptr, env }
            );
            NAPALM_GC.post_alloc_object(p, size);

            return p as ValueRepr;
        }

        #[cfg(not(feature = "gc"))] {
            use std::alloc::{alloc, Layout};

            let layout = Layout::from_size_align_unchecked(size, align);

            let p = alloc(layout);
            if p.is_null() { std::process::abort(); }

            let clo = p as *mut BoxedClosure;

            // Build Vec on the Rust heap. Filled with uninitialized i64.
            let mut env = Vec::<i64>::with_capacity(env_len);
            env.set_len(env_len);

            core::ptr::write(
                clo,
                BoxedClosure { hdr: ObjHeader { tag: TAG_CLOSURE, aux: 0 }, code_ptr, env }
            );

            return p as ValueRepr;
        }
    }
}

#[inline(always)]
pub unsafe fn as_closure_mut(v: ValueRepr) -> *mut BoxedClosure {
    v as *mut BoxedClosure
}

#[inline(always)]
pub unsafe fn closure_get_env_slot(v: ValueRepr, idx: usize) -> ValueRepr {
    let c = &*as_closure_mut(v);
    *c.env.as_ptr().add(idx)
}

#[inline(always)]
pub unsafe fn closure_set_env_slot(v: ValueRepr, idx: usize, val: ValueRepr) {
    let c = &mut *as_closure_mut(v);
    let slot: *mut ValueRepr = c.env.as_mut_ptr().add(idx);

    // (Optional pre barrier if you enable a plan that needs it)
    // #[cfg(feature = "gc")]
    // NAPALM_GC.pre_write_barrier(v as *mut u8, slot);

    *slot = val;

    #[cfg(feature = "gc")]
    NAPALM_GC.post_write_barrier(v as *mut u8, slot, val);
}

// ============================================================================
// Boxed object (JS-like dictionary)
// ============================================================================

#[repr(C)]
pub struct BoxedObj {
    pub hdr: ObjHeader,
    pub by_id:  HashMap<u32, ValueRepr>,   // FieldId fast path
    pub by_str: HashMap<String, ValueRepr> // string-key path
}

#[inline(always)]
pub fn obj_new() -> ValueRepr {
    unsafe {
        let size  = mem::size_of::<BoxedObj>();
        let align = mem::align_of::<BoxedObj>();

        #[cfg(feature = "gc")] {
            let mut p = NAPALM_GC.alloc_raw(size, align);
            if p.is_null() { p = NAPALM_GC.alloc_slow_path(size, align); }

            let obj = p as *mut BoxedObj;
            core::ptr::write(
                obj,
                BoxedObj {
                    hdr: ObjHeader { tag: TAG_OBJECT, aux: 0 },
                    by_id:  HashMap::new(),
                    by_str: HashMap::new(),
                }
            );

            NAPALM_GC.post_alloc_object(p, size);

            return p as ValueRepr;
        }

        #[cfg(not(feature = "gc"))] {
            use std::alloc::{alloc, Layout};

            let layout = Layout::from_size_align_unchecked(size, align);

            let p = alloc(layout);
            if p.is_null() { std::process::abort(); }

            let obj = p as *mut BoxedObj;
            core::ptr::write(
                obj,
                BoxedObj {
                    hdr: ObjHeader { tag: TAG_OBJECT, aux: 0 },
                    by_id:  HashMap::new(),
                    by_str: HashMap::new(),
                }
            );

            return p as ValueRepr;
        }
    }
}

#[inline(always)]
pub unsafe fn as_obj_mut(v: ValueRepr) -> *mut BoxedObj {
    v as *mut BoxedObj
}

// ---- FieldId-based (u32) helpers ----

#[inline(always)]
pub unsafe fn obj_get_field(obj_v: ValueRepr, fid: u32) -> ValueRepr {
    let o = &*as_obj_mut(obj_v); // Error
    o.by_id.get(&fid).cloned().unwrap_or(NULL)
}

#[inline(always)]
pub unsafe fn obj_set_field(obj_v: ValueRepr, fid: u32, val: ValueRepr) -> ValueRepr {
    let o = &mut *as_obj_mut(obj_v);
    let cell = o.by_id.entry(fid).or_insert(NULL);
    let slot: *mut ValueRepr = cell as *mut ValueRepr;
    *cell = val;

    // Post-write barrier
    #[cfg(feature = "gc")]
    NAPALM_GC.post_write_barrier(obj_v as *mut u8, slot, val);

    val
}

#[inline(always)]
pub unsafe fn obj_has_field(obj_v: ValueRepr, fid: u32) -> ValueRepr {
    let o = &*as_obj_mut(obj_v);
    if o.by_id.contains_key(&fid) { 1 } else { 0 }
}

#[inline(always)]
pub unsafe fn obj_del_field(obj_v: ValueRepr, fid: u32) -> ValueRepr {
    let o = &mut *as_obj_mut(obj_v);
    if o.by_id.remove(&fid).is_some() { 1 } else { 0 }
}

// ---- String-key helpers ----

#[inline(always)]
pub unsafe fn obj_get_str(obj_v: ValueRepr, key: &str) -> ValueRepr {
    let o = &*as_obj_mut(obj_v);
    o.by_str.get(key).cloned().unwrap_or(NULL)
}

#[inline(always)]
pub unsafe fn obj_set_str(obj_v: ValueRepr, key: &str, val: ValueRepr) -> ValueRepr {
    let o = &mut *as_obj_mut(obj_v);
    let cell = o.by_str.entry(key.to_string()).or_insert(NULL);
    let slot: *mut ValueRepr = cell as *mut ValueRepr;
    *cell = val;

    #[cfg(feature = "gc")]
    NAPALM_GC.post_write_barrier(obj_v as *mut u8, slot, val);

    val
}

#[inline(always)]
pub unsafe fn obj_has_str(obj_v: ValueRepr, key: &str) -> ValueRepr {
    let o = &*as_obj_mut(obj_v);
    if o.by_str.contains_key(key) { 1 } else { 0 }
}

#[inline(always)]
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
