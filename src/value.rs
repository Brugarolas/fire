#![allow(dead_code)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_unsafe)]

use crate::gc::NAPALM_GC;
use ahash::AHashMap as HashMap;
use core::mem;
use std::ptr;
use std::str;
use std::slice;

//use crate::gc::api::{alloc_raw, alloc_slow_path, post_alloc_object};
//use crate::gc::post_write_barrier;

// ============================================================================
// Value representation
// ============================================================================

pub type ValueRepr = i64;

// ---- Pointer / immediate tests ----
#[inline(always)]
pub fn is_ptr(v: ValueRepr) -> bool {
    (v & 1) == 0
}
#[inline(always)]
pub fn is_imm(v: ValueRepr) -> bool {
    (v & 1) == 1
}

// ---- Small Int (SMI) encoding ----
#[inline(always)]
pub fn make_smi(n: i64) -> ValueRepr {
    (n << 1) | 1
}
#[inline(always)]
pub fn smi_to_i64(v: ValueRepr) -> i64 {
    v >> 1
} // arithmetic shift

// ---- Null (boxed-null) ----
pub const NULL: ValueRepr = 0;

// ---- Booleans: raw 0/1 (not SMIs) ----
// (Kept for now to match your lowerer’s behavior)
#[inline(always)]
pub fn is_bool(v: i64) -> bool {
    v == 0 || v == 1
}
#[inline(always)]
pub fn to_bool(v: i64) -> bool {
    v != 0
}

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
pub const TAG_STRING: u32 = 2;
pub const TAG_ARRAY: u32 = 3;
pub const TAG_CLOSURE: u32 = 4;
pub const TAG_OBJECT: u32 = 5;

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

        #[cfg(feature = "gc")]
        {
            let mut p = NAPALM_GC.alloc_raw(size, align);
            if p.is_null() {
                p = NAPALM_GC.alloc_slow_path(size, align);
            }

            let obj = p as *mut BoxedF64;
            core::ptr::write(
                obj,
                BoxedF64 {
                    hdr: ObjHeader {
                        tag: TAG_BOXED_F64,
                        aux: 0,
                    },
                    val: x,
                },
            );

            NAPALM_GC.post_alloc_object(p, size);

            return p as ValueRepr;
        }

        #[cfg(not(feature = "gc"))]
        {
            use std::alloc::{Layout, alloc};

            let layout = Layout::from_size_align_unchecked(size, align);

            let p = alloc(layout);
            if p.is_null() {
                std::process::abort();
            }

            let obj = p as *mut BoxedF64;
            core::ptr::write(
                obj,
                BoxedF64 {
                    hdr: ObjHeader {
                        tag: TAG_BOXED_F64,
                        aux: 0,
                    },
                    val: x,
                },
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
// Arrays (Vec-backed) — full feature set (GC-friendly)
// ============================================================================

#[repr(C)]
pub struct Array {
    pub hdr: ObjHeader, // tag = TAG_ARRAY
    pub len: i64,       // unused in this Vec-backed impl; kept for offset compat if needed
}

// Offsets used by the JIT (kept for compatibility with any flat layout users)
pub const ARRAY_HDR_SIZE: i32 = core::mem::size_of::<ObjHeader>() as i32; // 8
pub const ARRAY_LEN_OFFSET: i32 = ARRAY_HDR_SIZE; // 8
pub const ARRAY_DATA_OFFSET: i32 = ARRAY_HDR_SIZE + core::mem::size_of::<i64>() as i32; // 16

#[repr(C)]
pub struct BoxedArray {
    pub hdr: ObjHeader,
    pub buf: Vec<i64>,
}

impl BoxedArray {
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.buf.len()
    }
    #[inline(always)]
    pub fn cap(&self) -> usize {
        self.buf.capacity()
    }
}

#[inline]
fn alloc_array_from_vec(mut buf: Vec<i64>) -> ValueRepr {
    unsafe {
        let size = core::mem::size_of::<BoxedArray>();
        let align = core::mem::align_of::<BoxedArray>();

        #[cfg(feature = "gc")]
        {
            let mut p = NAPALM_GC.alloc_raw(size, align);
            if p.is_null() {
                p = NAPALM_GC.alloc_slow_path(size, align);
            }

            let obj = p as *mut BoxedArray;
            core::ptr::write(
                obj,
                BoxedArray {
                    hdr: ObjHeader {
                        tag: TAG_ARRAY,
                        aux: 0,
                    },
                    buf,
                },
            );
            NAPALM_GC.post_alloc_object(p, size);
            return p as ValueRepr;
        }

        #[cfg(not(feature = "gc"))]
        {
            use std::alloc::{Layout, alloc};
            let layout = Layout::from_size_align_unchecked(size, align);
            let p = alloc(layout);
            if p.is_null() {
                std::process::abort();
            }
            let obj = p as *mut BoxedArray;
            core::ptr::write(
                obj,
                BoxedArray {
                    hdr: ObjHeader {
                        tag: TAG_ARRAY,
                        aux: 0,
                    },
                    buf,
                },
            );
            return p as ValueRepr;
        }
    }
}

#[inline]
pub fn box_array_with_len(len: usize) -> ValueRepr {
    // IMPORTANT: zero-init to avoid GC scanning garbage that mimics pointers.
    alloc_array_from_vec(vec![0; len])
}

#[inline]
pub fn array_new(len: usize) -> ValueRepr {
    box_array_with_len(len)
}

#[inline(always)]
pub unsafe fn as_boxed_array_mut(v: ValueRepr) -> *mut BoxedArray {
    v as *mut BoxedArray
}

#[inline(always)]
pub unsafe fn as_boxed_array_ref(v: ValueRepr) -> *const BoxedArray {
    v as *const BoxedArray
}

#[inline(always)]
pub unsafe fn array_len(arr_v: ValueRepr) -> usize {
    (&*as_boxed_array_ref(arr_v)).buf.len()
}

#[inline(always)]
pub unsafe fn array_len_smi(arr_v: ValueRepr) -> ValueRepr {
    make_smi(array_len(arr_v) as i64)
}

#[inline(always)]
pub unsafe fn array_get(arr_v: ValueRepr, idx: usize) -> ValueRepr {
    let a = &*as_boxed_array_ref(arr_v);
    *a.buf.get(idx).unwrap_or(&NULL)
}

#[inline(always)]
pub unsafe fn array_set(arr_v: ValueRepr, idx: usize, val: ValueRepr) -> ValueRepr {
    let a = &mut *as_boxed_array_mut(arr_v);
    if idx >= a.buf.len() {
        a.buf.resize(idx + 1, 0);
    }
    let slot: *mut i64 = a.buf.as_mut_ptr().add(idx);
    *slot = val;

    #[cfg(feature = "gc")]
    NAPALM_GC.post_write_barrier(arr_v as *mut u8, slot, val);

    0
}

#[inline(always)]
pub unsafe fn array_set_len(arr_v: ValueRepr, new_len: usize) -> ValueRepr {
    let a = &mut *as_boxed_array_mut(arr_v);
    a.buf.resize(new_len, 0);
    0
}

#[inline(always)]
pub unsafe fn array_push(arr_v: ValueRepr, val: ValueRepr) -> ValueRepr {
    let a = &mut *as_boxed_array_mut(arr_v);
    a.buf.push(val);
    let last = a.buf.len() - 1;
    let slot = a.buf.as_mut_ptr().add(last);

    #[cfg(feature = "gc")]
    NAPALM_GC.post_write_barrier(arr_v as *mut u8, slot, val);

    make_smi(a.buf.len() as i64)
}

#[inline(always)]
pub unsafe fn array_pop(arr_v: ValueRepr) -> ValueRepr {
    let a = &mut *as_boxed_array_mut(arr_v);
    a.buf.pop().unwrap_or(NULL)
}

#[inline(always)]
pub unsafe fn array_shift(arr_v: ValueRepr) -> ValueRepr {
    let a = &mut *as_boxed_array_mut(arr_v);
    if a.buf.is_empty() {
        return NULL;
    }
    // Vec::remove will shift elements internally; we don't fire per-slot barriers here.
    a.buf.remove(0)
}

#[inline(always)]
pub unsafe fn array_unshift(arr_v: ValueRepr, val: ValueRepr) -> ValueRepr {
    let a = &mut *as_boxed_array_mut(arr_v);
    a.buf.insert(0, val);
    let slot = a.buf.as_mut_ptr(); // index 0

    #[cfg(feature = "gc")]
    NAPALM_GC.post_write_barrier(arr_v as *mut u8, slot, val);

    make_smi(a.buf.len() as i64)
}

#[inline]
pub unsafe fn array_slice(arr_v: ValueRepr, start: usize, end: usize) -> ValueRepr {
    let a = &*as_boxed_array_ref(arr_v);
    let s = start.min(a.buf.len());
    let e = end.min(a.buf.len()).max(s);
    alloc_array_from_vec(a.buf[s..e].to_vec())
}

#[inline]
pub unsafe fn array_map(arr_v: ValueRepr, clo_ptr: ValueRepr) -> ValueRepr {
    unsafe extern "C" {
        fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64;
    }

    let a = &*as_boxed_array_ref(arr_v);
    let mut out = Vec::with_capacity(a.buf.len());
    for &x in &a.buf {
        let args = [x];
        let y = wir_call_closure(clo_ptr, args.as_ptr(), 1);
        out.push(y);

        #[cfg(feature = "gc")]
        NAPALM_GC.maybe_safepoint();
    }
    alloc_array_from_vec(out)
}

#[inline]
pub unsafe fn array_for_each(arr_v: ValueRepr, clo_ptr: ValueRepr) -> ValueRepr {
    unsafe extern "C" {
        fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64;
    }

    let a = &*as_boxed_array_ref(arr_v);
    for &x in &a.buf {
        let args = [x];
        let _ = wir_call_closure(clo_ptr, args.as_ptr(), 1);

        #[cfg(feature = "gc")]
        NAPALM_GC.maybe_safepoint();
    }
    0
}

#[inline]
pub unsafe fn array_find(arr_v: ValueRepr, clo_ptr: ValueRepr) -> ValueRepr {
    unsafe extern "C" {
        fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64;
    }

    let a = &*as_boxed_array_ref(arr_v);
    for &x in &a.buf {
        let args = [x];
        let ok = wir_call_closure(clo_ptr, args.as_ptr(), 1);
        if ok != 0 {
            return x;
        }

        #[cfg(feature = "gc")]
        NAPALM_GC.maybe_safepoint();
    }
    NULL
}

#[inline]
pub unsafe fn array_find_index(arr_v: ValueRepr, clo_ptr: ValueRepr) -> ValueRepr {
    unsafe extern "C" {
        fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64;
    }

    let a = &*as_boxed_array_ref(arr_v);
    for (i, &x) in a.buf.iter().enumerate() {
        let args = [x];
        let ok = wir_call_closure(clo_ptr, args.as_ptr(), 1);
        if ok != 0 {
            return make_smi(i as i64);
        }

        #[cfg(feature = "gc")]
        NAPALM_GC.maybe_safepoint();
    }
    make_smi(-1)
}

#[inline]
pub unsafe fn array_filter(arr_v: ValueRepr, clo_ptr: ValueRepr) -> ValueRepr {
    unsafe extern "C" {
        fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64;
    }

    let a = &*as_boxed_array_ref(arr_v);
    let mut out = Vec::new();
    for &x in &a.buf {
        let args = [x];
        let ok = wir_call_closure(clo_ptr, args.as_ptr(), 1);
        if ok != 0 {
            out.push(x);
        }

        #[cfg(feature = "gc")]
        NAPALM_GC.maybe_safepoint();
    }
    alloc_array_from_vec(out)
}

#[inline]
pub unsafe fn array_reduce(
    arr_v: ValueRepr,
    clo_ptr: ValueRepr,
    has_init: bool,
    init: ValueRepr,
) -> ValueRepr {
    unsafe extern "C" {
        fn wir_call_closure(clo_ptr: i64, argv: *const i64, argc: i64) -> i64;
    }

    let a = &*as_boxed_array_ref(arr_v);
    if a.buf.is_empty() {
        return if has_init { init } else { NULL };
    }
    let mut it = a.buf.iter().copied();
    let mut acc = if has_init { init } else { it.next().unwrap() };
    for x in it {
        let args = [acc, x];
        acc = wir_call_closure(clo_ptr, args.as_ptr(), 2);

        #[cfg(feature = "gc")]
        NAPALM_GC.maybe_safepoint();
    }
    acc
}

#[inline]
pub unsafe fn array_fill(arr_v: ValueRepr, val: ValueRepr) -> ValueRepr {
    let a = &mut *as_boxed_array_mut(arr_v);
    let base = a.buf.as_mut_ptr();
    for i in 0..a.buf.len() {
        let slot = base.add(i);
        *slot = val;

        #[cfg(feature = "gc")]
        {
            NAPALM_GC.post_write_barrier(arr_v as *mut u8, slot, val);
            NAPALM_GC.maybe_safepoint();
        }
    }
    0
}

#[inline]
pub unsafe fn array_copy(dst_v: ValueRepr, src_v: ValueRepr, n: usize) -> ValueRepr {
    let d = &mut *as_boxed_array_mut(dst_v);
    let s = &*as_boxed_array_ref(src_v);

    if d.buf.len() < n {
        d.buf.resize(n, 0);
    }

    let nn = n.min(s.buf.len());
    let dptr = d.buf.as_mut_ptr();
    let sptr = s.buf.as_ptr();

    for i in 0..nn {
        let v = *sptr.add(i);
        let slot = dptr.add(i);
        *slot = v;

        #[cfg(feature = "gc")]
        NAPALM_GC.post_write_barrier(dst_v as *mut u8, slot, v);
    }
    for i in nn..n {
        *dptr.add(i) = 0;
    }
    0
}

#[inline(always)]
fn smi(x: i64) -> i64 {
    (x << 1) | 1
}
#[inline(always)]
fn smi_to_i64_wrapped(v: i64) -> i64 {
    v >> 1
} // arithmetic shift

// ---- C exports expected by the JIT ----
#[unsafe(no_mangle)]
pub extern "C" fn wir_array_new(len: i64) -> i64 {
    let n = smi_to_i64_wrapped(len).max(0) as usize;
    array_new(n)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_len(arr: i64) -> i64 {
    if arr == 0 {
        return smi(0);
    }
    unsafe { smi(array_len(arr) as i64) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_get(arr: i64, idx: i64) -> i64 {
    if arr == 0 {
        return 0;
    }
    let i = smi_to_i64_wrapped(idx);
    if i < 0 {
        return 0;
    }
    unsafe { array_get(arr, i as usize) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_set(arr: i64, idx: i64, val: i64) -> i64 {
    if arr == 0 {
        return 0;
    }
    let i = smi_to_i64_wrapped(idx);
    if i < 0 {
        return 0;
    }
    unsafe { array_set(arr, i as usize, val) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_set_len(arr: i64, new_len: i64) -> i64 {
    if arr == 0 {
        return 0;
    }
    let n = smi_to_i64_wrapped(new_len).max(0) as usize;
    unsafe { array_set_len(arr, n) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_push(arr: i64, val: i64) -> i64 {
    if arr == 0 {
        return smi(0);
    }
    unsafe { array_push(arr, val) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_pop(arr: i64) -> i64 {
    if arr == 0 {
        return 0;
    }
    unsafe { array_pop(arr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_shift(arr: i64) -> i64 {
    if arr == 0 {
        return 0;
    }
    unsafe { array_shift(arr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_unshift(arr: i64, val: i64) -> i64 {
    if arr == 0 {
        return smi(0);
    }
    unsafe { array_unshift(arr, val) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_slice(arr: i64, start: i64, end: i64) -> i64 {
    if arr == 0 {
        return 0;
    }
    let s = smi_to_i64_wrapped(start).max(0) as usize;
    let e = smi_to_i64_wrapped(end).max(0) as usize;
    unsafe { array_slice(arr, s, e) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_map(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 {
        return 0;
    }
    unsafe { array_map(arr, clo_ptr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_for_each(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 {
        return 0;
    }
    unsafe { array_for_each(arr, clo_ptr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_find(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 {
        return 0;
    }
    unsafe { array_find(arr, clo_ptr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_find_index(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 {
        return smi(-1);
    }
    unsafe { array_find_index(arr, clo_ptr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_filter(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 {
        return 0;
    }
    unsafe { array_filter(arr, clo_ptr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_reduce(arr: i64, clo_ptr: i64, has_init: i64, init: i64) -> i64 {
    if arr == 0 {
        return 0;
    }
    unsafe { array_reduce(arr, clo_ptr, has_init != 0, init) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_fill(arr: i64, val: i64) -> i64 {
    if arr == 0 {
        return 0;
    }
    unsafe { array_fill(arr, val) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_copy(dst: i64, src: i64, len: i64) -> i64 {
    if dst == 0 || src == 0 {
        return 0;
    }
    let n = smi_to_i64_wrapped(len).max(0) as usize;
    unsafe { array_copy(dst, src, n) }
}

// ============================================================================
// Boxed string (placeholder wiring)
// ============================================================================

#[repr(C)]
pub struct BoxedStr {
    pub hdr: ObjHeader,
    pub len: usize,      // byte length (no trailing NUL)
    pub data: *const u8, // points to UTF-8 bytes (NUL-terminated OK, not required)
}

#[inline(always)]
unsafe fn value_as_str_slice<'a>(v: ValueRepr) -> Option<&'a str> {
    if !is_ptr(v) { return None; }
    let hdr = &*(v as *const ObjHeader);
    if hdr.tag != TAG_STRING { return None; }
    let s = &*(v as *const BoxedStr);
    if s.data.is_null() {
        return Some("");
    }
    let bytes = slice::from_raw_parts(s.data, s.len);
    str::from_utf8(bytes).ok()
}

#[inline(always)]
pub fn box_str_borrowed(bytes: &[u8]) -> ValueRepr {
    unsafe {
        let size = mem::size_of::<BoxedStr>();
        let align = mem::align_of::<BoxedStr>();

        #[cfg(feature = "gc")]
        {
            let mut p = NAPALM_GC.alloc_raw(size, align);
            if p.is_null() {
                p = NAPALM_GC.alloc_slow_path(size, align);
            }

            let obj = p as *mut BoxedStr;
            core::ptr::write(
                obj,
                BoxedStr {
                    hdr: ObjHeader {
                        tag: TAG_STRING,
                        aux: 0,
                    },
                    len: bytes.len(),
                    data: bytes.as_ptr(),
                },
            );

            NAPALM_GC.post_alloc_object(p, size);

            return p as ValueRepr;
        }

        #[cfg(not(feature = "gc"))]
        {
            use std::alloc::{Layout, alloc};

            let layout = Layout::from_size_align_unchecked(size, align);

            let p = alloc(layout);
            if p.is_null() {
                std::process::abort();
            }

            let obj = p as *mut BoxedStr;
            core::ptr::write(
                obj,
                BoxedStr {
                    hdr: ObjHeader {
                        tag: TAG_STRING,
                        aux: 0,
                    },
                    len: bytes.len(),
                    data: bytes.as_ptr(),
                },
            );

            return p as ValueRepr;
        }
    }
}

/// Allocates a new, contiguous string object and returns its value representation.
/// The single memory block contains the BoxedStr header followed by the character data.
#[inline]
pub fn allocate_new_string(s: &str) -> ValueRepr {
    let bytes = s.as_bytes();
    let len = bytes.len();

    // Step 1: Calculate the total size for our single allocation.
    // It's the size of the fixed header struct PLUS the size of the string's byte data.
    let header_size = mem::size_of::<BoxedStr>();
    let total_size = header_size + len;

    // The alignment of the allocation is determined by the header struct,
    // which is the most restrictive requirement.
    let align = mem::align_of::<BoxedStr>();

    unsafe {
        // Step 2: Perform a SINGLE allocation for the entire object.
        // This `total_size` is guaranteed to be >= sizeof(BoxedStr),
        // which will satisfy MMTk's minimum object size requirement.
        #[cfg(feature = "gc")]
        let p = {
            let mut p = NAPALM_GC.alloc_raw(total_size, align);
            if p.is_null() {
                p = NAPALM_GC.alloc_slow_path(total_size, align);
            }
            p
        };
        #[cfg(not(feature = "gc"))]
        let p = {
            use std::alloc::{Layout, alloc, handle_alloc_error};
            let layout = Layout::from_size_align_unchecked(total_size, align);
            let p = alloc(layout);
            if p.is_null() {
                handle_alloc_error(layout);
            }
            p
        };

        // Step 3: Set up the pointers.
        // `obj_ptr` points to the start of the block, where the header will live.
        let obj_ptr = p as *mut BoxedStr;
        // `data_ptr` points to the memory location IMMEDIATELY AFTER the header struct.
        let data_ptr = (obj_ptr as *mut u8).add(header_size);

        // Step 4: Write the header struct into the beginning of the block.
        // The crucial part is that `data` now points inside its own allocation block.
        ptr::write(obj_ptr, BoxedStr {
            hdr: ObjHeader { tag: TAG_STRING, aux: 0 },
            len,
            data: data_ptr, // The `data` pointer points to the area right after this struct.
        });

        // Step 5: Copy the actual string bytes into the data area.
        ptr::copy_nonoverlapping(bytes.as_ptr(), data_ptr, len);

        // Step 6: Notify the GC about the full object allocation.
        #[cfg(feature = "gc")]
        NAPALM_GC.post_alloc_object(p, total_size);

        // Return the pointer to the start of the object.
        p as ValueRepr
    }
}

/// Runtime helper for string indexing `str[i]`.
/// Returns a new 1-character string or NULL if out of bounds.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_get_char(s_val: i64, index_smi: i64) -> i64 {
    if !is_ptr(s_val) { return NULL; }

    let hdr = &*(s_val as *const ObjHeader);
    if hdr.tag != TAG_STRING { return NULL; }

    let s = &*(s_val as *const BoxedStr);
    let index = smi_to_i64(index_smi) as usize;

    if index >= s.len {
        return NULL; // Out of bounds
    }

    // Safely get the byte at the index
    let string_slice = std::slice::from_raw_parts(s.data, s.len);
    let char_byte_slice = &[string_slice[index]];

    // Create a new one-character string from that byte.
    // This is safe because we are taking a single byte from valid UTF-8.
    let new_char_str = std::str::from_utf8_unchecked(char_byte_slice);

    allocate_new_string(new_char_str)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_len(s_val: i64) -> i64 {
    if !is_ptr(s_val) { return make_smi(0); }

    let hdr = &*(s_val as *const ObjHeader);
    if hdr.tag != TAG_STRING { return make_smi(0); }

    let s = &*(s_val as *const BoxedStr);
    make_smi(s.len as i64)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_concat(s1_val: i64, s2_val: i64) -> i64 {
    let s1 = value_as_str_slice(s1_val).unwrap_or("");
    // FIX: Don't use fmt_value. Treat second argument as a string directly.
    let s2 = value_as_str_slice(s2_val).unwrap_or("");
    allocate_new_string(&[s1, s2].concat())
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_slice(s_val: i64, start_smi: i64, end_smi: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return NULL; };
    // FIX: Use byte length consistently.
    let len = s.len();

    let mut start = smi_to_i64(start_smi);
    if start < 0 { start = (len as i64 + start).max(0); }

    let mut end = smi_to_i64(end_smi);
    if end == -1 { // Sentinel for "to the end"
        end = len as i64;
    } else if end < 0 {
        end = (len as i64 + end).max(0);
    }

    let start_idx = (start as usize).min(len);
    // JS `slice` logic: end index can be smaller than start.
    let end_idx = (end as usize).min(len);

    if start_idx >= end_idx {
        return allocate_new_string("");
    }

    // Now uses simple, fast, and correct byte slicing.
    allocate_new_string(&s[start_idx..end_idx])
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_substring(s_val: i64, start_smi: i64, end_smi: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return NULL; };
    // FIX: Use byte length consistently.
    let len = s.len();

    let start_raw = smi_to_i64(start_smi);
    let end_raw = smi_to_i64(end_smi);

    let start = (start_raw.max(0) as usize).min(len);
    let end = if end_raw == -1 { len } else { (end_raw.max(0) as usize).min(len) };

    // JS `substring` swaps if start > end.
    let final_start = start.min(end);
    let final_end = start.max(end);

    allocate_new_string(&s[final_start..final_end])
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_index_of(s_val: i64, search_val: i64, pos_smi: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return make_smi(-1); };
    let Some(search) = value_as_str_slice(search_val) else { return make_smi(-1); };

    // Use byte index for starting position, clamped to string length.
    let start_byte = (smi_to_i64(pos_smi).max(0) as usize).min(s.len());

    // FIX: Search the sub-slice, then add the start_byte offset to the result.
    if let Some(relative_byte_index) = s[start_byte..].find(search) {
        let absolute_byte_index = start_byte + relative_byte_index;
        make_smi(absolute_byte_index as i64)
    } else {
        make_smi(-1)
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_last_index_of(s_val: i64, search_val: i64, pos_smi: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return make_smi(-1); };
    let Some(search) = value_as_str_slice(search_val) else { return make_smi(-1); };

    let pos = smi_to_i64(pos_smi);
    let len = s.len();

    // FIX: Correctly determine the search slice based on JS's `fromIndex` semantics.
    // The search occurs within the substring from the beginning to `pos`.
    let end_byte = if pos < 0 {
        len // Sentinel means search the whole string.
    } else {
        // Clamp to a valid end-of-slice index.
        (pos as usize).min(len.saturating_sub(1)).saturating_add(1)
    };

    if let Some(byte_index) = s[..end_byte].rfind(search) {
        make_smi(byte_index as i64)
    } else {
        make_smi(-1)
    }
}

// --- The rest of the functions are unchanged and correct ---
// (No need to copy them here, just replace the buggy ones above)
#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_split(s_val: i64, sep_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return array_new(0); };
    let Some(sep) = value_as_str_slice(sep_val) else {
        let arr = array_new(1);
        array_set(arr, 0, s_val);
        return arr;
    };
    let components: Vec<i64> = s.split(sep).map(|sub| allocate_new_string(sub)).collect();
    let arr = array_new(components.len());
    for (i, &comp) in components.iter().enumerate() { array_set(arr, i, comp); }
    arr
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_pad_end(s_val: i64, max_len_smi: i64, fill_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return NULL; };
    let Some(fill) = value_as_str_slice(fill_val) else { return s_val; };
    let target_len = smi_to_i64(max_len_smi) as usize;
    if s.len() >= target_len { return s_val; }
    let needed = target_len - s.len();
    let mut result = s.to_string();
    result.extend(fill.chars().cycle().take(needed));
    allocate_new_string(&result)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_pad_start(s_val: i64, max_len_smi: i64, fill_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return NULL; };
    let Some(fill) = value_as_str_slice(fill_val) else { return s_val; };
    let target_len = smi_to_i64(max_len_smi) as usize;
    if s.len() >= target_len { return s_val; }
    let needed = target_len - s.len();
    let mut padding = String::with_capacity(needed);
    padding.extend(fill.chars().cycle().take(needed));
    padding.push_str(s);
    allocate_new_string(&padding)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_repeat(s_val: i64, count_smi: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return NULL; };
    let count = smi_to_i64(count_smi).max(0) as usize;
    allocate_new_string(&s.repeat(count))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_replace(s_val: i64, search_val: i64, rep_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return NULL; };
    let Some(search) = value_as_str_slice(search_val) else { return s_val; };
    let Some(rep) = value_as_str_slice(rep_val) else { return s_val; };
    allocate_new_string(&s.replacen(search, rep, 1))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_replace_all(s_val: i64, search_val: i64, rep_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return NULL; };
    let Some(search) = value_as_str_slice(search_val) else { return s_val; };
    let Some(rep) = value_as_str_slice(rep_val) else { return s_val; };
    allocate_new_string(&s.replace(search, rep))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_starts_with(s_val: i64, search_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return 0; };
    let Some(search) = value_as_str_slice(search_val) else { return 0; };
    if s.starts_with(search) { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_ends_with(s_val: i64, search_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return 0; };
    let Some(search) = value_as_str_slice(search_val) else { return 0; };
    if s.ends_with(search) { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_includes(s_val: i64, search_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return 0; };
    let Some(search) = value_as_str_slice(search_val) else { return 0; };
    if s.contains(search) { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_to_upper_case(s_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return NULL; };
    allocate_new_string(&s.to_uppercase())
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_to_lower_case(s_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return NULL; };
    allocate_new_string(&s.to_lowercase())
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_trim(s_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return NULL; };
    allocate_new_string(s.trim())
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_trim_end(s_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return NULL; };
    allocate_new_string(s.trim_end())
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wir_string_trim_start(s_val: i64) -> i64 {
    let Some(s) = value_as_str_slice(s_val) else { return NULL; };
    allocate_new_string(s.trim_start())
}

// ============================================================================
// Boxed closure (placeholder wiring)
// ============================================================================

#[repr(C)]
pub struct BoxedClosure {
    pub hdr: ObjHeader,  // tag = TAG_CLOSURE
    pub code_ptr: usize, // or a function id/index if you prefer
    pub env: Vec<i64>,   // captured values
}

#[inline(always)]
pub fn closure_new(code_ptr: usize, env_len: usize) -> ValueRepr {
    unsafe {
        let size = core::mem::size_of::<BoxedClosure>();
        let align = core::mem::align_of::<BoxedClosure>();

        #[cfg(feature = "gc")]
        {
            let mut p = NAPALM_GC.alloc_raw(size, align);
            if p.is_null() {
                p = NAPALM_GC.alloc_slow_path(size, align);
            }

            let clo = p as *mut BoxedClosure;

            // Build Vec on the Rust heap. Filled with uninitialized i64.
            let env = vec![0i64; env_len];

            core::ptr::write(
                clo,
                BoxedClosure {
                    hdr: ObjHeader {
                        tag: TAG_CLOSURE,
                        aux: 0,
                    },
                    code_ptr,
                    env,
                },
            );
            NAPALM_GC.post_alloc_object(p, size);

            return p as ValueRepr;
        }

        #[cfg(not(feature = "gc"))]
        {
            use std::alloc::{Layout, alloc};

            let layout = Layout::from_size_align_unchecked(size, align);

            let p = alloc(layout);
            if p.is_null() {
                std::process::abort();
            }

            let clo = p as *mut BoxedClosure;

            // Build Vec on the Rust heap. Filled with uninitialized i64.
            let env = vec![0i64; env_len];

            core::ptr::write(
                clo,
                BoxedClosure {
                    hdr: ObjHeader {
                        tag: TAG_CLOSURE,
                        aux: 0,
                    },
                    code_ptr,
                    env,
                },
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
    pub proto: ValueRepr,
    pub by_id: HashMap<u32, ValueRepr>,     // FieldId fast path
    pub by_str: HashMap<String, ValueRepr>, // string-key path
}

#[inline(always)]
pub fn obj_new() -> ValueRepr {
    unsafe {
        let size = mem::size_of::<BoxedObj>();
        let align = mem::align_of::<BoxedObj>();

        #[cfg(feature = "gc")]
        {
            let mut p = NAPALM_GC.alloc_raw(size, align);
            if p.is_null() {
                p = NAPALM_GC.alloc_slow_path(size, align);
            }

            let obj = p as *mut BoxedObj;
            core::ptr::write(
                obj,
                BoxedObj {
                    hdr: ObjHeader {
                        tag: TAG_OBJECT,
                        aux: 0,
                    },
                    proto: NULL, // NEW
                    by_id: HashMap::new(),
                    by_str: HashMap::new(),
                },
            );

            NAPALM_GC.post_alloc_object(p, size);

            return p as ValueRepr;
        }

        #[cfg(not(feature = "gc"))]
        {
            use std::alloc::{Layout, alloc};

            let layout = Layout::from_size_align_unchecked(size, align);

            let p = alloc(layout);
            if p.is_null() {
                std::process::abort();
            }

            let obj = p as *mut BoxedObj;
            core::ptr::write(
                obj,
                BoxedObj {
                    hdr: ObjHeader {
                        tag: TAG_OBJECT,
                        aux: 0,
                    },
                    proto: NULL,
                    by_id: HashMap::new(),
                    by_str: HashMap::new(),
                },
            );

            return p as ValueRepr;
        }
    }
}

#[inline(always)]
pub unsafe fn as_obj_mut(v: ValueRepr) -> *mut BoxedObj {
    v as *mut BoxedObj
}

#[inline(always)]
pub unsafe fn obj_set_proto(obj_v: ValueRepr, proto: ValueRepr) -> ValueRepr {
    let o = &mut *as_obj_mut(obj_v);
    o.proto = proto;

    #[cfg(feature = "gc")]
    NAPALM_GC.post_write_barrier(obj_v as *mut u8, &mut o.proto, proto);

    0
}

#[inline(always)]
pub unsafe fn obj_get_proto(obj_v: ValueRepr) -> ValueRepr {
    let o = &*as_obj_mut(obj_v);
    o.proto
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

#[inline(always)]
pub unsafe fn obj_get_field_deep(mut obj_v: ValueRepr, fid: u32) -> ValueRepr {
    while obj_v != NULL {
        let o = &*(obj_v as *const BoxedObj);
        if let Some(&v) = o.by_id.get(&fid) {
            return v;
        }
        obj_v = o.proto;
    }
    NULL
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

#[inline(always)]
pub unsafe fn obj_get_str_deep(mut obj_v: ValueRepr, key: &str) -> ValueRepr {
    while obj_v != NULL {
        let o = &*(obj_v as *const BoxedObj);
        if let Some(&v) = o.by_str.get(key) {
            return v;
        }
        obj_v = o.proto;
    }
    NULL
}

#[inline(always)]
pub unsafe fn obj_assign(dst_v: ValueRepr, src_v: ValueRepr) -> ValueRepr {
    if dst_v == NULL || src_v == NULL || (dst_v & 1) == 1 || (src_v & 1) == 1 {
        return 0;
    }

    let dst = &mut *as_obj_mut(dst_v);
    let src = &*as_obj_mut(src_v);

    for (key, &val) in &src.by_str {
        let entry = dst.by_str.entry(key.clone()).or_insert(NULL);
        *entry = val;

        #[cfg(feature = "gc")]
        {
            let slot: *mut ValueRepr = entry as *mut ValueRepr;
            NAPALM_GC.post_write_barrier(dst_v as *mut u8, slot, val);
        }
    }

    0
}

#[inline(always)]
pub unsafe fn obj_clone_shallow(src_v: ValueRepr) -> ValueRepr {
    if src_v == NULL || (src_v & 1) == 1 {
        return obj_new();
    }

    let clone_v = obj_new();
    let clone = &mut *as_obj_mut(clone_v);
    let src = &*as_obj_mut(src_v);

    clone.proto = src.proto;

    #[cfg(feature = "gc")]
    {
        NAPALM_GC.post_write_barrier(clone_v as *mut u8, &mut clone.proto, src.proto);
    }

    obj_assign(clone_v, src_v);
    clone_v
}

// ============================================================================
// Debug formatting
// ============================================================================

/// Try to pretty-print a runtime value according to our tags.
/// Keep this conservative; it’s only for `print` and debugging.
pub fn fmt_value(v: i64) -> String {
    // Booleans are raw 0/1
    if is_bool(v) {
        return if v != 0 {
            "1".to_string()
        } else {
            "0".to_string()
        };
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

#[inline(always)]
pub fn dbg_classify(v: i64) -> &'static str {
    // We only say what we can know without dereferencing:
    // - "null"      => 0
    // - "smi"       => (v & 1) == 1
    // - "ptr"       => even, nonzero
    if v == 0 {
        "null"
    } else if (v & 1) == 1 {
        "smi"
    } else {
        "ptr"
    }
}

pub fn dbg_addr(v: i64) -> String {
    if (v & 1) == 1 || v == 0 {
        format!("{}", v)
    } else {
        format!("0x{:x}", v as u64)
    }
}
