#![allow(dead_code)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(unused_imports)]
#![allow(unused_variables)]

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
// Arrays (Vec-backed) — full feature set (GC-friendly)
// ============================================================================

#[repr(C)]
pub struct Array {
    pub hdr: ObjHeader, // tag = TAG_ARRAY
    pub len: i64,       // unused in this Vec-backed impl; kept for offset compat if needed
}

// Offsets used by the JIT (kept for compatibility with any flat layout users)
pub const ARRAY_HDR_SIZE:    i32 = core::mem::size_of::<ObjHeader>() as i32; // 8
pub const ARRAY_LEN_OFFSET:  i32 = ARRAY_HDR_SIZE;                           // 8
pub const ARRAY_DATA_OFFSET: i32 = ARRAY_HDR_SIZE + core::mem::size_of::<i64>() as i32; // 16

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
fn alloc_array_from_vec(mut buf: Vec<i64>) -> ValueRepr {
    unsafe {
        let size  = core::mem::size_of::<BoxedArray>();
        let align = core::mem::align_of::<BoxedArray>();

        #[cfg(feature = "gc")] {
            let mut p = NAPALM_GC.alloc_raw(size, align);
            if p.is_null() { p = NAPALM_GC.alloc_slow_path(size, align); }

            let obj = p as *mut BoxedArray;
            core::ptr::write(obj, BoxedArray { hdr: ObjHeader { tag: TAG_ARRAY, aux: 0 }, buf });
            NAPALM_GC.post_alloc_object(p, size);
            return p as ValueRepr;
        }

        #[cfg(not(feature = "gc"))] {
            use std::alloc::{alloc, Layout};
            let layout = Layout::from_size_align_unchecked(size, align);
            let p = alloc(layout);
            if p.is_null() { std::process::abort(); }
            let obj = p as *mut BoxedArray;
            core::ptr::write(obj, BoxedArray { hdr: ObjHeader { tag: TAG_ARRAY, aux: 0 }, buf });
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
    if idx >= a.buf.len() { a.buf.resize(idx + 1, 0); }
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
    if a.buf.is_empty() { return NULL; }
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
        if ok != 0 { return x; }

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
        if ok != 0 { return make_smi(i as i64); }

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
        if ok != 0 { out.push(x); }

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
    init: ValueRepr
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

        #[cfg(feature = "gc")] {
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

    if d.buf.len() < n { d.buf.resize(n, 0); }

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

#[inline(always)] fn smi(x: i64) -> i64 { (x << 1) | 1 }
#[inline(always)] fn smi_to_i64_wrapped(v: i64) -> i64 { v >> 1 } // arithmetic shift

// ---- C exports expected by the JIT ----
#[unsafe(no_mangle)]
pub extern "C" fn wir_array_new(len: i64) -> i64 {
    let n = smi_to_i64_wrapped(len).max(0) as usize;
    array_new(n)
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_len(arr: i64) -> i64 {
    if arr == 0 { return smi(0); }
    unsafe { smi(array_len(arr) as i64) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_get(arr: i64, idx: i64) -> i64 {
    if arr == 0 { return 0; }
    let i = smi_to_i64_wrapped(idx);
    if i < 0 { return 0; }
    unsafe { array_get(arr, i as usize) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_set(arr: i64, idx: i64, val: i64) -> i64 {
    if arr == 0 { return 0; }
    let i = smi_to_i64_wrapped(idx);
    if i < 0 { return 0; }
    unsafe { array_set(arr, i as usize, val) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_set_len(arr: i64, new_len: i64) -> i64 {
    if arr == 0 { return 0; }
    let n = smi_to_i64_wrapped(new_len).max(0) as usize;
    unsafe { array_set_len(arr, n) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_push(arr: i64, val: i64) -> i64 {
    if arr == 0 { return smi(0); }
    unsafe { array_push(arr, val) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_pop(arr: i64) -> i64 {
    if arr == 0 { return 0; }
    unsafe { array_pop(arr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_shift(arr: i64) -> i64 {
    if arr == 0 { return 0; }
    unsafe { array_shift(arr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_unshift(arr: i64, val: i64) -> i64 {
    if arr == 0 { return smi(0); }
    unsafe { array_unshift(arr, val) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_slice(arr: i64, start: i64, end: i64) -> i64 {
    if arr == 0 { return 0; }
    let s = smi_to_i64_wrapped(start).max(0) as usize;
    let e = smi_to_i64_wrapped(end).max(0) as usize;
    unsafe { array_slice(arr, s, e) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_map(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 { return 0; }
    unsafe { array_map(arr, clo_ptr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_for_each(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 { return 0; }
    unsafe { array_for_each(arr, clo_ptr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_find(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 { return 0; }
    unsafe { array_find(arr, clo_ptr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_find_index(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 { return smi(-1); }
    unsafe { array_find_index(arr, clo_ptr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_filter(arr: i64, clo_ptr: i64) -> i64 {
    if arr == 0 { return 0; }
    unsafe { array_filter(arr, clo_ptr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_reduce(arr: i64, clo_ptr: i64, has_init: i64, init: i64) -> i64 {
    if arr == 0 { return 0; }
    unsafe { array_reduce(arr, clo_ptr, has_init != 0, init) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_fill(arr: i64, val: i64) -> i64 {
    if arr == 0 { return 0; }
    unsafe { array_fill(arr, val) }
}

#[unsafe(no_mangle)]
pub extern "C" fn wir_array_copy(dst: i64, src: i64, len: i64) -> i64 {
    if dst == 0 || src == 0 { return 0; }
    let n = smi_to_i64_wrapped(len).max(0) as usize;
    unsafe { array_copy(dst, src, n) }
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
            let env = vec![0i64; env_len];

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
            let env = vec![0i64; env_len];

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
