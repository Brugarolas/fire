// src/value.rs
#![allow(dead_code)]

pub type ValueRepr = i64;

// ---- Pointer / immediate tests ----
#[inline] pub fn is_ptr(v: ValueRepr) -> bool { (v & 1) == 0 }
#[inline] pub fn is_imm(v: ValueRepr) -> bool { (v & 1) == 1 }

// ---- Small Int (SMI) encoding ----
#[inline] pub fn make_smi(n: i64) -> ValueRepr { (n << 1) | 1 }
#[inline] pub fn smi_to_i64(v: ValueRepr) -> i64 { v >> 1 } // arithmetic shift

// ---- Null (boxed-null) ----
pub const NULL: ValueRepr = 0;

// ---- (Future) Boolean singletons ----
// Leave disabled until the lowerer stops using 0/1 in logic and equality.
// pub const FALSE_IMM: ValueRepr = 0x15;
// pub const TRUE_IMM:  ValueRepr = 0x1D;
// #[inline] pub fn make_bool(b: bool) -> ValueRepr { if b { TRUE_IMM } else { FALSE_IMM } }
// #[inline] pub fn is_bool_imm(v: ValueRepr) -> bool { v == TRUE_IMM || v == FALSE_IMM }

#[repr(C)]
#[derive(Copy, Clone)]
pub struct ObjHeader {
    pub tag: u32,
    pub aux: u32, // size, hash, flags, etc (free for now)
}

// Object tags (grow as we add types)
pub const TAG_BOXED_F64: u32 = 1;
pub const TAG_STRING:   u32 = 2; // future
pub const TAG_ARRAY:    u32 = 3; // future
// pub const TAG_CLOSURE:  u32 = 4; // (we use a dedicated struct today)

// The distinguished null value (even=pointer space)

// ---- Small integers (SMI): odd values ----
#[inline] pub fn smi_from_i64(x: i64) -> i64      { (x << 1) | 1 }

// ---- Booleans: raw 0/1 (not SMIs)
#[inline] pub fn is_bool(v: i64) -> bool          { v == 0 || v == 1 }
#[inline] pub fn to_bool(v: i64) -> bool          { v != 0 }

// ---- Boxed f64 --------------------------------------------------------------

#[repr(C)]
pub struct BoxedF64 {
    pub hdr: ObjHeader,
    pub val: f64,
}

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

#[repr(C)]
pub struct BoxedStr {
    pub hdr: ObjHeader,
    pub len: usize,       // byte length (no trailing NUL)
    pub data: *const u8,  // points to UTF-8 bytes (NUL-terminated OK, not required)
}

#[repr(C)]
pub struct BoxedArray {
    pub hdr: ObjHeader,
    pub buf: Vec<i64>,
}

impl BoxedArray {
    #[inline] pub fn len(&self) -> usize { self.buf.len() }
    #[inline] pub fn cap(&self) -> usize { self.buf.capacity() }
}

// ---- Debug formatting --------------------------------------------------------

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
                    // when we add strings, decode here
                    return format!("<string@{:#x}>", v as u64);
                }
                TAG_ARRAY => {
                    return format!("<array@{:#x}>", v as u64);
                }
                _ => { /* fallthrough */ }
            }
        }
    }

    // Unknown object
    format!("{:#x}", v as u64)
}
