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

// Tags for heap objects we *box ourselves* in the JIT.
// (We won’t inspect foreign pointers; only ones we allocate.)
pub const TAG_BOXED_F64: u32 = 1;

#[repr(C)]
pub struct ObjHeader {
    pub tag: u32,
    pub aux: u32, // reserved for length/type-specific flags later
}

#[repr(C)]
pub struct BoxedF64 {
    pub hdr: ObjHeader,
    pub val: f64,
}