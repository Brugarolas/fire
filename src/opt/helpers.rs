// src/opt/helpers.rs
#![allow(dead_code)]

use crate::wir::{Constant, Function, Inst, ValueDef, ValueId};

/// Return the constant value of `v` if it is a constant (either a ValueDef::Const
/// OR produced by an Inst::Const).
pub fn value_const(func: &Function, v: ValueId) -> Option<Constant> {
    match &func.values[v.0 as usize].def {
        ValueDef::Const(c) => Some(c.clone()),
        ValueDef::InstResult(inst, _) => {
            match &func.nodes[inst.0 as usize].kind {
                Inst::Const(c) => Some(c.clone()),
                _ => None,
            }
        }
        _ => None,
    }
}

pub fn value_is_const_i32(func: &Function, v: ValueId, k: i32) -> bool {
    matches!(value_const(func, v), Some(Constant::Int32(c)) if c == k)
}

pub fn value_is_const_f64(func: &Function, v: ValueId, k: f64) -> bool {
    matches!(value_const(func, v), Some(Constant::F64(c)) if c == k)
}

pub fn value_is_const_bool(func: &Function, v: ValueId, k: bool) -> bool {
    matches!(value_const(func, v), Some(Constant::Bool(c)) if c == k)
}

pub fn value_is_const_str(func: &Function, v: ValueId, s: &str) -> bool {
    matches!(value_const(func, v), Some(Constant::Str(ref t)) if t == s)
}

pub fn value_as_i32(func: &Function, v: ValueId) -> Option<i32> {
    match value_const(func, v) {
        Some(Constant::Int32(c)) => Some(c),
        _ => None,
    }
}

pub fn value_as_f64(func: &Function, v: ValueId) -> Option<f64> {
    match value_const(func, v) {
        Some(Constant::F64(c)) => Some(c),
        _ => None,
    }
}

pub fn value_as_bool(func: &Function, v: ValueId) -> Option<bool> {
    match value_const(func, v) {
        Some(Constant::Bool(c)) => Some(c),
        _ => None,
    }
}

/// Return Some(x) if all items are equal (and slice non-empty); else None.
pub fn all_same<T: Copy + Eq>(xs: &[T]) -> Option<T> {
    if xs.is_empty() { return None; }
    let first = xs[0];
    if xs.iter().all(|&x| x == first) { Some(first) } else { None }
}
