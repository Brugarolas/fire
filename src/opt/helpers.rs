// src/opt/helpers.rs
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::wir::{Constant, Function, Inst, ValueDef, ValueId};

/// Return the constant value of `v` if it is a constant (either a ValueDef::Const
/// OR produced by an Inst::Const).
pub fn value_const(func: &Function, v: ValueId) -> Option<Constant> {
    match &func.values[v.0 as usize].def {
        ValueDef::Const(c) => Some(c.clone()),
        ValueDef::InstResult(inst, _) => match &func.nodes[inst.0 as usize].kind {
            Inst::Const(c) => Some(c.clone()),
            _ => None,
        },
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
    if xs.is_empty() {
        return None;
    }
    let first = xs[0];
    if xs.iter().all(|&x| x == first) {
        Some(first)
    } else {
        None
    }
}

/// Fold `x op y` with the runtime's number semantics (SMI arithmetic that overflows or
/// divides inexactly produces a float). Returns `None` when the result is not an exact i32.
pub fn fold_js_int_bin(op: crate::wir::IntBinOp, x: i32, y: i32) -> Option<i32> {
    use crate::wir::IntBinOp::*;
    let (x, y) = (x as i64, y as i64);
    let r = match op {
        Add => x + y,
        Sub => x - y,
        Mul => x * y,
        DivS if y != 0 && x % y == 0 => x / y,
        RemS if y != 0 => x % y,
        And => x & y,
        Or => x | y,
        Xor => x ^ y,
        Shl => x.checked_shl((y & 63) as u32)?,
        Sar => x >> (y & 63),
        ShrU if x >= 0 => x >> (y & 63),
        _ => return None,
    };
    i32::try_from(r).ok()
}

use crate::wir::{BlockId, FuncId}; // keep at top-level if you prefer

/// Replace all uses of `from` with `to` inside a single instruction.
/// Returns the number of replaced operands.
pub fn replace_uses_in_inst(inst: &mut Inst, from: ValueId, to: ValueId) -> usize {
    let mut n = 0usize;
    macro_rules! r {
        ($v:expr) => {
            if $v == from {
                $v = to;
                n += 1;
            }
        };
    }
    macro_rules! rv {
        ($vs:expr) => {{
            for v in $vs.iter_mut() {
                if *v == from {
                    *v = to;
                    n += 1;
                }
            }
        }};
    }

    match inst {
        // ---- Control ----
        Inst::Phi(args) => {
            rv!(args);
        }
        Inst::Jump(_b, args) => {
            rv!(args);
        }
        Inst::Branch { cond, .. } => {
            r!(*cond);
        }
        Inst::Switch { tag, .. } => {
            r!(*tag);
        }
        Inst::Return(vals) => {
            rv!(vals);
        }
        Inst::Throw(v) => {
            r!(*v);
        }

        // ---- Effect/bookkeeping ----
        Inst::EffectEntry | Inst::Safepoint => {}

        // ---- Const / mov ----
        Inst::Const(_) => {}
        Inst::Mov(v) => {
            r!(*v);
        }

        // ---- Guards ----
        Inst::GuardType { val, .. } => {
            r!(*val);
        }
        Inst::GuardShape { obj, .. } => {
            r!(*obj);
        }
        Inst::GuardBounds { idx, len, .. } => {
            r!(*idx);
            r!(*len);
        }
        Inst::GuardNotNull { val, .. } => {
            r!(*val);
        }
        Inst::GuardIsInt { val, .. } => {
            r!(*val);
        }
        Inst::GuardIsF64 { val, .. } => {
            r!(*val);
        }
        Inst::Bailout { .. } => {}

        // ---- Objects ----
        Inst::AllocObj { .. } => {}
        Inst::LoadField { obj, .. } => {
            r!(*obj);
        }
        Inst::StoreField { obj, val, .. } => {
            r!(*obj);
            r!(*val);
        }
        Inst::TransitionShape { obj, .. } => {
            r!(*obj);
        }

        // ---- Arrays ----
        Inst::AllocArray { len, .. } => {
            r!(*len);
        }
        Inst::ArrayLen(v) => {
            r!(*v);
        }
        Inst::ArraySetLen { arr, new_len } => {
            r!(*arr);
            r!(*new_len);
        }
        Inst::LoadElem { arr, idx } => {
            r!(*arr);
            r!(*idx);
        }
        Inst::StoreElem { arr, idx, val } => {
            r!(*arr);
            r!(*idx);
            r!(*val);
        }
        Inst::ArraySlice { arr, start, end } => {
            r!(*arr);
            r!(*start);
            r!(*end);
        }

        Inst::ArrayPush { arr, val } => {
            r!(*arr);
            r!(*val);
        }
        Inst::ArrayPop(arr) => {
            r!(*arr);
        }
        Inst::ArrayShift(arr) => {
            r!(*arr);
        }
        Inst::ArrayUnshift { arr, val } => {
            r!(*arr);
            r!(*val);
        }

        Inst::ArrayMap { .. } => {}
        Inst::ArrayReduce { func: _, init, arr } => {
            r!(*init);
            r!(*arr);
        }
        Inst::ArrayFill { arr, val } => {
            r!(*arr);
            r!(*val);
        }
        Inst::ArrayCopy { dst, src, len } => {
            r!(*dst);
            r!(*src);
            r!(*len);
        }

        Inst::ArrayForEach { .. } => {}
        Inst::ArrayFind { .. } => {}
        Inst::ArrayFindIndex { .. } => {}
        Inst::ArrayFilter { .. } => {}

        // ---- Strings ----
        Inst::StrLen(v) => {
            r!(*v);
        }
        Inst::StrConcat { a, b } => {
            r!(*a);
            r!(*b);
        }
        Inst::StrSlice { s, start, end } => {
            r!(*s);
            r!(*start);
            r!(*end);
        }
        Inst::StrCompare { a, b } => {
            r!(*a);
            r!(*b);
        }
        Inst::StrContains { s, sub } => {
            r!(*s);
            r!(*sub);
        }
        Inst::StrToNumber(v) => {
            r!(*v);
        }

        // ---- Numerics ----
        Inst::IntBin { a, b, .. } => {
            r!(*a);
            r!(*b);
        }
        Inst::F64Bin { a, b, .. } => {
            r!(*a);
            r!(*b);
        }
        Inst::NumAdd(a, b)
        | Inst::NumSub(a, b)
        | Inst::NumMul(a, b)
        | Inst::NumDiv(a, b)
        | Inst::NumRem(a, b) => {
            r!(*a);
            r!(*b);
        }

        Inst::CmpInt { a, b, .. } | Inst::CmpF64 { a, b, .. } | Inst::CmpRefEq { a, b } => {
            r!(*a);
            r!(*b);
        }

        // ---- Boxing / tagging ----
        Inst::BoxInt(v)
        | Inst::BoxF64(v)
        | Inst::BoxBool(v)
        | Inst::UnboxToInt(v)
        | Inst::UnboxToF64(v) => {
            r!(*v);
        }

        // ---- Calls / closures ----
        Inst::CallDirect { args, .. } => {
            rv!(args);
        }
        Inst::CallDirectMemoized { args, .. } => {
            rv!(args);
        }
        Inst::CallIC { recv, args, .. } => {
            r!(*recv);
            rv!(args);
        }
        Inst::MethodLookup { obj, .. } => {
            r!(*obj);
        }

        Inst::AllocClosure { .. } => {}
        Inst::LoadEnv { clos, .. } => {
            r!(*clos);
        }
        Inst::StoreEnv { clos, val, .. } => {
            r!(*clos);
            r!(*val);
        }

        Inst::MakeClosure { env, .. } => {
            r!(*env);
        }
        Inst::CallClosure { fun, args, .. } => {
            r!(*fun);
            rv!(args);
        }

        // ---- Natives / intrinsics ----
        Inst::CallNative { args, .. } => {
            rv!(args);
        }

        // ---- GC barriers ----
        Inst::PostWriteBarrier { obj, val } => {
            r!(*obj);
            r!(*val);
        }
        Inst::ReadBarrier { obj } => {
            r!(*obj);
        }

        // ---- OSR ----
        Inst::OSRPoint => {}

        _ => { /* skip other instructions */ }
    }
    n
}

pub fn is_pure(inst: &Inst) -> bool {
    use Inst::*;
    match inst {
        // Control or effectful explicitly not pure
        Phi(_) | Jump(_, _) | Branch { .. } | Switch { .. } | Return(_) | Throw(_) => false,
        EffectEntry | Safepoint => false,
        // Guards are effectful (ordering) — skip
        GuardType { .. }
        | GuardShape { .. }
        | GuardBounds { .. }
        | GuardNotNull { .. }
        | GuardIsInt { .. }
        | GuardIsF64 { .. }
        | Bailout { .. } => false,
        // Stores/allocs/calls/barriers are effectful — skip
        AllocObj { .. }
        | StoreField { .. }
        | TransitionShape { .. }
        | AllocArray { .. }
        | StoreElem { .. }
        | ArraySetLen { .. }
        | ArrayPush { .. }
        | ArrayPop(_)
        | ArrayShift(_)
        | ArrayUnshift { .. }
        | ArrayFill { .. }
        | ArrayCopy { .. }
        | ArrayMap { .. }
        | ArrayReduce { .. }
        | ArrayForEach { .. }
        | ArrayFind { .. }
        | ArrayFindIndex { .. }
        | ArrayFilter { .. }
        | CallDirect { .. }
        | CallIC { .. }
        | CallClosure { .. }
        | CallNative { .. }
        | AllocClosure { .. }
        | StoreEnv { .. }
        | PostWriteBarrier { .. }
        | ReadBarrier { .. }
        | StrToNumber(_)
        | OSRPoint => false,
        // Everything else is pure.
        _ => true,
    }
}
