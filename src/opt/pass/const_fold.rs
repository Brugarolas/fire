// src/opt/pass/const_fold.rs
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::opt::helpers::{
    value_const, value_as_i32, value_as_f64, value_is_const_i32, value_is_const_f64,
};
use crate::wir::{Constant, Inst, IntBinOp, F64BinOp, CmpKind, Type};

pub struct ConstFold;

impl OptimizationWIR for ConstFold {
    fn optimize_node(&mut self, cur: &mut InstCursor, _q: &mut WirEditQueue) -> bool {
        use Inst::*;
        let mut changed = false;

        // Small helpers -------------------------------------------------------
        macro_rules! replace_with_const {
            ($c:expr, $ty:expr) => {{
                cur.with_cur(|n| { n.kind = Inst::Const($c); n.ty = Some($ty); });
                changed = true;
            }};
        }
        macro_rules! replace_with_value {
            ($v:expr) => {{
                cur.with_cur(|n| { n.kind = Inst::Mov($v); /* type will be tightened elsewhere */ });
                changed = true;
            }};
        }

        let is_commutative_int = |op: IntBinOp| {
            matches!(op, IntBinOp::Add | IntBinOp::Mul | IntBinOp::And | IntBinOp::Or | IntBinOp::Xor)
        };

        match cur.cur_kind() {
            // Mov(Const c) -> Const c   (also tighten obvious type)
            Mov(v) => {
                if let Some(c) = cur.with_func(|f| value_const(f, v)) {
                    cur.with_cur(|n| {
                        n.kind = Const(c.clone());
                        n.ty = Some(match n.ty.clone().unwrap_or(Type::Top) {
                            _ => const_type_hint(&n.kind),
                        });
                    });
                    changed = true;
                }
            }

            // -------- Canonicalize commutative IntBin to put constants on RHS
            IntBin { op, a, b } if is_commutative_int(op) => {
                let (a_is_c, b_is_c) = cur.with_func(|f| {
                    (
                        matches!(value_const(f, a), Some(Constant::Int32(_))),
                        matches!(value_const(f, b), Some(Constant::Int32(_))),
                    )
                });
                if a_is_c && !b_is_c {
                    cur.with_cur(|n| if let Inst::IntBin { a: aa, b: bb, .. } = &mut n.kind {
                        std::mem::swap(aa, bb);
                    });
                    changed = true;
                }
            }

            // ---------- Int constant folding + identities ----------
            IntBin { op, a, b } => {
                let (ac, bc) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));

                // Algebraic/bitwise/shift identities when one side is a constant
                if ac.is_none() || bc.is_none() {
                    let a_is_c = ac.is_some();
                    let b_is_c = bc.is_some();

                    match op {
                        IntBinOp::Add => {
                            if b_is_c && bc == Some(0) { replace_with_value!(a); }
                            else if a_is_c && ac == Some(0) { replace_with_value!(b); }
                        }
                        IntBinOp::Sub => {
                            if b_is_c && bc == Some(0) { replace_with_value!(a); }
                            // 0 - x left as-is (no Neg op in IR)
                        }
                        IntBinOp::Mul => {
                            if b_is_c {
                                match bc.unwrap() {
                                    0 => replace_with_const!(Constant::Int32(0), Type::Int32),
                                    1 => replace_with_value!(a),
                                    _ => {}
                                }
                            } else if a_is_c {
                                match ac.unwrap() {
                                    0 => replace_with_const!(Constant::Int32(0), Type::Int32),
                                    1 => replace_with_value!(b),
                                    _ => {}
                                }
                            }
                        }
                        IntBinOp::And => {
                            if b_is_c {
                                let y = bc.unwrap();
                                if y == 0 { replace_with_const!(Constant::Int32(0), Type::Int32); }
                                else if y == -1 { replace_with_value!(a); }
                            } else if a_is_c {
                                let x = ac.unwrap();
                                if x == 0 { replace_with_const!(Constant::Int32(0), Type::Int32); }
                                else if x == -1 { replace_with_value!(b); }
                            }
                        }
                        IntBinOp::Or => {
                            if b_is_c {
                                let y = bc.unwrap();
                                if y == 0 { replace_with_value!(a); }
                                else if y == -1 { replace_with_const!(Constant::Int32(-1), Type::Int32); }
                            } else if a_is_c {
                                let x = ac.unwrap();
                                if x == 0 { replace_with_value!(b); }
                                else if x == -1 { replace_with_const!(Constant::Int32(-1), Type::Int32); }
                            }
                        }
                        IntBinOp::Xor => {
                            if b_is_c && bc == Some(0) { replace_with_value!(a); }
                            else if a_is_c && ac == Some(0) { replace_with_value!(b); }
                        }
                        IntBinOp::Shl | IntBinOp::ShrU | IntBinOp::Sar => {
                            if b_is_c {
                                let sh = (bc.unwrap() as u32) & 31;
                                if sh == 0 { replace_with_value!(a); }
                            }
                        }
                        IntBinOp::DivS | IntBinOp::RemS => { /* only fold when both consts (below) */ }
                    }
                }

                // Full constant fold when both sides are constants
                if let (Some(x), Some(y)) = (ac, bc) {
                    let folded = match op {
                        IntBinOp::Add => Some(x.wrapping_add(y)),
                        IntBinOp::Sub => Some(x.wrapping_sub(y)),
                        IntBinOp::Mul => Some(x.wrapping_mul(y)),
                        IntBinOp::DivS => {
                            if y == 0 || (x == i32::MIN && y == -1) { None } else { Some(x.wrapping_div(y)) }
                        }
                        IntBinOp::RemS => {
                            if y == 0 { None } else { Some(x.wrapping_rem(y)) }
                        }
                        IntBinOp::And => Some(x & y),
                        IntBinOp::Or  => Some(x | y),
                        IntBinOp::Xor => Some(x ^ y),
                        IntBinOp::Shl => Some(x.wrapping_shl((y as u32) & 31)),
                        IntBinOp::ShrU => Some(((x as u32) >> ((y as u32) & 31)) as i32),
                        IntBinOp::Sar => Some(x >> ((y as u32) & 31)), // arithmetic shift
                    };
                    if let Some(v) = folded {
                        replace_with_const!(Constant::Int32(v), Type::Int32);
                    }
                }
            }

            // ---------- F64 constant folding + IEEE-safe identities ----------
            F64Bin { op, a, b } => {
                let (ac, bc) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b)));

                // Identities with one const side that are always IEEE-safe
                if ac.is_none() || bc.is_none() {
                    let a_is_c = ac.is_some();
                    let b_is_c = bc.is_some();

                    match op {
                        F64BinOp::Add => {
                            if b_is_c && bc.unwrap() == 0.0 { replace_with_value!(a); }
                            else if a_is_c && ac.unwrap() == 0.0 { replace_with_value!(b); }
                        }
                        F64BinOp::Sub => {
                            if b_is_c && bc.unwrap() == 0.0 { replace_with_value!(a); }
                        }
                        F64BinOp::Mul => {
                            if b_is_c && bc.unwrap() == 1.0 { replace_with_value!(a); }
                            else if a_is_c && ac.unwrap() == 1.0 { replace_with_value!(b); }
                            // DO NOT fold *0.0 due to NaN*0.0 = NaN
                        }
                        F64BinOp::Div => {
                            if b_is_c && bc.unwrap() == 1.0 { replace_with_value!(a); }
                            // DO NOT fold 0.0/x or x/0.0 etc.
                        }
                        F64BinOp::Rem => { /* both-const only */ }
                    }
                }

                if let (Some(x), Some(y)) = (ac, bc) {
                    let folded = match op {
                        F64BinOp::Add => x + y,
                        F64BinOp::Sub => x - y,
                        F64BinOp::Mul => x * y,
                        F64BinOp::Div => x / y,
                        F64BinOp::Rem => x % y,
                    };
                    replace_with_const!(Constant::F64(folded), Type::F64);
                }
            }

            // ---------- Generic numeric ops (Num*) when both sides constant ----------
            NumAdd(a, b) | NumSub(a, b) | NumMul(a, b) | NumDiv(a, b) | NumRem(a, b) => {
                let (ai, bi) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));
                let (af, bf) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b)));

                // both int -> fold to Int32
                if let (Some(x), Some(y)) = (ai, bi) {
                    let v = match cur.cur_kind() {
                        NumAdd(_,_) => x.wrapping_add(y),
                        NumSub(_,_) => x.wrapping_sub(y),
                        NumMul(_,_) => x.wrapping_mul(y),
                        NumDiv(_,_) => {
                            if y == 0 || (x == i32::MIN && y == -1) { return changed; }
                            x.wrapping_div(y)
                        }
                        NumRem(_,_) => {
                            if y == 0 { return changed; }
                            x.wrapping_rem(y)
                        }
                        _ => unreachable!(),
                    };
                    replace_with_const!(Constant::Int32(v), Type::Int32);
                }
                // else if any f64 -> promote and fold to F64
                else if let (Some(x), Some(y)) = (af, bf) {
                    let v = match cur.cur_kind() {
                        NumAdd(_,_) => x + y,
                        NumSub(_,_) => x - y,
                        NumMul(_,_) => x * y,
                        NumDiv(_,_) => x / y,
                        NumRem(_,_) => x % y,
                        _ => unreachable!(),
                    };
                    replace_with_const!(Constant::F64(v), Type::F64);
                }
            }

            // ---------- Comparisons ----------
            // Same-SSA comparisons
            CmpInt { kind, a, b } if a == b => {
                let v = match kind {
                    CmpKind::Eq => true,
                    CmpKind::Ne => false,
                    CmpKind::Lt => false,
                    CmpKind::Le => true,
                    CmpKind::Gt => false,
                    CmpKind::Ge => true,
                };
                replace_with_const!(Constant::Bool(v), Type::Bool);
            }
            CmpF64 { kind, a, b } if a == b => {
                if let Some(x) = cur.with_func(|f| value_as_f64(f, a)) {
                    let (eq, ne, ord_true) = (x == x, x != x, !x.is_nan());
                    let v = match kind {
                        CmpKind::Eq => eq,
                        CmpKind::Ne => ne,
                        CmpKind::Lt => false,
                        CmpKind::Le => ord_true, // true for non-NaN, false for NaN
                        CmpKind::Gt => false,
                        CmpKind::Ge => ord_true, // true for non-NaN, false for NaN
                    };
                    replace_with_const!(Constant::Bool(v), Type::Bool);
                }
            }

            // Both-const fast paths
            CmpInt { kind, a, b } => {
                if let (Some(x), Some(y)) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b))) {
                    let r = match kind {
                        CmpKind::Eq => x == y,
                        CmpKind::Ne => x != y,
                        CmpKind::Lt => x < y,
                        CmpKind::Le => x <= y,
                        CmpKind::Gt => x > y,
                        CmpKind::Ge => x >= y,
                    };
                    replace_with_const!(Constant::Bool(r), Type::Bool);
                }
            }
            CmpF64 { kind, a, b } => {
                if let (Some(x), Some(y)) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b))) {
                    let r = match kind {
                        CmpKind::Eq => x == y,
                        CmpKind::Ne => x != y,
                        CmpKind::Lt => x < y,
                        CmpKind::Le => x <= y,
                        CmpKind::Gt => x > y,
                        CmpKind::Ge => x >= y,
                    };
                    replace_with_const!(Constant::Bool(r), Type::Bool);
                }
            }

            // ---------- Guards on constants ----------
            GuardIsInt { val, .. } => {
                if let Some(c) = cur.with_func(|f| value_const(f, val)) {
                    if let Constant::Int32(i) = c {
                        replace_with_const!(Constant::Int32(i), Type::Int32);
                    }
                }
            }
            GuardIsF64 { val, .. } => {
                if let Some(c) = cur.with_func(|f| value_const(f, val)) {
                    if let Constant::F64(x) = c {
                        replace_with_const!(Constant::F64(x), Type::F64);
                    }
                }
            }
            GuardNotNull { val, .. } => {
                if let Some(c) = cur.with_func(|f| value_const(f, val)) {
                    if !matches!(c, Constant::Null) {
                        replace_with_value!(val);
                    }
                }
            }

            // ---------- Strings ----------
            StrLen(sv) => {
                if let Some(Constant::Str(s)) = cur.with_func(|f| value_const(f, sv)) {
                    replace_with_const!(Constant::Int32(s.len() as i32), Type::Int32);
                }
            }

            StrConcat { a, b } => {
                let (ac, bc) = cur.with_func(|f| (value_const(f, a), value_const(f, b)));
                match (ac, bc) {
                    (Some(Constant::Str(sa)), Some(Constant::Str(sb))) => {
                        let mut s = String::with_capacity(sa.len() + sb.len());
                        s.push_str(&sa); s.push_str(&sb);
                        replace_with_const!(Constant::Str(s), Type::Str);
                    }
                    (Some(Constant::Str(sa)), None) if sa.is_empty() => replace_with_value!(b),
                    (None, Some(Constant::Str(sb))) if sb.is_empty() => replace_with_value!(a),
                    _ => {}
                }
            }

            StrSlice { s, start, end } => {
                if let (Some(Constant::Str(src)),
                        Some(i), Some(j)) =
                    cur.with_func(|f| (value_const(f, s),
                                       value_as_i32(f, start),
                                       value_as_i32(f, end)))
                {
                    let len = src.len() as i32;
                    if 0 <= i && i <= j && j <= len {
                        let ss = &src[(i as usize)..(j as usize)];
                        replace_with_const!(Constant::Str(ss.to_string()), Type::Str);
                    }
                }
            }

            StrCompare { a, b } => {
                if let (Some(Constant::Str(sa)), Some(Constant::Str(sb))) =
                    cur.with_func(|f| (value_const(f, a), value_const(f, b)))
                {
                    replace_with_const!(Constant::Bool(sa == sb), Type::Bool);
                }
            }

            StrContains { s, sub } => {
                if let (Some(Constant::Str(hay)), Some(Constant::Str(needle))) =
                    cur.with_func(|f| (value_const(f, s), value_const(f, sub)))
                {
                    replace_with_const!(Constant::Bool(hay.contains(&needle)), Type::Bool);
                }
            }

            // ---------- Ref equality on easy constants ----------
            CmpRefEq { a, b } => {
                if a == b {
                    replace_with_const!(Constant::Bool(true), Type::Bool);
                } else if let (Some(ca), Some(cb)) = cur.with_func(|f| (value_const(f, a), value_const(f, b))) {
                    let v = match (ca, cb) {
                        (Constant::Null, Constant::Null) => true,
                        (Constant::Null, _) | (_, Constant::Null) => false,
                        _ => return changed, // don't guess pointer equality for heap refs
                    };
                    replace_with_const!(Constant::Bool(v), Type::Bool);
                }
            }

            _ => {}
        }

        changed
    }
}

// Heuristic type hint for Const nodes created here.
fn const_type_hint(kind: &Inst) -> Type {
    match kind {
        Inst::Const(Constant::Int32(_)) => Type::Int32,
        Inst::Const(Constant::F64(_))   => Type::F64,
        Inst::Const(Constant::Bool(_))  => Type::Bool,
        Inst::Const(Constant::Null)     => Type::Null,
        Inst::Const(Constant::Str(_))   => Type::Str,
        _ => Type::Top,
    }
}
