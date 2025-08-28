// src/opts/const_fold.rs
#![allow(dead_code)]

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

        match cur.cur_kind() {
            // Mov(Const c) -> Const c
            Mov(v) => {
                if let Some(c) = cur.with_func(|f| value_const(f, v)) {
                    cur.with_cur(|n| {
                        n.kind = Const(c);
                        // Set a reasonable type if obvious.
                        n.ty = Some(match n.ty.clone().unwrap_or(Type::Top) {
                            _ => const_type_hint(&n.kind),
                        });
                    });
                    changed = true;
                }
            }

            // ---------- Int constant folding ----------
            IntBin { op, a, b } => {
                if let (Some(x), Some(y)) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b))) {
                    // Avoid folding division overflow / by-zero edge cases.
                    let folded = match op {
                        IntBinOp::Add => Some(x.wrapping_add(y)),
                        IntBinOp::Sub => Some(x.wrapping_sub(y)),
                        IntBinOp::Mul => Some(x.wrapping_mul(y)),
                        IntBinOp::DivS => {
                            // signed divide by zero: skip; INT_MIN/-1 overflow: skip (could trap/UB depending on lowering)
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
                        IntBinOp::Sar => Some(x.wrapping_shr((y as u32) & 31)), // arithmetic in Rust is >> for signed
                    };

                    if let Some(v) = folded {
                        cur.with_cur(|n| { n.kind = Const(Constant::Int32(v)); n.ty = Some(Type::Int32); });
                        changed = true;
                    }
                }
            }

            // ---------- F64 constant folding ----------
            F64Bin { op, a, b } => {
                if let (Some(x), Some(y)) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b))) {
                    let folded = match op {
                        F64BinOp::Add => x + y,
                        F64BinOp::Sub => x - y,
                        F64BinOp::Mul => x * y,
                        F64BinOp::Div => x / y,
                        F64BinOp::Rem => x % y,
                    };
                    cur.with_cur(|n| { n.kind = Const(Constant::F64(folded)); n.ty = Some(Type::F64); });
                    changed = true;
                }
            }

            // ---------- Comparisons ----------
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
                    cur.with_cur(|n| { n.kind = Const(Constant::Bool(r)); n.ty = Some(Type::Bool); });
                    changed = true;
                }
            }

            CmpF64 { kind, a, b } => {
                if let (Some(x), Some(y)) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b))) {
                    // IEEE: comparisons with NaN are false except !=
                    let r = match kind {
                        CmpKind::Eq => x == y,
                        CmpKind::Ne => x != y,
                        CmpKind::Lt => x < y,
                        CmpKind::Le => x <= y,
                        CmpKind::Gt => x > y,
                        CmpKind::Ge => x >= y,
                    };
                    cur.with_cur(|n| { n.kind = Const(Constant::Bool(r)); n.ty = Some(Type::Bool); });
                    changed = true;
                }
            }

            // ---------- Strings ----------
            StrLen(sv) => {
                if let Some(Constant::Str(s)) = cur.with_func(|f| value_const(f, sv)) {
                    cur.with_cur(|n| { n.kind = Const(Constant::Int32(s.len() as i32)); n.ty = Some(Type::Int32); });
                    changed = true;
                }
            }

            StrConcat { a, b } => {
                if let (Some(Constant::Str(sa)), Some(Constant::Str(sb))) = cur.with_func(|f| (value_const(f, a), value_const(f, b))) {
                    let mut s = String::with_capacity(sa.len() + sb.len());
                    s.push_str(&sa);
                    s.push_str(&sb);
                    cur.with_cur(|n| { n.kind = Const(Constant::Str(s)); n.ty = Some(Type::Str); });
                    changed = true;
                }
            }

            StrCompare { a, b } => {
                if let (Some(Constant::Str(sa)), Some(Constant::Str(sb))) = cur.with_func(|f| (value_const(f, a), value_const(f, b))) {
                    let ord = sa.cmp(&sb);
                    // Many IRs model string compare as tri-valued; here it returns bool (per your IR it's a compare returning Bool).
                    // If this is a lexicographic compare returning Ordering you can adapt; for now we fold Eq via CmpF64-like passes elsewhere.
                    let eq = ord == std::cmp::Ordering::Equal;
                    cur.with_cur(|n| { n.kind = Const(Constant::Bool(eq)); n.ty = Some(Type::Bool); });
                    changed = true;
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
