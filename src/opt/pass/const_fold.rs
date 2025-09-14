#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::mem::{discriminant, Discriminant};

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::opt::helpers::{ value_const, value_as_i32, value_as_f64 };
use crate::opt::EditQueueExt;
use crate::wir::{Constant, Inst, IntBinOp, F64BinOp, CmpKind, Type, ValueId};

pub struct ConstFold;
impl Default for ConstFold { fn default() -> Self { Self } }

impl OptimizationWIR for ConstFold {
    // Keep bucketing tight; avoid constructing variants that need extra fields (e.g., guards with `deopt`).
    fn maybe_interesting(&self, tag: Discriminant<Inst>) -> bool {
        use Inst::*;
        let v0 = ValueId(0);
        let tags = [
            discriminant(&Mov(v0)),
            discriminant(&IntBin { op: IntBinOp::Add, a: v0, b: v0 }),
            discriminant(&F64Bin { op: F64BinOp::Add, a: v0, b: v0 }),
            discriminant(&NumAdd(v0, v0)),
            discriminant(&NumSub(v0, v0)),
            discriminant(&NumMul(v0, v0)),
            discriminant(&NumDiv(v0, v0)),
            discriminant(&NumRem(v0, v0)),
            discriminant(&CmpInt { kind: CmpKind::Eq, a: v0, b: v0 }),
            discriminant(&CmpF64 { kind: CmpKind::Eq, a: v0, b: v0 }),
            discriminant(&CmpRefEq { a: v0, b: v0 }),
            discriminant(&StrLen(v0)),
            discriminant(&StrConcat { a: v0, b: v0 }),
            discriminant(&StrSlice { s: v0, start: v0, end: v0 }),
            discriminant(&StrCompare { a: v0, b: v0 }),
            discriminant(&StrContains { s: v0, sub: v0 }),
        ];
        tags.contains(&tag)
    }

    fn optimize_node(&mut self, cur: &mut InstCursor, q: &mut WirEditQueue) -> bool {
        use Inst::*;

        // Decide a single action first (purely from a cloned kind),
        // then apply once to avoid borrowing conflicts.
        enum Action {
            None,
            ReplaceKind(Inst, Option<Type>),
        }

        let mut act = Action::None;

        // Helpers (pure, no mutable borrows)
        let is_commutative_int = |op: IntBinOp| {
            matches!(op, IntBinOp::Add | IntBinOp::Mul | IntBinOp::And | IntBinOp::Or | IntBinOp::Xor)
        };

        let kind = cur.cur_kind(); // clone snapshot

        match kind {
            // ===== MOV canonicalizations =====
            // Mov(Const c) -> Const c ; Mov(Mov(x)) -> Mov(x)
            Mov(v) => {
                if let Some(c) = cur.with_func(|f| value_const(f, v)) {
                    act = Action::ReplaceKind(Const(c.clone()), Some(const_type_hint(&Const(c))));
                } else if let Some(src) = cur.with_func(|f| mov_source(f, v)) {
                    act = Action::ReplaceKind(Mov(src), None);
                }
            }

            // ===== INT rules =====
            // Put constant on RHS for commutative ops
            IntBin { op, a, b } if is_commutative_int(op) => {
                let (a_is_c, b_is_c) = cur.with_func(|f|
                    (value_as_i32(f, a).is_some(), value_as_i32(f, b).is_some()));
                if a_is_c && !b_is_c {
                    act = Action::ReplaceKind(IntBin { op, a: b, b: a }, None);
                }
            }

            // Identities/same-operand/full folds
            IntBin { op, a, b } => {
                let (ac, bc) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));

                // Same-operand simplifications (no new const values required)
                if a == b {
                    match op {
                        IntBinOp::Sub | IntBinOp::Xor =>
                            act = Action::ReplaceKind(Const(Constant::Int32(0)), Some(Type::Int32)),
                        IntBinOp::And | IntBinOp::Or =>
                            act = Action::ReplaceKind(Mov(a), None),
                        // Shifts with same SSA are not a standard identity; leave alone.
                        _ => {}
                    }
                }

                // One-constant identities
                if matches!(act, Action::None) && (ac.is_some() || bc.is_some()) {
                    match op {
                        IntBinOp::Add => {
                            if bc == Some(0)       { act = Action::ReplaceKind(Mov(a), None); }
                            else if ac == Some(0)  { act = Action::ReplaceKind(Mov(b), None); }
                        }
                        IntBinOp::Sub => {
                            if bc == Some(0)       { act = Action::ReplaceKind(Mov(a), None); }
                        }
                        IntBinOp::Mul => {
                            if let Some(y) = bc {
                                if y == 0 { act = Action::ReplaceKind(Const(Constant::Int32(0)), Some(Type::Int32)); }
                                else if y == 1 { act = Action::ReplaceKind(Mov(a), None); }
                            } else if let Some(x) = ac {
                                if x == 0 { act = Action::ReplaceKind(Const(Constant::Int32(0)), Some(Type::Int32)); }
                                else if x == 1 { act = Action::ReplaceKind(Mov(b), None); }
                            }
                        }
                        IntBinOp::DivS => {
                            // x/1 -> x   (avoid /-1 unless both consts)
                            if bc == Some(1) { act = Action::ReplaceKind(Mov(a), None); }
                        }
                        IntBinOp::RemS => {
                            // x%1 -> 0 ; x%-1 -> 0
                            if bc == Some(1) || bc == Some(-1) {
                                act = Action::ReplaceKind(Const(Constant::Int32(0)), Some(Type::Int32));
                            }
                        }
                        IntBinOp::And => {
                            if let Some(y) = bc {
                                if y == 0 { act = Action::ReplaceKind(Const(Constant::Int32(0)), Some(Type::Int32)); }
                                else if y == -1 { act = Action::ReplaceKind(Mov(a), None); }
                            } else if let Some(x) = ac {
                                if x == 0 { act = Action::ReplaceKind(Const(Constant::Int32(0)), Some(Type::Int32)); }
                                else if x == -1 { act = Action::ReplaceKind(Mov(b), None); }
                            }
                        }
                        IntBinOp::Or => {
                            if let Some(y) = bc {
                                if y == 0 { act = Action::ReplaceKind(Mov(a), None); }
                                else if y == -1 { act = Action::ReplaceKind(Const(Constant::Int32(-1)), Some(Type::Int32)); }
                            } else if let Some(x) = ac {
                                if x == 0 { act = Action::ReplaceKind(Mov(b), None); }
                                else if x == -1 { act = Action::ReplaceKind(Const(Constant::Int32(-1)), Some(Type::Int32)); }
                            }
                        }
                        IntBinOp::Xor => {
                            if bc == Some(0) { act = Action::ReplaceKind(Mov(a), None); }
                            else if ac == Some(0) { act = Action::ReplaceKind(Mov(b), None); }
                        }
                        IntBinOp::Shl | IntBinOp::ShrU | IntBinOp::Sar => {
                            if let Some(y) = bc {
                                if ((y as u32) & 31) == 0 {
                                    act = Action::ReplaceKind(Mov(a), None);
                                } else if y != ((y as u32) & 31) as i32 {
                                    // Canonicalize large/neg shift immediates to masked amount
                                    let m = ((y as u32) & 31) as i32;
                                    // Can't synthesize a new constant ValueId for `m` here,
                                    // so only handle the zero case; keep others as-is.
                                }
                            }
                        }
                    }
                }

                // Both-constant fold (wrap semantics)
                if matches!(act, Action::None) {
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
                            IntBinOp::Sar => Some(x >> ((y as u32) & 31)),
                        };
                        if let Some(v) = folded {
                            act = Action::ReplaceKind(Const(Constant::Int32(v)), Some(Type::Int32));
                        }
                    }
                }
            }

            // ===== F64 rules =====
            F64Bin { op, a, b } => {
                let (ac, bc) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b)));

                // One-const IEEE-safe identities
                if let Action::None = act {
                    match op {
                        F64BinOp::Add => {
                            if bc == Some(0.0) { act = Action::ReplaceKind(Mov(a), None); }
                            else if ac == Some(0.0) { act = Action::ReplaceKind(Mov(b), None); }
                        }
                        F64BinOp::Sub => {
                            if bc == Some(0.0) { act = Action::ReplaceKind(Mov(a), None); }
                        }
                        F64BinOp::Mul => {
                            if bc == Some(1.0) { act = Action::ReplaceKind(Mov(a), None); }
                            else if ac == Some(1.0) { act = Action::ReplaceKind(Mov(b), None); }
                            // avoid *0.0 due to NaN*0.0 = NaN
                        }
                        F64BinOp::Div => {
                            if bc == Some(1.0) { act = Action::ReplaceKind(Mov(a), None); }
                        }
                        F64BinOp::Rem => { /* both-const only */ }
                    }
                }

                // Both-const fold
                if let Action::None = act {
                    if let (Some(x), Some(y)) = (ac, bc) {
                        let v = match op {
                            F64BinOp::Add => x + y,
                            F64BinOp::Sub => x - y,
                            F64BinOp::Mul => x * y,
                            F64BinOp::Div => x / y,
                            F64BinOp::Rem => x % y,
                        };
                        act = Action::ReplaceKind(Const(Constant::F64(v)), Some(Type::F64));
                    }
                }
            }

            // ===== Generic numeric (Num*) =====
            NumAdd(a,b) => {
                let (ai, bi) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));
                let (af, bf) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b)));
                if ai == Some(0) || af == Some(0.0)      { act = Action::ReplaceKind(Mov(b), None); }
                else if bi == Some(0) || bf == Some(0.0) { act = Action::ReplaceKind(Mov(a), None); }
                else if let (Some(x), Some(y)) = (ai, bi) {
                    act = Action::ReplaceKind(Const(Constant::Int32(x.wrapping_add(y))), Some(Type::Int32));
                } else if let (Some(x), Some(y)) = (af, bf) {
                    act = Action::ReplaceKind(Const(Constant::F64(x + y)), Some(Type::F64));
                }
            }
            NumSub(a,b) => {
                let (ai, bi) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));
                let (af, bf) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b)));
                if bi == Some(0) || bf == Some(0.0) { act = Action::ReplaceKind(Mov(a), None); }
                else if let (Some(x), Some(y)) = (ai, bi) {
                    if !(y == 0) {
                        act = Action::ReplaceKind(Const(Constant::Int32(x.wrapping_sub(y))), Some(Type::Int32));
                    }
                } else if let (Some(x), Some(y)) = (af, bf) {
                    act = Action::ReplaceKind(Const(Constant::F64(x - y)), Some(Type::F64));
                }
            }
            NumMul(a,b) => {
                let (ai, bi) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));
                let (af, bf) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b)));
                if bi == Some(1) || bf == Some(1.0) { act = Action::ReplaceKind(Mov(a), None); }
                else if ai == Some(1) || af == Some(1.0) { act = Action::ReplaceKind(Mov(b), None); }
                else if let (Some(x), Some(y)) = (ai, bi) {
                    act = Action::ReplaceKind(Const(Constant::Int32(x.wrapping_mul(y))), Some(Type::Int32));
                } else if let (Some(x), Some(y)) = (af, bf) {
                    act = Action::ReplaceKind(Const(Constant::F64(x * y)), Some(Type::F64));
                }
            }
            NumDiv(a,b) => {
                let (ai, bi) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));
                let (af, bf) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b)));
                if bi == Some(1) || bf == Some(1.0) { act = Action::ReplaceKind(Mov(a), None); }
                else if let (Some(x), Some(y)) = (ai, bi) {
                    if !(y == 0 || (x == i32::MIN && y == -1)) {
                        act = Action::ReplaceKind(Const(Constant::Int32(x.wrapping_div(y))), Some(Type::Int32));
                    }
                } else if let (Some(x), Some(y)) = (af, bf) {
                    act = Action::ReplaceKind(Const(Constant::F64(x / y)), Some(Type::F64));
                }
            }
            NumRem(a,b) => {
                let (ai, bi) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));
                let (af, bf) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b)));
                if let (Some(x), Some(y)) = (ai, bi) {
                    if y != 0 {
                        act = Action::ReplaceKind(Const(Constant::Int32(x.wrapping_rem(y))), Some(Type::Int32));
                    }
                } else if let (Some(x), Some(y)) = (af, bf) {
                    act = Action::ReplaceKind(Const(Constant::F64(x % y)), Some(Type::F64));
                }
            }

            // ===== Comparisons =====
            CmpInt { kind, a, b } if a == b => {
                let v = match kind {
                    CmpKind::Eq => true,
                    CmpKind::Ne => false,
                    CmpKind::Lt => false,
                    CmpKind::Le => true,
                    CmpKind::Gt => false,
                    CmpKind::Ge => true,
                };
                act = Action::ReplaceKind(Const(Constant::Bool(v)), Some(Type::Bool));
            }
            CmpF64 { kind, a, b } if a == b => {
                if let Some(x) = cur.with_func(|f| value_as_f64(f, a)) {
                    let ord = !x.is_nan();
                    let v = match kind {
                        CmpKind::Eq => x == x,
                        CmpKind::Ne => x != x,
                        CmpKind::Lt => false,
                        CmpKind::Le => ord,
                        CmpKind::Gt => false,
                        CmpKind::Ge => ord,
                    };
                    act = Action::ReplaceKind(Const(Constant::Bool(v)), Some(Type::Bool));
                }
            }
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
                    act = Action::ReplaceKind(Const(Constant::Bool(r)), Some(Type::Bool));
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
                    act = Action::ReplaceKind(Const(Constant::Bool(r)), Some(Type::Bool));
                }
            }

            // ===== String ops =====
            StrLen(sv) => {
                if let Some(Constant::Str(s)) = cur.with_func(|f| value_const(f, sv)) {
                    act = Action::ReplaceKind(Const(Constant::Int32(s.len() as i32)), Some(Type::Int32));
                }
            }
            StrConcat { a, b } => {
                let (ac, bc) = cur.with_func(|f| (value_const(f, a), value_const(f, b)));
                match (ac, bc) {
                    (Some(Constant::Str(sa)), Some(Constant::Str(sb))) => {
                        let mut s = String::with_capacity(sa.len() + sb.len());
                        s.push_str(&sa); s.push_str(&sb);
                        act = Action::ReplaceKind(Const(Constant::Str(s)), Some(Type::Str));
                    }
                    (Some(Constant::Str(sa)), None) if sa.is_empty() =>
                        act = Action::ReplaceKind(Mov(b), None),
                    (None, Some(Constant::Str(sb))) if sb.is_empty() =>
                        act = Action::ReplaceKind(Mov(a), None),
                    _ => {}
                }
            }
            StrSlice { s, start, end } => {
                if let (Some(Constant::Str(src)), Some(i), Some(j)) =
                    cur.with_func(|f| (value_const(f, s), value_as_i32(f, start), value_as_i32(f, end)))
                {
                    let len = src.len() as i32;
                    if 0 <= i && i <= j && j <= len {
                        let ss = &src[(i as usize)..(j as usize)];
                        act = Action::ReplaceKind(Const(Constant::Str(ss.to_string())), Some(Type::Str));
                    }
                }
            }
            StrCompare { a, b } => {
                if let (Some(Constant::Str(sa)), Some(Constant::Str(sb))) =
                    cur.with_func(|f| (value_const(f, a), value_const(f, b)))
                {
                    act = Action::ReplaceKind(Const(Constant::Bool(sa == sb)), Some(Type::Bool));
                }
            }
            StrContains { s, sub } => {
                if let (Some(Constant::Str(hay)), Some(Constant::Str(needle))) =
                    cur.with_func(|f| (value_const(f, s), value_const(f, sub)))
                {
                    act = Action::ReplaceKind(Const(Constant::Bool(hay.contains(&needle))), Some(Type::Bool));
                }
            }

            // ===== Ref equality quick wins =====
            CmpRefEq { a, b } => {
                if a == b {
                    act = Action::ReplaceKind(Const(Constant::Bool(true)), Some(Type::Bool));
                } else if let (Some(ca), Some(cb)) = cur.with_func(|f| (value_const(f, a), value_const(f, b))) {
                    let res = match (ca, cb) {
                        (Constant::Null, Constant::Null) => Some(true),
                        (Constant::Null, _) | (_, Constant::Null) => Some(false),
                        _ => None, // don’t guess heap pointer equality
                    };
                    if let Some(v) = res {
                        act = Action::ReplaceKind(Const(Constant::Bool(v)), Some(Type::Bool));
                    }
                }
            }

            // Guards (won’t be woken by bucketing; pattern kept with `..` for IR compat)
            GuardIsInt { val, .. } => {
                if let Some(Constant::Int32(i)) = cur.with_func(|f| value_const(f, val)) {
                    act = Action::ReplaceKind(Const(Constant::Int32(i)), Some(Type::Int32));
                }
            }
            GuardIsF64 { val, .. } => {
                if let Some(Constant::F64(x)) = cur.with_func(|f| value_const(f, val)) {
                    act = Action::ReplaceKind(Const(Constant::F64(x)), Some(Type::F64));
                }
            }
            GuardNotNull { val, .. } => {
                if let Some(c) = cur.with_func(|f| value_const(f, val)) {
                    if !matches!(c, Constant::Null) {
                        act = Action::ReplaceKind(Mov(val), None);
                    }
                }
            }

            _ => {}
        }

        match act {
            Action::None => false,
            Action::ReplaceKind(newk, ty_hint) => {
                q.replace_cur_kind(cur, newk);
                if let Some(ty) = ty_hint {
                    cur.with_cur(|n| n.ty = Some(ty));
                }
                true
            }
        }
    }
}

/* ---------------- helpers ---------------- */

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

// Mov(Mov(x)) ⇒ return inner source ValueId (if any)
fn mov_source(f: &crate::wir::Function, v: ValueId) -> Option<ValueId> {
    use crate::wir::ValueDef;
    if let ValueDef::InstResult(iid, _) = f.values[v.0 as usize].def {
        if let Inst::Mov(src) = f.nodes[iid.0 as usize].kind {
            return Some(src);
        }
    }
    None
}
