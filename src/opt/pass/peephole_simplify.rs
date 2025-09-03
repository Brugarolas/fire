#![allow(dead_code)]

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::wir::{
    Constant, Function, Inst, IntBinOp, ValueDef, ValueId, Type, CmpKind, F64BinOp,
};
use crate::opt::helpers::{
    all_same, value_is_const_i32, value_is_const_str, value_as_i32, value_as_f64,
};

pub struct PeepholeSimplify;

impl OptimizationWIR for PeepholeSimplify {
    fn optimize_node(&mut self, cur: &mut InstCursor, _q: &mut WirEditQueue) -> bool {
        use Inst::*;

        let mut changed = false;

        // Small helpers (local, pure)
        #[inline]
        fn canonical_pair(a: ValueId, b: ValueId) -> (ValueId, ValueId) {
            if a <= b { (a, b) } else { (b, a) }
        }

        #[inline]
        fn flip_cmp(k: CmpKind) -> CmpKind {
            use CmpKind::*;
            match k { Lt => Gt, Le => Ge, Gt => Lt, Ge => Le, Eq => Eq, Ne => Ne }
        }

        match cur.cur_kind() {
            // ---------- Integer algebra & folding ----------
            IntBin { op, a, b } => {
                use IntBinOp::*;

                // Constants (if any)
                let (ka, kb) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));
                let (is0a, is0b, is1a, is1b, isneg1a, isneg1b) = (
                    ka == Some(0), kb == Some(0),
                    ka == Some(1), kb == Some(1),
                    ka == Some(-1), kb == Some(-1)
                );
                let same = a == b;

                // Canonicalize commutative ops: order by ValueId and put constant on RHS
                match op {
                    IntBinOp::Add | IntBinOp::Mul | IntBinOp::And | IntBinOp::Or | IntBinOp::Xor => {
                        let swap_for_const_rhs = ka.is_some() && kb.is_none();
                        let (aa, bb) = if swap_for_const_rhs {
                            (b, a)
                        } else {
                            canonical_pair(a, b)
                        };
                        if aa != a || bb != b {
                            cur.with_cur(|n| n.kind = IntBin { op, a: aa, b: bb });
                            changed = true;
                            return changed;
                        }
                    }
                    _ => {}
                }

                // Idempotence / neutral element / annihilators
                match op {
                    IntBinOp::Add => {
                        if is0a { cur.with_cur(|n| n.kind = Mov(b)); changed = true; }
                        else if is0b { cur.with_cur(|n| n.kind = Mov(a)); changed = true; }
                    }
                    IntBinOp::Sub => {
                        if is0b { cur.with_cur(|n| n.kind = Mov(a)); changed = true; }
                        else if same {
                            cur.with_cur(|n| { n.kind = Const(Constant::Int32(0)); n.ty = Some(Type::Int32); });
                            changed = true;
                        }
                    }
                    IntBinOp::Mul => {
                        if is1a { cur.with_cur(|n| n.kind = Mov(b)); changed = true; }
                        else if is1b { cur.with_cur(|n| n.kind = Mov(a)); changed = true; }
                        else if is0a || is0b {
                            cur.with_cur(|n| { n.kind = Const(Constant::Int32(0)); n.ty = Some(Type::Int32); });
                            changed = true;
                        }
                    }
                    IntBinOp::DivS => {
                        if is1b { cur.with_cur(|n| n.kind = Mov(a)); changed = true; }
                        // No rewrite for / -1 (overflow corner on INT_MIN), keep semantics exact.
                    }
                    IntBinOp::RemS => {
                        if is1b || isneg1b {
                            cur.with_cur(|n| { n.kind = Const(Constant::Int32(0)); n.ty = Some(Type::Int32); });
                            changed = true;
                        }
                    }
                    IntBinOp::And => {
                        if is0a || is0b {
                            cur.with_cur(|n| { n.kind = Const(Constant::Int32(0)); n.ty = Some(Type::Int32); });
                            changed = true;
                        } else if isneg1a { cur.with_cur(|n| n.kind = Mov(b)); changed = true; }
                        else if isneg1b { cur.with_cur(|n| n.kind = Mov(a)); changed = true; }
                        else if same { cur.with_cur(|n| n.kind = Mov(a)); changed = true; }
                    }
                    IntBinOp::Or => {
                        if is0a { cur.with_cur(|n| n.kind = Mov(b)); changed = true; }
                        else if is0b { cur.with_cur(|n| n.kind = Mov(a)); changed = true; }
                        else if isneg1a || isneg1b {
                            cur.with_cur(|n| { n.kind = Const(Constant::Int32(-1)); n.ty = Some(Type::Int32); });
                            changed = true;
                        } else if same { cur.with_cur(|n| n.kind = Mov(a)); changed = true; }
                    }
                    IntBinOp::Xor => {
                        if is0a { cur.with_cur(|n| n.kind = Mov(b)); changed = true; }
                        else if is0b { cur.with_cur(|n| n.kind = Mov(a)); changed = true; }
                        else if same {
                            cur.with_cur(|n| { n.kind = Const(Constant::Int32(0)); n.ty = Some(Type::Int32); });
                            changed = true;
                        }
                    }
                    IntBinOp::Shl | IntBinOp::ShrU | IntBinOp::Sar => {
                        let is0shift = kb == Some(0);
                        if is0shift { cur.with_cur(|n| n.kind = Mov(a)); changed = true; }
                    }
                }

                if changed { return true; }

                // Constant folding for IntBin when both sides are constants (safe cases)
                if let (Some(x), Some(y)) = (ka, kb) {
                    let folded = match op {
                        IntBinOp::Add => Some(x.wrapping_add(y)),
                        IntBinOp::Sub => Some(x.wrapping_sub(y)),
                        IntBinOp::Mul => Some(x.wrapping_mul(y)),
                        IntBinOp::DivS => if y != 0 { Some(x.wrapping_div(y)) } else { None },
                        IntBinOp::RemS => if y != 0 { Some(x.wrapping_rem(y)) } else { None },
                        IntBinOp::And => Some(x & y),
                        IntBinOp::Or  => Some(x | y),
                        IntBinOp::Xor => Some(x ^ y),
                        IntBinOp::Shl => {
                            if (0..32).contains(&(y as i64)) { Some(x.wrapping_shl(y as u32)) } else { None }
                        }
                        IntBinOp::ShrU => {
                            if (0..32).contains(&(y as i64)) { Some(((x as u32) >> (y as u32)) as i32) } else { None }
                        }
                        IntBinOp::Sar => {
                            if (0..32).contains(&(y as i64)) { Some(x.wrapping_shr(y as u32)) } else { None }
                        }
                    };
                    if let Some(v) = folded {
                        cur.with_cur(|n| { n.kind = Const(Constant::Int32(v)); n.ty = Some(Type::Int32); });
                        return true;
                    }
                }
            }

            // ---------- Float algebra & folding (safe identities) ----------
            F64Bin { op, a, b } => {
                use F64BinOp::*;

                let (ka, kb) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b)));
                // Canonicalize commutative ops and prefer constant on RHS.
                match op {
                    F64BinOp::Add | F64BinOp::Mul => {
                        let swap_for_const_rhs = ka.is_some() && kb.is_none();
                        let (aa, bb) = if swap_for_const_rhs {
                            (b, a)
                        } else {
                            canonical_pair(a, b)
                        };
                        if aa != a || bb != b {
                            cur.with_cur(|n| n.kind = F64Bin { op, a: aa, b: bb });
                            return true;
                        }
                    }
                    _ => {}
                }

                match op {
                    F64BinOp::Add => {
                        let zero_b = kb == Some(0.0);
                        let zero_a = ka == Some(0.0);
                        if zero_b { cur.with_cur(|n| n.kind = Mov(a)); return true; }
                        if zero_a { cur.with_cur(|n| n.kind = Mov(b)); return true; }
                    }
                    F64BinOp::Sub => {
                        let zero_b = kb == Some(0.0);
                        if zero_b { cur.with_cur(|n| n.kind = Mov(a)); return true; }
                    }
                    F64BinOp::Mul => {
                        let one_b = kb == Some(1.0);
                        let one_a = ka == Some(1.0);
                        if one_b { cur.with_cur(|n| n.kind = Mov(a)); return true; }
                        if one_a { cur.with_cur(|n| n.kind = Mov(b)); return true; }
                    }
                    F64BinOp::Div => {
                        let one_b = kb == Some(1.0);
                        if one_b { cur.with_cur(|n| n.kind = Mov(a)); return true; }
                    }
                    F64BinOp::Rem => {}
                }

                // Constant fold if both constants (IEEE-754 semantics via Rust)
                if let (Some(x), Some(y)) = (ka, kb) {
                    let v = match op {
                        F64BinOp::Add => x + y,
                        F64BinOp::Sub => x - y,
                        F64BinOp::Mul => x * y,
                        F64BinOp::Div => x / y,
                        F64BinOp::Rem => x % y,
                    };
                    cur.with_cur(|n| { n.kind = Const(Constant::F64(v)); n.ty = Some(Type::F64); });
                    return true;
                }
            }

            // ---------- Integer comparisons ----------
            CmpInt { kind, a, b } => {
                if a == b {
                    let val = match kind {
                        CmpKind::Eq | CmpKind::Le | CmpKind::Ge => true,
                        CmpKind::Ne | CmpKind::Lt | CmpKind::Gt => false,
                    };
                    cur.with_cur(|n| { n.kind = Const(Constant::Bool(val)); n.ty = Some(Type::Bool); });
                    return true;
                }

                // Canonicalize operands (helps CSE/GVN)
                match kind {
                    CmpKind::Eq | CmpKind::Ne => {
                        let (aa, bb) = canonical_pair(a, b);
                        if aa != a || bb != b {
                            cur.with_cur(|n| n.kind = CmpInt { kind, a: aa, b: bb });
                            return true;
                        }
                    }
                    _ => {
                        if b < a {
                            cur.with_cur(|n| n.kind = CmpInt { kind: flip_cmp(kind), a: b, b: a });
                            return true;
                        }
                    }
                }

                // Constant fold if both sides constant
                let (ka, kb) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));
                if let (Some(x), Some(y)) = (ka, kb) {
                    use CmpKind::*;
                    let res = match kind {
                        Eq => x == y, Ne => x != y, Lt => x < y,
                        Le => x <= y, Gt => x > y, Ge => x >= y,
                    };
                    cur.with_cur(|n| { n.kind = Const(Constant::Bool(res)); n.ty = Some(Type::Bool); });
                    return true;
                }
            }

            // ---------- Float comparisons ----------
            Inst::CmpF64 { kind, a, b } => {
                // Canonicalize
                match kind {
                    CmpKind::Eq | CmpKind::Ne => {
                        let (aa, bb) = canonical_pair(a, b);
                        if aa != a || bb != b {
                            cur.with_cur(|n| n.kind = Inst::CmpF64 { kind, a: aa, b: bb });
                            return true;
                        }
                    }
                    _ => {
                        if b < a {
                            cur.with_cur(|n| n.kind = Inst::CmpF64 { kind: flip_cmp(kind), a: b, b: a });
                            return true;
                        }
                    }
                }

                // Constant fold (IEEE NaN behavior preserved by Rust ops)
                let (ka, kb) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b)));
                if let (Some(x), Some(y)) = (ka, kb) {
                    use CmpKind::*;
                    let res = match kind {
                        Eq => x == y, Ne => x != y, Lt => x < y,
                        Le => x <= y, Gt => x > y, Ge => x >= y,
                    };
                    cur.with_cur(|n| { n.kind = Const(Constant::Bool(res)); n.ty = Some(Type::Bool); });
                    return true;
                }
            }

            // ---------- Ref equality ----------
            CmpRefEq { a, b } => {
                if a == b {
                    cur.with_cur(|n| { n.kind = Const(Constant::Bool(true)); n.ty = Some(Type::Bool); });
                    return true;
                }
                let (aa, bb) = canonical_pair(a, b);
                if aa != a || bb != b {
                    cur.with_cur(|n| n.kind = CmpRefEq { a: aa, b: bb });
                    return true;
                }
            }

            // ---------- Move chain flattening ----------
            Mov(x) => {
                if let Some(y) = cur.with_func(|f| mov_source_if_mov(f, x)) {
                    cur.with_cur(|n| n.kind = Mov(y));
                    return true;
                }
                // Mov(Const K) => Const K
                if let Some(k) = cur.with_func(|f| const_of_value(f, x)) {
                    cur.with_cur(|n| { n.kind = Const(k); /* keep n.ty as-is or let later passes set */ });
                    return true;
                }
            }

            // ---------- Phi simplifications ----------
            Phi(args) => {
                if let Some(one) = all_same(&args) {
                    cur.with_cur(|n| n.kind = Mov(one));
                    return true;
                } else if args.len() == 1 {
                    cur.with_cur(|n| n.kind = Mov(args[0]));
                    return true;
                }
            }

            // ---------- Strings ----------
            StrConcat { a, b } => {
                let (empty_a, empty_b) =
                    cur.with_func(|f| (value_is_const_str(f, a, ""), value_is_const_str(f, b, "")));
                if empty_a { cur.with_cur(|n| n.kind = Mov(b)); return true; }
                if empty_b { cur.with_cur(|n| n.kind = Mov(a)); return true; }

                // Fold if both sides const strings
                if let Some((sa, sb)) = cur.with_func(|f| (const_str(f, a), const_str(f, b))).into() {
                    if let (Some(sa), Some(sb)) = (sa, sb) {
                        let mut s = sa.clone();
                        s.push_str(&sb);
                        cur.with_cur(|n| { n.kind = Const(Constant::Str(s)); n.ty = Some(Type::Str); });
                        return true;
                    }
                }
            }

            _ => {}
        }

        changed
    }
}

// ----------------------
// Local-only helpers
// ----------------------

fn mov_source_if_mov(func: &Function, v: ValueId) -> Option<ValueId> {
    if let ValueDef::InstResult(inst, _) = &func.values[v.0 as usize].def {
        if let Inst::Mov(y) = func.nodes[inst.0 as usize].kind {
            return Some(y);
        }
    }
    None
}

fn const_of_value(func: &Function, v: ValueId) -> Option<Constant> {
    match &func.values[v.0 as usize].def {
        ValueDef::Const(c) => Some(c.clone()),
        ValueDef::InstResult(iid, _) => {
            if let Inst::Const(ref c) = func.nodes[iid.0 as usize].kind { Some(c.clone()) } else { None }
        }
        _ => None,
    }
}

fn const_str(func: &Function, v: ValueId) -> Option<String> {
    match const_of_value(func, v) {
        Some(Constant::Str(s)) => Some(s),
        _ => None,
    }
}
