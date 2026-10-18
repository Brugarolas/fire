// src/opt/pass/peephole.rs
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::mem::{Discriminant, discriminant};

use crate::opt::helpers::{
    all_same, value_as_f64, value_as_i32, value_is_const_i32, value_is_const_str,
};
use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::wir::{CmpKind, Constant, F64BinOp, Function, Inst, IntBinOp, Type, ValueDef, ValueId};

pub struct PeepholeSimplify;

impl Default for PeepholeSimplify {
    fn default() -> Self {
        Self
    }
}

impl OptimizationWIR for PeepholeSimplify {
    // Keep the wake-up set tight; only tags we actually handle.
    fn maybe_interesting(&self, tag: Discriminant<Inst>) -> bool {
        use Inst::*;
        let v0 = ValueId(0);
        let tags = [
            discriminant(&Mov(v0)),
            discriminant(&IntBin {
                op: IntBinOp::Add,
                a: v0,
                b: v0,
            }),
            discriminant(&F64Bin {
                op: F64BinOp::Add,
                a: v0,
                b: v0,
            }),
            discriminant(&CmpInt {
                kind: CmpKind::Eq,
                a: v0,
                b: v0,
            }),
            discriminant(&CmpF64 {
                kind: CmpKind::Eq,
                a: v0,
                b: v0,
            }),
            discriminant(&CmpRefEq { a: v0, b: v0 }),
            discriminant(&Phi(vec![v0, v0])),
            discriminant(&StrLen(v0)),
            discriminant(&StrConcat { a: v0, b: v0 }),
            discriminant(&StrSlice {
                s: v0,
                start: v0,
                end: v0,
            }),
            discriminant(&StrCompare { a: v0, b: v0 }),
        ];
        tags.contains(&tag)
    }

    fn optimize_node(&mut self, cur: &mut InstCursor, _q: &mut WirEditQueue) -> bool {
        use Inst::*;

        // local pure helpers
        #[inline]
        fn canonical_pair(a: ValueId, b: ValueId) -> (ValueId, ValueId) {
            if a.0 <= b.0 { (a, b) } else { (b, a) }
        }
        #[inline]
        fn flip_cmp(k: CmpKind) -> CmpKind {
            use CmpKind::*;
            match k {
                Lt => Gt,
                Le => Ge,
                Gt => Lt,
                Ge => Le,
                Eq | Ne => k,
            }
        }

        let kind = cur.cur_kind(); // snapshot
        match kind {
            // ---------------- Moves ----------------
            // Mov(Mov(x)) → Mov(x) ; Mov(Const K) → Const K
            Mov(x) => {
                if let Some(src) = cur.with_func(|f| mov_source_if_mov(f, x)) {
                    cur.with_cur(|n| n.kind = Mov(src));
                    return true;
                }
                if let Some(k) = cur.with_func(|f| const_of_value(f, x)) {
                    cur.with_cur(|n| {
                        n.kind = Const(k); /* type will be tightened elsewhere */
                    });
                    return true;
                }
            }

            // ---------------- Int binops ----------------
            // `IntBin` operands may be floats or strings at runtime, so only rewrites that
            // hold for every number are applied and `+` is never reordered (string concat).
            IntBin { op, a, b } => {
                use IntBinOp::*;
                let (ai, bi) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));

                if matches!(op, Mul | And | Or | Xor) {
                    let swap_for_const_rhs = ai.is_some() && bi.is_none();
                    let (aa, bb) = if swap_for_const_rhs {
                        (b, a)
                    } else {
                        canonical_pair(a, b)
                    };
                    if aa != a || bb != b {
                        cur.with_cur(|n| n.kind = IntBin { op, a: aa, b: bb });
                        return true;
                    }
                }

                let replacement = match op {
                    Sub if bi == Some(0) => Some(Mov(a)),
                    DivS if bi == Some(1) => Some(Mov(a)),
                    Mul if bi == Some(1) => Some(Mov(a)),
                    Mul if ai == Some(1) => Some(Mov(b)),
                    And if ai == Some(0) || bi == Some(0) => Some(Const(Constant::Int32(0))),
                    Or if ai == Some(-1) || bi == Some(-1) => Some(Const(Constant::Int32(-1))),
                    Xor if a == b => Some(Const(Constant::Int32(0))),
                    _ => match (ai, bi) {
                        (Some(x), Some(y)) => crate::opt::helpers::fold_js_int_bin(op, x, y)
                            .map(|v| Const(Constant::Int32(v))),
                        _ => None,
                    },
                };
                if let Some(kind) = replacement {
                    cur.with_cur(|n| {
                        if matches!(kind, Const(_)) {
                            n.ty = Some(Type::Int32);
                        }
                        n.kind = kind;
                    });
                    return true;
                }
            }

            // ---------------- F64 binops ----------------
            F64Bin { op, a, b } => {
                use F64BinOp::*;
                let (af, bf) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b)));

                // Canonicalize commutatives; const RHS preference
                match op {
                    Add | Mul => {
                        let swap_for_const_rhs = af.is_some() && bf.is_none();
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

                // Safe identities
                match op {
                    Add => {
                        if bf == Some(0.0) {
                            cur.with_cur(|n| n.kind = Mov(a));
                            return true;
                        }
                        if af == Some(0.0) {
                            cur.with_cur(|n| n.kind = Mov(b));
                            return true;
                        }
                    }
                    Sub => {
                        if bf == Some(0.0) {
                            cur.with_cur(|n| n.kind = Mov(a));
                            return true;
                        }
                    }
                    Mul => {
                        if bf == Some(1.0) {
                            cur.with_cur(|n| n.kind = Mov(a));
                            return true;
                        }
                        if af == Some(1.0) {
                            cur.with_cur(|n| n.kind = Mov(b));
                            return true;
                        }
                        // avoid *0.0 (NaN*0.0)
                    }
                    Div => {
                        if bf == Some(1.0) {
                            cur.with_cur(|n| n.kind = Mov(a));
                            return true;
                        }
                    }
                    Rem => {}
                }

                // Constant fold
                if let (Some(x), Some(y)) = (af, bf) {
                    let v = match op {
                        Add => x + y,
                        Sub => x - y,
                        Mul => x * y,
                        Div => x / y,
                        Rem => x % y,
                    };
                    cur.with_cur(|n| {
                        n.kind = Const(Constant::F64(v));
                        n.ty = Some(Type::F64);
                    });
                    return true;
                }
            }

            // ---------------- Integer comparisons ----------------
            CmpInt { kind, a, b } => {
                // Operands may be NaN at runtime, so only `x < x` / `x > x` are always false.
                if a == b && matches!(kind, CmpKind::Lt | CmpKind::Gt) {
                    cur.with_cur(|n| {
                        n.kind = Const(Constant::Bool(false));
                        n.ty = Some(Type::Bool);
                    });
                    return true;
                }

                // Canonicalize
                match kind {
                    CmpKind::Eq | CmpKind::Ne => {
                        let (aa, bb) = canonical_pair(a, b);
                        if aa != a || bb != b {
                            cur.with_cur(|n| n.kind = CmpInt { kind, a: aa, b: bb });
                            return true;
                        }
                    }
                    _ => {
                        if b.0 < a.0 {
                            cur.with_cur(|n| {
                                n.kind = CmpInt {
                                    kind: flip_cmp(kind),
                                    a: b,
                                    b: a,
                                }
                            });
                            return true;
                        }
                    }
                }

                // Both-const fold
                let (ai, bi) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));
                if let (Some(x), Some(y)) = (ai, bi) {
                    use CmpKind::*;
                    let res = match kind {
                        Eq => x == y,
                        Ne => x != y,
                        Lt => x < y,
                        Le => x <= y,
                        Gt => x > y,
                        Ge => x >= y,
                    };
                    cur.with_cur(|n| {
                        n.kind = Const(Constant::Bool(res));
                        n.ty = Some(Type::Bool);
                    });
                    return true;
                }
            }

            // ---------------- Float comparisons ----------------
            CmpF64 { kind, a, b } => {
                // Canonicalize
                match kind {
                    CmpKind::Eq | CmpKind::Ne => {
                        let (aa, bb) = canonical_pair(a, b);
                        if aa != a || bb != b {
                            cur.with_cur(|n| n.kind = CmpF64 { kind, a: aa, b: bb });
                            return true;
                        }
                    }
                    _ => {
                        if b.0 < a.0 {
                            cur.with_cur(|n| {
                                n.kind = CmpF64 {
                                    kind: flip_cmp(kind),
                                    a: b,
                                    b: a,
                                }
                            });
                            return true;
                        }
                    }
                }

                // Both-const fold (Rust f64 ops preserve IEEE semantics)
                let (af, bf) = cur.with_func(|f| (value_as_f64(f, a), value_as_f64(f, b)));
                if let (Some(x), Some(y)) = (af, bf) {
                    use CmpKind::*;
                    let res = match kind {
                        Eq => x == y,
                        Ne => x != y,
                        Lt => x < y,
                        Le => x <= y,
                        Gt => x > y,
                        Ge => x >= y,
                    };
                    cur.with_cur(|n| {
                        n.kind = Const(Constant::Bool(res));
                        n.ty = Some(Type::Bool);
                    });
                    return true;
                }
            }

            // ---------------- Ref equality ----------------
            CmpRefEq { a, b } => {
                if a == b {
                    cur.with_cur(|n| {
                        n.kind = Const(Constant::Bool(true));
                        n.ty = Some(Type::Bool);
                    });
                    return true;
                }
                // Canonicalize arg order for Eq/Ne-like symmetry
                let (aa, bb) = canonical_pair(a, b);
                if aa != a || bb != b {
                    cur.with_cur(|n| n.kind = CmpRefEq { a: aa, b: bb });
                    return true;
                }
                // Cheap constant cases: null vs null / null vs non-null const
                if let (Some(ca), Some(cb)) =
                    cur.with_func(|f| (const_of_value(f, a), const_of_value(f, b)))
                {
                    let res = match (ca, cb) {
                        (Constant::Null, Constant::Null) => Some(true),
                        (Constant::Null, _) | (_, Constant::Null) => Some(false),
                        _ => None,
                    };
                    if let Some(v) = res {
                        cur.with_cur(|n| {
                            n.kind = Const(Constant::Bool(v));
                            n.ty = Some(Type::Bool);
                        });
                        return true;
                    }
                }
            }

            // ---------------- Phi ----------------
            Phi(args) => {
                if let Some(one) = all_same(&args) {
                    cur.with_cur(|n| n.kind = Mov(one));
                    return true;
                }
                if args.len() == 1 {
                    cur.with_cur(|n| n.kind = Mov(args[0]));
                    return true;
                }
            }

            // ---------------- Strings ----------------
            StrLen(sv) => {
                if let Some(Constant::Str(s)) = cur.with_func(|f| const_of_value(f, sv)) {
                    cur.with_cur(|n| {
                        n.kind = Const(Constant::Int32(s.len() as i32));
                        n.ty = Some(Type::Int32);
                    });
                    return true;
                }
            }
            StrConcat { a, b } => {
                let (empty_a, empty_b) =
                    cur.with_func(|f| (value_is_const_str(f, a, ""), value_is_const_str(f, b, "")));
                if empty_a {
                    cur.with_cur(|n| n.kind = Mov(b));
                    return true;
                }
                if empty_b {
                    cur.with_cur(|n| n.kind = Mov(a));
                    return true;
                }

                let (sa, sb) = cur.with_func(|f| (const_str(f, a), const_str(f, b)));
                if let (Some(sa), Some(sb)) = (sa, sb) {
                    let mut s = String::with_capacity(sa.len() + sb.len());
                    s.push_str(&sa);
                    s.push_str(&sb);
                    cur.with_cur(|n| {
                        n.kind = Const(Constant::Str(s));
                        n.ty = Some(Type::Str);
                    });
                    return true;
                }
            }
            StrSlice { s, start, end } => {
                if let (Some(Constant::Str(src)), Some(i), Some(j)) = cur.with_func(|f| {
                    (
                        const_of_value(f, s),
                        value_as_i32(f, start),
                        value_as_i32(f, end),
                    )
                }) {
                    let len = src.len() as i32;
                    if 0 <= i && i <= j && j <= len {
                        let ss = &src[(i as usize)..(j as usize)];
                        cur.with_cur(|n| {
                            n.kind = Const(Constant::Str(ss.to_string()));
                            n.ty = Some(Type::Str);
                        });
                        return true;
                    }
                }
            }
            StrCompare { a, b } => {
                let (sa, sb) = cur.with_func(|f| (const_str(f, a), const_str(f, b)));
                if let (Some(sa), Some(sb)) = (sa, sb) {
                    cur.with_cur(|n| {
                        n.kind = Const(Constant::Bool(sa == sb));
                        n.ty = Some(Type::Bool);
                    });
                    return true;
                }
            }

            _ => {}
        }

        false
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
            if let Inst::Const(ref c) = func.nodes[iid.0 as usize].kind {
                Some(c.clone())
            } else {
                None
            }
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
