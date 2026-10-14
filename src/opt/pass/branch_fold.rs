//! Branch/compare/switch folding to flatten obvious control and reduce work
#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::opt::helpers::{value_as_f64, value_as_i32, value_is_const_bool};
use crate::opt::{OptimizationWIR, WirEditQueue};
use crate::wir::{BlockId, CmpKind, Constant, Function, Inst, ValueDef, ValueId};

#[derive(Default)]
pub struct BranchFold {
    ran: bool,
}

impl BranchFold {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn run(&mut self, func: &mut Function) {
        if self.ran {
            return;
        }
        self.ran = true;

        // Iterate to a fixed point so cascaded folds kick in.
        loop {
            let mut changed = false;
            let mut q = WirEditQueue::new();

            // --- helpers (pure, read-only over func) -----------------------
            #[inline]
            fn flip(kind: CmpKind) -> CmpKind {
                use CmpKind::*;
                match kind {
                    Lt => Gt,
                    Le => Ge,
                    Gt => Lt,
                    Ge => Le,
                    Eq => Eq,
                    Ne => Ne,
                }
            }

            #[inline]
            fn eval_i32(kind: CmpKind, x: i32, y: i32) -> bool {
                use CmpKind::*;
                match kind {
                    Eq => x == y,
                    Ne => x != y,
                    Lt => x < y,
                    Le => x <= y,
                    Gt => x > y,
                    Ge => x >= y,
                }
            }
            #[inline]
            fn eval_f64(kind: CmpKind, x: f64, y: f64) -> bool {
                use CmpKind::*;
                match kind {
                    Eq => x == y,
                    Ne => x != y,
                    Lt => x < y,
                    Le => x <= y,
                    Gt => x > y,
                    Ge => x >= y,
                }
            }

            // Follow trivial Mov chains a few hops to reveal an underlying value.
            #[inline]
            fn peel_mov(func: &Function, mut v: ValueId) -> ValueId {
                for _ in 0..4 {
                    if let ValueDef::InstResult(iid, _) = &func.values[v.0 as usize].def {
                        if let Inst::Mov(src) = func.nodes[iid.0 as usize].kind {
                            v = src;
                            continue;
                        }
                    }
                    break;
                }
                v
            }

            #[inline]
            fn const_bool(func: &Function, v: ValueId) -> Option<bool> {
                let v = peel_mov(func, v);
                if value_is_const_bool(func, v, true) {
                    return Some(true);
                }
                if value_is_const_bool(func, v, false) {
                    return Some(false);
                }
                if let ValueDef::InstResult(iid, _) = &func.values[v.0 as usize].def {
                    if let Inst::Const(Constant::Bool(b)) = func.nodes[iid.0 as usize].kind {
                        return Some(b);
                    }
                }
                None
            }

            #[inline]
            fn const_of_value(func: &Function, v: ValueId) -> Option<Constant> {
                let v = peel_mov(func, v);
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

            #[inline]
            fn const_str(func: &Function, v: ValueId) -> Option<String> {
                match const_of_value(func, v) {
                    Some(Constant::Str(s)) => Some(s),
                    _ => None,
                }
            }

            // --- main scan --------------------------------------------------
            for bb in &func.blocks {
                for &nid in &bb.insts {
                    let node = &func.nodes[nid.0 as usize];
                    match node.kind {
                        // ---------- Branch folding ----------
                        Inst::Branch {
                            cond,
                            then_b,
                            else_b,
                        } => {
                            // Trivial: both arms identical.
                            if then_b == else_b {
                                q.replace_kind(nid, Inst::Jump(then_b, vec![]));
                                changed = true;
                                continue;
                            }
                            // Constant condition (with Mov peeling).
                            if let Some(b) = const_bool(func, cond) {
                                let target = if b { then_b } else { else_b };
                                q.replace_kind(nid, Inst::Jump(target, vec![]));
                                changed = true;
                                continue;
                            }

                            // Peephole: if cond is a comparison (CmpInt/F64/StrCompare/StrContains) with
                            // constant operands, fold branch immediately.
                            if let ValueDef::InstResult(cid, _) = &func.values[cond.0 as usize].def
                            {
                                match func.nodes[cid.0 as usize].kind {
                                    Inst::CmpInt { kind, a, b } => {
                                        if let (Some(x), Some(y)) =
                                            (value_as_i32(func, a), value_as_i32(func, b))
                                        {
                                            let res = eval_i32(kind, x, y);
                                            let target = if res { then_b } else { else_b };
                                            q.replace_kind(nid, Inst::Jump(target, vec![]));
                                            changed = true;
                                        }
                                    }
                                    Inst::CmpF64 { kind, a, b } => {
                                        if let (Some(x), Some(y)) =
                                            (value_as_f64(func, a), value_as_f64(func, b))
                                        {
                                            let res = eval_f64(kind, x, y);
                                            let target = if res { then_b } else { else_b };
                                            q.replace_kind(nid, Inst::Jump(target, vec![]));
                                            changed = true;
                                        }
                                    }
                                    Inst::StrCompare { a, b } => {
                                        if let (Some(sa), Some(sb)) =
                                            (const_str(func, a), const_str(func, b))
                                        {
                                            let res = sa == sb;
                                            let target = if res { then_b } else { else_b };
                                            q.replace_kind(nid, Inst::Jump(target, vec![]));
                                            changed = true;
                                        }
                                    }
                                    Inst::StrContains { s, sub } => {
                                        if let (Some(h), Some(n)) =
                                            (const_str(func, s), const_str(func, sub))
                                        {
                                            let res = h.contains(&n);
                                            let target = if res { then_b } else { else_b };
                                            q.replace_kind(nid, Inst::Jump(target, vec![]));
                                            changed = true;
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }

                        // ---------- Switch folding / cleanup ----------
                        Inst::Switch {
                            tag,
                            default_b,
                            ref table,
                        } => {
                            // 1) Constant tag → Jump(target)
                            if let Some(tag_i32) = value_as_i32(func, tag) {
                                let tag64 = tag_i32 as i64;
                                let mut dest = default_b;
                                for &(key, b) in table {
                                    if key == tag64 {
                                        dest = b;
                                        break;
                                    }
                                }
                                q.replace_kind(nid, Inst::Jump(dest, vec![]));
                                changed = true;
                                continue;
                            }

                            // 2) Degenerate tables
                            if table.is_empty() {
                                q.replace_kind(nid, Inst::Jump(default_b, vec![]));
                                changed = true;
                                continue;
                            }
                            // 3) All arms (table + default) are the same → Jump(that)
                            let all_to = default_b;
                            let mut all_same = true;
                            for &(_, b) in table {
                                if b != default_b {
                                    all_same = false;
                                    break;
                                }
                            }
                            if all_same {
                                q.replace_kind(nid, Inst::Jump(all_to, vec![]));
                                changed = true;
                                continue;
                            }
                        }

                        // ---------- Int compare canonicalize + fold ----------
                        Inst::CmpInt { kind, a, b } => {
                            // a ? a  (always decidable for integers)
                            if a == b {
                                use CmpKind::*;
                                let res = match kind {
                                    Eq | Le | Ge => true,
                                    Ne | Lt | Gt => false,
                                };
                                q.replace_kind(nid, Inst::Const(Constant::Bool(res)));
                                changed = true;
                                continue;
                            }

                            // Canonicalize operands for CSE.
                            match kind {
                                CmpKind::Eq | CmpKind::Ne => {
                                    let (aa, bb) = canonical_pair(a, b);
                                    if aa != a || bb != b {
                                        q.replace_kind(nid, Inst::CmpInt { kind, a: aa, b: bb });
                                        changed = true;
                                        continue;
                                    }
                                }
                                _ => {
                                    // Normalize by ordering operands; flip predicate if swapped.
                                    if b < a {
                                        q.replace_kind(
                                            nid,
                                            Inst::CmpInt {
                                                kind: flip(kind),
                                                a: b,
                                                b: a,
                                            },
                                        );
                                        changed = true;
                                        continue;
                                    }
                                }
                            }

                            // Constant fold when both sides are constants.
                            if let (Some(x), Some(y)) =
                                (value_as_i32(func, a), value_as_i32(func, b))
                            {
                                let res = eval_i32(kind, x, y);
                                q.replace_kind(nid, Inst::Const(Constant::Bool(res)));
                                changed = true;
                                continue;
                            }
                        }

                        // ---------- F64 compare canonicalize + fold ----------
                        Inst::CmpF64 { kind, a, b } => {
                            // NOTE: do NOT fold a op a in general for f64 because of NaN.
                            // Canonicalize for CSE.
                            match kind {
                                CmpKind::Eq | CmpKind::Ne => {
                                    let (aa, bb) = canonical_pair(a, b);
                                    if aa != a || bb != b {
                                        q.replace_kind(nid, Inst::CmpF64 { kind, a: aa, b: bb });
                                        changed = true;
                                        continue;
                                    }
                                }
                                _ => {
                                    if b < a {
                                        q.replace_kind(
                                            nid,
                                            Inst::CmpF64 {
                                                kind: flip(kind),
                                                a: b,
                                                b: a,
                                            },
                                        );
                                        changed = true;
                                        continue;
                                    }
                                }
                            }

                            // Constant fold when both sides are constants.
                            if let (Some(x), Some(y)) =
                                (value_as_f64(func, a), value_as_f64(func, b))
                            {
                                let res = eval_f64(kind, x, y);
                                q.replace_kind(nid, Inst::Const(Constant::Bool(res)));
                                changed = true;
                                continue;
                            }
                        }

                        // ---------- Ref equality ----------
                        Inst::CmpRefEq { a, b } => {
                            // Canonicalize
                            let (aa, bb) = canonical_pair(a, b);
                            if aa != a || bb != b {
                                q.replace_kind(nid, Inst::CmpRefEq { a: aa, b: bb });
                                changed = true;
                                continue;
                            }
                            // Same SSA → true
                            if a == b {
                                q.replace_kind(nid, Inst::Const(Constant::Bool(true)));
                                changed = true;
                                continue;
                            }
                            // Null/null and null/non-null constant cases
                            match (const_of_value(func, a), const_of_value(func, b)) {
                                (Some(Constant::Null), Some(Constant::Null)) => {
                                    q.replace_kind(nid, Inst::Const(Constant::Bool(true)));
                                    changed = true;
                                }
                                (Some(Constant::Null), Some(k))
                                | (Some(k), Some(Constant::Null)) => {
                                    // For heap references, only Null vs non-Null is safe to decide
                                    if !matches!(k, Constant::Null) {
                                        q.replace_kind(nid, Inst::Const(Constant::Bool(false)));
                                        changed = true;
                                    }
                                }
                                _ => {}
                            }
                        }

                        // ---------- Tiny cleanups that help subsequent passes ----------
                        Inst::Mov(src) => {
                            // Mov(Mov(x)) => Mov(x)
                            if let ValueDef::InstResult(iid, _) = &func.values[src.0 as usize].def {
                                if let Inst::Mov(y) = func.nodes[iid.0 as usize].kind {
                                    q.replace_kind(nid, Inst::Mov(y));
                                    changed = true;
                                    continue;
                                }
                            }
                            // Mov(Const K) => Const K
                            if let ValueDef::InstResult(iid, _) = &func.values[src.0 as usize].def {
                                if let Inst::Const(ref k) = func.nodes[iid.0 as usize].kind {
                                    q.replace_kind(nid, Inst::Const(k.clone()));
                                    changed = true;
                                    continue;
                                }
                            }
                        }

                        _ => {}
                    }
                }
            }

            if !changed {
                break;
            }
            q.apply(func);
        }
    }
}

impl OptimizationWIR for BranchFold {
    fn optimize_node(&mut self, cur: &mut crate::opt::InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| self.run(f));
        // Function-level fixed-point pass; per-node flag not meaningful.
        false
    }
}

/// Canonicalize commutative binary operands order (by ValueId) for CSE.
#[inline]
pub fn canonical_pair(a: ValueId, b: ValueId) -> (ValueId, ValueId) {
    if a <= b { (a, b) } else { (b, a) }
}
