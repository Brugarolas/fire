use std::mem;
use crate::opt::{OptimizationWIR, WirEditQueue};
use crate::opt::helpers::{value_is_const_bool, value_as_i32, value_as_f64};
use crate::wir::{Function, Inst, CmpKind, ValueId, Constant};

#[derive(Default)]
pub struct BranchFold { ran: bool }

impl BranchFold {
    pub fn new() -> Self { Self::default() }

    fn run(&mut self, func: &mut Function) {
        if self.ran { return; }
        self.ran = true;

        // Iterate to a fixed point so cascaded folds kick in.
        loop {
            let mut changed = false;
            let mut q = WirEditQueue::new();

            // --- helpers (pure, read-only over func) -----------------------
            fn flip(kind: CmpKind) -> CmpKind {
                use CmpKind::*;
                match kind { Lt => Gt, Le => Ge, Gt => Lt, Ge => Le, Eq => Eq, Ne => Ne }
            }

            fn eval_i32(kind: CmpKind, x: i32, y: i32) -> bool {
                use CmpKind::*;
                match kind {
                    Eq => x == y, Ne => x != y, Lt => x <  y,
                    Le => x <= y, Gt => x >  y, Ge => x >= y,
                }
            }
            fn eval_f64(kind: CmpKind, x: f64, y: f64) -> bool {
                use CmpKind::*;
                match kind {
                    Eq => x == y, Ne => x != y, Lt => x <  y,
                    Le => x <= y, Gt => x >  y, Ge => x >= y,
                }
            }

            // Follow trivial Mov chains once/few times to reveal a const.
            fn peel_mov(func: &Function, mut v: ValueId) -> ValueId {
                for _ in 0..4 {
                    let def = &func.values[v.0 as usize].def;
                    if let crate::wir::ValueDef::InstResult(iid, _idx) = def {
                        if let Inst::Mov(src) = func.nodes[iid.0 as usize].kind {
                            v = src;
                            continue;
                        }
                    }
                    break;
                }
                v
            }

            fn const_bool(func: &Function, v: ValueId) -> Option<bool> {
                let v = peel_mov(func, v);
                // Fast path via value table (literal constants)
                if value_is_const_bool(func, v, true) { return Some(true); }
                if value_is_const_bool(func, v, false) { return Some(false); }

                // Also recognize Const(Bool) producers
                if let crate::wir::ValueDef::InstResult(iid, _)
                    = &func.values[v.0 as usize].def
                {
                    if let Inst::Const(Constant::Bool(b)) = func.nodes[iid.0 as usize].kind {
                        return Some(b);
                    }
                }
                None
            }

            // --- main scan --------------------------------------------------
            for bb in &func.blocks {
                for &nid in &bb.insts {
                    let node = &func.nodes[nid.0 as usize];
                    match node.kind {
                        // ---------- Branch folding ----------
                        Inst::Branch { cond, then_b, else_b } => {
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

                            // Peephole: if cond is a Cmp with constant operands, fold branch now.
                            if let crate::wir::ValueDef::InstResult(cid, _)
                                = &func.values[cond.0 as usize].def
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
                                            // let the CmpInt arm below also fold the cmp itself.
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
                                    _ => {}
                                }
                            }
                        }

                        // ---------- Switch folding ----------
                        Inst::Switch { tag, default_b, ref table } => {
                            if let Some(tag_i32) = value_as_i32(func, tag) {
                                let tag64 = tag_i32 as i64;
                                let mut dest = default_b;
                                for &(key, b) in table {
                                    if key == tag64 { dest = b; break; }
                                }
                                q.replace_kind(nid, Inst::Jump(dest, vec![]));
                                changed = true;
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
                                        q.replace_kind(nid, Inst::CmpInt { kind: flip(kind), a: b, b: a });
                                        changed = true;
                                        continue;
                                    }
                                }
                            }

                            // Constant fold when both sides are constants.
                            if let (Some(x), Some(y)) = (value_as_i32(func, a), value_as_i32(func, b)) {
                                let res = eval_i32(kind, x, y);
                                q.replace_kind(nid, Inst::Const(Constant::Bool(res)));
                                changed = true;
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
                                        q.replace_kind(nid, Inst::CmpF64 { kind: flip(kind), a: b, b: a });
                                        changed = true;
                                        continue;
                                    }
                                }
                            }

                            // Constant fold when both sides are constants.
                            if let (Some(x), Some(y)) = (value_as_f64(func, a), value_as_f64(func, b)) {
                                let res = eval_f64(kind, x, y);
                                q.replace_kind(nid, Inst::Const(Constant::Bool(res)));
                                changed = true;
                            }
                        }

                        // ---------- Tiny cleanups that help subsequent passes ----------
                        Inst::Mov(src) => {
                            // Mov(Const K) => Const K (any constant)
                            if let crate::wir::ValueDef::InstResult(iid, _)
                                = &func.values[src.0 as usize].def
                            {
                                if let Inst::Const(ref k) = func.nodes[iid.0 as usize].kind {
                                    q.replace_kind(nid, Inst::Const(k.clone()));
                                    changed = true;
                                }
                            }
                        }

                        // (Optionally: CmpRefEq canonicalization)
                        Inst::CmpRefEq { a, b } => {
                            let (aa, bb) = canonical_pair(a, b);
                            if aa != a || bb != b {
                                q.replace_kind(nid, Inst::CmpRefEq { a: aa, b: bb });
                                changed = true;
                            }
                            // Fold trivially equal SSA values (same producer) => true.
                            if a == b {
                                q.replace_kind(nid, Inst::Const(Constant::Bool(true)));
                                changed = true;
                            }
                        }

                        _ => {}
                    }
                }
            }

            if !changed { break; }
            q.apply(func);
        }
    }
}

impl OptimizationWIR for BranchFold {
    fn optimize_node(&mut self, cur: &mut crate::opt::InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| self.run(f));
        // This is a function-level fixed-point pass; per-node "changed" isn't meaningful here.
        false
    }
}

/// Canonicalize commutative binary operands order (by ValueId) for CSE.
#[inline]
pub fn canonical_pair(a: ValueId, b: ValueId) -> (ValueId, ValueId) {
    if a <= b { (a, b) } else { (b, a) }
}
