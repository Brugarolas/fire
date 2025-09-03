// src/opts/strength_reduction.rs
#![allow(dead_code)]

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::wir::{Function, Inst, IntBinOp, ValueDef, ValueId, Constant, Type};
use crate::opt::helpers::{value_as_i32, value_is_const_i32};

pub struct StrengthReduction;

impl OptimizationWIR for StrengthReduction {
    fn optimize_node(&mut self, cur: &mut InstCursor, _q: &mut WirEditQueue) -> bool {
        use IntBinOp::*;
        use Inst::*;

        // Helpers in scope
        #[inline]
        fn is_pow2_i32(x: i32) -> Option<u32> {
            if x > 0 && (x & (x - 1)) == 0 {
                Some(x.trailing_zeros())
            } else {
                None
            }
        }

        // Reuse an *existing* const i32 ValueId if present (either literal value or Const node)
        fn find_const_i32(func: &Function, k: i32) -> Option<ValueId> {
            // First try literal constants resident in value table
            for v in &func.values {
                if let ValueDef::Const(Constant::Int32(c)) = v.def {
                    if c == k { return Some(v.id); }
                }
            }
            // Then try results of Inst::Const nodes
            for v in &func.values {
                if let ValueDef::InstResult(iid, _ix) = v.def {
                    if let Inst::Const(Constant::Int32(c)) = func.nodes[iid.0 as usize].kind {
                        if c == k { return Some(v.id); }
                    }
                }
            }
            None
        }

        // Very small “non-negative” recognizer (sound subset).
        // If this returns true, x is guaranteed ≥ 0 at runtime.
        fn is_non_negative(func: &Function, v: ValueId) -> bool {
            match &func.values[v.0 as usize].def {
                // Literal non-negative constant
                ValueDef::Const(Constant::Int32(c)) => *c >= 0,

                ValueDef::InstResult(iid, _ix) => {
                    match &func.nodes[iid.0 as usize].kind {
                        // Lengths and push/unshift results are ≥ 0 by construction
                        Inst::ArrayLen(_)
                        | Inst::ArrayPush { .. }
                        | Inst::ArrayUnshift { .. }
                        // String length is ≥ 0
                        | Inst::StrLen(_) => true,

                        // Anything else: we don't claim non-negativity.
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        // Try to rewrite on a per-node basis
        match cur.cur_kind() {
            // -----------------------
            // Integer multiply
            // -----------------------
            IntBin { op: Mul, a, b } => {
                // Put constant on RHS if only LHS is const (canonical for later rules)
                let (ka, kb) = cur.with_func(|f| (value_as_i32(f, a), value_as_i32(f, b)));
                if ka.is_some() && kb.is_none() {
                    // Swap to keep const on the right (commutative)
                    cur.with_cur(|n| n.kind = IntBin { op: Mul, a: b, b: a });
                    return true;
                }

                // Now prefer constant on RHS
                let k = kb;
                if let Some(c) = k {
                    // x * (1<<k)  -->  x << k   (mod-2^32 semantics)
                    if let Some(sh) = is_pow2_i32(c) {
                        // We need an existing ValueId for `k` (the shift amount in *bits*).
                        if let Some(k_vid) = cur.with_func(|f| find_const_i32(f, sh as i32)) {
                            cur.with_cur(|n| {
                                n.kind = IntBin { op: Shl, a, b: k_vid };
                                n.ty = Some(Type::Int32);
                            });
                            return true;
                        }
                    }
                    // No multi-instruction “shift-add” expansion here (we don’t insert nodes).
                }
            }

            // -----------------------
            // Integer division by 2^k (only when x >= 0)
            // -----------------------
            IntBin { op: DivS, a, b } => {
                if let Some(den) = cur.with_func(|f| value_as_i32(f, b)) {
                    if let Some(k) = is_pow2_i32(den) {
                        // Only safe for known non-negative dividend (trunc-to-zero == floor)
                        let nonneg = cur.with_func(|f| is_non_negative(f, a));
                        if nonneg {
                            if let Some(k_vid) = cur.with_func(|f| find_const_i32(f, k as i32)) {
                                // Use logical shift right (ShrU) to make the intent explicit.
                                cur.with_cur(|n| {
                                    n.kind = IntBin { op: ShrU, a, b: k_vid };
                                    n.ty = Some(Type::Int32);
                                });
                                return true;
                            }
                        }
                    }
                }
            }

            // -----------------------
            // Integer remainder by 2^k (only when x >= 0)
            // -----------------------
            IntBin { op: RemS, a, b } => {
                if let Some(den) = cur.with_func(|f| value_as_i32(f, b)) {
                    if let Some(k) = is_pow2_i32(den) {
                        let nonneg = cur.with_func(|f| is_non_negative(f, a));
                        if nonneg {
                            let mask = (1i32 << k) - 1;
                            if let Some(mask_vid) = cur.with_func(|f| find_const_i32(f, mask)) {
                                cur.with_cur(|n| {
                                    n.kind = IntBin { op: And, a, b: mask_vid };
                                    n.ty = Some(Type::Int32);
                                });
                                return true;
                            }
                        }
                    }
                }
            }

            // Nothing to do
            _ => {}
        }

        false
    }
}
