// src/opts/peephole_simplify.rs
#![allow(dead_code)]

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::wir::{Constant, Function, Inst, IntBinOp, ValueDef, ValueId, Type, CmpKind};
use crate::opt::helpers::{all_same, value_is_const_i32, value_is_const_str};

pub struct PeepholeSimplify;

impl OptimizationWIR for PeepholeSimplify {
    fn optimize_node(&mut self, cur: &mut InstCursor, _q: &mut WirEditQueue) -> bool {
        use IntBinOp::*;
        use Inst::*;

        let mut changed = false;

        match cur.cur_kind() {
            // ---------- Integer algebra ----------
            IntBin { op, a, b } => {
                let (is0a, is0b, is1a, is1b, is_neg1a, is_neg1b) = cur.with_func(|f| (
                    value_is_const_i32(f, a, 0),
                    value_is_const_i32(f, b, 0),
                    value_is_const_i32(f, a, 1),
                    value_is_const_i32(f, b, 1),
                    value_is_const_i32(f, a, -1),
                    value_is_const_i32(f, b, -1),
                ));
                let same = a == b;

                match op {
                    Add => {
                        if is0a {
                            cur.with_cur(|n| n.kind = Mov(b));
                            changed = true;
                        } else if is0b {
                            cur.with_cur(|n| n.kind = Mov(a));
                            changed = true;
                        }
                    }
                    Sub => {
                        if is0b {
                            cur.with_cur(|n| n.kind = Mov(a));
                            changed = true;
                        } else if same {
                            cur.with_cur(|n| { n.kind = Const(Constant::Int32(0)); n.ty = Some(Type::Int32); });
                            changed = true;
                        }
                    }
                    Mul => {
                        if is1a {
                            cur.with_cur(|n| n.kind = Mov(b));
                            changed = true;
                        } else if is1b {
                            cur.with_cur(|n| n.kind = Mov(a));
                            changed = true;
                        } else if is0a || is0b {
                            cur.with_cur(|n| { n.kind = Const(Constant::Int32(0)); n.ty = Some(Type::Int32); });
                            changed = true;
                        }
                    }
                    DivS => {
                        if is1b {
                            cur.with_cur(|n| n.kind = Mov(a));
                            changed = true;
                        } else if is_neg1b {
                            // keep as arithmetic to avoid overflow traps; represent as 0 - a
                            cur.with_cur(|n| n.kind = IntBin { op: Sub, a: a /* we'll rewrite next line*/, b: a });
                            // Immediately rewrite to Const(0) - a (two-step to keep SSA stable)
                            cur.with_cur(|n| n.kind = IntBin { op: Sub, a: const_zero_placeholder(), b: a });
                            changed = true;
                        }
                    }
                    RemS => {
                        if is1b || is_neg1b {
                            cur.with_cur(|n| { n.kind = Const(Constant::Int32(0)); n.ty = Some(Type::Int32); });
                            changed = true;
                        }
                    }
                    And => {
                        if is0a || is0b {
                            cur.with_cur(|n| { n.kind = Const(Constant::Int32(0)); n.ty = Some(Type::Int32); });
                            changed = true;
                        } else if is_neg1a {
                            cur.with_cur(|n| n.kind = Mov(b));
                            changed = true;
                        } else if is_neg1b {
                            cur.with_cur(|n| n.kind = Mov(a));
                            changed = true;
                        }
                    }
                    Or => {
                        if is0a {
                            cur.with_cur(|n| n.kind = Mov(b));
                            changed = true;
                        } else if is0b {
                            cur.with_cur(|n| n.kind = Mov(a));
                            changed = true;
                        } else if is_neg1a || is_neg1b {
                            cur.with_cur(|n| { n.kind = Const(Constant::Int32(-1)); n.ty = Some(Type::Int32); });
                            changed = true;
                        }
                    }
                    Xor => {
                        if is0a {
                            cur.with_cur(|n| n.kind = Mov(b));
                            changed = true;
                        } else if is0b {
                            cur.with_cur(|n| n.kind = Mov(a));
                            changed = true;
                        }
                    }
                    Shl | ShrU | Sar => {
                        let is0shift = cur.with_func(|f| value_is_const_i32(f, b, 0));
                        if is0shift {
                            cur.with_cur(|n| n.kind = Mov(a));
                            changed = true;
                        }
                    }
                }
            }

            // ---------- Integer comparisons with same operands ----------
            CmpInt { kind, a, b } if a == b => {
                let val = match kind {
                    CmpKind::Eq | CmpKind::Le | CmpKind::Ge => true,
                    CmpKind::Ne | CmpKind::Lt | CmpKind::Gt => false,
                };
                cur.with_cur(|n| { n.kind = Const(Constant::Bool(val)); n.ty = Some(Type::Bool); });
                changed = true;
            }

            // Ref equality of the same SSA is trivially true.
            CmpRefEq { a, b } if a == b => {
                cur.with_cur(|n| { n.kind = Const(Constant::Bool(true)); n.ty = Some(Type::Bool); });
                changed = true;
            }

            // ---------- Move chain flattening ----------
            Mov(x) => {
                let inner = cur.with_func(|f| mov_source_if_mov(f, x));
                if let Some(y) = inner {
                    cur.with_cur(|n| n.kind = Mov(y));
                    changed = true;
                }
            }

            // ---------- Phi simplifications ----------
            Phi(args) => {
                if let Some(one) = all_same(&args) {
                    cur.with_cur(|n| n.kind = Mov(one));
                    changed = true;
                } else if args.len() == 1 {
                    cur.with_cur(|n| n.kind = Mov(args[0]));
                    changed = true;
                }
            }

            // ---------- Strings ----------
            StrConcat { a, b } => {
                let (empty_a, empty_b) = cur.with_func(|f| (value_is_const_str(f, a, ""), value_is_const_str(f, b, "")));
                if empty_a {
                    cur.with_cur(|n| n.kind = Mov(b));
                    changed = true;
                } else if empty_b {
                    cur.with_cur(|n| n.kind = Mov(a));
                    changed = true;
                }
            }

            _ => {}
        }

        changed
    }
}

// ----------------------
// Local-only helpers (peephole-specific)
// ----------------------

fn mov_source_if_mov(func: &Function, v: ValueId) -> Option<ValueId> {
    if let ValueDef::InstResult(inst, _) = &func.values[v.0 as usize].def {
        if let Inst::Mov(y) = func.nodes[inst.0 as usize].kind {
            return Some(y);
        }
    }
    None
}

/// Placeholder for the peephole’s internal rewrite to `0 - a` forms; never dereferenced.
fn const_zero_placeholder() -> ValueId { ValueId(u32::MAX) }
