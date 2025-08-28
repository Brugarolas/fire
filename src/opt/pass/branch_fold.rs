use std::mem;
use crate::opt::{OptimizationWIR, WirEditQueue};
use crate::opt::helpers::{value_is_const_bool, value_as_i32, value_as_f64};
use crate::wir::{Function, Inst, CmpKind, ValueId, Constant};

#[derive(Default)]
pub struct BranchFold { ran: bool }

impl BranchFold {
    fn run_once(&mut self, func: &mut Function) {
        if mem::take(&mut self.ran) { return; }
        let mut q = WirEditQueue::new();
        for (bb_ix, bb) in func.blocks.iter().enumerate() {
            for (i, &nid) in bb.insts.iter().enumerate() {
                let node = &func.nodes[nid.0 as usize];
                match &node.kind {
                    Inst::Branch { cond, then_b, else_b } => {
                        if value_is_const_bool(func, *cond, true) {
                            q.replace_kind(nid, Inst::Jump(*then_b, vec![]));
                        } else if value_is_const_bool(func, *cond, false) {
                            q.replace_kind(nid, Inst::Jump(*else_b, vec![]));
                        }
                    }
                    Inst::CmpInt { kind, a, b } => {
                        if let (Some(x), Some(y)) = (value_as_i32(func, *a), value_as_i32(func, *b)) {
                            let res = match kind {
                                CmpKind::Eq => x == y,
                                CmpKind::Ne => x != y,
                                CmpKind::Lt => x < y,
                                CmpKind::Le => x <= y,
                                CmpKind::Gt => x > y,
                                CmpKind::Ge => x >= y,
                            };
                            q.replace_kind(nid, Inst::Const(Constant::Bool(res)));
                        }
                    }
                    Inst::CmpF64 { kind, a, b } => {
                        if let (Some(x), Some(y)) = (value_as_f64(func, *a), value_as_f64(func, *b)) {
                            let res = match kind {
                                CmpKind::Eq => x == y,
                                CmpKind::Ne => x != y,
                                CmpKind::Lt => x < y,
                                CmpKind::Le => x <= y,
                                CmpKind::Gt => x > y,
                                CmpKind::Ge => x >= y,
                            };
                            q.replace_kind(nid, Inst::Const(Constant::Bool(res)));
                        }
                    }
                    _ => {}
                }
            }
        }
        q.apply(func);
    }
}

impl OptimizationWIR for BranchFold {
    fn optimize_node(&mut self, cur: &mut crate::opt::InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| self.run_once(f));
        false
    }
}

/// Canonicalize commutative binary operands order (by ValueId) for CSE.
#[inline]
pub fn canonical_pair(a: ValueId, b: ValueId) -> (ValueId, ValueId) {
    if a <= b { (a, b) } else { (b, a) }
}
