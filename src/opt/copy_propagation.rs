//! Copy propagation (local/linear).
//!
//! Strategy:
//!  - Collapse Mov chains: `Mov(Mov(x)) -> Mov(x)` (idempotence).
//!  - If an instruction is `Mov(s)` producing `%r`, and the *next* instruction
//!    uses `%r`, rewrite that next instruction to use `s` directly and erase the Mov.
//!
//! This is a conservative, single-window forward propagation that leverages the
//! batch edit queue to erase the Mov when it becomes dead locally.
//!
//! It’s safe because `Mov` is pure and value-only (no effects, no control).

use std::any::Any;

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::opt::helpers::replace_uses_in_inst;
use crate::wir::{Function, Inst, InstId, ValueDef, ValueId};

pub struct CopyPropagation {
    /// Maximum number of Mov links to chase when collapsing Mov(Mov(..)).
    chase_limit: usize,
}
impl CopyPropagation {
    pub fn new() -> Self {
        Self { chase_limit: 8 }
    }

    /// Follow Mov chains up to `chase_limit`, returning the first non-Mov source.
    fn chase_mov_chain(func: &Function, mut v: ValueId, limit: usize) -> ValueId {
        let mut steps = 0usize;
        loop {
            if steps >= limit { return v; }
            steps += 1;

            let def = &func.values[v.0 as usize].def;
            match def {
                ValueDef::InstResult(inst, _res_ix) => {
                    match &func.nodes[inst.0 as usize].kind {
                        Inst::Mov(src) => {
                            v = *src;
                            continue;
                        }
                        _ => return v,
                    }
                }
                _ => return v,
            }
        }
    }
}

impl OptimizationWIR for CopyPropagation {
    fn set_metadata_any(&mut self, _data: &dyn Any) { /* unused */ }

    fn optimize_node(&mut self, cur: &mut InstCursor, q: &mut WirEditQueue) -> bool {
        // Fast path: only care about Mov.
        let kind = cur.cur_kind();
        let Inst::Mov(src0) = kind else { return false; };

        // ID and result of this Mov
        let this_id = cur.cur_id();
        let mut res_v: Option<ValueId> = None;
        cur.with_cur(|n| {
            res_v = n.results.get(0).copied();
        });
        let Some(res) = res_v else { return false; };

        // 1) Collapse Mov chains: Mov(Mov(x)) -> Mov(x_final)
        let final_src = cur.with_func(|f| Self::chase_mov_chain(f, src0, self.chase_limit));
        if final_src != src0 {
            // Replace the Mov's operand in-place, keep results/effects the same.
            q.replace_kind(this_id, Inst::Mov(final_src));
            // We changed this node; let the driver re-check here.
            return true;
        }

        // 2) Single-window forward propagation:
        // If the *next* instruction uses `res`, rewrite it to use `src0`, then erase Mov.
        let mut replaced = false;
        cur.with_next(|nxt| {
            let uses = replace_uses_in_inst(&mut nxt.kind, res, src0);
            if uses > 0 {
                replaced = true;
            }
        });

        if replaced {
            // We can erase the Mov now; indices are (block, pos)
            let bb = cur.block();
            let at = cur.pos();
            q.erase(bb, at);
            // We changed block layout, ask driver to re-check around here.
            return true;
        }

        // Nothing to do for this Mov.
        false
    }
}
