//! Copy propagation (block-local, fixed-point).
//!
//! Improvements over the simple single-window pass:
//!  - Collapse deep Mov chains (with CHASE_LIMIT).
//!  - Propagate through the entire remainder of the current block.
//!  - Mov(Const K) canonicalizes to Const K.
//!  - Safely erase Mov when all its uses have been rewritten (use-count proof).
//!  - Iterate to a fixed point so new opportunities chain.
//!
//! Soundness: we only substitute within the same block *after* the Mov,
//! which is dominated by the Mov’s operand in SSA, so dominance holds.

#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::opt::{OptimizationWIR, WirEditQueue};
use crate::opt::helpers::replace_uses_in_inst;
use crate::wir::{Function, Inst, ValueDef, ValueId, Constant, InstId};

pub const CHASE_LIMIT: usize = 16;

#[derive(Default)]
pub struct CopyPropagation;

impl CopyPropagation {
    pub fn new() -> Self { Self::default() }

    /// Follow Mov chains up to `limit`, returning the first non-Mov source.
    fn chase_mov(func: &Function, mut v: ValueId, limit: usize) -> ValueId {
        let mut steps = 0usize;
        while steps < limit {
            steps += 1;
            match &func.values[v.0 as usize].def {
                ValueDef::InstResult(iid, _ix) => {
                    if let Inst::Mov(src) = func.nodes[iid.0 as usize].kind {
                        v = src;
                        continue;
                    }
                }
                _ => {}
            }
            break;
        }
        v
    }

    /// Count uses of `v` in the whole function by cloning node kinds and
    /// using `replace_uses_in_inst` as a finder (replace v -> v is a no-op).
    fn count_uses(func: &Function, v: ValueId) -> usize {
        let mut uses = 0usize;
        for n in &func.nodes {
            let mut k = n.kind.clone();
            uses += replace_uses_in_inst(&mut k, v, v);
        }
        uses
    }

    fn run(&mut self, func: &mut Function) {
        loop {
            let mut changed = false;
            let mut q = WirEditQueue::new();

            // Walk blocks in order; we only forward within the same block.
            for bb in &func.blocks {
                // Snapshot the inst list; we'll refer to node kinds from `func.nodes`
                // and stage replacements in `q`.
                for (pos, &nid) in bb.insts.iter().enumerate() {
                    let node = &func.nodes[nid.0 as usize];

                    // Only interested in Mov.
                    let Inst::Mov(src0) = node.kind else { continue; };

                    // Mov result value (if any).
                    let res = match node.results.get(0) {
                        Some(&v) => v,
                        None => continue,
                    };

                    // 1) Collapse Mov chains.
                    let final_src = Self::chase_mov(func, src0, CHASE_LIMIT);
                    if final_src != src0 {
                        q.replace_kind(nid, Inst::Mov(final_src));
                        changed = true;
                        // After canonicalizing, keep going; the forward pass below will use `final_src`.
                    }

                    // Canonicalize Mov(Const K) => Const K (helps DCE/CSE).
                    if let ValueDef::InstResult(src_iid, _)
                        = &func.values[final_src.0 as usize].def
                    {
                        if let Inst::Const(ref k) = func.nodes[src_iid.0 as usize].kind {
                            q.replace_kind(nid, Inst::Const(k.clone()));
                            changed = true;
                            // After this, there is no "Mov" to propagate; but we can still
                            // do full forward substitution using `final_src` below.
                        }
                    }

                    // 2) Block-local forward propagation: rewrite all later insts in this block.
                    let mut replaced_in_block = 0usize;
                    for &later_id in bb.insts.iter().skip(pos + 1) {
                        let later = &func.nodes[later_id.0 as usize];
                        let mut new_kind = later.kind.clone();
                        let hits = replace_uses_in_inst(&mut new_kind, res, final_src);
                        if hits > 0 {
                            replaced_in_block += hits;
                            q.replace_kind(later_id, new_kind);
                            changed = true;
                        }
                    }

                    // 3) If we rewrote *all* uses of `res` in the function, the Mov is dead: erase it.
                    if replaced_in_block > 0 {
                        let total_uses = Self::count_uses(func, res);
                        if replaced_in_block == total_uses {
                            // Remove the Mov at (bb, pos).
                            q.erase(bb.id, pos);
                            changed = true;
                        }
                    }
                }
            }

            if !changed { break; }
            q.apply(func);
        }
    }
}

impl OptimizationWIR for CopyPropagation {
    fn optimize_node(&mut self, cur: &mut crate::opt::InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| self.run(f));
        false
    }
}
