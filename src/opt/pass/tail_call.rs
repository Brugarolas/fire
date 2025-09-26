#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::wir::{BlockId, Function, Inst, InstId, ValueDef, ValueId};
use std::mem::{Discriminant, discriminant};

pub struct TailCallOpt {
    last_func_ptr: Option<usize>,
}

impl Default for TailCallOpt {
    fn default() -> Self {
        Self {
            last_func_ptr: None,
        }
    }
}
impl TailCallOpt {
    pub fn new() -> Self {
        Self::default()
    }
}

impl OptimizationWIR for TailCallOpt {
    /// Wake up only when we see returns/movs (enough to trigger once per function).
    fn maybe_interesting(&self, tag: Discriminant<Inst>) -> bool {
        use crate::wir::Inst::*;
        let v0 = ValueId(0);
        let tags = [
            discriminant(&Return(Vec::<ValueId>::new())),
            discriminant(&Mov(v0)),
        ];
        tags.contains(&tag)
    }

    fn optimize_node(&mut self, cur: &mut InstCursor, q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| {
            let ptr = f as *mut Function as usize;
            if self.last_func_ptr != Some(ptr) {
                self.last_func_ptr = Some(ptr);
                run_on_function(f, q);
            }
        });
        false
    }
}

fn run_on_function(func: &Function, q: &mut WirEditQueue) {
    if func.blocks.is_empty() {
        return;
    }

    // BlockId -> index
    let mut bix_of = ahash::AHashMap::with_capacity(func.blocks.len());
    for (i, b) in func.blocks.iter().enumerate() {
        bix_of.insert(b.id, i);
    }

    for (bix, bb) in func.blocks.iter().enumerate() {
        if bb.insts.is_empty() {
            continue;
        }

        // Find the last Return in this block (usually the terminator).
        let Some(ret_ix) = bb
            .insts
            .iter()
            .rposition(|&nid| matches!(func.nodes[nid.0 as usize].kind, Inst::Return(_)))
        else {
            continue;
        };

        let ret_id = bb.insts[ret_ix];
        let ret_vals = match &func.nodes[ret_id.0 as usize].kind {
            Inst::Return(vs) => vs.clone(),
            _ => continue,
        };

        if ret_vals.is_empty() {
            continue;
        } // nothing to do

        // Helpers (read-only)
        let value_producer = |v: ValueId| -> Option<(InstId, u8)> {
            match &func.values[v.0 as usize].def {
                ValueDef::InstResult(iid, ix) => Some((*iid, *ix)),
                _ => None,
            }
        };
        let chase_mov = |mut v: ValueId| -> ValueId {
            for _ in 0..8 {
                match &func.values[v.0 as usize].def {
                    ValueDef::InstResult(iid, _) => {
                        if let Inst::Mov(src) = &func.nodes[iid.0 as usize].kind {
                            v = *src;
                            continue;
                        }
                    }
                    _ => {}
                }
                break;
            }
            v
        };

        // 1) Identify the candidate call by inspecting each returned value.
        let mut call_nid: Option<InstId> = None;
        let mut call_res_indices: Vec<u8> = Vec::with_capacity(ret_vals.len());
        let mut all_from_same_call = true;

        for &rv in &ret_vals {
            let peeled = chase_mov(rv);
            let Some((prod_iid, prod_ix)) = value_producer(peeled) else {
                all_from_same_call = false;
                break;
            };
            let is_call = matches!(
                func.nodes[prod_iid.0 as usize].kind,
                Inst::CallDirect { .. } | Inst::CallClosure { .. } | Inst::CallIC { .. }
            );
            if !is_call {
                all_from_same_call = false;
                break;
            }

            if let Some(cid) = call_nid {
                if cid != prod_iid {
                    all_from_same_call = false;
                    break;
                }
            } else {
                call_nid = Some(prod_iid);
            }
            call_res_indices.push(prod_ix);
        }

        if !all_from_same_call {
            continue;
        }
        let Some(call_iid) = call_nid else {
            continue;
        };

        // 2) Ensure tail position: only Movs (forwarding that call's results) between call and Return.
        let Some(call_pos) = bb.insts.iter().position(|&id| id == call_iid) else {
            continue;
        };
        if call_pos > ret_ix {
            continue;
        }

        let mut erasable_mov_positions: Vec<usize> = Vec::new();
        let mut safe_tail = true;
        for mid_pos in (call_pos + 1)..ret_ix {
            let mid_id = bb.insts[mid_pos];
            match &func.nodes[mid_id.0 as usize].kind {
                Inst::Mov(v) => {
                    let src = chase_mov(*v);
                    if let Some((src_iid, _)) = value_producer(src) {
                        if src_iid == call_iid {
                            erasable_mov_positions.push(mid_pos);
                        } else {
                            safe_tail = false;
                            break;
                        }
                    } else {
                        safe_tail = false;
                        break;
                    }
                }
                _ => {
                    safe_tail = false;
                    break;
                }
            }
        }
        if !safe_tail {
            continue;
        }

        // 3) Tail-position cleanup: Return(Mov(call_res*)) -> Return(call_res*)
        let call_node = &func.nodes[call_iid.0 as usize];
        let call_res = call_node.results.clone();
        if call_res.len() != ret_vals.len() {
            continue;
        }

        let mut direct_rets: Vec<ValueId> = Vec::with_capacity(ret_vals.len());
        for &ix in &call_res_indices {
            let idx = ix as usize;
            if idx >= call_res.len() {
                direct_rets.clear();
                break;
            }
            direct_rets.push(call_res[idx]);
        }
        if direct_rets.len() != ret_vals.len() {
            continue;
        }

        // Queue: rewrite Return to point to call results directly.
        q.replace_kind(ret_id, Inst::Return(direct_rets));

        // Queue: erase Movs strictly between call and return (from end to start).
        if !erasable_mov_positions.is_empty() {
            let mut poss = erasable_mov_positions;
            poss.sort_unstable();
            for p in poss.into_iter().rev() {
                q.erase_ix(bix, p);
            }
        }

        // 4) Tail recursion elimination: self-call -> Jump(entry, args) + erase call.
        if let Inst::CallDirect { callee, args, .. } = &call_node.kind {
            if *callee == func.id {
                q.replace_kind(ret_id, Inst::Jump(func.entry, args.clone()));
                q.erase_ix(bix, call_pos);
            }
        }
    }
}
