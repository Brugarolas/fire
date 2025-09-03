#![allow(dead_code)]

use crate::opt::{OptimizationWIR, WirEditQueue};
use crate::wir::{Function, Inst, InstId, ValueDef, ValueId, BlockId};

/// Tail-call & friends:
///  - Tail recursion elimination (self-call -> Jump(entry, args)).
///  - Tail position cleanup: Return(Mov(call_res*))->Return(call_res*), erase Movs.
///
/// Assumptions:
///  - Tail position == last effect in block and immediately returned.
///  - We allow only Movs between the call and the Return (and we erase them).
pub struct TailCallOpt {
    ran: bool,
}

impl Default for TailCallOpt {
    fn default() -> Self { Self { ran: false } }
}

impl TailCallOpt {
    pub fn new() -> Self { Self::default() }

    pub fn run(&mut self, func: &mut Function) {
        if self.ran { return; }
        self.ran = true;

        loop {
            let mut changed = false;
            let mut q = WirEditQueue::new();

            for bb in &func.blocks {
                if bb.insts.is_empty() { continue; }

                // Find last Return in this block (should normally be the last inst).
                let mut ret_pos: Option<usize> = None;
                for (i, &nid) in bb.insts.iter().enumerate().rev() {
                    if matches!(func.nodes[nid.0 as usize].kind, Inst::Return(_)) {
                        ret_pos = Some(i);
                        break;
                    }
                }
                let Some(ret_ix) = ret_pos else { continue; };
                let ret_id = bb.insts[ret_ix];
                let ret_kind = func.nodes[ret_id.0 as usize].kind.clone();
                let Inst::Return(ret_vals) = ret_kind else { continue; };

                // Peel Mov chains on return operands and figure out whether they all come
                // from *the same* call node (and remember which one).
                let mut call_nid: Option<InstId> = None;
                let mut call_res_indices: Vec<u8> = Vec::with_capacity(ret_vals.len());

                // Map movs we can erase (strictly between call and return and forwarding call results).
                let mut erasable_mov_positions: Vec<usize> = Vec::new();

                // Helper: follow Mov chains to underlying producer (with a small bound).
                let chase_mov = |f: &Function, mut v: ValueId| -> ValueId {
                    for _ in 0..8 {
                        match &f.values[v.0 as usize].def {
                            ValueDef::InstResult(iid, _ix) => {
                                if let Inst::Mov(src) = &f.nodes[iid.0 as usize].kind {
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

                // Helper: if v is a Mov result, return (mov_inst_id, src)
                let mov_of = |f: &Function, v: ValueId| -> Option<(InstId, ValueId)> {
                    if let ValueDef::InstResult(iid, _ix) = &f.values[v.0 as usize].def {
                        if let Inst::Mov(src) = f.nodes[iid.0 as usize].kind {
                            return Some((*iid, src));
                        }
                    }
                    None
                };

                // 0) Early-out: empty return (no values) -> nothing to TCO.
                if ret_vals.is_empty() {
                    // Still do post-call cleanup if pattern exists, but no call to tie to.
                    continue;
                }

                // 1) Identify the candidate call by inspecting each returned value.
                let mut all_from_same_call = true;
                for &rv in &ret_vals {
                    let peeled = chase_mov(func, rv);
                    // Producer of peeled must be InstResult
                    let Some((prod_iid, prod_ix)) = value_producer(func, peeled) else {
                        all_from_same_call = false; break;
                    };
                    // Producer node must be some Call* we can consider "a call"
                    let is_call = matches!(
                        func.nodes[prod_iid.0 as usize].kind,
                        Inst::CallDirect { .. } | Inst::CallClosure { .. } | Inst::CallIC { .. }
                    );
                    if !is_call { all_from_same_call = false; break; }

                    if let Some(cid) = call_nid {
                        if cid != prod_iid { all_from_same_call = false; break; }
                    } else {
                        call_nid = Some(prod_iid);
                    }
                    call_res_indices.push(prod_ix);
                }

                if !all_from_same_call { continue; }
                let Some(call_iid) = call_nid else { continue; };

                // 2) Ensure that between `call_iid` and `ret_id` there are no effectful instructions
                //    except *pure* Movs that forward that call's results. Also record these Movs for erasure.
                let Some(call_pos) = position_of_inst(func, bb.id, call_iid) else { continue; };
                if call_pos > ret_ix { continue; } // sanity

                let mut safe_tail = true;
                for mid_pos in (call_pos + 1)..ret_ix {
                    let mid_id = bb.insts[mid_pos];
                    let mid_k = &func.nodes[mid_id.0 as usize].kind;
                    match mid_k {
                        Inst::Mov(v) => {
                            // Mov must forward either a call result, or another Mov of a call result (covered by chase)
                            let src = chase_mov(func, *v);
                            if let Some((src_iid, _)) = value_producer(func, src) {
                                if src_iid == call_iid {
                                    // Can erase this Mov after we rewrite the Return
                                    erasable_mov_positions.push(mid_pos);
                                } else {
                                    safe_tail = false; break;
                                }
                            } else {
                                safe_tail = false; break;
                            }
                        }
                        // Anything else in between => not tail position
                        _ => { safe_tail = false; break; }
                    }
                }
                if !safe_tail { continue; }

                // 3) Tail position cleanup (for any call): remove Movs by making Return use call results directly.
                // Build a new Return value list that refers directly to the call results in the same order.
                let call_node = &func.nodes[call_iid.0 as usize];
                let call_res = call_node.results.clone();
                if call_res.len() != ret_vals.len() {
                    // Arity mismatch => cannot be "return of call results", skip.
                    continue;
                }

                // Repoint Return to the exact call results (by index mapping).
                let mut direct_rets: Vec<ValueId> = Vec::with_capacity(ret_vals.len());
                for &ix in &call_res_indices {
                    let idx = ix as usize;
                    if idx >= call_res.len() { direct_rets.clear(); break; }
                    direct_rets.push(call_res[idx]);
                }
                if direct_rets.len() != ret_vals.len() {
                    // Something odd; be conservative.
                    continue;
                }

                // Replace Return to directly return call results.
                q.replace_kind(ret_id, Inst::Return(direct_rets));
                // Erase intermediate Movs (erase from the end so indices remain valid).
                erasable_mov_positions.sort_unstable();
                erasable_mov_positions.drain(..).rev().for_each(|pos| q.erase(bb.id, pos));
                changed = true;

                // 4) Tail recursion elimination: if it’s a self-call, convert Call+Return to Jump(entry,args)
                let self_call = match &call_node.kind {
                    Inst::CallDirect { callee, args, .. } if *callee == func.id => {
                        // 4a) Replace Return with Jump(entry, args)
                        q.replace_kind(ret_id, Inst::Jump(func.entry, args.clone()));
                        // 4b) Erase the call itself
                        q.erase(bb.id, call_pos);
                        changed = true;
                        true
                    }
                    _ => false,
                };

                // If TRE fired, we already rewrote Return; the cleanup above still stands.
                // If not, we at least removed mov-chaff around tail calls.
                let _ = self_call;
            }

            if !changed {
                if !q.is_empty() { q.apply(func); }
                break;
            }
            q.apply(func);
        }
    }
}

/// Helper: get the producer InstId and result index for a ValueId (if it is an InstResult).
fn value_producer(func: &Function, v: ValueId) -> Option<(InstId, u8)> {
    match &func.values[v.0 as usize].def {
        ValueDef::InstResult(iid, ix) => Some((*iid, *ix)),
        _ => None,
    }
}

/// Helper: find the position of an instruction `iid` inside its block `bid`.
fn position_of_inst(func: &Function, bid: BlockId, iid: InstId) -> Option<usize> {
    let b = func.blocks.iter().find(|b| b.id == bid)?;
    b.insts.iter().position(|&id| id == iid)
}

impl OptimizationWIR for TailCallOpt {
    fn optimize_node(&mut self, cur: &mut crate::opt::InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| self.run(f));
        false
    }
}
