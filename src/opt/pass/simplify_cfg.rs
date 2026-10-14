// src/opts/simplify_cfg.rs
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::opt::{OptimizationWIR, WirEditQueue};
use crate::wir::{BlockId, Function, Inst, InstId, ValueId};
use std::collections::HashMap;

pub struct SimplifyCFG {
    ran: bool,
}

impl Default for SimplifyCFG {
    fn default() -> Self {
        Self { ran: false }
    }
}
impl SimplifyCFG {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn run(&mut self, func: &mut Function) {
        if self.ran {
            return;
        }
        self.ran = true;

        loop {
            let mut changed = false;
            let mut q = WirEditQueue::new();

            // --------------------------------------------
            // 0) Build quick lookup tables
            // --------------------------------------------
            let term_of = collect_terminators(func);
            let (preds, succs) = build_cfg(func, &term_of);

            // Precompute “trampoline” blocks (Jump-only) and a resolver for 0-param trampolines.
            let mut trivial_jump: HashMap<BlockId, (BlockId, Vec<ValueId>)> = HashMap::new();
            for b in &func.blocks {
                if let Some(tid) = term_of.get(&b.id).cloned().flatten() {
                    if let Inst::Jump(tgt, args) = &func.nodes[tid.0 as usize].kind {
                        // Trampoline definition: block has no non-terminators
                        if is_block_jump_only(func, b.id) {
                            trivial_jump.insert(b.id, (*tgt, args.clone()));
                        }
                    }
                }
            }

            // Resolves chains of “0-param empty trampolines with empty args”.
            let resolve_zero_param_trampoline = |mut bid: BlockId, func: &Function| -> BlockId {
                let mut guard = 0usize;
                while guard < 64 {
                    guard += 1;
                    let blk = func.blocks.iter().find(|x| x.id == bid).unwrap();
                    if !blk.params.is_empty() {
                        break;
                    }
                    // Only follow if block is Jump-only and the jump carries NO args.
                    if let Some(Some(tid)) = term_of.get(&bid) {
                        if let Inst::Jump(t, args) = &func.nodes[tid.0 as usize].kind {
                            if args.is_empty() && is_block_jump_only(func, bid) {
                                bid = *t;
                                continue;
                            }
                        }
                    }
                    break;
                }
                bid
            };

            // --------------------------------------------
            // 1) Thread final targets through 0-param trampolines
            //    (safe for Jump/Branch/Switch; no arg changes)
            // --------------------------------------------
            for b in &func.blocks {
                if let Some(tid) = term_of.get(&b.id).cloned().flatten() {
                    match &func.nodes[tid.0 as usize].kind {
                        Inst::Jump(t, args) => {
                            let t2 = resolve_zero_param_trampoline(*t, func);
                            if t2 != *t {
                                q.replace_kind(tid, Inst::Jump(t2, args.clone()));
                                changed = true;
                            }
                        }
                        Inst::Branch {
                            cond,
                            then_b,
                            else_b,
                        } => {
                            let nthen = resolve_zero_param_trampoline(*then_b, func);
                            let nelse = resolve_zero_param_trampoline(*else_b, func);
                            if nthen != *then_b || nelse != *else_b {
                                q.replace_kind(
                                    tid,
                                    Inst::Branch {
                                        cond: *cond,
                                        then_b: nthen,
                                        else_b: nelse,
                                    },
                                );
                                changed = true;
                            }
                        }
                        Inst::Switch {
                            tag,
                            default_b,
                            table,
                        } => {
                            let nd = resolve_zero_param_trampoline(*default_b, func);
                            let mut nt = table.clone();
                            let mut any = nd != *default_b;
                            for it in nt.iter_mut() {
                                let nb = resolve_zero_param_trampoline(it.1, func);
                                if nb != it.1 {
                                    it.1 = nb;
                                    any = true;
                                }
                            }
                            if any {
                                q.replace_kind(
                                    tid,
                                    Inst::Switch {
                                        tag: *tag,
                                        default_b: nd,
                                        table: nt,
                                    },
                                );
                                changed = true;
                            }
                        }
                        _ => {}
                    }
                }
            }

            // --------------------------------------------
            // 2) Argument-forwarding jump threading:
            //    B is a trampoline “Jump(X, A)”; for every pred P: Jump(B, J)
            //    rewrite P -> Jump(X, A[J/params])
            //    (only when all preds of B are Jumps; Branch/Switch can’t pass args)
            // --------------------------------------------
            for b in &func.blocks {
                let bid = b.id;
                // A trampoline we can forward across?
                let (succ, a_args) = match trivial_jump.get(&bid).cloned() {
                    Some(v) => v,
                    None => continue,
                };

                // Quick pred list
                let ps = match preds.get(&bid) {
                    Some(v) => v,
                    None => continue,
                };

                // If ANY pred is not a Jump -> we cannot forward args safely (Branches carry no args)
                if ps
                    .iter()
                    .any(|&(pb, _)| !pred_is_jump_to(func, pb, bid, &term_of))
                {
                    continue;
                }

                // If the trampoline has params, we need them for substitution; allowed.
                // Build param index lookup: param -> idx
                let mut pidx: HashMap<ValueId, usize> = HashMap::new();
                for (i, &pv) in b.params.iter().enumerate() {
                    pidx.insert(pv, i);
                }

                // For each predecessor Jump(P -> B, Jargs), build new args for succ:
                // new_arg = if a_args[k] is one of B.params[j] then Jargs[j] else a_args[k]
                for &(pb, ptid) in ps {
                    let (jargs, same_target) = match jump_args_to(func, pb, bid, ptid) {
                        Some(x) => x,
                        None => continue,
                    };
                    if !same_target {
                        continue;
                    } // sanity
                    let mut new_args: Vec<ValueId> = Vec::with_capacity(a_args.len());
                    for aa in &a_args {
                        if let Some(&jx) = pidx.get(aa) {
                            // Substitute from predecessor's jump args
                            if jx < jargs.len() {
                                new_args.push(jargs[jx]);
                            } else {
                                new_args.push(*aa);
                            }
                        } else {
                            new_args.push(*aa);
                        }
                    }
                    // Rewrite pred's terminator to jump to final succ with composed args.
                    q.replace_kind(ptid, Inst::Jump(succ, new_args));
                    changed = true;
                }
            }

            // --------------------------------------------
            // 3) Merge zero-param single-pred blocks into their predecessor.
            //    (only if the pred ends with Jump to the block)
            // --------------------------------------------
            // Rebuild preds if we changed edges
            if changed {
                q.apply(func);
                // rebuild to continue processing below
                let term_of2 = collect_terminators(func);
                let (preds2, _succs2) = build_cfg(func, &term_of2);

                // Collect safe merges first (avoid borrow churn).
                let mut merges: Vec<(BlockId, BlockId, usize)> = Vec::new(); // (pred, block, pred_jump_pos)
                for b in &func.blocks {
                    if b.id == func.entry {
                        continue;
                    }
                    if !b.params.is_empty() {
                        continue;
                    }
                    if contains_phi(func, b.id) {
                        continue;
                    }
                    let ps = match preds2.get(&b.id) {
                        Some(v) => v,
                        None => continue,
                    };
                    if ps.len() != 1 {
                        continue;
                    }
                    let (pred_b, ptid) = ps[0];
                    // pred must end with Jump(pred -> b)
                    if let Some(Some(tid)) = term_of2.get(&pred_b) {
                        if *tid != ptid {
                            continue;
                        } // sanity
                        if let Inst::Jump(tgt, _a) = &func.nodes[ptid.0 as usize].kind {
                            if *tgt != b.id {
                                continue;
                            }
                        } else {
                            continue;
                        }
                        // Record the position of pred's terminator and the block id to merge.
                        if let Some(pos) = inst_pos_in_block(func, pred_b, ptid) {
                            merges.push((pred_b, b.id, pos));
                        }
                    }
                }

                for (pred_b, merge_b, pred_term_pos) in merges {
                    // Append all insts from merge_b after removing pred's final jump.
                    let pred_ix = func.blocks.iter().position(|bb| bb.id == pred_b).unwrap();
                    let merge_ix = func.blocks.iter().position(|bb| bb.id == merge_b).unwrap();

                    // Remove pred's last instruction (the Jump)
                    if pred_term_pos < func.blocks[pred_ix].insts.len() {
                        func.blocks[pred_ix].insts.remove(pred_term_pos);
                    }

                    // Move all instructions from merge_b into pred
                    let moved = func.blocks[merge_ix].insts.clone();
                    func.blocks[pred_ix].insts.extend(moved.iter());
                    // Clear merged block’s body (it will be unreachable after threading; DCE can erase)
                    func.blocks[merge_ix].insts.clear();

                    // Note: block params are zero, so no operand substitution is needed.
                }

                // After merges, continue another outer iteration to re-scan everything.
                continue;
            }

            // --------------------------------------------
            // 4) Unreachable block cleanup: erase instructions (DCE will later drop blocks)
            // --------------------------------------------
            let reachable = compute_reachable(func);
            for b in &func.blocks {
                if !reachable.contains(&b.id) {
                    for i in (0..b.insts.len()).rev() {
                        q.erase(b.id, i);
                        changed = true;
                    }
                }
            }

            // --------------------------------------------
            // 5) Tiny φ cleanups (length 1 / all-equal)
            // --------------------------------------------
            for b in &func.blocks {
                for (i, &nid) in b.insts.iter().enumerate() {
                    if let Inst::Phi(ref vs) = func.nodes[nid.0 as usize].kind {
                        if vs.is_empty() {
                            continue;
                        }
                        if vs.len() == 1 {
                            q.replace_kind(nid, Inst::Mov(vs[0]));
                            changed = true;
                            continue;
                        }
                        let first = vs[0];
                        if vs.iter().all(|&x| x == first) {
                            q.replace_kind(nid, Inst::Mov(first));
                            changed = true;
                        }
                    }
                }
            }

            if !changed {
                if !q.is_empty() {
                    q.apply(func);
                }
                break;
            }
            q.apply(func);
            // iterate to fixed point
        }
    }
}

impl OptimizationWIR for SimplifyCFG {
    fn optimize_node(&mut self, cur: &mut crate::opt::InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| self.run(f));
        false
    }
}

// ============================== helpers ==============================

fn collect_terminators(func: &Function) -> HashMap<BlockId, Option<InstId>> {
    let mut out = HashMap::new();
    for b in &func.blocks {
        let mut t: Option<InstId> = None;
        if let Some(&nid) = b.insts.last() {
            match func.nodes[nid.0 as usize].kind {
                Inst::Jump(_, _)
                | Inst::Branch { .. }
                | Inst::Switch { .. }
                | Inst::Return(_)
                | Inst::Throw(_) => t = Some(nid),
                _ => {}
            }
        }
        out.insert(b.id, t);
    }
    out
}

fn build_cfg(
    func: &Function,
    term_of: &HashMap<BlockId, Option<InstId>>,
) -> (
    HashMap<BlockId, Vec<(BlockId, InstId)>>,
    HashMap<BlockId, Vec<BlockId>>,
) {
    // preds: succ -> [(pred_block, pred_term_id)]
    let mut preds: HashMap<BlockId, Vec<(BlockId, InstId)>> = HashMap::new();
    let mut succs: HashMap<BlockId, Vec<BlockId>> = HashMap::new();

    for b in &func.blocks {
        let mut outs = Vec::new();
        if let Some(Some(tid)) = term_of.get(&b.id) {
            match &func.nodes[tid.0 as usize].kind {
                Inst::Jump(t, _) => {
                    outs.push(*t);
                    preds.entry(*t).or_default().push((b.id, *tid));
                }
                Inst::Branch { then_b, else_b, .. } => {
                    outs.push(*then_b);
                    outs.push(*else_b);
                    preds.entry(*then_b).or_default().push((b.id, *tid));
                    preds.entry(*else_b).or_default().push((b.id, *tid));
                }
                Inst::Switch {
                    default_b, table, ..
                } => {
                    outs.push(*default_b);
                    preds.entry(*default_b).or_default().push((b.id, *tid));
                    for &(_, bb) in table {
                        outs.push(bb);
                        preds.entry(bb).or_default().push((b.id, *tid));
                    }
                }
                _ => {}
            }
        }
        succs.insert(b.id, outs);
    }
    (preds, succs)
}

fn is_block_jump_only(func: &Function, bid: BlockId) -> bool {
    let blk = func.blocks.iter().find(|x| x.id == bid).unwrap();
    if blk.insts.is_empty() {
        return false;
    }
    // Only last is a terminator jump, and all before are non-terminators? keep it *strict*: exactly one inst
    if blk.insts.len() != 1 {
        return false;
    }
    let nid = blk.insts[0];
    matches!(func.nodes[nid.0 as usize].kind, Inst::Jump(_, _))
}

fn pred_is_jump_to(
    func: &Function,
    pred_b: BlockId,
    to: BlockId,
    term_of: &HashMap<BlockId, Option<InstId>>,
) -> bool {
    if let Some(Some(tid)) = term_of.get(&pred_b) {
        if let Inst::Jump(tgt, _a) = &func.nodes[tid.0 as usize].kind {
            return *tgt == to;
        }
    }
    false
}

fn jump_args_to(
    func: &Function,
    pred_b: BlockId,
    to: BlockId,
    pred_term: InstId,
) -> Option<(Vec<ValueId>, bool)> {
    if let Inst::Jump(tgt, args) = &func.nodes[pred_term.0 as usize].kind {
        Some((args.clone(), *tgt == to))
    } else {
        None
    }
}

fn inst_pos_in_block(func: &Function, bid: BlockId, nid: InstId) -> Option<usize> {
    let blk = func.blocks.iter().find(|b| b.id == bid)?;
    blk.insts.iter().position(|&x| x == nid)
}

fn contains_phi(func: &Function, bid: BlockId) -> bool {
    let blk = func.blocks.iter().find(|b| b.id == bid).unwrap();
    blk.insts
        .iter()
        .any(|&nid| matches!(func.nodes[nid.0 as usize].kind, Inst::Phi(_)))
}

fn is_terminator(k: &Inst) -> bool {
    matches!(
        k,
        Inst::Return(_)
            | Inst::Branch { .. }
            | Inst::Jump(_, _)
            | Inst::Throw(_)
            | Inst::Switch { .. }
    )
}

fn compute_reachable(func: &Function) -> std::collections::HashSet<BlockId> {
    let mut seen: std::collections::HashSet<BlockId> = std::collections::HashSet::new();
    let mut stack: Vec<BlockId> = vec![func.entry];

    while let Some(bid) = stack.pop() {
        if !seen.insert(bid) {
            continue;
        }
        if let Some(block) = func.blocks.iter().find(|b| b.id == bid) {
            for &nid in &block.insts {
                let k = &func.nodes[nid.0 as usize].kind;
                if is_terminator(k) {
                    match k {
                        Inst::Jump(t, _) => stack.push(*t),
                        Inst::Branch { then_b, else_b, .. } => {
                            stack.push(*then_b);
                            stack.push(*else_b);
                        }
                        Inst::Switch {
                            default_b, table, ..
                        } => {
                            stack.push(*default_b);
                            for &(_, blk) in table {
                                stack.push(blk);
                            }
                        }
                        Inst::Return(_) | Inst::Throw(_) => {}
                        _ => {}
                    }
                    break;
                }
            }
        }
    }
    seen
}
