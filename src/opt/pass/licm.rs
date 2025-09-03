// src/opt/pass/licm.rs
use std::collections::{BTreeSet, HashSet, VecDeque};
use ahash::AHashMap as HashMap;
use crate::opt::InstCursor;
use crate::opt::WirEditQueue;
use crate::opt::OptimizationWIR;
use crate::wir::{
    Block, BlockId, Function, Inst, InstId, Type, ValueDef, ValueId,
    IntBinOp, F64BinOp, CmpKind,
};

/// Loop-Invariant Code Motion (function pass).
/// Returns `true` if it moved at least one instruction.
pub struct Licm;

impl OptimizationWIR for Licm {
    fn optimize_node(&mut self, cur: &mut InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| Licm::run_on_function(f));
        // function-level pass; per-node "changed" not meaningful
        false
    }
}

impl Licm {
    pub fn run_on_function(func: &mut Function) -> bool {
        // Build quick indices
        let bid_to_idx: HashMap<BlockId, usize> = func.blocks.iter()
            .enumerate().map(|(i,b)| (b.id, i)).collect();
        let idx_to_bid: Vec<BlockId> = func.blocks.iter().map(|b| b.id).collect();

        let (succs, preds) = build_cfg(func, &bid_to_idx);
        let doms = compute_dominators(func, &succs, &preds, &bid_to_idx);

        let backedges = collect_backedges(&succs, &doms);
        if backedges.is_empty() {
            return false;
        }

        // Map InstId -> BlockId for fast lookup
        let inst_block: HashMap<InstId, BlockId> = map_inst_to_block(func);

        // Build natural loops and (unique) preheaders.
        let loops = build_loops(&preds, &idx_to_bid, &backedges);
        let mut header_to_preheader: HashMap<BlockId, BlockId> = HashMap::new();
        for lp in &loops {
            if let Some(pre) = find_preheader(lp, &preds, &bid_to_idx, &idx_to_bid) {
                header_to_preheader.insert(lp.header, pre);
            }
        }

        // Nothing to hoist if no unique preheaders.
        if header_to_preheader.is_empty() {
            return false;
        }

        // Per loop, identify & hoist candidates.
        let mut changed = false;

        // Process inner loops first (smaller set first)
        let mut loops_sorted = loops.clone();
        loops_sorted.sort_by_key(|lp| lp.members.len());

        for lp in loops_sorted {
            let Some(preheader) = header_to_preheader.get(&lp.header).copied() else { continue; };

            // Build invariants set: values defined outside loop are initially invariant.
            let mut invariant_vals: HashSet<ValueId> = HashSet::new();
            for v in &func.values {
                if is_value_defined_outside_loop(v, &inst_block, &lp.members) {
                    invariant_vals.insert(v.id);
                }
            }

            // Gather hoistable insts (and do it in a stable order).
            let mut hoist_list: Vec<InstId> = Vec::new();

            for &bid in &lp.members {
                let blk = &func.blocks[bid_to_idx[&bid]];
                // Iterate in block order — simple and predictable.
                for &nid in &blk.insts {
                    let n = &func.nodes[nid.0 as usize];

                    if !is_hoistable_pure(&n.kind) {
                        continue;
                    }

                    // Don't re-hoist if it's already in preheader.
                    if bid == preheader {
                        continue;
                    }

                    // All operands must be invariant *at this point*.
                    if inst_operands(&n.kind).into_iter().all(|op| invariant_vals.contains(&op)) {
                        hoist_list.push(nid);
                        for &res in &n.results {
                            invariant_vals.insert(res);
                        }
                    }
                }
            }

            if hoist_list.is_empty() {
                continue;
            }

            // Mutate CFG order: move each candidate to the preheader,
            // inserting right before the preheader's terminator (if any),
            // or append to the end otherwise.
            for nid in hoist_list {
                let from_bid = inst_block[&nid];

                // Remove from old block
                {
                    let bi = bid_to_idx[&from_bid];
                    let insts = &mut func.blocks[bi].insts;
                    if let Some(pos) = insts.iter().position(|&x| x == nid) {
                        insts.remove(pos);
                    }
                }

                // Insert at preheader: just before a terminating control inst if present
                {
                    let bi = bid_to_idx[&preheader];
                    let insts = &mut func.blocks[bi].insts;
                    let insert_pos = insts.iter().rposition(|&iid| !is_terminator(&func.nodes[iid.0 as usize].kind))
                        .map(|i| i + 1)
                        .unwrap_or(0);
                    insts.insert(insert_pos, nid);
                }
            }

            changed = true;
        }

        changed
    }
}

/* ---------- helpers ---------- */

#[derive(Clone)]
struct NaturalLoop {
    header: BlockId,
    tail: BlockId,          // backedge: tail -> header
    members: BTreeSet<BlockId>,
}

fn build_cfg(
    func: &Function,
    bid_to_idx: &HashMap<BlockId, usize>,
) -> (Vec<Vec<usize>>, Vec<Vec<usize>>) {
    let n = func.blocks.len();
    let mut succs = vec![Vec::<usize>::new(); n];
    let mut preds = vec![Vec::<usize>::new(); n];

    for (i, b) in func.blocks.iter().enumerate() {
        if let Some(&last) = b.insts.last() {
            use Inst::*;
            match &func.nodes[last.0 as usize].kind {
                Jump(tgt, _) => {
                    let j = bid_to_idx[tgt];
                    succs[i].push(j);
                    preds[j].push(i);
                }
                Branch { then_b, else_b, .. } => {
                    let j1 = bid_to_idx[then_b];
                    let j2 = bid_to_idx[else_b];
                    succs[i].push(j1); preds[j1].push(i);
                    succs[i].push(j2); preds[j2].push(i);
                }
                Switch { default_b, table, .. } => {
                    let jd = bid_to_idx[default_b];
                    succs[i].push(jd); preds[jd].push(i);
                    for &(_, bid) in table {
                        let j = bid_to_idx[&bid];
                        succs[i].push(j); preds[j].push(i);
                    }
                }
                Return(_) | Throw(_) => { /* no succs */ }
                _ => { /* block may not be terminated yet; no edges */ }
            }
        }
    }

    (succs, preds)
}

fn compute_dominators(
    func: &Function,
    succs: &[Vec<usize>],
    preds: &[Vec<usize>],
    bid_to_idx: &HashMap<BlockId, usize>,
) -> Vec<HashSet<usize>> {
    let n = func.blocks.len();
    let entry_idx = bid_to_idx[&func.entry];

    let universe: HashSet<usize> = (0..n).collect();
    let mut dom: Vec<HashSet<usize>> = vec![universe.clone(); n];
    dom[entry_idx] = [entry_idx].into_iter().collect();

    let mut changed = true;
    while changed {
        changed = false;
        for b in 0..n {
            if b == entry_idx { continue; }
            let mut new = universe.clone();
            for &p in &preds[b] {
                if new.is_empty() { break; }
                new = &new & &dom[p]; // intersection
            }
            new.insert(b);
            if new != dom[b] {
                dom[b] = new;
                changed = true;
            }
        }
    }
    dom
}

fn collect_backedges(
    succs: &[Vec<usize>],
    doms: &[HashSet<usize>],
) -> Vec<(usize, usize)> {
    // (tail_idx, header_idx)
    let mut res = Vec::new();
    for (u, outs) in succs.iter().enumerate() {
        for &v in outs {
            if doms[u].contains(&v) {
                res.push((u, v));
            }
        }
    }
    res
}

fn build_loops(
    preds: &[Vec<usize>],
    idx_to_bid: &[BlockId],
    backedges: &[(usize, usize)],
) -> Vec<NaturalLoop> {
    let mut loops = Vec::new();

    for &(tail, header) in backedges {
        let header_bid = idx_to_bid[header];
        let tail_bid = idx_to_bid[tail];

        let mut members: BTreeSet<BlockId> = BTreeSet::new();
        members.insert(header_bid);
        members.insert(tail_bid);

        // Worklist backward through predecessors of `tail` to gather the loop.
        let mut stack = vec![tail];
        while let Some(x) = stack.pop() {
            for &p in &preds[x] {
                let pb = idx_to_bid[p];
                if !members.contains(&pb) {
                    members.insert(pb);
                    if p != header { stack.push(p); }
                }
            }
        }

        loops.push(NaturalLoop { header: header_bid, tail: tail_bid, members });
    }

    loops
}

/// Safer version that requires an index map (callers can precompute).
fn find_preheader(lp: &NaturalLoop, preds_full: &[Vec<usize>], bid_to_idx: &HashMap<BlockId, usize>, idx_to_bid: &[BlockId]) -> Option<BlockId> {
    let h_idx = bid_to_idx[&lp.header];
    let mut outside_preds = Vec::new();
    for &p_idx in &preds_full[h_idx] {
        let pb = idx_to_bid[p_idx];
        if !lp.members.contains(&pb) {
            outside_preds.push(pb);
        }
    }
    if outside_preds.len() == 1 {
        Some(outside_preds[0])
    } else {
        None
    }
}

fn map_inst_to_block(func: &Function) -> HashMap<InstId, BlockId> {
    let mut m = HashMap::new();
    for b in &func.blocks {
        for &nid in &b.insts {
            m.insert(nid, b.id);
        }
    }
    m
}

fn is_value_defined_outside_loop(
    v: &crate::wir::Value,
    inst_block: &HashMap<crate::wir::InstId, crate::wir::BlockId>,
    loop_members: &BTreeSet<crate::wir::BlockId>,
) -> bool {
    use crate::wir::ValueDef;
    match &v.def {
        ValueDef::Const(_) => true,
        ValueDef::EffectToken(_) => true, // effect tokens aren't data defs; safe to consider "outside"
        ValueDef::BlockParam(bid, _) => !loop_members.contains(bid),
        ValueDef::InstResult(inst, _) => {
            // Be conservative: if the defining Inst isn't currently placed in any block,
            // treat it as defined "inside" (not invariant), which avoids hoisting and avoids panic.
            if let Some(b) = inst_block.get(inst) {
                !loop_members.contains(b)
            } else {
                false
            }
        }
    }
}

fn is_terminator(k: &Inst) -> bool {
    use Inst::*;
    matches!(k, Return(_) | Throw(_) | Jump(_, _) | Branch { .. } | Switch { .. })
}

fn is_hoistable_pure(k: &Inst) -> bool {
    use Inst::*;
    // Only side-effect-free, non-memory instructions. Be conservative.
    match k {
        // Never hoist these trivial “defs”
        Const(_) | Mov(_) => false,

        // Arithmetic / comparisons
        IntBin { .. } |
        F64Bin { .. } |
        NumAdd(_,_) | NumSub(_,_) | NumMul(_,_) | NumDiv(_,_) | NumRem(_,_) |
        CmpInt { .. } | CmpF64 { .. } => true,

        // String ops that are pure and cheap/safe to move
        StrLen(_) | StrCompare { .. } => true,

        // Everything else: be conservative (loads, calls, guards, arrays, etc.)
        _ => false,
    }
}

fn inst_operands(k: &Inst) -> Vec<ValueId> {
    use Inst::*;
    match k {
        IntBin { a, b, .. } => vec![*a, *b],
        F64Bin { a, b, .. } => vec![*a, *b],
        NumAdd(a,b) | NumSub(a,b) | NumMul(a,b) | NumDiv(a,b) | NumRem(a,b) => vec![*a, *b],
        CmpInt { a, b, .. } => vec![*a, *b],
        CmpF64 { a, b, .. } => vec![*a, *b],
        StrLen(v) => vec![*v],
        StrCompare { a, b } => vec![*a, *b],
        _ => Vec::new(),
    }
}
