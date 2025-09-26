#![allow(unused_imports)]
#![allow(unused_variables)]

use ahash::AHashMap as HashMap;
use ahash::AHashSet as HashSet;
use smallvec::SmallVec;
use std::mem::{Discriminant, discriminant};

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::wir::{BlockId, CmpKind, F64BinOp, Function, Inst, InstId, IntBinOp, ValueDef, ValueId};

/// Loop-Invariant Code Motion (function pass; emits edits via WirEditQueue).
pub struct Licm {
    last_func_ptr: Option<usize>,
}

impl Default for Licm {
    fn default() -> Self {
        Self {
            last_func_ptr: None,
        }
    }
}

impl OptimizationWIR for Licm {
    /// Wake up on things that indicate loops (terminators) and things we may hoist.
    fn maybe_interesting(&self, tag: Discriminant<Inst>) -> bool {
        use Inst::*;
        let v0 = ValueId(0);
        let tags = [
            // Terminators (for CFG/loop discovery)
            discriminant(&Jump(BlockId(0), Vec::<ValueId>::new())),
            discriminant(&Branch {
                cond: v0,
                then_b: BlockId(0),
                else_b: BlockId(0),
            }),
            // NOTE: we intentionally skip Switch's discriminant construction to avoid depending
            // on exact fields; LICM will still be woken by arithmetic/comparison ops below.

            // Hoistable pure ops (also wake the pass inside loops)
            discriminant(&IntBin {
                op: IntBinOp::Add,
                a: v0,
                b: v0,
            }),
            discriminant(&F64Bin {
                op: F64BinOp::Add,
                a: v0,
                b: v0,
            }),
            discriminant(&NumAdd(v0, v0)),
            discriminant(&NumSub(v0, v0)),
            discriminant(&NumMul(v0, v0)),
            discriminant(&NumDiv(v0, v0)),
            discriminant(&NumRem(v0, v0)),
            discriminant(&CmpInt {
                kind: CmpKind::Eq,
                a: v0,
                b: v0,
            }),
            discriminant(&CmpF64 {
                kind: CmpKind::Eq,
                a: v0,
                b: v0,
            }),
            discriminant(&StrLen(v0)),
            discriminant(&StrCompare { a: v0, b: v0 }),
        ];
        tags.contains(&tag)
    }

    fn optimize_node(&mut self, cur: &mut InstCursor, q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| {
            let ptr = f as *mut Function as usize;
            if self.last_func_ptr != Some(ptr) {
                self.last_func_ptr = Some(ptr);
                run_licm_once(f, q);
            }
        });
        false
    }
}

// ------------------------------------------------------------
// Core LICM
// ------------------------------------------------------------

fn run_licm_once(func: &Function, q: &mut WirEditQueue) {
    if func.blocks.is_empty() {
        return;
    }

    // -------- indices / fast lookups --------
    let mut bix_of: HashMap<BlockId, usize> = HashMap::with_capacity(func.blocks.len());
    let mut bid_of: Vec<BlockId> = Vec::with_capacity(func.blocks.len());
    for (i, b) in func.blocks.iter().enumerate() {
        bix_of.insert(b.id, i);
        bid_of.push(b.id);
    }

    // InstId -> (block_ix, pos)  [dense, O(1)]
    let mut pos_of_inst: Vec<Option<(usize, usize)>> = vec![None; func.nodes.len()];
    for (bi, bb) in func.blocks.iter().enumerate() {
        for (i, &iid) in bb.insts.iter().enumerate() {
            pos_of_inst[iid.0 as usize] = Some((bi, i));
        }
    }
    let pos = |iid: InstId| pos_of_inst[iid.0 as usize];

    // -------- CFG / Dominators / Loops --------
    let (succs, preds) = build_cfg(func, &bix_of);
    let doms = compute_dominators_bitset(func, &succs, &preds, &bix_of); // doms[b] is bitset of dominators of b
    let backedges = collect_backedges(&succs, &doms); // (tail_idx, header_idx)
    if backedges.is_empty() {
        return;
    }

    // Build natural loops and unique preheaders
    let loops = build_loops(&preds, &bid_of, &backedges);
    let mut header_to_preheader: HashMap<BlockId, BlockId> = HashMap::new();
    for lp in &loops {
        if let Some(pre) = find_preheader(lp, &preds, &bix_of, &bid_of) {
            header_to_preheader.insert(lp.header, pre);
        }
    }
    if header_to_preheader.is_empty() {
        return;
    }

    // -------- Hoisting: per-loop --------
    // We'll accumulate per-block edits using IX-based APIs.
    let mut inserts_for_pre: HashMap<usize, SmallVec<[InstId; 16]>> = HashMap::new();
    let mut erases_for_block: HashMap<usize, SmallVec<[usize; 16]>> = HashMap::new();

    // Process inner loops first
    let mut loops_sorted = loops.clone();
    loops_sorted.sort_by_key(|lp| lp.members.len());

    for lp in loops_sorted {
        let Some(pre_bid) = header_to_preheader.get(&lp.header).copied() else {
            continue;
        };
        let pre_bix = bix_of[&pre_bid];

        // Build fast membership bitset
        let mut in_loop = vec![false; func.blocks.len()];
        for &bid in &lp.members {
            in_loop[bix_of[&bid]] = true;
        }

        // Track values proven invariant inside this run
        let mut locally_invariant: HashSet<ValueId> = HashSet::default();
        let is_invariant =
            |v: ValueId, in_loop: &Vec<bool>, pos_of_inst: &Vec<Option<(usize, usize)>>| -> bool {
                match &func.values[v.0 as usize].def {
                    ValueDef::Const(_) => true,
                    ValueDef::EffectToken(_) => false, // don't hoist anything depending on effects
                    ValueDef::BlockParam(bid, _) => !in_loop[bix_of[bid]],
                    ValueDef::InstResult(iid, _) => {
                        if let Some((bi, _)) = pos_of_inst[iid.0 as usize] {
                            !in_loop[bi]
                        } else {
                            false
                        }
                    }
                }
            };

        // Preheader insertion anchor (before terminator, or append)
        let pre_blk = &func.blocks[pre_bix];
        let insert_anchor = pre_blk
            .insts
            .iter()
            .rposition(|&iid| !is_terminator(&func.nodes[iid.0 as usize].kind))
            .map(|i| i + 1)
            .unwrap_or(0);

        // Gather hoistable instructions in stable order (by block, then position)
        for (bi, bb) in func.blocks.iter().enumerate() {
            if !in_loop[bi] || bi == pre_bix {
                continue;
            }
            for (i, &iid) in bb.insts.iter().enumerate() {
                let node = &func.nodes[iid.0 as usize];
                if !is_hoistable_pure(&node.kind) {
                    continue;
                }

                if inst_operands_small(&node.kind).iter().all(|&op| {
                    locally_invariant.contains(&op) || is_invariant(op, &in_loop, &pos_of_inst)
                }) {
                    erases_for_block.entry(bi).or_default().push(i);
                    inserts_for_pre.entry(pre_bix).or_default().push(iid);
                    for &r in &node.results {
                        locally_invariant.insert(r);
                    }
                }
            }
        }

        // Emit edits for this loop
        if let Some(list) = inserts_for_pre.get(&pre_bix) {
            if !list.is_empty() {
                // Into<SmallVec<[InstId; 4]>> via Vec<InstId>
                q.insert_before_ix(pre_bix, insert_anchor, list.clone().into_vec());
            }
        }
        if let Some(poss) = erases_for_block.get_mut(&pre_bix) {
            // nothing to erase in preheader; leave as-is
            let _ = poss;
        }
        for (bi, poss) in erases_for_block.iter_mut() {
            if poss.is_empty() {
                continue;
            }
            poss.sort_unstable();
            poss.dedup();
            for &p in poss.iter().rev() {
                q.erase_ix(*bi, p);
            }
            poss.clear();
        }
    }
}

// ------------------------------------------------------------
// Helpers
// ------------------------------------------------------------

#[derive(Clone)]
struct NaturalLoop {
    header: BlockId,
    tail: BlockId,                    // backedge: tail -> header
    members: SmallVec<[BlockId; 16]>, // deterministic order
}

fn build_cfg(
    func: &Function,
    bix_of: &HashMap<BlockId, usize>,
) -> (Vec<Vec<usize>>, Vec<Vec<usize>>) {
    let n = func.blocks.len();
    let mut succs: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];

    for (i, b) in func.blocks.iter().enumerate() {
        if let Some(&last) = b.insts.last() {
            use Inst::*;
            match &func.nodes[last.0 as usize].kind {
                Jump(tgt, _) => {
                    let j = bix_of[tgt];
                    succs[i].push(j);
                    preds[j].push(i);
                }
                Branch { then_b, else_b, .. } => {
                    let j1 = bix_of[then_b];
                    let j2 = bix_of[else_b];
                    succs[i].push(j1);
                    preds[j1].push(i);
                    succs[i].push(j2);
                    preds[j2].push(i);
                }
                Switch {
                    default_b, table, ..
                } => {
                    let jd = bix_of[default_b];
                    succs[i].push(jd);
                    preds[jd].push(i);
                    for &(_, bid) in table {
                        let j = bix_of[&bid];
                        succs[i].push(j);
                        preds[j].push(i);
                    }
                }
                _ => { /* Return/Throw or unterminated: no succs */ }
            }
        }
    }

    (succs, preds)
}

/// Dominators via simple bitset fixed-point: dom[b][x] == x dominates b.
fn compute_dominators_bitset(
    func: &Function,
    succs: &[Vec<usize>],
    preds: &[Vec<usize>],
    bix_of: &HashMap<BlockId, usize>,
) -> Vec<Vec<bool>> {
    let n = func.blocks.len();
    let entry = bix_of[&func.entry];

    let mut dom = vec![vec![true; n]; n];
    for b in 0..n {
        if b == entry {
            dom[b].fill(false);
            dom[b][entry] = true;
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for b in 0..n {
            if b == entry {
                continue;
            }
            let mut new_row = vec![true; n];
            if preds[b].is_empty() {
                new_row.fill(false);
            } else {
                for &p in &preds[b] {
                    for x in 0..n {
                        new_row[x] = new_row[x] & dom[p][x];
                    }
                }
            }
            new_row[b] = true;
            if new_row != dom[b] {
                dom[b] = new_row;
                changed = true;
            }
        }
    }
    dom
}

fn collect_backedges(succs: &[Vec<usize>], doms: &[Vec<bool>]) -> SmallVec<[(usize, usize); 16]> {
    let mut out = SmallVec::new();
    for (u, outs) in succs.iter().enumerate() {
        for &v in outs {
            if doms[u][v] {
                out.push((u, v));
            }
        }
    }
    out
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

        let mut members: SmallVec<[BlockId; 16]> = SmallVec::new();
        let mut in_set: HashSet<BlockId> = HashSet::default();
        members.push(header_bid);
        in_set.insert(header_bid);
        members.push(tail_bid);
        in_set.insert(tail_bid);

        // Worklist: backward from tail through preds to gather loop.
        let mut stack = SmallVec::<[usize; 32]>::new();
        stack.push(tail);
        while let Some(x) = stack.pop() {
            for &p in &preds[x] {
                let pb = idx_to_bid[p];
                if !in_set.contains(&pb) {
                    in_set.insert(pb);
                    members.push(pb);
                    if p != header {
                        stack.push(p);
                    }
                }
            }
        }

        loops.push(NaturalLoop {
            header: header_bid,
            tail: tail_bid,
            members,
        });
    }
    loops
}

/// Unique preheader = only one predecessor of header that is outside the loop.
fn find_preheader(
    lp: &NaturalLoop,
    preds_full: &[Vec<usize>],
    bix_of: &HashMap<BlockId, usize>,
    idx_to_bid: &[BlockId],
) -> Option<BlockId> {
    let h_idx = bix_of[&lp.header];
    let mut outside: SmallVec<[BlockId; 4]> = SmallVec::new();
    // Build quick membership test
    let mut in_loop = HashSet::default();
    for &bid in &lp.members {
        in_loop.insert(bid);
    }

    for &p_idx in &preds_full[h_idx] {
        let pb = idx_to_bid[p_idx];
        if !in_loop.contains(&pb) {
            outside.push(pb);
        }
    }
    if outside.len() == 1 {
        Some(outside[0])
    } else {
        None
    }
}

fn is_terminator(k: &Inst) -> bool {
    use Inst::*;
    matches!(
        k,
        Return(_) | Throw(_) | Jump(_, _) | Branch { .. } | Switch { .. }
    )
}

fn is_hoistable_pure(k: &Inst) -> bool {
    use Inst::*;
    // Only side-effect-free, non-memory instructions. Be conservative.
    match k {
        // Never hoist trivial defs
        Const(_) | Mov(_) => false,

        // Arithmetic / comparisons
        IntBin { .. } |
        F64Bin { .. } |
        NumAdd(_,_) | NumSub(_,_) | NumMul(_,_) | NumDiv(_,_) | NumRem(_,_) |
        CmpInt { .. } | CmpF64 { .. } |

        // Simple string ops
        StrLen(_) | StrCompare { .. } => true,

        _ => false,
    }
}

#[inline]
fn inst_operands_small(k: &Inst) -> SmallVec<[ValueId; 4]> {
    use Inst::*;
    let mut out = SmallVec::<[ValueId; 4]>::new();
    match k {
        IntBin { a, b, .. } => {
            out.push(*a);
            out.push(*b);
        }
        F64Bin { a, b, .. } => {
            out.push(*a);
            out.push(*b);
        }
        NumAdd(a, b) | NumSub(a, b) | NumMul(a, b) | NumDiv(a, b) | NumRem(a, b) => {
            out.push(*a);
            out.push(*b);
        }
        CmpInt { a, b, .. } => {
            out.push(*a);
            out.push(*b);
        }
        CmpF64 { a, b, .. } => {
            out.push(*a);
            out.push(*b);
        }
        StrLen(v) => {
            out.push(*v);
        }
        StrCompare { a, b } => {
            out.push(*a);
            out.push(*b);
        }
        _ => {}
    }
    out
}
