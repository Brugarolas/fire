//! Napalm optimization scaffold for WIR (optimized).
//!
//! - O(1) InstCursor via cached block index.
//! - Zero-copy opcode peek; no Inst clones on hot path.
//! - Batch-safe edits with single-pass per-block rebuild.
//! - ReplaceKind applied in-place during apply.
//! - Unified pass runner with lazy per-block apply + local fixups.
//! - Optional dominator utilities (idom + preorder walk).
//!
//! Usage:
//!   let mut opt = Optimize::new().with_pass(your_pass());
//!   opt.optimize_module(&mut module);

#![allow(dead_code)]
#![allow(clippy::needless_return)]

pub mod helpers;
pub mod pass;
pub mod optimization;

use std::any::Any;
use std::cmp::Ordering;
use std::mem::{discriminant, Discriminant};

// ----- pull WIR types -----
use crate::wir::{
    Block, BlockId, Function, Inst, InstId, Module, Type, Value, ValueDef, ValueId,
};

/// =======================================
/// Vec-backed O(1) cursor (stack)
/// =======================================

/// A cursor into a block's instruction list (`block.insts: Vec<InstId>`).
/// Holds the block index + a raw pointer to `Function` so we can reborrow safely in closures
/// without heap allocations. The cursor itself is a tiny stack object.
pub struct InstCursor<'f> {
    func: *mut Function,
    block_ix: usize, // index into func.blocks
    pos: usize,      // index into block.insts
    _marker: std::marker::PhantomData<&'f mut Function>,
}

impl<'f> InstCursor<'f> {
    /// # Safety
    /// `func` must outlive the cursor and remain valid.
    pub fn new(func: &'f mut Function, block: BlockId, pos: usize) -> Self {
        let block_ix = unsafe {
            (*(&*func as *const Function as *mut Function))
                .blocks
                .iter()
                .position(|bb| bb.id == block)
        }
        .expect("invalid BlockId");
        Self { func, block_ix, pos, _marker: std::marker::PhantomData }
    }

    #[inline] pub fn block(&self) -> BlockId { unsafe { (*self.func).blocks[self.block_ix].id } }
    #[inline] pub fn pos(&self) -> usize { self.pos }

    /// Length (instruction count) of the current block.
    #[inline]
    pub fn len(&self) -> usize {
        unsafe { (*self.func).blocks[self.block_ix].insts.len() }
    }

    /// Current InstId.
    #[inline]
    pub fn cur_id(&self) -> InstId {
        unsafe { (*self.func).blocks[self.block_ix].insts[self.pos] }
    }

    /// Zero-copy peek of the current opcode/kind.
    #[inline]
    pub fn peek_cur<R>(&self, f: impl FnOnce(&Inst) -> R) -> R {
        let id = self.cur_id();
        unsafe { f(&(*self.func).nodes[id.0 as usize].kind) }
    }

    /// Cheap tag (discriminant) for opcode dispatch.
    #[inline]
    pub fn cur_tag(&self) -> Discriminant<Inst> {
        let id = self.cur_id();
        unsafe { discriminant(&(*self.func).nodes[id.0 as usize].kind) }
    }

    /// Read-only clone of current instruction kind (compat shim).
    /// Prefer `peek_cur` or `cur_tag` to avoid cloning on the hot path.
    #[inline]
    pub fn cur_kind(&self) -> Inst {
        let id = self.cur_id();
        unsafe { (*self.func).nodes[id.0 as usize].kind.clone() }
    }

    /// Mutate the current node via a scoped closure.
    #[inline]
    pub fn with_cur<R>(&mut self, f: impl FnOnce(&mut crate::wir::Node) -> R) -> R {
        let id = self.cur_id();
        unsafe { f(&mut (*self.func).nodes[id.0 as usize]) }
    }

    /// Mutate the previous node (if any) via a scoped closure.
    #[inline]
    pub fn with_prev<R>(&mut self, f: impl FnOnce(&mut crate::wir::Node) -> R) -> Option<R> {
        if self.pos == 0 { return None; }
        let prev_id = unsafe { (*self.func).blocks[self.block_ix].insts[self.pos - 1] };
        Some(unsafe { f(&mut (*self.func).nodes[prev_id.0 as usize]) })
    }

    /// Mutate the next node (if any) via a scoped closure.
    #[inline]
    pub fn with_next<R>(&mut self, f: impl FnOnce(&mut crate::wir::Node) -> R) -> Option<R> {
        let len = self.len();
        if self.pos + 1 >= len { return None; }
        let next_id = unsafe { (*self.func).blocks[self.block_ix].insts[self.pos + 1] };
        Some(unsafe { f(&mut (*self.func).nodes[next_id.0 as usize]) })
    }

    /// Access to the owning function (scoped, exclusive).
    #[inline]
    pub fn with_func<R>(&mut self, f: impl FnOnce(&mut Function) -> R) -> R {
        unsafe { f(&mut *self.func) }
    }
}

/// Helper on Function for internal use (non-hot path).
trait FuncExt {
    fn block_by_id(&mut self, b: BlockId) -> &mut Block;
}
impl FuncExt for Function {
    #[inline]
    fn block_by_id(&mut self, b: BlockId) -> &mut Block {
        self.blocks.iter_mut().find(|bb| bb.id == b).expect("invalid BlockId")
    }
}

/// =======================================
/// Batch-safe edits (per block, by index)
/// =======================================

#[derive(Debug, Clone)]
pub enum WirEdit {
    /// Insert existing InstIds before index `at` in block `bb`.
    InsertBefore { bb: BlockId, at: usize, insts: Vec<InstId> },
    /// Insert after index `at` in block `bb`.
    InsertAfter  { bb: BlockId, at: usize, insts: Vec<InstId> },
    /// Replace the opcode/kind of an instruction in place (keeps ids/results/effects as-is).
    ReplaceKind  { id: InstId, new_kind: Inst },
    /// Remove one instruction at index `at` in block `bb`.
    Erase        { bb: BlockId, at: usize },
    /// Replace a half-open range [start, end) in a block with given InstIds.
    SpliceRange  { bb: BlockId, start: usize, end: usize, insts: Vec<InstId> },
}

#[derive(Default)]
pub struct WirEditQueue {
    edits: Vec<WirEdit>,
}
impl WirEditQueue {
    pub fn new() -> Self { Self { edits: Vec::new() } }
    pub fn is_empty(&self) -> bool { self.edits.is_empty() }
    pub fn clear(&mut self) { self.edits.clear(); }

    #[inline] pub fn insert_before(&mut self, bb: BlockId, at: usize, insts: Vec<InstId>) { self.edits.push(WirEdit::InsertBefore{bb, at, insts}); }
    #[inline] pub fn insert_after (&mut self, bb: BlockId, at: usize, insts: Vec<InstId>) { self.edits.push(WirEdit::InsertAfter {bb, at, insts}); }
    #[inline] pub fn replace_kind  (&mut self, id: InstId, new_kind: Inst) { self.edits.push(WirEdit::ReplaceKind{ id, new_kind }); }
    #[inline] pub fn erase         (&mut self, bb: BlockId, at: usize) { self.edits.push(WirEdit::Erase{ bb, at }); }
    #[inline] pub fn splice_range  (&mut self, bb: BlockId, start: usize, end: usize, insts: Vec<InstId>) {
        self.edits.push(WirEdit::SpliceRange{ bb, start, end, insts });
    }

    /// How many edits are queued for a given block (excluding ReplaceKind).
    #[inline]
    pub fn len_for_block(&self, bb: BlockId) -> usize {
        self.edits.iter().filter(|e| match e {
            WirEdit::ReplaceKind{..} => false,
            WirEdit::InsertBefore{bb: b, ..}
            | WirEdit::InsertAfter{bb: b, ..}
            | WirEdit::Erase{bb: b, ..}
            | WirEdit::SpliceRange{bb: b, ..} => *b == bb,
        }).count()
    }
    #[inline]
    pub fn has_any_for_block(&self, bb: BlockId) -> bool { self.len_for_block(bb) > 0 }

    /// Apply all queued edits for the specified block in a single pass.
    /// Also applies *all* ReplaceKind edits (anchorless) immediately.
    pub fn apply_block(&mut self, f: &mut Function, bb: BlockId) {
        if self.edits.is_empty() { return; }

        // 1) Apply all ReplaceKind in-place and drop them.
        let mut i = 0;
        while i < self.edits.len() {
            if let WirEdit::ReplaceKind { id, new_kind } = &self.edits[i] {
                f.nodes[id.0 as usize].kind = new_kind.clone();
                self.edits.swap_remove(i);
            } else { i += 1; }
        }

        // Collect and drain edits for this block. Keep insertion order for determinism.
        let mut block_edits: Vec<(usize /*seq*/, WirEdit)> = Vec::new();
        let mut seq: usize = 0;
        let mut j = 0;
        while j < self.edits.len() {
            let take = match &self.edits[j] {
                WirEdit::InsertBefore{bb:b, ..}
                | WirEdit::InsertAfter{bb:b, ..}
                | WirEdit::Erase{bb:b, ..}
                | WirEdit::SpliceRange{bb:b, ..} => *b == bb,
                WirEdit::ReplaceKind{..} => false, // already removed above
            };
            if take {
                let e = self.edits.swap_remove(j);
                block_edits.push((seq, e));
                seq += 1;
            } else {
                j += 1;
            }
        }
        if block_edits.is_empty() { return; }

        // Snapshot old insts.
        let block_ix = f.blocks.iter().position(|b| b.id == bb).expect("invalid bb in edits");
        let old = f.blocks[block_ix].insts.clone();
        let old_len = old.len();

        // Prepare per-anchor inserts and range edits.
        #[derive(Clone)]
        struct RangeEdit { start: usize, end: usize, repl: Vec<InstId>, seq: usize }

        let mut before_map: Vec<Vec<InstId>> = vec![Vec::new(); old_len + 1]; // allow before at old_len (append)
        let mut after_map:  Vec<Vec<InstId>> = vec![Vec::new(); old_len];     // valid after anchors: 0..old_len-1
        let mut ranges: Vec<RangeEdit> = Vec::new();

        for (seq, e) in block_edits.into_iter() {
            match e {
                WirEdit::InsertBefore{ at, insts, .. } => {
                    let at = at.min(old_len);
                    before_map[at].extend(insts);
                }
                WirEdit::InsertAfter{ at, insts, .. } => {
                    if old_len == 0 { // treat as append
                        before_map[0].extend(insts);
                    } else {
                        let at = at.min(old_len - 1);
                        after_map[at].extend(insts);
                    }
                }
                WirEdit::Erase{ at, .. } => {
                    if at < old_len {
                        ranges.push(RangeEdit{ start: at, end: at+1, repl: Vec::new(), seq });
                    }
                }
                WirEdit::SpliceRange{ start, end, insts, .. } => {
                    let s = start.min(old_len);
                    let e = end.min(old_len).max(s);
                    ranges.push(RangeEdit{ start: s, end: e, repl: insts, seq });
                }
                WirEdit::ReplaceKind{ .. } => { /* already applied */ }
            }
        }

        // Sort ranges by (start, seq) for determinism.
        ranges.sort_by(|a, b| match a.start.cmp(&b.start) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal => a.seq.cmp(&b.seq),
        });

        // Single-pass rebuild.
        let total_inserts: usize =
            before_map.iter().map(|v| v.len()).sum::<usize>()
          + after_map.iter().map(|v| v.len()).sum::<usize>()
          + ranges.iter().map(|r| r.repl.len()).sum::<usize>();
        let mut out: Vec<InstId> = Vec::with_capacity(old_len + total_inserts);

        let mut i_old = 0usize;
        let mut r_ix = 0usize;

        while i_old < old_len {
            // Before at this anchor
            if !before_map[i_old].is_empty() {
                out.extend_from_slice(&before_map[i_old]);
            }

            // Apply any range edits that start here, in queued order.
            let mut applied_range = false;
            while r_ix < ranges.len() && ranges[r_ix].start == i_old {
                let r = &ranges[r_ix];
                if !r.repl.is_empty() { out.extend_from_slice(&r.repl); }
                i_old = r.end; // skip replaced/erased region
                r_ix += 1;
                applied_range = true;
                // Allow multiple edits with same start; continue to check next.
            }
            if applied_range {
                // We jumped `i_old`; loop back without copying old element.
                continue;
            }

            // Copy the original instruction.
            out.push(old[i_old]);

            // After at this element
            if !after_map[i_old].is_empty() {
                out.extend_from_slice(&after_map[i_old]);
            }

            i_old += 1;
        }

        // "before" at end appends.
        if !before_map[old_len].is_empty() {
            out.extend_from_slice(&before_map[old_len]);
        }

        // Commit new inst list.
        f.blocks[block_ix].insts = out;
    }

    /// Back-compat: apply all queued edits (old API).
    /// Internally uses the optimized per-block single-pass rebuild.
    #[inline]
    pub fn apply(&mut self, f: &mut Function) {
        self.apply_all(f)
    }

    /// Apply all queued edits across all affected blocks.
    pub fn apply_all(&mut self, f: &mut Function) {
        if self.edits.is_empty() { return; }

        // Apply ReplaceKind globally up-front.
        let mut i = 0;
        while i < self.edits.len() {
            if let WirEdit::ReplaceKind { id, new_kind } = &self.edits[i] {
                f.nodes[id.0 as usize].kind = new_kind.clone();
                self.edits.swap_remove(i);
            } else { i += 1; }
        }
        if self.edits.is_empty() { return; }

        // Gather unique blocks.
        let mut blocks: Vec<BlockId> = Vec::new();
        for e in &self.edits {
            match e {
                WirEdit::InsertBefore{bb, ..}
                | WirEdit::InsertAfter{bb, ..}
                | WirEdit::Erase{bb, ..}
                | WirEdit::SpliceRange{bb, ..} => {
                    if !blocks.contains(bb) { blocks.push(*bb); }
                }
                WirEdit::ReplaceKind{..} => {}
            }
        }
        for bb in blocks {
            self.apply_block(f, bb);
        }
    }
}

/// =======================================
/// Optimization API
/// =======================================

/// Trait for node-local optimizations.
/// Return:
///  - `true`  => stop running further optimizations for this node (advance)
///  - `false` => keep trying the remaining optimizations on this same node
pub trait OptimizationWIR {
    fn set_metadata_any(&mut self, _data: &dyn Any) {}

    fn optimize_node(&mut self, cur: &mut InstCursor, q: &mut WirEditQueue) -> bool;

    /// Optional: override if you want to do a quick early-out based on opcode tag.
    /// Default `None` runs the opt for all nodes.
    fn maybe_interesting(&self, _tag: Discriminant<Inst>) -> bool { true }
}

/// A pass wraps a set of optimizations and optional per-pass metadata broadcast.
pub struct OptimizationPass {
    pub optimizations: Vec<Box<dyn OptimizationWIR>>,
    pass_meta: Option<Box<dyn Any>>,
}
impl OptimizationPass {
    pub fn new(optimizations: Vec<Box<dyn OptimizationWIR>>) -> Self {
        Self { optimizations, pass_meta: None }
    }

    /// Broadcast pass-level metadata to every optimization.
    /// `meta` is stored so that the reference we hand out stays valid.
    pub fn initialize(&mut self, meta: impl Any) {
        self.pass_meta = Some(Box::new(meta));
        let meta_ref: &dyn Any = self.pass_meta.as_deref().unwrap();
        for o in &mut self.optimizations {
            o.set_metadata_any(meta_ref);
        }
    }

    /// Run across all blocks and instructions with local fixups.
    /// `recheck_window=1..=3` is typically enough.
    pub fn pass_optimizations(&mut self, func: &mut Function, recheck_window: usize) {
        const EDIT_APPLY_THRESHOLD: usize = 16;

        // Visit each block by index to keep order stable even if we edit other blocks.
        let mut q = WirEditQueue::new();
        for b_ix in 0..func.blocks.len() {
            let bb = func.blocks[b_ix].id;

            // Manual while-loop to allow local fixups.
            let mut i = 0usize;
            loop {
                let len = func.blocks[b_ix].insts.len();
                if i >= len { break; }

                // Build a cursor at (bb, i).
                let mut cur = InstCursor::new(func, bb, i);
                let tag = cur.cur_tag();

                for opt in self.optimizations.iter_mut() {
                    if !opt.maybe_interesting(tag) { continue; }
                    if opt.optimize_node(&mut cur, &mut q) {
                        break;
                    }
                }

                if q.has_any_for_block(bb) && q.len_for_block(bb) >= EDIT_APPLY_THRESHOLD {
                    // Apply accumulated edits for this block; then recheck a small window around `i`.
                    q.apply_block(func, bb);
                    let new_len = func.blocks[b_ix].insts.len();
                    if new_len == 0 { break; }
                    i = i.saturating_sub(recheck_window).min(new_len - 1);
                } else {
                    i += 1;
                }
            }

            // Flush tail edits for this block (if any), then recheck the tail window once.
            if q.has_any_for_block(bb) {
                q.apply_block(func, bb);
                // A final local recheck is optional; we skip to keep passes linear.
            }
        }

        // Safety net: if anything else accumulated (other blocks), flush.
        if !q.is_empty() {
            q.apply_all(func);
        }
    }
}

/// =======================================
/// Optimizer façade
/// =======================================

pub struct Optimize {
    passes: Vec<OptimizationPass>,
}
impl Default for Optimize { fn default() -> Self { Self { passes: Vec::new() } } }
impl Optimize {
    pub fn new() -> Self { Self::default() }
    pub fn with_pass(mut self, pass: OptimizationPass) -> Self { self.passes.push(pass); self }

    /// Run over every function in the module.
    pub fn optimize_module(mut self, module: &mut Module) {
        for f in &mut module.funcs {
            self.optimize_function(f);
        }
    }

    /// Run over a single function.
    pub fn optimize_function(&mut self, func: &mut Function) {
        for pass in self.passes.iter_mut() {
            pass.pass_optimizations(func, 1);
        }
    }
}

/// =======================================
/// Dominator utilities (optional)
/// =======================================

/// Get successor blocks from a block's terminator.
pub fn block_succs(func: &Function, b: BlockId) -> Vec<BlockId> {
    let blk = func.blocks.iter().find(|bb| bb.id == b).unwrap();
    let last_inst = match blk.insts.last() {
        Some(id) => &func.nodes[id.0 as usize].kind,
        None => return vec![],
    };
    use Inst::*;
    match last_inst {
        // explicit control
        Jump(tgt, _)                      => vec![*tgt],
        Branch { then_b, else_b, .. }     => vec![*then_b, *else_b],
        Switch { default_b, table, .. }   => {
            let mut v = Vec::with_capacity(1 + table.len());
            v.push(*default_b);
            for (_, bb) in table { v.push(*bb); }
            v
        }
        Return(_) | Throw(_)              => vec![],
        _                                 => vec![], // no fallthrough in this WIR
    }
}

/// Compute immediate dominators using a simple iterative algorithm.
/// Returns `idom[i]` as an `Option<BlockId>` aligned with `func.blocks` order.
/// `idom[entry_index] = None`.
pub fn compute_idoms(func: &Function, entry: BlockId) -> Vec<Option<BlockId>> {
    let n = func.blocks.len();
    assert!(n > 0, "function has no blocks");

    // Map BlockId <-> index in func.blocks
    use std::collections::HashMap;
    let mut index_of: HashMap<BlockId, usize> = HashMap::new();
    for (i, b) in func.blocks.iter().enumerate() { index_of.insert(b.id, i); }

    // Build predecessors (by indices)
    let mut preds: Vec<Vec<usize>> = vec![vec![]; n];
    for (i, b) in func.blocks.iter().enumerate() {
        for s in block_succs(func, b.id) {
            let si = *index_of.get(&s).expect("succ not in function blocks");
            preds[si].push(i);
        }
    }

    let entry_i = *index_of.get(&entry).expect("invalid entry id");
    let mut idom_idx: Vec<Option<usize>> = vec![None; n];
    idom_idx[entry_i] = None;

    // Iterative dataflow for idoms.
    let mut changed = true;
    while changed {
        changed = false;
        for b in 0..n {
            if b == entry_i { continue; }
            // choose a predecessor with a defined idom (or entry)
            let mut new_idom: Option<usize> = None;
            for &p in &preds[b] {
                if p == b { continue; }
                if idom_idx[p].is_some() || p == entry_i { new_idom = Some(p); break; }
            }
            if new_idom.is_none() { continue; }
            let mut cand = new_idom.unwrap();
            for &p in &preds[b] {
                if p == b { continue; }
                if idom_idx[p].is_some() || p == entry_i {
                    cand = intersect(&idom_idx, cand, p, entry_i);
                }
            }
            if idom_idx[b] != Some(cand) { idom_idx[b] = Some(cand); changed = true; }
        }
    }

    // Map back to BlockIds aligned with func.blocks order.
    let by_index: Vec<BlockId> = func.blocks.iter().map(|b| b.id).collect();
    idom_idx.into_iter().map(|o| o.map(|i| by_index[i])).collect()
}

fn intersect(idom: &Vec<Option<usize>>, mut a: usize, mut b: usize, entry: usize) -> usize {
    // Compute depths lazily and walk up the deeper node until they meet.
    let mut depth = |mut x: usize| { let mut d = 0; while x != entry { x = idom[x].unwrap_or(entry); d += 1; } d };
    let mut da = depth(a);
    let mut db = depth(b);
    while a != b {
        while da > db { a = idom[a].unwrap_or(entry); da -= 1; }
        while db > da { b = idom[b].unwrap_or(entry); db -= 1; }
        if a != b {
            a = idom[a].unwrap_or(entry);
            b = idom[b].unwrap_or(entry);
            if da > 0 { da -= 1; }
            if db > 0 { db -= 1; }
        }
    }
    a
}

/// Build dom-children adjacency aligned with `func.blocks` order.
/// `children[i]` contains BlockIds of nodes immediately dominated by `func.blocks[i].id`.
pub fn build_dom_tree(func: &Function, idom: &[Option<BlockId>]) -> Vec<Vec<BlockId>> {
    use std::collections::HashMap;
    let mut index_of: HashMap<BlockId, usize> = HashMap::new();
    for (i, b) in func.blocks.iter().enumerate() { index_of.insert(b.id, i); }

    let mut children: Vec<Vec<BlockId>> = vec![Vec::new(); func.blocks.len()];
    for (i, parent) in idom.iter().enumerate() {
        if let Some(p) = parent {
            let pi = index_of[p];
            children[pi].push(func.blocks[i].id);
        }
    }
    children
}

/// Convenience: compute idoms and walk in dom-preorder, calling `visit(BlockId)`.
pub fn dom_preorder_walk_func(func: &Function, entry: BlockId, mut visit: impl FnMut(BlockId)) {
    use std::collections::HashMap;
    let idom = compute_idoms(func, entry);
    let children = build_dom_tree(func, &idom);

    let mut idx_of: HashMap<BlockId, usize> = HashMap::new();
    for (i, b) in func.blocks.iter().enumerate() { idx_of.insert(b.id, i); }

    fn dfs(visit: &mut impl FnMut(BlockId),
           kids: &Vec<Vec<BlockId>>,
           idx_of: &std::collections::HashMap<BlockId, usize>,
           at: BlockId) {
        visit(at);
        let i = idx_of[&at];
        for &c in &kids[i] { dfs(visit, kids, idx_of, c); }
    }

    dfs(&mut visit, &children, &idx_of, entry);
}

/// =======================================
/// Minimal helpers to allocate new instructions (optional)
/// =======================================

/// Helper to allocate new nodes/values in a `Function`. Use it when you need to
/// create instructions to later insert via `WirEditQueue::insert_*`/`splice_range`.
pub struct InstFactory<'f> {
    func: &'f mut Function,
}
impl<'f> InstFactory<'f> {
    pub fn new(func: &'f mut Function) -> Self { Self { func } }

    /// Append a new node + result values to `func.nodes/values`, returning its InstId and result ValueIds.
    /// You can then queue its InstId for insertion via `WirEditQueue`.
    ///
    /// NOTE:
    ///  - This does **not** auto-thread effect tokens; pass appropriate effect_in/out if relevant.
    ///  - `result_tys` is per-result; `node_ty` mirrors your Node.ty convenience field.
    pub fn create(
        &mut self,
        kind: Inst,
        node_ty: Option<Type>,
        result_tys: &[Option<Type>],
        effect_in: Option<ValueId>,
        effect_out: Option<ValueId>,
    ) -> (InstId, Vec<ValueId>) {
        let id = InstId(self.func.nodes.len() as u32);
        let mut results = Vec::with_capacity(result_tys.len());
        for _ in 0..result_tys.len() {
            results.push(ValueId(self.func.values.len() as u32 + results.len() as u32));
        }
        self.func.nodes.push(crate::wir::Node {
            id,
            kind,
            ty: node_ty.clone(),
            effect_in,
            effect_out,
            results: results.clone(),
        });
        self.func.values.reserve(result_tys.len());
        for (i, rty) in result_tys.iter().enumerate() {
            self.func.values.push(Value {
                id: ValueId(self.func.values.len() as u32),
                ty: rty.clone(),
                def: ValueDef::InstResult(id, i as u8),
            });
        }
        (id, results)
    }
}
