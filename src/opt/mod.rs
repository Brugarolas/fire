// opt.rs
//! Napalm optimization scaffold for WIR.
//!
//! - Per-block Inst cursor with prev/next (stack-only).
//! - Safe, batchable edits against (BlockId, inst_index).
//! - Unified pass runner with short-circuit per node and local fixups.
//! - Optional dominator utilities (idom + preorder walk).
//!
//! Usage:
//!   let mut opt = Optimize::new().with_pass(your_pass());
//!   opt.optimize_module(&mut module);

#![allow(dead_code)]
#![allow(clippy::needless_return)]

pub mod helpers;
pub mod peephole_simplify;

use std::any::Any;
use std::cmp::Ordering;

// ----- pull WIR types -----
use crate::wir::{
    Block, BlockId, Function, Inst, InstId, Module, Type, Value, ValueDef, ValueId,
};

/// =======================================
/// Vec-backed "doubly linked" cursor (stack)
/// =======================================

/// A cursor into a block's instruction list (`block.insts: Vec<InstId>`).
/// Holds indices + a raw pointer to `Function` so we can reborrow safely in closures
/// without heap allocations. The cursor itself is a tiny stack object.
pub struct InstCursor<'f> {
    func: *mut Function,
    block: BlockId,
    pos: usize, // index into block.insts
    _marker: std::marker::PhantomData<&'f mut Function>,
}

impl<'f> InstCursor<'f> {
    /// # Safety
    /// `func` must outlive the cursor and remain valid.
    pub fn new(func: &'f mut Function, block: BlockId, pos: usize) -> Self {
        Self { func, block, pos, _marker: std::marker::PhantomData }
    }

    #[inline] pub fn block(&self) -> BlockId { self.block }
    #[inline] pub fn pos(&self) -> usize { self.pos }

    /// Length (instruction count) of the current block.
    #[inline]
    pub fn len(&self) -> usize {
        unsafe { (*self.func).block_by_id(self.block).insts.len() }
    }

    /// Current InstId.
    #[inline]
    pub fn cur_id(&self) -> InstId {
        unsafe { (*self.func).block_by_id(self.block).insts[self.pos] }
    }

    /// Read-only clone of current instruction kind (cheap to pattern-match on).
    #[inline]
    pub fn cur_kind(&self) -> Inst {
        unsafe { (*self.func).nodes[self.cur_id().0 as usize].kind.clone() }
    }

    /// Mutate the current node via a scoped closure.
    pub fn with_cur<R>(&mut self, f: impl FnOnce(&mut crate::wir::Node) -> R) -> R {
        let id = self.cur_id();
        unsafe { f(&mut (*self.func).nodes[id.0 as usize]) }
    }

    /// Mutate the previous node (if any) via a scoped closure.
    pub fn with_prev<R>(&mut self, f: impl FnOnce(&mut crate::wir::Node) -> R) -> Option<R> {
        if self.pos == 0 { return None; }
        let prev_id = unsafe { (*self.func).block_by_id(self.block).insts[self.pos - 1] };
        Some(unsafe { f(&mut (*self.func).nodes[prev_id.0 as usize]) })
    }

    /// Mutate the next node (if any) via a scoped closure.
    pub fn with_next<R>(&mut self, f: impl FnOnce(&mut crate::wir::Node) -> R) -> Option<R> {
        let len = self.len();
        if self.pos + 1 >= len { return None; }
        let next_id = unsafe { (*self.func).block_by_id(self.block).insts[self.pos + 1] };
        Some(unsafe { f(&mut (*self.func).nodes[next_id.0 as usize]) })
    }

    /// Access to the owning function (scoped, exclusive).
    pub fn with_func<R>(&mut self, f: impl FnOnce(&mut Function) -> R) -> R {
        unsafe { f(&mut *self.func) }
    }
}

/// Helper on Function for internal use.
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

    /// Deterministic in-place application:
    /// Per (bb, anchor) order: InsertBefore → ReplaceKind/Erase/Splice → InsertAfter.
    pub fn apply(&mut self, f: &mut Function) {
        if self.edits.is_empty() { return; }

        #[derive(Clone)]
        struct Key { bb: BlockId, at: usize, phase: u8 }
        let mut expanded: Vec<(Key, WirEdit)> = Vec::with_capacity(self.edits.len());

        for e in self.edits.drain(..) {
            match &e {
                WirEdit::InsertBefore{ bb, at, .. } => expanded.push((Key{bb:*bb, at:*at, phase:0}, e)),
                WirEdit::ReplaceKind { .. }          => expanded.push((Key{bb:BlockId(u32::MAX), at:usize::MAX, phase:1}, e)), // no anchor
                WirEdit::Erase{ bb, at }             => expanded.push((Key{bb:*bb, at:*at, phase:2}, e)),
                WirEdit::SpliceRange{ bb, start, .. }=> expanded.push((Key{bb:*bb, at:*start, phase:2}, e)),
                WirEdit::InsertAfter{ bb, at, .. }   => expanded.push((Key{bb:*bb, at:*at, phase:3}, e)),
            }
        }
        expanded.sort_by(|a, b| {
            let ka = &a.0; let kb = &b.0;
            match ka.bb.cmp(&kb.bb) {
                Ordering::Less => Ordering::Less,
                Ordering::Greater => Ordering::Greater,
                Ordering::Equal => match ka.at.cmp(&kb.at) {
                    Ordering::Less => Ordering::Less,
                    Ordering::Greater => Ordering::Greater,
                    Ordering::Equal => ka.phase.cmp(&kb.phase),
                }
            }
        });

        // Apply, block by block.
        let mut i = 0;
        while i < expanded.len() {
            let bb = expanded[i].0.bb;

            // Handle anchorless ReplaceKind (bb==MAX sentinel) inline and skip.
            if bb.0 == u32::MAX {
                let (_, e) = &expanded[i];
                if let WirEdit::ReplaceKind { id, new_kind } = e {
                    f.nodes[id.0 as usize].kind = new_kind.clone();
                }
                i += 1;
                continue;
            }

            // collect contiguous edits for this block
            let start = i;
            while i < expanded.len() && expanded[i].0.bb == bb { i += 1; }
            let end = i;

            // we'll map indices with offset as we mutate the inst vector
            let insts = &mut f.block_by_id(bb).insts;
            let mut offset: isize = 0;
            for (_k, e) in &expanded[start..end] {
                match e {
                    WirEdit::InsertBefore{ at, insts: add } => {
                        let pos = map_with_offset(*at, offset, insts.len());
                        insts.splice(pos..pos, add.clone());
                        offset += add.len() as isize;
                    }
                    WirEdit::InsertAfter{ at, insts: add } => {
                        let pos = map_with_offset(*at, offset, insts.len()) + 1;
                        insts.splice(pos..pos, add.clone());
                        offset += add.len() as isize;
                    }
                    WirEdit::ReplaceKind{ id, new_kind } => {
                        f.nodes[id.0 as usize].kind = new_kind.clone();
                    }
                    WirEdit::Erase{ at } => {
                        let pos = map_with_offset(*at, offset, insts.len());
                        insts.remove(pos);
                        offset -= 1;
                    }
                    WirEdit::SpliceRange{ start, end, insts: add } => {
                        let s = map_with_offset(*start, offset, insts.len());
                        let e = map_with_offset(*end,   offset, insts.len());
                        let removed = e - s;
                        insts.splice(s..e, add.clone());
                        offset += add.len() as isize - removed as isize;
                    }
                }
            }
        }

        #[inline]
        fn map_with_offset(idx: usize, offset: isize, len_now: usize) -> usize {
            let v = (idx as isize) + offset;
            debug_assert!(v >= 0 && (v as usize) <= len_now);
            v as usize
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
    fn set_metadata_any(&mut self, _data: Box<dyn Any>) {}
    fn set_metadata<M: Any>(&mut self, data: M) { self.set_metadata_any(Box::new(data)); }
    fn optimize_node(&mut self, cur: &mut InstCursor, q: &mut WirEditQueue) -> bool;
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

    pub fn initialize<M: Any + Clone>(&mut self, meta: M) {
        self.pass_meta = Some(Box::new(meta.clone()));
        for o in &mut self.optimizations {
            o.set_metadata(meta.clone());
        }
    }

    /// Run across all blocks and instructions with local fixups.
    /// `recheck_window=1..=3` is typically enough.
    pub fn pass_optimizations(&mut self, func: &mut Function, recheck_window: usize) {
        let mut q = WirEditQueue::new();

        // Visit each block (by index to keep order stable even if we edit other blocks).
        for b_ix in 0..func.blocks.len() {
            let bb = func.blocks[b_ix].id;

            // Manual while-loop to allow local fixups.
            let mut i = 0usize;
            loop {
                let len = func.block_by_id(bb).insts.len();
                if i >= len { break; }

                // Build a cursor at (bb, i).
                let mut cur = InstCursor::new(func, bb, i);
                for opt in self.optimizations.iter_mut() {
                    if opt.optimize_node(&mut cur, &mut q) {
                        break;
                    }
                }

                if q.is_empty() {
                    i += 1;
                } else {
                    // Apply edits; then recheck a small window around `i`.
                    q.apply(func);
                    let new_len = func.block_by_id(bb).insts.len();
                    if new_len == 0 { break; }
                    i = i.saturating_sub(recheck_window).min(new_len - 1);
                }
            }
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
