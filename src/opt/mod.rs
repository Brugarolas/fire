//! Napalm optimizer core (worklist + tag bucketing, BC fixed).
//!
//! - Per-block worklist: only revisit affected instructions.
//! - Amortized pre-bucketing: opcode tag → relevant optimizations.
//! - Per-block edit queues (O(1) route/drain) + **BlockId-compatible APIs**.
//! - O(1) InstId→(block_ix,pos) map; incrementally maintained.
//! - Peephole window (prev2..next2) built once per visit.
//! - ReplaceKind uses `mem::replace` (no clones).
//! - `SmallVec` in all hot/transient paths.
//!
//! Legacy APIs restored:
//!   - `InstCursor::cur_kind()`
//!   - `WirEditQueue::{apply, erase, insert_before, insert_after, splice_range, replace_kind}`
//!
//! Usage:
//!   let mut opt = Optimize::new().with_pass(your_pass());
//!   opt.optimize_module(&mut module);

#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(clippy::needless_return)]

pub mod helpers;
pub mod optimization;
pub mod pass;

use std::any::Any;
use std::collections::{HashMap, VecDeque};
use std::mem::{Discriminant, discriminant, replace};

use smallvec::SmallVec;

// ----- pull WIR types -----
use crate::wir::{BlockId, Function, Inst, InstId, Module, Type, Value, ValueDef, ValueId};

/// =======================================
/// O(1) cursor into a block (no BlockId scans)
/// =======================================
pub struct InstCursor<'f> {
    func: *mut Function,
    block_ix: usize,
    pos: usize,
    _marker: std::marker::PhantomData<&'f mut Function>,
}

impl<'f> InstCursor<'f> {
    #[inline]
    pub fn new(func: &'f mut Function, block: BlockId, pos: usize) -> Self {
        // We have &mut Function here, so we can safely search blocks directly.
        let block_ix = func
            .blocks
            .iter()
            .position(|bb| bb.id == block)
            .expect("invalid BlockId");
        // Store the raw pointer for later cursor use.
        Self {
            func: func as *mut Function,
            block_ix,
            pos,
            _marker: std::marker::PhantomData,
        }
    }

    #[inline]
    pub fn new_ix(func: &'f mut Function, block_ix: usize, pos: usize) -> Self {
        Self {
            func: func as *mut Function,
            block_ix,
            pos,
            _marker: std::marker::PhantomData,
        }
    }

    // ----- explicit materialization helpers (avoid implicit autoref) -----
    #[inline(always)]
    unsafe fn func_ref(&self) -> &Function {
        &*self.func
    }
    #[inline(always)]
    unsafe fn func_mut(&mut self) -> &mut Function {
        &mut *self.func
    }

    #[inline]
    pub fn block_id(&self) -> BlockId {
        unsafe { self.func_ref().blocks[self.block_ix].id }
    }
    #[inline]
    pub fn block_index(&self) -> usize {
        self.block_ix
    }
    #[inline]
    pub fn pos(&self) -> usize {
        self.pos
    }
    #[inline]
    pub fn len(&self) -> usize {
        unsafe { self.func_ref().blocks[self.block_ix].insts.len() }
    }

    #[inline]
    pub fn cur_id(&self) -> InstId {
        unsafe {
            let insts = &self.func_ref().blocks[self.block_ix].insts;
            *insts
                .get(self.pos)
                .expect("InstCursor::cur_id OOB (stale pos); guard before constructing cursor")
        }
    }

    /// Cheap tag for dispatch.
    #[inline]
    pub fn cur_tag(&self) -> std::mem::Discriminant<Inst> {
        let id = self.cur_id();
        unsafe { std::mem::discriminant(&self.func_ref().nodes[id.0 as usize].kind) }
    }

    /// Back-compat: clone of current kind (avoid in hot paths if possible).
    #[inline]
    pub fn cur_kind(&self) -> Inst {
        let id = self.cur_id();
        unsafe { self.func_ref().nodes[id.0 as usize].kind.clone() }
    }

    #[inline]
    pub fn peek_cur<R>(&self, f: impl FnOnce(&Inst) -> R) -> R {
        let id = self.cur_id();
        unsafe { f(&self.func_ref().nodes[id.0 as usize].kind) }
    }

    #[inline]
    pub fn with_cur<R>(&mut self, f: impl FnOnce(&mut crate::wir::Node) -> R) -> R {
        let id = self.cur_id();
        unsafe { f(&mut self.func_mut().nodes[id.0 as usize]) }
    }

    #[inline]
    pub fn with_prev<R>(&mut self, f: impl FnOnce(&mut crate::wir::Node) -> R) -> Option<R> {
        if self.pos == 0 {
            return None;
        }
        let prev_id = unsafe { self.func_ref().blocks[self.block_ix].insts[self.pos - 1] };
        Some(unsafe { f(&mut self.func_mut().nodes[prev_id.0 as usize]) })
    }

    #[inline]
    pub fn with_next<R>(&mut self, f: impl FnOnce(&mut crate::wir::Node) -> R) -> Option<R> {
        let len = self.len();
        if self.pos + 1 >= len {
            return None;
        }
        let next_id = unsafe { self.func_ref().blocks[self.block_ix].insts[self.pos + 1] };
        Some(unsafe { f(&mut self.func_mut().nodes[next_id.0 as usize]) })
    }

    #[inline]
    pub fn with_func<R>(&mut self, f: impl FnOnce(&mut Function) -> R) -> R {
        unsafe { f(self.func_mut()) }
    }
}

/// =======================================
/// Peephole window (prev2..next2)
/// =======================================
#[derive(Clone, Copy)]
pub struct Window {
    pub prev2: Option<InstId>,
    pub prev1: Option<InstId>,
    pub cur: InstId,
    pub next1: Option<InstId>,
    pub next2: Option<InstId>,
}

impl<'f> InstCursor<'f> {
    /// Peephole window (prev2..next2)
    #[inline]
    pub fn window5(&self) -> Window {
        let len = self.len();
        let p = self.pos;
        let block = unsafe { &self.func_ref().blocks[self.block_ix] };
        let at = |i: usize| block.insts.get(i).copied();
        Window {
            prev2: if p >= 2 { at(p - 2) } else { None },
            prev1: if p >= 1 { at(p - 1) } else { None },
            cur: at(p).unwrap(),
            next1: if p + 1 < len { at(p + 1) } else { None },
            next2: if p + 2 < len { at(p + 2) } else { None },
        }
    }
}

/// =======================================
/// Per-block edits (fast) + BlockId-compatible layer
/// =======================================
#[derive(Debug, Clone)]
pub enum WirEdit {
    InsertBefore {
        at: usize,
        insts: SmallVec<[InstId; 4]>,
    },
    InsertAfter {
        at: usize,
        insts: SmallVec<[InstId; 4]>,
    },
    ReplaceKind {
        id: InstId,
        new_kind: Inst,
    }, // global
    Erase {
        at: usize,
    },
    SpliceRange {
        start: usize,
        end: usize,
        insts: SmallVec<[InstId; 4]>,
    },
}

/// Compatibility wrapper for old BlockId-based APIs.
#[derive(Debug, Clone)]
enum CompatKind {
    InsertBefore {
        at: usize,
        insts: SmallVec<[InstId; 4]>,
    },
    InsertAfter {
        at: usize,
        insts: SmallVec<[InstId; 4]>,
    },
    Erase {
        at: usize,
    },
    SpliceRange {
        start: usize,
        end: usize,
        insts: SmallVec<[InstId; 4]>,
    },
}
#[derive(Debug, Clone)]
struct CompatEdit {
    bb: BlockId,
    kind: CompatKind,
}

#[derive(Default)]
pub struct WirEditQueue {
    /// Per-block edit lists; index by block_ix.
    by_block: Vec<SmallVec<[WirEdit; 8]>>,
    /// Global replace-kind buffer (anchorless).
    replaces: SmallVec<[(InstId, Inst); 16]>,
    /// Back-compat edits addressed by BlockId (routed lazily).
    compat: SmallVec<[CompatEdit; 32]>,
}

impl WirEditQueue {
    /// Create with block count (fast path).
    pub fn new() -> Self {
        Self {
            by_block: vec![SmallVec::new(); 16],
            replaces: SmallVec::new(),
            compat: SmallVec::new(),
        }
    }

    /// Back-compat constructor when you don't know #blocks yet.
    pub fn new_uninit() -> Self {
        Self::default()
    }

    #[inline]
    pub fn clear(&mut self) {
        for v in &mut self.by_block {
            v.clear();
        }
        self.replaces.clear();
        self.compat.clear();
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.replaces.is_empty()
            && self.compat.is_empty()
            && self.by_block.iter().all(|v| v.is_empty())
    }

    // ---------- Fast IX-based API (preferred) ----------
    #[inline]
    pub fn insert_before_ix(
        &mut self,
        bix: usize,
        at: usize,
        insts: impl Into<SmallVec<[InstId; 4]>>,
    ) {
        self.ensure_blocks(bix + 1);
        self.by_block[bix].push(WirEdit::InsertBefore {
            at,
            insts: insts.into(),
        });
    }
    #[inline]
    pub fn insert_after_ix(
        &mut self,
        bix: usize,
        at: usize,
        insts: impl Into<SmallVec<[InstId; 4]>>,
    ) {
        self.ensure_blocks(bix + 1);
        self.by_block[bix].push(WirEdit::InsertAfter {
            at,
            insts: insts.into(),
        });
    }
    #[inline]
    pub fn erase_ix(&mut self, bix: usize, at: usize) {
        self.ensure_blocks(bix + 1);
        self.by_block[bix].push(WirEdit::Erase { at });
    }
    #[inline]
    pub fn splice_range_ix(
        &mut self,
        bix: usize,
        start: usize,
        end: usize,
        insts: impl Into<SmallVec<[InstId; 4]>>,
    ) {
        self.ensure_blocks(bix + 1);
        self.by_block[bix].push(WirEdit::SpliceRange {
            start,
            end,
            insts: insts.into(),
        });
    }
    #[inline]
    pub fn replace_kind(&mut self, id: InstId, new_kind: Inst) {
        self.replaces.push((id, new_kind));
    }

    // ---------- Back-compat BlockId API (legacy signatures) ----------
    #[inline]
    pub fn insert_before(
        &mut self,
        bb: BlockId,
        at: usize,
        insts: impl Into<SmallVec<[InstId; 4]>>,
    ) {
        self.compat.push(CompatEdit {
            bb,
            kind: CompatKind::InsertBefore {
                at,
                insts: insts.into(),
            },
        });
    }
    #[inline]
    pub fn insert_after(
        &mut self,
        bb: BlockId,
        at: usize,
        insts: impl Into<SmallVec<[InstId; 4]>>,
    ) {
        self.compat.push(CompatEdit {
            bb,
            kind: CompatKind::InsertAfter {
                at,
                insts: insts.into(),
            },
        });
    }
    #[inline]
    pub fn erase(&mut self, bb: BlockId, at: usize) {
        // <— restored
        self.compat.push(CompatEdit {
            bb,
            kind: CompatKind::Erase { at },
        });
    }
    #[inline]
    pub fn splice_range(
        &mut self,
        bb: BlockId,
        start: usize,
        end: usize,
        insts: impl Into<SmallVec<[InstId; 4]>>,
    ) {
        self.compat.push(CompatEdit {
            bb,
            kind: CompatKind::SpliceRange {
                start,
                end,
                insts: insts.into(),
            },
        });
    }

    /// Legacy global apply (no FuncState in signature). Routes compat edits and applies all.
    pub fn apply(&mut self, f: &mut Function) {
        // <— restored
        // Build func-local state for position updates.
        let mut fs = FuncState::new(f);
        // Ensure by_block is sized.
        self.ensure_blocks(f.blocks.len());
        // Route legacy compat edits to by_block.
        self.route_all_compat(f);
        // Apply replaces once, then each block that has work.
        if !self.replaces.is_empty() || self.by_block.iter().any(|v| !v.is_empty()) {
            // Apply replaces globally (drains).
            for (id, mut nk) in self.replaces.drain(..) {
                let node = &mut f.nodes[id.0 as usize];
                nk = replace(&mut node.kind, nk);
                let _ = nk;
            }
            for bix in 0..f.blocks.len() {
                if !self.by_block[bix].is_empty() {
                    self.apply_block(f, &mut fs, bix);
                }
            }
        }
    }

    #[inline]
    pub fn has_any_for_block_ix(&self, bix: usize) -> bool {
        self.by_block.get(bix).map_or(false, |v| !v.is_empty())
            || self
                .compat
                .iter()
                .any(|c| /* cheap check; rare */ c_bb_index_eq(self, bix))
    }

    /// Apply to one block; also updates `FuncState` position map.
    pub fn apply_block(&mut self, f: &mut Function, fs: &mut FuncState, bix: usize) {
        self.ensure_blocks(f.blocks.len());
        // Route compat edits for this block (if any).
        self.route_compat_for_block(f, bix);

        let empty_block = self.by_block[bix].is_empty();
        let have_repl = !self.replaces.is_empty();
        if empty_block && !have_repl {
            return;
        }

        // Apply ReplaceKind globally (drains).
        if have_repl {
            for (id, mut nk) in self.replaces.drain(..) {
                let node = &mut f.nodes[id.0 as usize];
                nk = replace(&mut node.kind, nk);
                let _ = nk;
            }
        }
        if empty_block {
            return;
        }

        // Drain edits (stable order).
        let mut edits: SmallVec<[WirEdit; 16]> = SmallVec::new();
        edits.extend(self.by_block[bix].drain(..));

        // Old insts snapshot.
        let old = f.blocks[bix].insts.clone();
        let old_len = old.len();

        // Per-anchor inserts and ranges.
        #[derive(Clone)]
        struct RangeEdit {
            start: usize,
            end: usize,
            repl: SmallVec<[InstId; 4]>,
            seq: usize,
        }

        let mut before_map: Vec<SmallVec<[InstId; 4]>> = vec![SmallVec::new(); old_len + 1];
        let mut after_map: Vec<SmallVec<[InstId; 4]>> = vec![SmallVec::new(); old_len];
        let mut ranges: SmallVec<[RangeEdit; 16]> = SmallVec::new();

        let mut seq = 0usize;
        for e in edits {
            match e {
                WirEdit::InsertBefore { at, insts } => {
                    let at = at.min(old_len);
                    before_map[at].extend(insts);
                }
                WirEdit::InsertAfter { at, insts } => {
                    if old_len == 0 {
                        before_map[0].extend(insts);
                    } else {
                        let at = at.min(old_len - 1);
                        after_map[at].extend(insts);
                    }
                }
                WirEdit::Erase { at } => {
                    if at < old_len {
                        ranges.push(RangeEdit {
                            start: at,
                            end: at + 1,
                            repl: SmallVec::new(),
                            seq,
                        });
                        seq += 1;
                    }
                }
                WirEdit::SpliceRange { start, end, insts } => {
                    let s = start.min(old_len);
                    let e = end.min(old_len).max(s);
                    ranges.push(RangeEdit {
                        start: s,
                        end: e,
                        repl: insts,
                        seq,
                    });
                    seq += 1;
                }
                WirEdit::ReplaceKind { .. } => {}
            }
        }

        ranges.sort_by(|a, b| match a.start.cmp(&b.start) {
            std::cmp::Ordering::Less => std::cmp::Ordering::Less,
            std::cmp::Ordering::Greater => std::cmp::Ordering::Greater,
            std::cmp::Ordering::Equal => a.seq.cmp(&b.seq),
        });

        let total_inserts: usize = before_map.iter().map(|v| v.len()).sum::<usize>()
            + after_map.iter().map(|v| v.len()).sum::<usize>()
            + ranges.iter().map(|r| r.repl.len()).sum::<usize>();

        let mut out: SmallVec<[InstId; 32]> = SmallVec::with_capacity(old_len + total_inserts);

        // Rebuild.
        let mut i_old = 0usize;
        let mut r_ix = 0usize;
        while i_old < old_len {
            if !before_map[i_old].is_empty() {
                out.extend_from_slice(&before_map[i_old]);
            }

            let mut applied_range = false;
            while r_ix < ranges.len() && ranges[r_ix].start == i_old {
                let r = &ranges[r_ix];
                if !r.repl.is_empty() {
                    out.extend_from_slice(&r.repl);
                }
                i_old = r.end;
                r_ix += 1;
                applied_range = true;
            }
            if applied_range {
                continue;
            }

            out.push(old[i_old]);
            if !after_map[i_old].is_empty() {
                out.extend_from_slice(&after_map[i_old]);
            }
            i_old += 1;
        }
        if !before_map[old_len].is_empty() {
            out.extend_from_slice(&before_map[old_len]);
        }

        // Commit and update positions for this block only.
        let new_insts = out.into_vec();
        for &id in &f.blocks[bix].insts {
            fs.pos_of_inst[id.0 as usize] = None;
        }
        for (i, &id) in new_insts.iter().enumerate() {
            fs.pos_of_inst[id.0 as usize] = Some((bix, i));
        }
        f.blocks[bix].insts = new_insts;
    }

    // ---------- internal helpers ----------
    #[inline]
    fn ensure_blocks(&mut self, n: usize) {
        if self.by_block.len() < n {
            self.by_block.resize_with(n, SmallVec::new);
        }
    }

    /// Route all legacy compat edits into by_block using the current Function.
    fn route_all_compat(&mut self, f: &Function) {
        if self.compat.is_empty() {
            return;
        }
        // Build BlockId -> index map once.
        let mut ix_of: HashMap<BlockId, usize> = HashMap::with_capacity(f.blocks.len());
        for (i, b) in f.blocks.iter().enumerate() {
            ix_of.insert(b.id, i);
        }
        let drained: SmallVec<[CompatEdit; 32]> = self.compat.drain(..).collect();
        for c in drained {
            if let Some(&bix) = ix_of.get(&c.bb) {
                self.ensure_blocks(bix + 1);
                match c.kind {
                    CompatKind::InsertBefore { at, insts } => {
                        self.by_block[bix].push(WirEdit::InsertBefore { at, insts })
                    }
                    CompatKind::InsertAfter { at, insts } => {
                        self.by_block[bix].push(WirEdit::InsertAfter { at, insts })
                    }
                    CompatKind::Erase { at } => self.by_block[bix].push(WirEdit::Erase { at }),
                    CompatKind::SpliceRange { start, end, insts } => {
                        self.by_block[bix].push(WirEdit::SpliceRange { start, end, insts })
                    }
                }
            } else {
                debug_assert!(false, "Compat edit with invalid BlockId");
            }
        }
    }

    /// Route only compat edits for a specific block index.
    fn route_compat_for_block(&mut self, f: &Function, bix: usize) {
        if self.compat.is_empty() {
            return;
        }
        let bb_id = f.blocks[bix].id;
        // partition_drain manually (SmallVec has no retain_drain).
        let mut i = 0;
        while i < self.compat.len() {
            if self.compat[i].bb == bb_id {
                let c = self.compat.swap_remove(i);
                self.ensure_blocks(bix + 1);
                match c.kind {
                    CompatKind::InsertBefore { at, insts } => {
                        self.by_block[bix].push(WirEdit::InsertBefore { at, insts })
                    }
                    CompatKind::InsertAfter { at, insts } => {
                        self.by_block[bix].push(WirEdit::InsertAfter { at, insts })
                    }
                    CompatKind::Erase { at } => self.by_block[bix].push(WirEdit::Erase { at }),
                    CompatKind::SpliceRange { start, end, insts } => {
                        self.by_block[bix].push(WirEdit::SpliceRange { start, end, insts })
                    }
                }
            } else {
                i += 1;
            }
        }
    }
}

// Tiny helper for has_any_for_block_ix compat probe.
#[inline]
fn c_bb_index_eq(q: &WirEditQueue, bix: usize) -> bool {
    // Without Function we can't resolve; conservatively return false here.
    // `has_any_for_block_ix` is used during a pass with a Function, so we don't rely on this path.
    let _ = q;
    let _ = bix;
    false
}

/// =======================================
/// Function-local fast state (positions)
/// =======================================
struct FuncState {
    /// InstId (index into nodes) → Some((block_ix, pos)) or None if not in any block.
    pos_of_inst: Vec<Option<(usize, usize)>>,
}

impl FuncState {
    fn new(func: &Function) -> Self {
        let mut pos = vec![None; func.nodes.len()];
        for (bix, bb) in func.blocks.iter().enumerate() {
            for (i, &id) in bb.insts.iter().enumerate() {
                pos[id.0 as usize] = Some((bix, i));
            }
        }
        Self { pos_of_inst: pos }
    }
    #[inline]
    fn pos_of(&self, id: InstId) -> Option<(usize, usize)> {
        self.pos_of_inst.get(id.0 as usize).and_then(|o| *o)
    }
}

/// =======================================
/// Optimization API (unchanged externally)
/// =======================================
pub trait OptimizationWIR {
    fn set_metadata_any(&mut self, _data: &dyn Any) {}
    fn optimize_node(&mut self, cur: &mut InstCursor, q: &mut WirEditQueue) -> bool;
    /// Optional: prefilter by opcode tag (used in amortized bucketing).
    fn maybe_interesting(&self, _tag: Discriminant<Inst>) -> bool {
        true
    }
}

/// A pass holds optimizations, metadata, tag buckets, and a tiny cache.
pub struct OptimizationPass {
    pub optimizations: SmallVec<[Box<dyn OptimizationWIR>; 8]>,
    pass_meta: Option<Box<dyn Any>>,
    /// Cache: opcode tag → indices of optimizations that care about it.
    by_tag: HashMap<Discriminant<Inst>, SmallVec<[usize; 8]>>,
}

impl OptimizationPass {
    pub fn new(optimizations: Vec<Box<dyn OptimizationWIR>>) -> Self {
        Self {
            optimizations: SmallVec::from_vec(optimizations),
            pass_meta: None,
            by_tag: HashMap::new(),
        }
    }

    pub fn initialize(&mut self, meta: impl Any) {
        self.pass_meta = Some(Box::new(meta));
        let meta_ref: &dyn Any = self.pass_meta.as_deref().unwrap();
        for o in &mut self.optimizations {
            o.set_metadata_any(meta_ref);
        }
        self.by_tag.clear();
    }

    /// Return a *cloned* tiny list to avoid aliasing/borrow issues; cache the original.
    #[inline]
    fn interested_for(&mut self, tag: Discriminant<Inst>) -> SmallVec<[usize; 8]> {
        if let Some(v) = self.by_tag.get(&tag) {
            return v.clone();
        }
        let mut v: SmallVec<[usize; 8]> = SmallVec::new();
        for (i, opt) in self.optimizations.iter().enumerate() {
            if opt.maybe_interesting(tag) {
                v.push(i);
            }
        }
        self.by_tag.insert(tag, v.clone());
        v
    }

    /// Worklist, per-block; only revisit affected instructions.
    pub fn pass_optimizations(&mut self, func: &mut Function, recheck_window: usize) {
        // Rebuild func-local state once per pass.
        let mut fs = FuncState::new(func);
        let mut q = WirEditQueue::new();

        // ticketed "seen" bitmap to avoid requeue storms; one per function.
        let mut seen_ticket: Vec<u32> = vec![0; func.nodes.len()];
        let mut current_ticket: u32 = 1;

        // Process per block.
        for bix in 0..func.blocks.len() {
            // Fresh ticket per block run.
            current_ticket = current_ticket.wrapping_add(1);
            if current_ticket == 0 {
                current_ticket = 1;
                seen_ticket.fill(0);
            }

            // Seed worklist with a snapshot of ids.
            let seed = func.blocks[bix].insts.clone();
            let mut wl: VecDeque<InstId> = VecDeque::with_capacity(seed.len());
            for id in seed {
                wl.push_back(id);
                seen_ticket[id.0 as usize] = current_ticket;
            }

            // Pop/process.
            while let Some(id) = wl.pop_front() {
                let Some((cur_bix, mut pos)) = fs.pos_of(id) else {
                    continue;
                }; // deleted/moved
                if cur_bix != bix {
                    continue;
                } // moved to another block

                let blen = func.blocks[bix].insts.len();
                if blen == 0 || pos >= blen {
                    continue; // id deleted/moved; skip
                }
                let mut cur = InstCursor::new_ix(func, bix, pos);
                let tag = cur.cur_tag();

                // Run only interested opts.
                let interested = self.interested_for(tag);
                for ix in interested {
                    if self.optimizations[ix].optimize_node(&mut cur, &mut q) {
                        break;
                    }
                }

                // If edits for this block accumulated, apply and requeue local window.
                if q.has_any_for_block_ix(bix) {
                    q.apply_block(func, &mut fs, bix);

                    // Update pos of current id post-rebuild if it still exists here.
                    if let Some((nbix, npos)) = fs.pos_of(id) {
                        if nbix == bix {
                            pos = npos;
                        } else {
                            continue;
                        }
                    } else {
                        // Deleted: still requeue around former pos (best effort)
                    }

                    // Window [pos - recheck_window, pos + recheck_window]
                    let len = func.blocks[bix].insts.len();
                    if len == 0 {
                        continue;
                    }
                    let start = pos.saturating_sub(recheck_window);
                    let end = (pos + recheck_window + 1).min(len);
                    for i in start..end {
                        let nid = func.blocks[bix].insts[i];
                        if seen_ticket[nid.0 as usize] != current_ticket {
                            seen_ticket[nid.0 as usize] = current_ticket;
                            wl.push_back(nid);
                        }
                    }
                }
            }

            // Safety net: flush anything routed to other blocks (rare).
            if !q.is_empty() {
                q.route_all_compat(func);
                for obix in 0..func.blocks.len() {
                    if q.has_any_for_block_ix(obix) {
                        q.apply_block(func, &mut fs, obix);
                    }
                }
            }
        }
    }
}

/// =======================================
/// Optimizer façade (unchanged externally)
/// =======================================
pub struct Optimize {
    passes: SmallVec<[OptimizationPass; 4]>,
}
impl Default for Optimize {
    fn default() -> Self {
        Self {
            passes: SmallVec::new(),
        }
    }
}
impl Optimize {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn with_pass(mut self, pass: OptimizationPass) -> Self {
        self.passes.push(pass);
        self
    }

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
/// Minimal helpers to allocate new nodes/values
/// =======================================
pub struct InstFactory<'f> {
    func: &'f mut Function,
}
impl<'f> InstFactory<'f> {
    pub fn new(func: &'f mut Function) -> Self {
        Self { func }
    }

    pub fn create(
        &mut self,
        kind: Inst,
        node_ty: Option<Type>,
        result_tys: &[Option<Type>],
        effect_in: Option<ValueId>,
        effect_out: Option<ValueId>,
    ) -> (InstId, Vec<ValueId>) {
        let id = InstId(self.func.nodes.len() as u32);
        let mut results: SmallVec<[ValueId; 4]> = SmallVec::with_capacity(result_tys.len());
        for _ in 0..result_tys.len() {
            results.push(ValueId(
                self.func.values.len() as u32 + results.len() as u32,
            ));
        }
        let results_vec = results.clone().into_vec();
        self.func.nodes.push(crate::wir::Node {
            id,
            kind,
            ty: node_ty.clone(),
            effect_in,
            effect_out,
            results: results_vec.clone(),
        });
        self.func.values.reserve(result_tys.len());
        for (i, rty) in result_tys.iter().enumerate() {
            self.func.values.push(Value {
                id: ValueId(self.func.values.len() as u32),
                ty: rty.clone(),
                def: ValueDef::InstResult(id, i as u8),
            });
        }
        (id, results_vec)
    }
}

/// =======================================
/// Convenience shims for opts (IX-based API)
/// =======================================
pub trait EditQueueExt {
    fn insert_before_cur(&mut self, cur: &InstCursor, insts: impl Into<SmallVec<[InstId; 4]>>);
    fn insert_after_cur(&mut self, cur: &InstCursor, insts: impl Into<SmallVec<[InstId; 4]>>);
    fn erase_cur(&mut self, cur: &InstCursor);
    fn replace_cur_kind(&mut self, cur: &mut InstCursor, new_kind: Inst);
    fn splice_cur_range(
        &mut self,
        cur: &InstCursor,
        start: usize,
        end: usize,
        insts: impl Into<SmallVec<[InstId; 4]>>,
    );
}

impl EditQueueExt for WirEditQueue {
    #[inline]
    fn insert_before_cur(&mut self, cur: &InstCursor, insts: impl Into<SmallVec<[InstId; 4]>>) {
        self.insert_before_ix(cur.block_index(), cur.pos(), insts)
    }
    #[inline]
    fn insert_after_cur(&mut self, cur: &InstCursor, insts: impl Into<SmallVec<[InstId; 4]>>) {
        self.insert_after_ix(cur.block_index(), cur.pos(), insts)
    }
    #[inline]
    fn erase_cur(&mut self, cur: &InstCursor) {
        self.erase_ix(cur.block_index(), cur.pos())
    }
    #[inline]
    fn replace_cur_kind(&mut self, cur: &mut InstCursor, new_kind: Inst) {
        cur.with_cur(|n| {
            let _old = replace(&mut n.kind, new_kind);
        });
    }
    #[inline]
    fn splice_cur_range(
        &mut self,
        cur: &InstCursor,
        start: usize,
        end: usize,
        insts: impl Into<SmallVec<[InstId; 4]>>,
    ) {
        self.splice_range_ix(cur.block_index(), start, end, insts)
    }
}
