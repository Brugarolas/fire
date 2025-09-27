#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use ahash::{AHashMap as HashMap, AHashSet as HashSet};
use std::mem::{Discriminant, discriminant};

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::wir::{BlockId, Function, Inst, InstId, ValueDef, ValueId};

pub struct DCE {
    last_func_ptr: Option<usize>,
}

impl Default for DCE {
    fn default() -> Self {
        Self {
            last_func_ptr: None,
        }
    }
}
impl DCE {
    pub fn new() -> Self {
        Self::default()
    }
}

impl OptimizationWIR for DCE {
    /// Wake up on control-flow-ish things (enough to trigger once per function).
    fn maybe_interesting(&self, tag: Discriminant<Inst>) -> bool {
        use crate::wir::Inst::*;
        let v0 = ValueId(0);
        let tags = [
            discriminant(&Return(Vec::<ValueId>::new())),
            discriminant(&Branch {
                cond: v0,
                then_b: BlockId(0),
                else_b: BlockId(0),
            }),
            discriminant(&Jump(BlockId(0), Vec::<ValueId>::new())),
            discriminant(&Throw(v0)),
            // Keep Switch construction out (field-shape differences), we’ll still
            // be triggered by the others and by regular instructions.
        ];
        tags.contains(&tag)
    }

    fn optimize_node(&mut self, cur: &mut InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| {
            let ptr = f as *mut Function as usize;
            if self.last_func_ptr != Some(ptr) {
                self.last_func_ptr = Some(ptr);
                run_mega_dce(f);
            }
        });
        false
    }
}

/* ================= core ================= */

fn run_mega_dce(func: &mut Function) {
    if func.blocks.is_empty() {
        return;
    }

    loop {
        let mut changed_any = false;
        let mut q = WirEditQueue::new();

        // Fast BlockId <-> index
        let mut bix_of: HashMap<BlockId, usize> = HashMap::with_capacity(func.blocks.len());
        for (i, b) in func.blocks.iter().enumerate() {
            bix_of.insert(b.id, i);
        }

        // 1) Reachability (from entry), using first terminator’s edges per block
        let reachable = compute_reachable_vec(func, &bix_of);

        // 2) Nuke everything in unreachable blocks
        for (bi, b) in func.blocks.iter().enumerate() {
            if !reachable[bi] {
                if !b.insts.is_empty() {
                    changed_any = true;
                    for pos in (0..b.insts.len()).rev() {
                        q.erase_ix(bi, pos);
                    }
                }
            }
        }

        // 3) In reachable blocks, remove instructions after the first terminator
        for (bi, b) in func.blocks.iter().enumerate() {
            if !reachable[bi] {
                continue;
            }
            let mut first_term: Option<usize> = None;
            for (i, &nid) in b.insts.iter().enumerate() {
                if first_term.is_none() && is_terminator(&func.nodes[nid.0 as usize].kind) {
                    first_term = Some(i);
                    continue;
                }
                if first_term.is_some() {
                    q.erase_ix(bi, i);
                    changed_any = true;
                }
            }
        }

        // If we changed CFG shape, apply before recomputing reachability/uses.
        if changed_any {
            q.apply(func);
        }

        // 4) Recompute reachability post-tail-cut (fresh maps)
        let mut bix_of: HashMap<BlockId, usize> = HashMap::with_capacity(func.blocks.len());
        for (i, b) in func.blocks.iter().enumerate() {
            bix_of.insert(b.id, i);
        }
        let reachable = compute_reachable_vec(func, &bix_of);

        // 5) Build use counts for values (only scanning reachable blocks)
        let mut uses = vec![0usize; func.values.len()];
        for (bi, b) in func.blocks.iter().enumerate() {
            if !reachable[bi] {
                continue;
            }
            for &nid in &b.insts {
                let k = &func.nodes[nid.0 as usize].kind;
                bump_uses_for_inst(&mut uses, k);
            }
        }

        // 6) Aggressive DCE: dead pure value producers and dead Phis
        let mut phase2_changed = false;
        for (bi, b) in func.blocks.iter().enumerate() {
            if !reachable[bi] {
                continue;
            }
            for (pos, &nid) in b.insts.iter().enumerate() {
                let node = &func.nodes[nid.0 as usize];
                let k = &node.kind;

                // Keep control & effectful ops.
                if is_terminator(k) || is_effectful(k) {
                    continue;
                }

                // Dead Phi?
                let is_phi = matches!(k, Inst::Phi(_));
                let all_unused = node.results.iter().all(|&v| {
                    let ix = v.0 as usize;
                    ix >= uses.len() || uses[ix] == 0
                });

                if (is_phi && all_unused) || (is_pure_value(k) && all_unused) {
                    q.erase_ix(bi, pos);
                    phase2_changed = true;
                }
            }
        }

        if phase2_changed {
            q.apply(func);
        }

        if !(changed_any || phase2_changed) {
            // No more progress this iteration — we’re done.
            break;
        }
        // Otherwise, iterate to fixed point.
    }
}

/* =============== helpers =============== */

#[inline]
fn is_terminator(k: &Inst) -> bool {
    use Inst::*;
    matches!(
        k,
        Return(_) | Branch { .. } | Jump(_, _) | Throw(_) | Switch { .. }
    )
}

#[inline]
fn is_effectful(k: &Inst) -> bool {
    k.needs_effect_in()
}

#[inline]
fn is_pure_value(k: &Inst) -> bool {
    // Value-only & pure: no effects, not control, not bookkeeping-only.
    !is_effectful(k) && !is_terminator(k) && !matches!(k, Inst::EffectEntry | Inst::Safepoint)
}

/// Reachability from entry using the *first terminator* (after prior tail trimming).
fn compute_reachable_vec(func: &Function, bix_of: &HashMap<BlockId, usize>) -> Vec<bool> {
    let n = func.blocks.len();
    let mut reach = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    if let Some(&entry) = bix_of.get(&func.entry) {
        stack.push(entry);
    }

    while let Some(bi) = stack.pop() {
        if reach[bi] {
            continue;
        }
        reach[bi] = true;

        let b = &func.blocks[bi];
        // Walk to the first terminator, then add edges.
        for &nid in &b.insts {
            let k = &func.nodes[nid.0 as usize].kind;
            if is_terminator(k) {
                use Inst::*;
                match k {
                    Jump(t, _) => stack.push(bix_of[t]),
                    Branch { then_b, else_b, .. } => {
                        stack.push(bix_of[then_b]);
                        stack.push(bix_of[else_b]);
                    }
                    Switch {
                        default_b, table, ..
                    } => {
                        stack.push(bix_of[default_b]);
                        for &(_, blk) in table {
                            stack.push(bix_of[&blk]);
                        }
                    }
                    Return(_) | Throw(_) => {}
                    _ => {}
                }
                break;
            }
        }
    }
    reach
}

/// Enumerate operands and bump `uses[v]` for each occurrence.
/// Keep in sync with the IR; conservative overcounting is safe for DCE.
/// Enumerate operands and bump `uses[v]` for each occurrence.
fn bump_uses_for_inst(uses: &mut [usize], k: &Inst) {
    #[inline]
    fn bump(uses: &mut [usize], v: ValueId) {
        let i = v.0 as usize;
        if i < uses.len() {
            uses[i] += 1;
        }
    }

    // A helper for instructions with a common `(receiver, [args...])` pattern
    fn bump_recv_args(uses: &mut [usize], recv: ValueId, args: &[ValueId]) {
        bump(uses, recv);
        for &arg in args {
            bump(uses, arg);
        }
    }

    match k {
        // ---- Control ----
        Inst::Phi(vals) => vals.iter().for_each(|&v| bump(uses, v)),
        Inst::Jump(_b, args) => args.iter().for_each(|&v| bump(uses, v)),
        Inst::Branch { cond, .. } => bump(uses, *cond),
        Inst::Switch { tag, .. } => bump(uses, *tag),
        Inst::Return(vals) => vals.iter().for_each(|&v| bump(uses, v)),
        Inst::Throw(v) => bump(uses, *v),

        // ---- Effect / bookkeeping ----
        Inst::EffectEntry | Inst::Safepoint | Inst::OSRPoint => {}

        // ---- Constants / moves ----
        Inst::Const(_) => {}
        Inst::Mov(v) => bump(uses, *v),

        // ---- Guards ----
        Inst::GuardType { val, .. } => bump(uses, *val),
        Inst::GuardShape { obj, .. } => bump(uses, *obj),
        Inst::GuardBounds { idx, len, .. } => {
            bump(uses, *idx);
            bump(uses, *len);
        }
        Inst::GuardNotNull { val, .. } => bump(uses, *val),
        Inst::GuardIsInt { val, .. } => bump(uses, *val),
        Inst::GuardIsF64 { val, .. } => bump(uses, *val),
        Inst::Bailout { .. } => {}

        // ---- Objects & Classes ----
        Inst::AllocObj { .. } | Inst::AllocInstance { .. } => {}
        Inst::LoadField { obj, .. } => bump(uses, *obj),
        Inst::StoreField { obj, val, .. } => {
            bump(uses, *obj);
            bump(uses, *val);
        }
        Inst::TransitionShape { obj, .. } => bump(uses, *obj),
        Inst::LoadMethod { obj, .. } => bump(uses, *obj),
        Inst::LoadSuperMethod { recv, .. } => bump(uses, *recv),
        Inst::InstanceOf { obj, .. } => bump(uses, *obj),
        
        // ---- Arrays ----
        Inst::AllocArray { len, .. } => bump(uses, *len),
        Inst::ArrayLen(v) => bump(uses, *v),
        Inst::ArraySetLen { arr, new_len } => {
            bump(uses, *arr);
            bump(uses, *new_len);
        }
        Inst::LoadElem { arr, idx } => {
            bump(uses, *arr);
            bump(uses, *idx);
        }
        Inst::StoreElem { arr, idx, val } => {
            bump(uses, *arr);
            bump(uses, *idx);
            bump(uses, *val);
        }
        Inst::ArraySlice { arr, start, end } => {
            bump(uses, *arr);
            bump(uses, *start);
            bump(uses, *end);
        }
        Inst::ArrayPush { arr, val } => {
            bump(uses, *arr);
            bump(uses, *val);
        }
        Inst::ArrayPop(arr) | Inst::ArrayShift(arr) => bump(uses, *arr),
        Inst::ArrayUnshift { arr, val } => {
            bump(uses, *arr);
            bump(uses, *val);
        }
        Inst::ArrayMap { arr, .. } => bump(uses, *arr),
        Inst::ArrayReduce { init, arr, .. } => {
            bump(uses, *init);
            bump(uses, *arr);
        }
        Inst::ArrayFill { arr, val } => {
            bump(uses, *arr);
            bump(uses, *val);
        }
        Inst::ArrayCopy { dst, src, len } => {
            bump(uses, *dst);
            bump(uses, *src);
            bump(uses, *len);
        }
        Inst::ArrayForEach { arr, .. }
        | Inst::ArrayFind { arr, .. }
        | Inst::ArrayFindIndex { arr, .. }
        | Inst::ArrayFilter { arr, .. } => bump(uses, *arr),

        // ---- Strings ----
        Inst::StrLen(s) => bump(uses, *s),
        Inst::StrConcat { a, b } | Inst::StrCompare { a, b } => {
            bump(uses, *a);
            bump(uses, *b);
        }
        Inst::StrSlice { s, start, end } => {
            bump(uses, *s);
            bump(uses, *start);
            bump(uses, *end);
        }
        Inst::StrContains { s, sub } => {
            bump(uses, *s);
            bump(uses, *sub);
        }
        Inst::StrToNumber(s) => bump(uses, *s),

        // ---- Numerics ----
        Inst::IntBin { a, b, .. }
        | Inst::F64Bin { a, b, .. }
        | Inst::NumAdd(a, b)
        | Inst::NumSub(a, b)
        | Inst::NumMul(a, b)
        | Inst::NumDiv(a, b)
        | Inst::NumRem(a, b)
        | Inst::CmpInt { a, b, .. }
        | Inst::CmpF64 { a, b, .. }
        | Inst::CmpRefEq { a, b } => {
            bump(uses, *a);
            bump(uses, *b);
        }

        // ---- Boxing / tagging ----
        Inst::BoxInt(v)
        | Inst::BoxF64(v)
        | Inst::BoxBool(v)
        | Inst::UnboxToInt(v)
        | Inst::UnboxToF64(v) => bump(uses, *v),

        // ---- Calls / closures ----
        Inst::CallDirect { args, .. } 
        | Inst::CallDirectMemoized { args, .. } => args.iter().for_each(|&v| bump(uses, v)),
        Inst::CallIC { recv, args, .. } => bump_recv_args(uses, *recv, args),
        Inst::CallMethodIC { recv, args, .. } => bump_recv_args(uses, *recv, args),
        Inst::CallSuper { recv, args, .. } => bump_recv_args(uses, *recv, args),
        Inst::MethodLookup { obj, .. } => bump(uses, *obj),
        Inst::AllocClosure { .. } => {} // Produces a value, has no ValueId operands
        Inst::LoadEnv { clos, .. } => bump(uses, *clos),
        Inst::StoreEnv { clos, val, .. } => {
            bump(uses, *clos);
            bump(uses, *val);
        }
        Inst::MakeClosure { env, .. } => bump(uses, *env),
        Inst::CallClosure { fun, args, .. } => {
            bump(uses, *fun);
            args.iter().for_each(|&v| bump(uses, v));
        }

        // ---- Natives / Timers / GC ----
        Inst::CallNative { args, .. } => args.iter().for_each(|&v| bump(uses, v)),
        Inst::SetTimeout { fun, delay_ms } => {
            bump(uses, *fun);
            bump(uses, *delay_ms);
        }
        Inst::SetInterval { fun, period_ms } => {
            bump(uses, *fun);
            bump(uses, *period_ms);
        }
        Inst::ClearTimeout { id } | Inst::ClearInterval { id } => bump(uses, *id),
        Inst::PostWriteBarrier { obj, val } => {
            bump(uses, *obj);
            bump(uses, *val);
        }
        Inst::ReadBarrier { obj } => bump(uses, *obj),

        // ---- Modules / ESM ----
        // This was the critical missing case!
        Inst::StoreBinding { val, .. } => bump(uses, *val),
        // These produce values but have no ValueId operands
        Inst::LoadBinding { .. } | Inst::MakeNamespace { .. } => {}
        // This one was also missing
        Inst::ImportDynamic { spec } => bump(uses, *spec),

        // ---- Classes (that were not covered yet) ----
        // These instructions use IDs, not ValueIds, so they don't need bumping
        Inst::RegisterClass { .. } => {}

        // ---- Other ----
        _ => {}
    }
}
