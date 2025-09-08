// src/opts/mega_dce.rs
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use ahash::{AHashSet as HashSet, AHashMap as HashMap};

use crate::opt::{OptimizationWIR, WirEditQueue};
use crate::wir::{Function, Inst, BlockId, ValueId, ValueDef};

pub struct MegaDCE {
    ran: bool,
}

impl Default for MegaDCE {
    fn default() -> Self { Self { ran: false } }
}

impl MegaDCE {
    pub fn new() -> Self { Self::default() }

    pub fn run(&mut self, func: &mut Function) {
        if self.ran { return; }
        self.ran = true;

        loop {
            let mut changed = false;
            let mut q = WirEditQueue::new();

            // 1) Compute reachability from entry.
            let reachable = compute_reachable(func);

            // 2) Erase every instruction in unreachable blocks.
            for b in &func.blocks {
                if !reachable.contains(&b.id) {
                    for pos in (0..b.insts.len()).rev() {
                        q.erase(b.id, pos);
                        changed = true;
                    }
                }
            }

            // 3) Remove any instructions that appear *after* the first terminator.
            for b in &func.blocks {
                if !reachable.contains(&b.id) { continue; }
                let mut killed_tail = false;
                let mut first_term: Option<usize> = None;
                for (i, &nid) in b.insts.iter().enumerate() {
                    if first_term.is_none() && is_terminator(&func.nodes[nid.0 as usize].kind) {
                        first_term = Some(i);
                        continue;
                    }
                    if first_term.is_some() {
                        q.erase(b.id, i);
                        killed_tail = true;
                    }
                }
                if killed_tail { changed = true; }
            }

            // 4) Recompute reachability (tail removal may cut paths) before DCE.
            let reachable = compute_reachable(func);

            // 5) Build global use counts for values (only from *reachable* blocks).
            let mut uses = vec![0usize; func.values.len()];
            for b in &func.blocks {
                if !reachable.contains(&b.id) { continue; }
                for &nid in &b.insts {
                    let k = &func.nodes[nid.0 as usize].kind;
                    bump_uses_for_inst(&mut uses, k);
                }
            }

            // 6) Aggressive DCE on pure value-only instructions (and dead Phis).
            for b in &func.blocks {
                if !reachable.contains(&b.id) { continue; }

                for (pos, &nid) in b.insts.iter().enumerate() {
                    let node = &func.nodes[nid.0 as usize];
                    let k = &node.kind;

                    // Keep control & side-effecting ops.
                    if is_terminator(k) || is_effectful(k) {
                        continue;
                    }

                    // If it's a Phi with zero uses, kill it (common after CFG simplifications).
                    // (Phis are value-only in this IR.)
                    let is_phi = matches!(k, Inst::Phi(_));

                    // All-result-unused test (most nodes have 0 or 1 result).
                    let all_unused = node.results.iter().all(|&v| {
                        let ix = v.0 as usize;
                        ix >= uses.len() || uses[ix] == 0
                    });

                    if is_phi && all_unused {
                        q.erase(b.id, pos);
                        changed = true;
                        continue;
                    }

                    // Generic pure DCE: if pure and all results unused, erase it.
                    if is_pure_value(k) && all_unused {
                        q.erase(b.id, pos);
                        changed = true;
                        continue;
                    }
                }
            }

            if !changed {
                // Nothing else to do.
                if !q.is_empty() { q.apply(func); } // no-op but safe
                break;
            }

            q.apply(func);
            // loop to fixed point
        }
    }
}

impl OptimizationWIR for MegaDCE {
    fn optimize_node(&mut self, cur: &mut crate::opt::InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| self.run(f));
        false
    }
}

// -------------------------- internals --------------------------

fn is_terminator(k: &Inst) -> bool {
    matches!(k, Inst::Return(_)
                | Inst::Branch { .. }
                | Inst::Jump(_, _)
                | Inst::Throw(_)
                | Inst::Switch { .. })
}

fn is_effectful(k: &Inst) -> bool {
    k.needs_effect_in()
}

fn is_pure_value(k: &Inst) -> bool {
    // Value-only & pure: no effects, not control, not bookkeeping-only.
    !is_effectful(k) && !is_terminator(k) && !matches!(k, Inst::EffectEntry | Inst::Safepoint)
}

/// Compute the set of blocks reachable from the entry by following terminator edges.
fn compute_reachable(func: &Function) -> HashSet<BlockId> {
    let mut seen: HashSet<BlockId> = HashSet::new();
    let mut stack: Vec<BlockId> = vec![func.entry];

    while let Some(bid) = stack.pop() {
        if !seen.insert(bid) { continue; }
        // Collect successors from the (first) terminator in the block.
        if let Some(block) = func.blocks.iter().find(|b| b.id == bid) {
            // Find the first terminator in the block (if any).
            for &nid in &block.insts {
                let k = &func.nodes[nid.0 as usize].kind;
                if is_terminator(k) {
                    match k {
                        Inst::Jump(t, _) => stack.push(*t),
                        Inst::Branch { then_b, else_b, .. } => {
                            stack.push(*then_b);
                            stack.push(*else_b);
                        }
                        Inst::Switch { default_b, table, .. } => {
                            stack.push(*default_b);
                            for &(_, blk) in table { stack.push(blk); }
                        }
                        Inst::Return(_) | Inst::Throw(_) => {}
                        _ => {}
                    }
                    break; // Only the first terminator defines control flow.
                }
            }
        }
    }

    seen
}

/// Enumerate operands and bump `uses[v]` for each occurrence.
/// Keep in sync with the IR; conservative overcounting is safe for DCE.
fn bump_uses_for_inst(uses: &mut [usize], k: &Inst) {
    #[inline]
    fn bump(uses: &mut [usize], v: ValueId) {
        if v.0 as usize >= uses.len() { return; }
        uses[v.0 as usize] += 1;
    }

    match k {
        // ---- Control ----
        Inst::Phi(vals)                           => for &v in vals { bump(uses, v); }
        Inst::Jump(_b, args)                      => for &v in args { bump(uses, v); }
        Inst::Branch { cond, .. }                 => bump(uses, *cond),
        Inst::Switch { tag, .. }                  => bump(uses, *tag),
        Inst::Return(vals)                        => for &v in vals { bump(uses, v); }
        Inst::Throw(v)                            => bump(uses, *v),

        // ---- Effect / bookkeeping ----
        Inst::EffectEntry | Inst::Safepoint       => {},

        // ---- Constants / moves ----
        Inst::Const(_)                            => {},
        Inst::Mov(v)                              => bump(uses, *v),

        // ---- Guards ----
        Inst::GuardType { val, .. }               => bump(uses, *val),
        Inst::GuardShape { obj, .. }              => bump(uses, *obj),
        Inst::GuardBounds { idx, len, .. }        => { bump(uses, *idx); bump(uses, *len); }
        Inst::GuardNotNull { val, .. }            => bump(uses, *val),
        Inst::GuardIsInt { val, .. }              => bump(uses, *val),
        Inst::GuardIsF64 { val, .. }              => bump(uses, *val),
        Inst::Bailout { .. }                      => {},

        // ---- Objects ----
        Inst::AllocObj { .. }                     => {},
        Inst::LoadField { obj, .. }               => bump(uses, *obj),
        Inst::StoreField { obj, val, .. }         => { bump(uses, *obj); bump(uses, *val); }
        Inst::TransitionShape { obj, .. }         => bump(uses, *obj),

        // ---- Arrays ----
        Inst::AllocArray { len, .. }              => bump(uses, *len),
        Inst::ArrayLen(v)                         => bump(uses, *v),
        Inst::ArraySetLen { arr, new_len }        => { bump(uses, *arr); bump(uses, *new_len); }
        Inst::LoadElem { arr, idx }               => { bump(uses, *arr); bump(uses, *idx); }
        Inst::StoreElem { arr, idx, val }         => { bump(uses, *arr); bump(uses, *idx); bump(uses, *val); }
        Inst::ArraySlice { arr, start, end }      => { bump(uses, *arr); bump(uses, *start); bump(uses, *end); }

        // Array methods / higher-level ops
        Inst::ArrayPush { arr, val }              => { bump(uses, *arr); bump(uses, *val); }
        Inst::ArrayPop(arr)                       => bump(uses, *arr),
        Inst::ArrayShift(arr)                     => bump(uses, *arr),
        Inst::ArrayUnshift { arr, val }           => { bump(uses, *arr); bump(uses, *val); }

        Inst::ArrayMap { arr, .. }                => bump(uses, *arr),
        Inst::ArrayReduce { init, arr, .. }       => { bump(uses, *init); bump(uses, *arr); }
        Inst::ArrayFill { arr, val }              => { bump(uses, *arr); bump(uses, *val); }
        Inst::ArrayCopy { dst, src, len }         => { bump(uses, *dst); bump(uses, *src); bump(uses, *len); }

        Inst::ArrayForEach { arr, .. }            => bump(uses, *arr),
        Inst::ArrayFind { arr, .. }               => bump(uses, *arr),
        Inst::ArrayFindIndex { arr, .. }          => bump(uses, *arr),
        Inst::ArrayFilter { arr, .. }             => bump(uses, *arr),

        // ---- Strings ----
        Inst::StrLen(s)                           => bump(uses, *s),
        Inst::StrConcat { a, b }                  => { bump(uses, *a); bump(uses, *b); }
        Inst::StrSlice { s, start, end }          => { bump(uses, *s); bump(uses, *start); bump(uses, *end); }
        Inst::StrCompare { a, b }                 => { bump(uses, *a); bump(uses, *b); }
        Inst::StrContains { s, sub }              => { bump(uses, *s); bump(uses, *sub); }
        Inst::StrToNumber(s)                      => bump(uses, *s),

        // ---- Numerics ----
        Inst::IntBin { a, b, .. }                 => { bump(uses, *a); bump(uses, *b); }
        Inst::F64Bin { a, b, .. }                 => { bump(uses, *a); bump(uses, *b); }
        Inst::NumAdd(a, b) | Inst::NumSub(a, b)
        | Inst::NumMul(a, b) | Inst::NumDiv(a, b)
        | Inst::NumRem(a, b)                      => { bump(uses, *a); bump(uses, *b); }
        Inst::CmpInt { a, b, .. }                 => { bump(uses, *a); bump(uses, *b); }
        Inst::CmpF64 { a, b, .. }                 => { bump(uses, *a); bump(uses, *b); }
        Inst::CmpRefEq { a, b }                   => { bump(uses, *a); bump(uses, *b); }

        // ---- Boxing / tagging ----
        Inst::BoxInt(v) | Inst::BoxF64(v)
        | Inst::BoxBool(v) | Inst::UnboxToInt(v)
        | Inst::UnboxToF64(v)                     => bump(uses, *v),

        // ---- Calls / closures ----
        Inst::CallDirect { args, .. }             => for &v in args { bump(uses, v); }
        Inst::CallDirectMemoized { args, .. }     => for &v in args { bump(uses, v); }
        Inst::CallIC { recv, args, .. }           => { bump(uses, *recv); for &v in args { bump(uses, v); } }
        Inst::MethodLookup { obj, .. }            => bump(uses, *obj),
        Inst::AllocClosure { .. }                 => {}
        Inst::LoadEnv { clos, .. }                => bump(uses, *clos),
        Inst::StoreEnv { clos, val, .. }          => { bump(uses, *clos); bump(uses, *val); }
        Inst::MakeClosure { env, .. }             => bump(uses, *env),
        Inst::CallClosure { fun, args, .. }       => { bump(uses, *fun); for &v in args { bump(uses, v); } }

        // ---- Native / intrinsics ----
        Inst::CallNative { args, .. }             => for &v in args { bump(uses, v); }

        // ---- GC barriers ----
        Inst::PostWriteBarrier { obj, val }       => { bump(uses, *obj); bump(uses, *val); }
        Inst::ReadBarrier { obj }                 => bump(uses, *obj),

        // ---- OSR ----
        Inst::OSRPoint                             => {},

        _ => { /* skip other instructions */ }
    }
}
