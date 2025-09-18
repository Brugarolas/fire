// src/opt/pass/dse.rs
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use ahash::{AHashMap as HashMap, AHashSet as HashSet};

use crate::opt::{OptimizationWIR, WirEditQueue, InstCursor};
use crate::opt::helpers::value_as_i32;
use crate::wir::{
    Function, BlockId, Inst, InstId, ValueId, ValueDef, FieldId, Constant, Type,
};

/// Dead Store Elimination:
///  * Intra-block, backwards pass.
///  * Tracks locations:
///      - Object field:      (obj, field)
///      - Array element:     (arr, const idx)   [only when idx is known i32]
///      - Array length:      arr
///      - Closure env slot:  (clos, index)
///  * A store is dead if a later store to the **same precise location** exists
///    with no intervening read or unknown effect.
///  * Any instruction with `needs_effect_in()` (except the store/ barrier kinds
///    themselves) conservatively **flushes** the write-sets.
///  * If we delete a store, and the **next instruction** in the same block is a
///    `PostWriteBarrier` with matching `(obj,val)`, we delete that too.
pub struct DeadStoreElim {
    ran: bool,
}

impl Default for DeadStoreElim {
    fn default() -> Self { Self { ran: false } }
}

impl DeadStoreElim {
    pub fn new() -> Self { Self::default() }

    pub fn run(&mut self, func: &mut Function) {
        if self.ran { return; }
        self.ran = true;

        loop {
            let mut changed = false;
            let mut q = WirEditQueue::new();

            for b in &func.blocks {
                // Backward scan state
                let mut last_field_store: HashSet<(ValueId, FieldId)> = HashSet::new();
                let mut last_elem_store:  HashSet<(ValueId, i32)>     = HashSet::new();
                let mut last_len_store:   HashSet<ValueId>            = HashSet::new();
                let mut last_env_store:   HashSet<(ValueId, u32)>     = HashSet::new();

                // To also drop immediate barriers after dead stores
                let mut to_erase_positions: Vec<usize> = Vec::new();

                // Helper: canonicalize value identity by peeling short Mov chains
                #[inline]
                fn rep(func: &Function, mut v: ValueId) -> ValueId {
                    for _ in 0..6 {
                        match &func.values[v.0 as usize].def {
                            ValueDef::InstResult(iid, _ix) => {
                                if let Inst::Mov(src) = func.nodes[iid.0 as usize].kind {
                                    v = src; continue;
                                }
                            }
                            _ => {}
                        }
                        break;
                    }
                    v
                }

                // Helper: unknown effect — flush write-sets conservatively
                #[inline]
                fn flush_all(
                    last_field: &mut HashSet<(ValueId, FieldId)>,
                    last_elem: &mut HashSet<(ValueId, i32)>,
                    last_len: &mut HashSet<ValueId>,
                    last_env: &mut HashSet<(ValueId, u32)>,
                ) {
                    last_field.clear();
                    last_elem.clear();
                    last_len.clear();
                    last_env.clear();
                }

                // Scan block backwards
                for (pos, &nid) in b.insts.iter().enumerate().rev() {
                    let k = &func.nodes[nid.0 as usize].kind;

                    match k {
                        // ================= READS =================
                        Inst::LoadField { obj, field, .. } => {
                            let o = rep(func, *obj);
                            last_field_store.remove(&(o, *field));
                        }
                        Inst::LoadElem { arr, idx } => {
                            let a = rep(func, *arr);
                            if let Some(i) = value_as_i32(func, *idx) {
                                last_elem_store.remove(&(a, i));
                            } else {
                                // unknown index read: clear all elem writes for this array
                                last_elem_store.retain(|(aa, _)| *aa != a);
                            }
                        }
                        Inst::ArrayLen(arr) => {
                            let a = rep(func, *arr);
                            last_len_store.remove(&a);
                        }
                        Inst::LoadEnv { clos, index } => {
                            let c = rep(func, *clos);
                            last_env_store.remove(&(c, *index));
                        }

                        // ================= WRITES =================
                        Inst::StoreField { obj, field, val, .. } => {
                            let o = rep(func, *obj);
                            let loc = (o, *field);
                            if last_field_store.contains(&loc) {
                                // Dead store — it will be overwritten before any read.
                                let real_pos = pos;
                                to_erase_positions.push(real_pos);
                                // If immediate next inst is a matching PostWriteBarrier, drop it too.
                                if pos + 1 < b.insts.len() {
                                    if let Inst::PostWriteBarrier { obj: bo, val: bv } =
                                        func.nodes[b.insts[pos + 1].0 as usize].kind
                                    {
                                        let o2 = rep(func, bo);
                                        let v2 = rep(func, bv);
                                        if o2 == o && v2 == rep(func, *val) {
                                            to_erase_positions.push(pos + 1);
                                        }
                                    }
                                }
                                // Keep tracking the last (later) store in the set
                            } else {
                                last_field_store.insert(loc);
                            }
                        }

                        Inst::StoreElem { arr, idx, val } => {
                            let a = rep(func, *arr);
                            if let Some(i) = value_as_i32(func, *idx) {
                                let loc = (a, i);
                                if last_elem_store.contains(&loc) {
                                    // Dead store to same const element
                                    to_erase_positions.push(pos);
                                    if pos + 1 < b.insts.len() {
                                        if let Inst::PostWriteBarrier { obj: bo, val: bv } =
                                            func.nodes[b.insts[pos + 1].0 as usize].kind
                                        {
                                            let o2 = rep(func, bo);
                                            let v2 = rep(func, bv);
                                            if o2 == a && v2 == rep(func, *val) {
                                                to_erase_positions.push(pos + 1);
                                            }
                                        }
                                    }
                                } else {
                                    last_elem_store.insert(loc);
                                }
                            } else {
                                // Unknown index store does not guarantee overwrite of any particular element.
                                // It also does not help us prove earlier stores dead. Do nothing.
                            }
                        }

                        Inst::ArraySetLen { arr, .. } => {
                            let a = rep(func, *arr);
                            if last_len_store.contains(&a) {
                                to_erase_positions.push(pos);
                            } else {
                                last_len_store.insert(a);
                            }
                        }

                        Inst::StoreEnv { clos, index, val } => {
                            let c = rep(func, *clos);
                            let key = (c, *index);
                            if last_env_store.contains(&key) {
                                to_erase_positions.push(pos);
                            } else {
                                last_env_store.insert(key);
                            }
                        }

                        // ================= BARRIERS / NO-OPS =================
                        Inst::PostWriteBarrier { .. } => {
                            // Handled when erasing a store; by itself, do not flush.
                        }
                        Inst::EffectEntry | Inst::Safepoint => {
                            // Be conservative around safepoints; they may observe memory via GC.
                            flush_all(&mut last_field_store, &mut last_elem_store, &mut last_len_store, &mut last_env_store);
                        }

                        // ================= CONTROL / PURE =================
                        Inst::Phi(_) | Inst::Const(_) | Inst::Mov(_)
                        | Inst::CmpInt { .. } | Inst::CmpF64 { .. } | Inst::CmpRefEq { .. }
                        | Inst::IntBin { .. } | Inst::F64Bin { .. }
                        | Inst::NumAdd(_,_) | Inst::NumSub(_,_) | Inst::NumMul(_,_) | Inst::NumDiv(_,_) | Inst::NumRem(_,_)
                        | Inst::StrLen(_) | Inst::StrConcat { .. } | Inst::StrSlice { .. }
                        | Inst::StrCompare { .. } | Inst::StrContains { .. } | Inst::StrToNumber(_)
                        | Inst::ArrayLen(_) | Inst::ArraySlice { .. }
                        => {
                            // Pure or modeled loads handled above; nothing to do.
                        }

                        // ================= UNKNOWN EFFECTS =================
                        _ => {
                            // Any other effectful instruction (calls, allocs, guards, transitions, map/filter/etc.)
                            // could read memory we track (or make it observable), so flush conservatively.
                            if func.nodes[nid.0 as usize].kind.needs_effect_in() {
                                // NOTE: we keep `PostWriteBarrier` out of this branch above.
                                flush_all(&mut last_field_store, &mut last_elem_store, &mut last_len_store, &mut last_env_store);
                            }
                        }
                    }
                }

                if !to_erase_positions.is_empty() {
                    to_erase_positions.sort_unstable();
                    to_erase_positions.drain(..).rev().for_each(|p| q.erase(b.id, p));
                    changed = true;
                }
            }

            if !changed {
                if !q.is_empty() { q.apply(func); }
                break;
            }
            q.apply(func);
        }
    }
}

impl OptimizationWIR for DeadStoreElim {
    fn optimize_node(&mut self, cur: &mut InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| self.run(f));
        false
    }
}
