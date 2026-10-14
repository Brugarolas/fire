// src/opt/pass/rle_lsf.rs
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::collections::{HashMap, HashSet};

use crate::opt::helpers::value_as_i32;
use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::wir::{BlockId, Constant, FieldId, Function, Inst, InstId, Type, ValueDef, ValueId};

/// Redundant Load Elimination + Load–Store Forwarding (intra-block)
///
/// Tracks last-known values for precise memory locations while scanning a block
/// **forward**. When we see a load:
///   - if we have a known value for that location, rewrite to `Mov(known_val)`.
///   - otherwise, record this load's result as the leader for that location.
///
/// When we see a write:
///   - update the tracked value for the precise location to the stored `ValueId`
///     (forwards later loads), or invalidate a whole family when the store is
///     imprecise (unknown array index, bulk ops, etc.).
///
/// Any **unknown effect** (calls, map/reduce/filter, etc.) conservatively
/// flushes all tracked maps. We special-case fine-grained updates for the
/// known write operations (StoreField/StoreElem/ArraySetLen/StoreEnv) and avoid
/// flushing for harmless barriers.
///
/// Locations we track:
///   - Field      : (obj_rep, field)
///   - Elem       : (arr_rep, const_i32_index)
///   - Array Length : arr_rep
///   - Env Slot   : (clos_rep, u32_index)
///
/// Notes:
///   - Intra-block only (fast, robust). Inter-block redundancy will usually be
///     removed by your CSE/SCCP/SimplifyCFG passes anyway.
///   - Peels short Mov chains to stabilize object/array identities & stored values.
pub struct RedundantLoadElim {
    ran: bool,
}

impl Default for RedundantLoadElim {
    fn default() -> Self {
        Self { ran: false }
    }
}
impl RedundantLoadElim {
    pub fn new() -> Self {
        Self::default()
    }
}

impl OptimizationWIR for RedundantLoadElim {
    fn optimize_node(&mut self, cur: &mut InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| self.run(f));
        false
    }
}

impl RedundantLoadElim {
    pub fn run(&mut self, func: &mut Function) {
        if self.ran {
            return;
        }
        self.ran = true;

        loop {
            let mut changed = false;
            let mut q = WirEditQueue::new();

            for b in &func.blocks {
                // Per-block “available values” for precise locations
                let mut last_field: HashMap<(ValueId, FieldId), ValueId> = HashMap::new();
                let mut last_elem: HashMap<(ValueId, i32), ValueId> = HashMap::new();
                let mut last_len: HashMap<ValueId, ValueId> = HashMap::new();
                let mut last_env: HashMap<(ValueId, u32), ValueId> = HashMap::new();

                // -------- helpers ----------
                #[inline]
                fn rep(func: &Function, mut v: ValueId) -> ValueId {
                    // short Mov peeling
                    for _ in 0..6 {
                        match &func.values[v.0 as usize].def {
                            ValueDef::InstResult(iid, _ix) => {
                                if let Inst::Mov(src) = func.nodes[iid.0 as usize].kind {
                                    v = src;
                                    continue;
                                }
                            }
                            _ => {}
                        }
                        break;
                    }
                    v
                }

                #[inline]
                fn flush_all(
                    last_field: &mut HashMap<(ValueId, FieldId), ValueId>,
                    last_elem: &mut HashMap<(ValueId, i32), ValueId>,
                    last_len: &mut HashMap<ValueId, ValueId>,
                    last_env: &mut HashMap<(ValueId, u32), ValueId>,
                ) {
                    last_field.clear();
                    last_elem.clear();
                    last_len.clear();
                    last_env.clear();
                }

                #[inline]
                fn clear_arr_elems(map: &mut HashMap<(ValueId, i32), ValueId>, arr: ValueId) {
                    map.retain(|(a, _), _| *a != arr);
                }

                #[inline]
                fn clear_obj_fields(map: &mut HashMap<(ValueId, FieldId), ValueId>, obj: ValueId) {
                    map.retain(|(o, _), _| *o != obj);
                }

                // --------------------------------
                // Forward scan of instructions
                // --------------------------------
                for &nid in &b.insts {
                    let node = &func.nodes[nid.0 as usize];
                    match &node.kind {
                        // ===== READS we can forward/eliminate =====
                        Inst::LoadField { obj, field, .. } => {
                            let o = rep(func, *obj);
                            let key = (o, *field);
                            if let Some(&val) = last_field.get(&key) {
                                // RLE: replace repeated load with Mov(cached)
                                q.replace_kind(nid, Inst::Mov(val));
                                changed = true;
                            } else {
                                // remember the produced value as leader
                                if let Some(&dst) = node.results.get(0) {
                                    last_field.insert(key, dst);
                                }
                            }
                        }

                        Inst::LoadElem { arr, idx } => {
                            // only track constant index
                            if let Some(i) = value_as_i32(func, *idx) {
                                let a = rep(func, *arr);
                                let key = (a, i);
                                if let Some(&val) = last_elem.get(&key) {
                                    q.replace_kind(nid, Inst::Mov(val));
                                    changed = true;
                                } else {
                                    if let Some(&dst) = node.results.get(0) {
                                        last_elem.insert(key, dst);
                                    }
                                }
                            } else {
                                // unknown index read — nothing to track precisely
                            }
                        }

                        Inst::ArrayLen(arr) => {
                            let a = rep(func, *arr);
                            if let Some(&val) = last_len.get(&a) {
                                q.replace_kind(nid, Inst::Mov(val));
                                changed = true;
                            } else {
                                if let Some(&dst) = node.results.get(0) {
                                    last_len.insert(a, dst);
                                }
                            }
                        }

                        Inst::LoadEnv { clos, index } => {
                            let c = rep(func, *clos);
                            let key = (c, *index);
                            if let Some(&val) = last_env.get(&key) {
                                q.replace_kind(nid, Inst::Mov(val));
                                changed = true;
                            } else {
                                if let Some(&dst) = node.results.get(0) {
                                    last_env.insert(key, dst);
                                }
                            }
                        }

                        // ===== WRITES we can use to forward later loads =====
                        Inst::StoreField { obj, field, val, .. } => {
                            let o = rep(func, *obj);
                            let v = rep(func, *val);
                            last_field.insert((o, *field), v);
                        }

                        Inst::StoreElem { arr, idx, val } => {
                            let a = rep(func, *arr);
                            if let Some(i) = value_as_i32(func, *idx) {
                                let v = rep(func, *val);
                                last_elem.insert((a, i), v);
                            } else {
                                // imprecise store: kill all element knowledge for this array
                                clear_arr_elems(&mut last_elem, a);
                            }
                        }

                        Inst::ArraySetLen { arr, new_len } => {
                            let a = rep(func, *arr);
                            let v = rep(func, *new_len);
                            last_len.insert(a, v);
                            // Truncation/growth may change element visibility; drop elem cache
                            clear_arr_elems(&mut last_elem, a);
                        }

                        Inst::StoreEnv { clos, index, val } => {
                            let c = rep(func, *clos);
                            let v = rep(func, *val);
                            last_env.insert((c, *index), v);
                        }

                        // ===== Object shape mutations =====
                        Inst::TransitionShape { obj, .. } => {
                            // safest: forget field values for this object
                            let o = rep(func, *obj);
                            clear_obj_fields(&mut last_field, o);
                        }

                        // ===== Array bulk updates / mutators (invalidate) =====
                        Inst::ArrayFill { arr, .. } => {
                            let a = rep(func, *arr);
                            clear_arr_elems(&mut last_elem, a);
                            last_len.remove(&a); // some impls also set length; conservative
                        }
                        Inst::ArrayCopy { dst, .. } => {
                            let a = rep(func, *dst);
                            clear_arr_elems(&mut last_elem, a);
                            last_len.remove(&a);
                        }
                        Inst::ArrayPush { arr, .. }
                        | Inst::ArrayPop (arr)
                        | Inst::ArrayShift (arr)
                        | Inst::ArrayUnshift { arr, .. } => {
                            let a = rep(func, *arr);
                            clear_arr_elems(&mut last_elem, a);
                            last_len.remove(&a);
                        }

                        // ===== Harmless barriers / no-ops for our state =====
                        Inst::PostWriteBarrier { .. } | Inst::ReadBarrier { .. } => {
                            // do not flush tracked values
                        }

                        // ===== Pure ops / control that do not affect memory we track =====
                        Inst::Phi(_)
                        | Inst::Const(_)
                        | Inst::Mov(_)
                        | Inst::CmpInt { .. }
                        | Inst::CmpF64 { .. }
                        | Inst::CmpRefEq { .. }
                        | Inst::IntBin { .. }
                        | Inst::F64Bin { .. }
                        | Inst::NumAdd(_,_) | Inst::NumSub(_,_) | Inst::NumMul(_,_) | Inst::NumDiv(_,_) | Inst::NumRem(_,_)
                        | Inst::StrLen(_) | Inst::StrConcat { .. } | Inst::StrSlice { .. }
                        | Inst::StrCompare { .. } | Inst::StrContains { .. }
                        | Inst::ArraySlice { .. }
                        | Inst::Return(_) | Inst::Throw(_)
                        | Inst::Branch { .. } | Inst::Jump(_, _) | Inst::Switch { .. } => {
                            // nothing to do
                        }

                        // ===== Unknown effects: flush everything =====
                        // Guards, calls, alloc closures, natives, map/reduce/filter, etc.
                        other => {
                            if other.needs_effect_in() {
                                // We already handled precise write ops above; everything else flushes
                                flush_all(&mut last_field, &mut last_elem, &mut last_len, &mut last_env);
                            }
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
        }
    }
}
