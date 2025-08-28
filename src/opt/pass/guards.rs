use std::collections::{HashMap, HashSet};
use std::mem;
use crate::opt::{OptimizationWIR, WirEditQueue};
use crate::wir::{Function, Inst, BlockId, ValueId, Type, ShapeSet, DeoptId};
use crate::opt::dom_preorder_walk_func; // available in opt.rs root

#[derive(Default)]
pub struct GuardElim { ran: bool }

impl GuardElim {
    fn run_once(&mut self, func: &mut Function) {
        if mem::take(&mut self.ran) { return; }

        // Walk in dominance order and record facts proven by guards.
        let entry = func.entry;
        let mut facts: HashMap<BlockId, GuardFacts> = HashMap::new();
        let mut q = WirEditQueue::new();

        dom_preorder_walk_func(func, entry, |bb| {
            // Merge parent facts if any.
            let mut gf = if let Some(parent) = immediate_dominator(func, bb) {
                facts.get(&parent).cloned().unwrap_or_default()
            } else { GuardFacts::default() };

            // Scan instructions of this block.
            let inst_ids = func.blocks.iter().find(|b| b.id == bb).unwrap().insts.clone();
            for (pos, nid) in inst_ids.iter().enumerate() {
                let node = &func.nodes[nid.0 as usize];
                match &node.kind {
                    Inst::GuardType { val, ty, .. } => {
                        if gf.known_type.get(val).map_or(false, |t| t == ty) {
                            // Redundant guard; drop by replacing with Mov(val).
                            q.replace_kind(*nid, Inst::Mov(*val));
                        } else {
                            gf.known_type.insert(*val, ty.clone());
                        }
                    }
                    Inst::GuardNotNull { val, .. } => {
                        if gf.not_null.contains(val) {
                            q.replace_kind(*nid, Inst::Mov(*val));
                        } else {
                            gf.not_null.insert(*val);
                        }
                    }
                    Inst::GuardIsInt { val, .. } => {
                        if gf.known_type.get(val).map_or(false, |t| *t == Type::Int32) || gf.is_int.contains(val) {
                            q.replace_kind(*nid, Inst::Mov(*val));
                        } else {
                            gf.is_int.insert(*val);
                            gf.known_type.insert(*val, Type::Int32);
                        }
                    }
                    Inst::GuardIsF64 { val, .. } => {
                        if gf.known_type.get(val).map_or(false, |t| *t == Type::F64) || gf.is_f64.contains(val) {
                            q.replace_kind(*nid, Inst::Mov(*val));
                        } else {
                            gf.is_f64.insert(*val);
                            gf.known_type.insert(*val, Type::F64);
                        }
                    }
                    Inst::GuardShape { obj, shapes, .. } => {
                        if gf.shape_has(obj, shapes) {
                            q.replace_kind(*nid, Inst::Mov(*obj));
                        } else {
                            gf.add_shape(*obj, shapes.clone());
                        }
                    }
                    Inst::GuardBounds { idx, len, .. } => {
                        let key = (*idx, *len);
                        if gf.bounds.contains(&key) {
                            // Kill redundant bounds guard.
                            q.replace_kind(*nid, Inst::Mov(*idx));
                        } else {
                            gf.bounds.insert(key);
                        }
                    }
                    _ => {}
                }
            }

            facts.insert(bb, gf);
        });

        q.apply(func);
    }
}

impl OptimizationWIR for GuardElim {
    fn optimize_node(&mut self, cur: &mut crate::opt::InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| self.run_once(f));
        false
    }
}

#[derive(Clone, Default)]
struct GuardFacts {
    known_type: HashMap<ValueId, Type>,
    not_null: HashSet<ValueId>,
    is_int: HashSet<ValueId>,
    is_f64: HashSet<ValueId>,
    shape_of: HashMap<ValueId, ShapeSet>,
    bounds: HashSet<(ValueId, ValueId)>,
}
impl GuardFacts {
    fn add_shape(&mut self, v: ValueId, ss: ShapeSet) {
        self.shape_of
            .entry(v)
            .and_modify(|cur| { for s in &ss.shapes { cur.shapes.insert(*s); } })
            .or_insert(ss);
    }
    fn shape_has(&self, v: &ValueId, ss: &ShapeSet) -> bool {
        if let Some(cur) = self.shape_of.get(v) {
            ss.shapes.is_subset(&cur.shapes)
        } else { false }
    }
}

fn immediate_dominator(func: &Function, b: BlockId) -> Option<BlockId> {
    use std::collections::HashMap;
    // recompute idoms cheaply for small functions
    let idom = crate::opt::compute_idoms(func, func.entry);
    // Map BlockId -> index order matches func.blocks
    let mut index_of: HashMap<BlockId, usize> = HashMap::new();
    for (i, bb) in func.blocks.iter().enumerate() { index_of.insert(bb.id, i); }
    idom[index_of[&b]]
}
