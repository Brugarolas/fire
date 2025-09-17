// src/opts/sroa.rs
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::collections::{HashMap, HashSet};

use crate::opt::{OptimizationWIR, WirEditQueue};
use crate::opt::helpers::value_as_i32;
use crate::wir::{
    BlockId, Constant, FieldId, Function, Inst, InstId, Type, ValueDef, ValueId,
};

#[derive(Default)]
pub struct SROA {
    ran: bool,
}

impl SROA {
    pub fn new() -> Self { Self::default() }

    pub fn run(&mut self, func: &mut Function) {
        if self.ran { return; }
        self.ran = true;

        loop {
            let mut changed = false;
            let mut q = WirEditQueue::new();

            // Precompute inst -> (block, pos) and value uses
            let (inst_block_pos, uses) = index_func(func);

            // -------- Objects: scalarize AllocObj when safe (single block, no escape) --------
            for (nid, obj_v) in alloc_objs(func) {
                let Some((bid, alloc_pos)) = inst_block_pos.get(&nid).copied() else { continue; };

                // collect the whole mov-closure of the object value
                let aliases = mov_closure(func, obj_v);

                // Check all (direct) uses of any alias are within the same block and are allowed
                let mut all_use_inst_ids: HashSet<InstId> = HashSet::new();
                let mut ok = true;

                for &v in &aliases {
                    if let Some(us) = uses.get(&v) {
                        for &uid in us {
                            all_use_inst_ids.insert(uid);
                        }
                    }
                }

                for uid in &all_use_inst_ids {
                    let Some((ubid, _upos)) = inst_block_pos.get(uid) else { ok = false; break; };
                    if *ubid != bid { ok = false; break; }
                    // Only allow: Mov(obj), LoadField{obj}, StoreField{obj}, PostWriteBarrier{obj, _}
                    match &func.nodes[uid.0 as usize].kind {
                        Inst::Mov(v) if aliases.contains(v) => {}
                        Inst::LoadField { obj, .. } if aliases.contains(obj) => {}
                        Inst::StoreField { obj, .. } if aliases.contains(obj) => {}
                        Inst::PostWriteBarrier { obj, .. } if aliases.contains(obj) => {}
                        // Any other use means escape or unknown effects
                        k => {
                            // Disallow TransitionShape / MethodLookup / calls / compares / array ops / etc.
                            match k {
                                Inst::TransitionShape { obj, .. } if aliases.contains(obj) => { ok = false; break; }
                                _ => { ok = false; break; }
                            }
                        }
                    }
                }
                if !ok { continue; }

                // Single-block linear scalar replacement
                // Walk block from alloc to end, track last stored value per field, rewrite loads, remember stores/barriers to erase.
                let block = func.blocks.iter().find(|b| b.id == bid).unwrap();
                let mut last: HashMap<FieldId, ValueId> = HashMap::new();
                let mut to_erase_positions: Vec<usize> = Vec::new();
                let mut failed = false;

                for (i, &cur_id) in block.insts.iter().enumerate().skip(alloc_pos + 1) {
                    let k = &func.nodes[cur_id.0 as usize].kind;

                    match k {
                        Inst::StoreField { obj, field, val, expected: _ } if aliases.contains(obj) => {
                            last.insert(*field, *val);
                            to_erase_positions.push(i);
                        }
                        Inst::LoadField { obj, field, expected: _ } if aliases.contains(obj) => {
                            if let Some(&v) = last.get(field) {
                                q.replace_kind(cur_id, Inst::Mov(v));
                                changed = true;
                            } else {
                                // load-before-store: cannot prove initialization
                                failed = true; break;
                            }
                        }
                        Inst::PostWriteBarrier { obj, .. } if aliases.contains(obj) => {
                            // Becomes dead once we remove the StoreField; drop it.
                            to_erase_positions.push(i);
                        }
                        _ => {}
                    }
                }

                if failed { continue; }

                // If we actually rewrote at least one load/store, remove the stores/barriers and the alloc itself
                if !to_erase_positions.is_empty() || changed {
                    // erase from the end to keep indices valid
                    for pos in to_erase_positions.into_iter().rev() {
                        q.erase(bid, pos);
                    }
                    // erase the AllocObj itself
                    if let Some((_, apos)) = inst_block_pos.get(&nid) {
                        q.erase(bid, *apos);
                    }
                    changed = true;
                }
            }

            // -------- Arrays: scalarize small fixed-size arrays with const index uses --------
            for (nid, arr_v, len_n) in alloc_arrays_with_const_len(func) {
                let Some((bid, alloc_pos)) = inst_block_pos.get(&nid).copied() else { continue; };

                let aliases = mov_closure(func, arr_v);

                // ensure all uses are in the same block and are LoadElem/StoreElem/ArrayLen/Mov
                let mut all_use_inst_ids: HashSet<InstId> = HashSet::new();
                let mut ok = true;

                for &v in &aliases {
                    if let Some(us) = uses.get(&v) {
                        for &uid in us { all_use_inst_ids.insert(uid); }
                    }
                }

                for uid in &all_use_inst_ids {
                    let Some((ubid, _upos)) = inst_block_pos.get(uid) else { ok = false; break; };
                    if *ubid != bid { ok = false; break; }
                    match &func.nodes[uid.0 as usize].kind {
                        Inst::Mov(v) if aliases.contains(v) => {}
                        Inst::LoadElem { arr, idx } if aliases.contains(arr) => {
                            if value_as_i32(func, *idx).is_none() { ok = false; break; }
                        }
                        Inst::StoreElem { arr, idx, val: _ } if aliases.contains(arr) => {
                            if value_as_i32(func, *idx).is_none() { ok = false; break; }
                        }
                        Inst::ArrayLen(v) if aliases.contains(v) => {}
                        // any other use => escape / unknown
                        _ => { ok = false; break; }
                    }
                }
                if !ok { continue; }

                // linear scalarization in the block
                let block = func.blocks.iter().find(|b| b.id == bid).unwrap();
                let mut elems: HashMap<i32, ValueId> = HashMap::new();
                let mut to_erase_positions: Vec<usize> = Vec::new();
                let mut failed = false;

                for (i, &cur_id) in block.insts.iter().enumerate().skip(alloc_pos + 1) {
                    match &func.nodes[cur_id.0 as usize].kind {
                        Inst::StoreElem { arr, idx, val } if aliases.contains(arr) => {
                            if let Some(ix) = value_as_i32(func, *idx) {
                                if 0 <= ix && ix < len_n {
                                    elems.insert(ix, *val);
                                    to_erase_positions.push(i);
                                } else { failed = true; break; }
                            } else { failed = true; break; }
                        }
                        Inst::LoadElem { arr, idx } if aliases.contains(arr) => {
                            if let Some(ix) = value_as_i32(func, *idx) {
                                if let Some(&v) = elems.get(&ix) {
                                    q.replace_kind(cur_id, Inst::Mov(v));
                                    changed = true;
                                } else {
                                    failed = true; break; // read-before-write or unknown
                                }
                            } else { failed = true; break; }
                        }
                        Inst::ArrayLen(v) if aliases.contains(v) => {
                            q.replace_kind(cur_id, Inst::Const(Constant::Int32(len_n)));
                            changed = true;
                        }
                        _ => {}
                    }
                }

                if failed { continue; }

                if !to_erase_positions.is_empty() || changed {
                    for pos in to_erase_positions.into_iter().rev() {
                        q.erase(bid, pos);
                    }
                    if let Some((_, apos)) = inst_block_pos.get(&nid) {
                        q.erase(bid, *apos);
                    }
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

impl OptimizationWIR for SROA {
    fn optimize_node(&mut self, cur: &mut crate::opt::InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| self.run(f));
        false
    }
}

/* ===================== helpers ===================== */

fn index_func(func: &Function) -> (HashMap<InstId, (BlockId, usize)>, HashMap<ValueId, Vec<InstId>>) {
    let mut map_inst: HashMap<InstId, (BlockId, usize)> = HashMap::new();
    let mut uses: HashMap<ValueId, Vec<InstId>> = HashMap::new();

    for b in &func.blocks {
        for (i, &nid) in b.insts.iter().enumerate() {
            map_inst.insert(nid, (b.id, i));

            // bump uses for all operands of nid
            let k = &func.nodes[nid.0 as usize].kind;
            for v in inst_operands(k) {
                uses.entry(v).or_default().push(nid);
            }
        }
    }
    (map_inst, uses)
}

fn inst_operands(k: &Inst) -> Vec<ValueId> {
    use Inst::*;
    match k {
        Phi(vs)                           => vs.clone(),
        Jump(_, args)                     => args.clone(),
        Branch { cond, .. }               => vec![*cond],
        Switch { tag, .. }                => vec![*tag],
        Return(vals)                      => vals.clone(),
        Throw(v)                          => vec![*v],

        Mov(v)                            => vec![*v],
        Const(_)                          => vec![],

        GuardType { val, .. }             => vec![*val],
        GuardShape { obj, .. }            => vec![*obj],
        GuardBounds { idx, len, .. }      => vec![*idx, *len],
        GuardNotNull { val, .. }          => vec![*val],
        GuardIsInt { val, .. }            => vec![*val],
        GuardIsF64 { val, .. }            => vec![*val],

        AllocObj { .. }                   => vec![],
        LoadField { obj, .. }             => vec![*obj],
        StoreField { obj, val, .. }       => vec![*obj, *val],
        TransitionShape { obj, .. }       => vec![*obj],

        AllocArray { len, .. }            => vec![*len],
        ArrayLen(v)                       => vec![*v],
        ArraySetLen { arr, new_len }      => vec![*arr, *new_len],
        LoadElem { arr, idx }             => vec![*arr, *idx],
        StoreElem { arr, idx, val }       => vec![*arr, *idx, *val],
        ArraySlice { arr, start, end }    => vec![*arr, *start, *end],

        ArrayPush { arr, val }            => vec![*arr, *val],
        ArrayPop(arr)                     => vec![*arr],
        ArrayShift(arr)                   => vec![*arr],
        ArrayUnshift { arr, val }         => vec![*arr, *val],
        ArrayMap { arr, .. }              => vec![*arr],
        ArrayReduce { init, arr, .. }     => vec![*init, *arr],
        ArrayFill { arr, val }            => vec![*arr, *val],
        ArrayCopy { dst, src, len }       => vec![*dst, *src, *len],
        ArrayForEach { arr, .. }          => vec![*arr],
        ArrayFind { arr, .. }             => vec![*arr],
        ArrayFindIndex { arr, .. }        => vec![*arr],
        ArrayFilter { arr, .. }           => vec![*arr],

        StrLen(v)                         => vec![*v],
        StrConcat { a, b }                => vec![*a, *b],
        StrSlice { s, start, end }        => vec![*s, *start, *end],
        StrCompare { a, b }               => vec![*a, *b],
        StrContains { s, sub }            => vec![*s, *sub],
        StrToNumber(v)                    => vec![*v],

        IntBin { a, b, .. }               => vec![*a, *b],
        F64Bin { a, b, .. }               => vec![*a, *b],
        NumAdd(a,b) | NumSub(a,b)
        | NumMul(a,b) | NumDiv(a,b)
        | NumRem(a,b)                    => vec![*a, *b],
        CmpInt { a, b, .. }              => vec![*a, *b],
        CmpF64 { a, b, .. }              => vec![*a, *b],
        CmpRefEq { a, b }                => vec![*a, *b],

        BoxInt(v) | BoxF64(v) | BoxBool(v)
        | UnboxToInt(v) | UnboxToF64(v)  => vec![*v],

        CallDirect { args, .. }          => args.clone(),
        CallDirectMemoized { args, .. }  => args.clone(),
        CallIC { recv, args, .. }        => {
            let mut vs = vec![*recv]; vs.extend_from_slice(args); vs
        }
        MethodLookup { obj, .. }         => vec![*obj],
        AllocClosure { .. }              => vec![],
        LoadEnv { clos, .. }             => vec![*clos],
        StoreEnv { clos, val, .. }       => vec![*clos, *val],
        MakeClosure { env, .. }          => vec![*env],
        CallClosure { fun, args, .. }    => {
            let mut vs = vec![*fun]; vs.extend_from_slice(args); vs
        }

        CallNative { args, .. }          => args.clone(),

        PostWriteBarrier { obj, val }    => vec![*obj, *val],
        ReadBarrier { obj }              => vec![*obj],
        EffectEntry | Safepoint | OSRPoint => vec![],
        RegisterClass { .. } | AllocInstance { .. } | EventLoopPump { .. }
        | SetTimeout { .. } | SetInterval { .. } | ClearTimeout { .. } | ClearInterval { .. } => vec![],

        _ => vec![],
    }
}

fn alloc_objs(func: &Function) -> Vec<(InstId, ValueId)> {
    let mut out = Vec::new();
    for b in &func.blocks {
        for &nid in &b.insts {
            if let Inst::AllocObj { .. } = func.nodes[nid.0 as usize].kind {
                if let Some(&v) = func.nodes[nid.0 as usize].results.get(0) {
                    out.push((nid, v));
                }
            }
        }
    }
    out
}

fn alloc_arrays_with_const_len(func: &Function) -> Vec<(InstId, ValueId, i32)> {
    let mut out = Vec::new();
    for b in &func.blocks {
        for &nid in &b.insts {
            if let Inst::AllocArray { len, .. } = func.nodes[nid.0 as usize].kind {
                if let Some(n) = value_as_i32(func, len) {
                    if let Some(&v) = func.nodes[nid.0 as usize].results.get(0) {
                        out.push((nid, v, n));
                    }
                }
            }
        }
    }
    out
}

/// Compute the set of ValueIds that are Mov-chained from `root` (including root).
fn mov_closure(func: &Function, root: ValueId) -> HashSet<ValueId> {
    let mut set: HashSet<ValueId> = HashSet::new();
    set.insert(root);
    let mut changed = true;
    while changed {
        changed = false;
        for v in &func.values {
            if let ValueDef::InstResult(iid, _ix) = v.def {
                if let Inst::Mov(src) = func.nodes[iid.0 as usize].kind {
                    if set.contains(&src) && !set.contains(&v.id) {
                        set.insert(v.id);
                        changed = true;
                    }
                }
            }
        }
    }
    set
}
