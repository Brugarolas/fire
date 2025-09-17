// src/opt/pass/inliner.rs
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::collections::{HashMap, HashSet};

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::wir::{
    Block, BlockId, Constant, Function, Inst, InstId, Module, Type, Value, ValueDef, ValueId, FuncId,
    IntBinOp, F64BinOp, CmpKind,
};

// ======================================================================
// Public pass
// ======================================================================

pub struct AggressiveInliner { ran: bool }
impl Default for AggressiveInliner { fn default() -> Self { Self { ran: false } } }
impl AggressiveInliner { pub fn new() -> Self { Self::default() } }

impl OptimizationWIR for AggressiveInliner {
    fn optimize_node(&mut self, cur: &mut InstCursor, _q: &mut WirEditQueue) -> bool {
        if self.ran { return false; }
        self.ran = true;
        // Use your scaffold to reach the whole module.
        cur.with_module(|m| self.run_on_module(m));
        false
    }
}

impl AggressiveInliner {
    /// Run once after modules are merged.
    pub fn run_on_module(&mut self, m: &mut Module) {
        // --- Precompute size, purity, call histogram, loop blocks
        let mut size_lines: HashMap<FuncId, usize> = HashMap::new();
        let mut pure_callee: HashMap<FuncId, bool> = HashMap::new();
        let mut callsites: HashMap<FuncId, HashSet<(FuncId, BlockId, usize)>> = HashMap::new();

        for f in &m.funcs {
            size_lines.insert(f.id, count_lines(f));
            pure_callee.insert(f.id, is_pure_function(f));
        }
        for f in &m.funcs {
            for b in &f.blocks {
                for (pos, &nid) in b.insts.iter().enumerate() {
                    if let Inst::CallDirect { callee, .. } = &f.nodes[nid.0 as usize].kind {
                        callsites.entry(*callee).or_default().insert((f.id, b.id, pos));
                    }
                }
            }
        }
        let mut loop_blocks: HashMap<FuncId, HashSet<BlockId>> = HashMap::new();
        for f in &m.funcs {
            loop_blocks.insert(f.id, compute_loop_blocks(f));
        }

        // --- Fixed point
        let mut changed_any = true;
        while changed_any {
            changed_any = false;

            for caller_ix in 0..m.funcs.len() {
                let caller_id = m.funcs[caller_ix].id;
                let loop_set = loop_blocks.get(&caller_id).cloned().unwrap_or_default();

                // Snapshot callsites of this caller up-front (so we can freely mutate later).
                let (blocks_meta, calls_snapshot) = {
                    let f = &m.funcs[caller_ix];
                    let mut snaps = Vec::<(BlockId, usize, FuncId, InstId)>::new();
                    for b in &f.blocks {
                        for (pos, &nid) in b.insts.iter().enumerate() {
                            if let Inst::CallDirect { callee, .. } = &f.nodes[nid.0 as usize].kind {
                                snaps.push((b.id, pos, *callee, nid));
                            }
                        }
                    }
                    let blk_meta: HashMap<BlockId, usize> = f.blocks.iter()
                        .enumerate().map(|(i,b)| (b.id, i)).collect();
                    (blk_meta, snaps)
                };

                let mut changed_caller = false;

                for (bid, pos, callee_id, call_nid) in calls_snapshot {
                    if callee_id == caller_id { continue; } // skip recursion here

                    let size = *size_lines.get(&callee_id).unwrap_or(&usize::MAX);
                    if size > 6 { continue; }
                    if !pure_callee.get(&callee_id).copied().unwrap_or(false) { continue; }

                    let inside_loop = loop_set.contains(&bid);
                    let sites = callsites.get(&callee_id).map(|s| s.len()).unwrap_or(0);
                    if !(inside_loop || sites >= 3) { continue; }

                    // --- Snapshot callee (so we drop immutable borrows before mutating caller)
                    let callee_ix = match m.funcs.iter().position(|f| f.id == callee_id) { Some(ix) => ix, None => continue };
                    let callee_snap = CalleeSnapshot::from(&m.funcs[callee_ix]);

                    let did = if callee_snap.blocks.len() > 1 && callee_snap.single_return.is_some() {
                        inline_multiblock_single_return_snap(m, caller_ix, &blocks_meta, bid, pos, call_nid, &callee_snap)
                    } else {
                        inline_single_block_snap(m, caller_ix, &blocks_meta, bid, pos, call_nid, &callee_snap)
                    };

                    if did {
                        changed_any = true;
                        changed_caller = true;
                        let loops_new = compute_loop_blocks(&m.funcs[caller_ix]);
                        loop_blocks.insert(caller_id, loops_new);
                    }
                }

                if changed_caller {
                    let f = &m.funcs[caller_ix];
                    size_lines.insert(f.id, count_lines(f));
                }
            }
        }
    }
}

// ======================================================================
// Callee snapshot (break borrows cleanly)
// ======================================================================

#[derive(Clone)]
struct SnapBlock {
    id: BlockId,
    params: Vec<ValueId>,
    insts: Vec<InstId>,
}
#[derive(Clone)]
struct CalleeSnapshot {
    id: FuncId,
    entry: BlockId,
    blocks: Vec<SnapBlock>,
    nodes: Vec<crate::wir::Node>,
    values: Vec<Value>,
    single_return: Option<(InstId, Vec<ValueId>)>,
}
impl CalleeSnapshot {
    fn from(f: &Function) -> Self {
        let blocks = f.blocks.iter().map(|b| SnapBlock {
            id: b.id, params: b.params.clone(), insts: b.insts.clone()
        }).collect::<Vec<_>>();
        let single_return = {
            let mut r: Option<(InstId, Vec<ValueId>)> = None;
            for b in &f.blocks {
                for &nid in &b.insts {
                    if let Inst::Return(vals) = &f.nodes[nid.0 as usize].kind {
                        if r.is_some() { r = None; break; }
                        r = Some((nid, vals.clone()));
                    }
                }
            }
            r
        };
        CalleeSnapshot {
            id: f.id,
            entry: f.entry,
            blocks,
            nodes: f.nodes.clone(),
            values: f.values.clone(),
            single_return,
        }
    }
}

// ======================================================================
// Size / purity / loops
// ======================================================================

fn count_lines(f: &Function) -> usize {
    let mut n = 0usize;
    for b in &f.blocks {
        for &nid in &b.insts {
            let k = &f.nodes[nid.0 as usize].kind;
            if is_countable_line(k) { n += 1; }
        }
    }
    n
}
fn is_countable_line(k: &Inst) -> bool {
    use Inst::*;
    match k {
        Phi(_) | Return(_) | Throw(_)
        | Jump(_,_) | Branch{..} | Switch{..}
        | EffectEntry | Safepoint => false,
        _ => !k.needs_effect_in(),
    }
}
fn is_pure_function(f: &Function) -> bool {
    for n in &f.nodes {
        if n.kind.needs_effect_in() { return false; }
    }
    true
}

fn build_cfg(f: &Function) -> (Vec<Vec<usize>>, Vec<Vec<usize>>, HashMap<BlockId, usize>, Vec<BlockId>) {
    let n = f.blocks.len();
    let mut succs = vec![Vec::<usize>::new(); n];
    let mut preds = vec![Vec::<usize>::new(); n];
    let mut bix_of: HashMap<BlockId, usize> = HashMap::new();
    for (i, b) in f.blocks.iter().enumerate() { bix_of.insert(b.id, i); }
    for (i, b) in f.blocks.iter().enumerate() {
        if let Some(&last) = b.insts.last() {
            match &f.nodes[last.0 as usize].kind {
                Inst::Jump(t, _) => { let j = bix_of[t]; succs[i].push(j); preds[j].push(i); }
                Inst::Branch { then_b, else_b, .. } => {
                    let j1 = bix_of[then_b]; let j2 = bix_of[else_b];
                    succs[i].push(j1); preds[j1].push(i);
                    succs[i].push(j2); preds[j2].push(i);
                }
                Inst::Switch { default_b, table, .. } => {
                    let jd = bix_of[default_b]; succs[i].push(jd); preds[jd].push(i);
                    for &(_, bb) in table { let j = bix_of[&bb]; succs[i].push(j); preds[j].push(i); }
                }
                _ => {}
            }
        }
    }
    let id_of: Vec<BlockId> = f.blocks.iter().map(|b| b.id).collect();
    (succs, preds, bix_of, id_of)
}
fn compute_doms(entry_ix: usize, preds: &[Vec<usize>]) -> Vec<HashSet<usize>> {
    let n = preds.len();
    let universe: HashSet<usize> = (0..n).collect();
    let mut dom = vec![universe.clone(); n];
    dom[entry_ix] = [entry_ix].into_iter().collect();
    let mut changed = true;
    while changed {
        changed = false;
        for b in 0..n {
            if b == entry_ix { continue; }
            let mut new = universe.clone();
            for &p in &preds[b] { new = &new & &dom[p]; if new.is_empty() { break; } }
            new.insert(b);
            if new != dom[b] { dom[b] = new; changed = true; }
        }
    }
    dom
}
fn compute_loop_blocks(f: &Function) -> HashSet<BlockId> {
    let (succs, preds, bix_of, id_of) = build_cfg(f);
    if f.blocks.is_empty() { return HashSet::new(); }
    let entry_ix = bix_of[&f.entry];
    let doms = compute_doms(entry_ix, &preds);
    let mut loops: HashSet<BlockId> = HashSet::new();
    for (u, outs) in succs.iter().enumerate() {
        for &v in outs {
            if doms[u].contains(&v) {
                loops.insert(id_of[v]); loops.insert(id_of[u]);
                let mut stack = vec![u];
                let mut seen = HashSet::new();
                while let Some(x) = stack.pop() {
                    for &p in &preds[x] {
                        if p == v { continue; }
                        if seen.insert(p) {
                            loops.insert(id_of[p]);
                            stack.push(p);
                        }
                    }
                }
            }
        }
    }
    loops
}

// ======================================================================
// Low-level IR utilities (no InstFactory/WirEditQueue)
// ======================================================================

#[inline]
fn const_type(c: &Constant) -> Type {
    match c {
        Constant::Int32(_) => Type::Int32,
        Constant::F64(_)   => Type::F64,
        Constant::Bool(_)  => Type::Bool,
        Constant::Null     => Type::Null,
        Constant::Str(_)   => Type::Str,
    }
}
fn push_value(func: &mut Function, ty: Option<Type>, def: ValueDef) -> ValueId {
    let vid = ValueId(func.values.len() as u32);
    func.values.push(Value { id: vid, ty, def });
    vid
}
fn new_block(func: &mut Function) -> BlockId {
    let bid = BlockId(func.blocks.len() as u32);
    func.blocks.push(Block { id: bid, params: Vec::new(), insts: Vec::new(), sealed: false });
    bid
}
fn add_block_param(func: &mut Function, b: BlockId, ty: Type) -> ValueId {
    let idx = func.blocks[b.0 as usize].params.len() as u8;
    let vid = push_value(func, Some(ty.clone()), ValueDef::BlockParam(b, idx));
    func.blocks[b.0 as usize].params.push(vid);
    func.block_params.entry(b).or_default().push(ty);
    vid
}
fn append_inst(func: &mut Function, b: BlockId, kind: Inst, ty: Option<Type>, res_count: usize) -> (InstId, Vec<ValueId>) {
    let nid = InstId(func.nodes.len() as u32);
    let mut results = Vec::new();
    for r in 0..res_count {
        results.push(ValueId(func.values.len() as u32 + r as u32));
    }
    func.nodes.push(crate::wir::Node {
        id: nid, kind, ty: ty.clone(),
        effect_in: None, effect_out: None,
        results: results.clone(),
    });
    for (i, _) in results.iter().enumerate() {
        func.values.push(Value {
            id: ValueId(func.values.len() as u32),
            ty: ty.clone(),
            def: ValueDef::InstResult(nid, i as u8),
        });
    }
    func.blocks[b.0 as usize].insts.push(nid);
    (nid, results)
}
fn insert_inst(func: &mut Function, b: BlockId, pos: usize, kind: Inst, ty: Option<Type>, res_count: usize) -> (InstId, Vec<ValueId>) {
    let nid = InstId(func.nodes.len() as u32);
    let mut results = Vec::new();
    for r in 0..res_count {
        results.push(ValueId(func.values.len() as u32 + r as u32));
    }
    func.nodes.push(crate::wir::Node {
        id: nid, kind, ty: ty.clone(),
        effect_in: None, effect_out: None,
        results: results.clone(),
    });
    for (i, _) in results.iter().enumerate() {
        func.values.push(Value {
            id: ValueId(func.values.len() as u32),
            ty: ty.clone(),
            def: ValueDef::InstResult(nid, i as u8),
        });
    }
    func.blocks[b.0 as usize].insts.insert(pos, nid);
    (nid, results)
}
fn map_value_id(v: ValueId, vmap: &HashMap<ValueId, ValueId>) -> ValueId {
    *vmap.get(&v).unwrap_or(&v)
}
fn map_block_id(b: BlockId, bmap: &HashMap<BlockId, BlockId>) -> BlockId {
    *bmap.get(&b).unwrap_or(&b)
}
fn rewrite_operands(kind: &mut Inst, vmap: &HashMap<ValueId, ValueId>, bmap: &HashMap<BlockId, BlockId>) {
    use Inst::*;
    let mv = |v: &mut ValueId| *v = map_value_id(*v, vmap);
    let mb = |b: &mut BlockId| *b = map_block_id(*b, bmap);
    match kind {
        Jump(to, args) => { mb(to); for v in args { mv(v); } }
        Branch { cond, then_b, else_b } => { mv(cond); mb(then_b); mb(else_b); }
        Switch { tag, default_b, table } => { mv(tag); mb(default_b); for &mut (_, ref mut bb) in table { mb(bb); } }
        Return(vals) => for v in vals { mv(v) },
        Throw(v) => mv(v),
        Phi(vs) => for v in vs { mv(v) },
        Mov(v) => mv(v),
        Const(_) => {}
        IntBin { a, b, .. } | F64Bin { a, b, .. } | CmpInt { a, b, .. } | CmpF64 { a, b, .. } | CmpRefEq { a, b }
            => { mv(a); mv(b); }
        NumAdd(a,b) | NumSub(a,b) | NumMul(a,b) | NumDiv(a,b) | NumRem(a,b) => { mv(a); mv(b); }
        StrConcat { a, b } | StrCompare { a, b } => { mv(a); mv(b); }
        StrContains { s, sub } => { mv(s); mv(sub); }
        StrSlice { s, start, end } => { mv(s); mv(start); mv(end); }
        ArrayLen(a) | ArrayPop(a) | ArrayShift(a) | StrLen(a) | StrToNumber(a) => mv(a),
        _ => {}
    }
}
fn replace_uses_in_inst(kind: &mut Inst, from: &[ValueId], to: &[ValueId]) {
    let mut vmap: HashMap<ValueId, ValueId> = HashMap::new();
    for (f, t) in from.iter().zip(to.iter()) { vmap.insert(*f, *t); }
    let bmap: HashMap<BlockId, BlockId> = HashMap::new();
    rewrite_operands(kind, &vmap, &bmap);
}

// ======================================================================
// Inlining (borrow-safe, snapshot-based)
// ======================================================================

fn inline_single_block_snap(
    m: &mut Module,
    caller_ix: usize,
    blocks_meta: &HashMap<BlockId, usize>,
    call_bid: BlockId,
    call_pos: usize,
    call_nid: InstId,
    callee: &CalleeSnapshot,
) -> bool {
    // Call info (snapshot from caller)
    let (args, call_res) = {
        let f = &m.funcs[caller_ix];
        let k = &f.nodes[call_nid.0 as usize].kind;
        match k {
            Inst::CallDirect { args, .. } => (args.clone(), f.nodes[call_nid.0 as usize].results.clone()),
            _ => return false,
        }
    };
    if callee.blocks.len() != 1 { return false; }

    // Value mapping callee -> caller
    let mut vmap: HashMap<ValueId, ValueId> = HashMap::new();

    // Constants
    for v in &callee.values {
        if let ValueDef::Const(ref c) = v.def {
            let vid = push_value(&mut m.funcs[caller_ix], Some(const_type(c)), ValueDef::Const(c.clone()));
            vmap.insert(v.id, vid);
        }
    }
    // Params
    for (i, &p) in callee.blocks[0].params.iter().enumerate() {
        if i < args.len() { vmap.insert(p, args[i]); }
    }

    // Clone nodes up to Return into caller block, at call position
    let caller_bix = *blocks_meta.get(&call_bid).unwrap();
    let mut insert_off = 0usize;
    let mut ret_vals: Option<Vec<ValueId>> = None;

    for &nid in &callee.blocks[0].insts {
        let node = &callee.nodes[nid.0 as usize];
        match &node.kind {
            Inst::Return(vals) => {
                ret_vals = Some(vals.iter().map(|&v| map_value_id(v, &vmap)).collect());
                break;
            }
            _ => {
                let mut kind = node.kind.clone();
                let bmap: HashMap<BlockId, BlockId> = HashMap::new();
                rewrite_operands(&mut kind, &vmap, &bmap);
                let (new_nid, outs) = insert_inst(&mut m.funcs[caller_ix], call_bid, call_pos + insert_off, kind, node.ty.clone(), node.results.len());
                insert_off += 1;
                for (i, &ov) in node.results.iter().enumerate() { vmap.insert(ov, outs[i]); }
            }
        }
    }

    let Some(ret_map) = ret_vals else { return false; };
    if ret_map.len() != call_res.len() { return false; }

    // Rewrite uses of call results to ret_map
    {
        let f = &mut m.funcs[caller_ix];
        for n in &mut f.nodes {
            if n.id == call_nid { continue; }
            replace_uses_in_inst(&mut n.kind, &call_res, &ret_map);
        }
    }

    // Remove the call
    {
        let f = &mut m.funcs[caller_ix];
        let insts = &mut f.blocks[call_bid.0 as usize].insts;
        if call_pos < insts.len() && insts[call_pos] == call_nid { insts.remove(call_pos); }
        else if let Some(ix) = insts.iter().position(|&x| x == call_nid) { insts.remove(ix); }
    }

    true
}

fn inline_multiblock_single_return_snap(
    m: &mut Module,
    caller_ix: usize,
    blocks_meta: &HashMap<BlockId, usize>,
    call_bid: BlockId,
    call_pos: usize,
    call_nid: InstId,
    callee: &CalleeSnapshot,
) -> bool {
    let (args, call_res) = {
        let f = &m.funcs[caller_ix];
        let n = &f.nodes[call_nid.0 as usize];
        match &n.kind {
            Inst::CallDirect { args, .. } => (args.clone(), n.results.clone()),
            _ => return false,
        }
    };
    let Some((_ret_nid, _ret_vals)) = &callee.single_return else { return false; };

    // Continuation block with params for call results
    let cont_bid = new_block(&mut m.funcs[caller_ix]);
    let mut cont_params: Vec<ValueId> = Vec::new();
    for _ in &call_res {
        cont_params.push(add_block_param(&mut m.funcs[caller_ix], cont_bid, Type::Top));
    }

    // Move tail after call into continuation, remapping uses of call_res to cont_params
    {
        let f = &mut m.funcs[caller_ix];
        let insts = &mut f.blocks[call_bid.0 as usize].insts;
        let tail: Vec<InstId> = if call_pos + 1 <= insts.len() { insts.drain((call_pos+1)..).collect() } else { Vec::new() };
        for &tid in &tail {
            let n = &mut f.nodes[tid.0 as usize];
            replace_uses_in_inst(&mut n.kind, &call_res, &cont_params);
        }
        f.blocks[cont_bid.0 as usize].insts.extend(tail);
    }

    // Clone callee blocks
    let mut vmap: HashMap<ValueId, ValueId> = HashMap::new();
    let mut bmap: HashMap<BlockId, BlockId> = HashMap::new();

    for sb in &callee.blocks {
        let nb = new_block(&mut m.funcs[caller_ix]);
        bmap.insert(sb.id, nb);
    }
    // Params
    for sb in &callee.blocks {
        let nb = bmap[&sb.id];
        for &p in &sb.params {
            let pty = callee.values[p.0 as usize].ty.clone().unwrap_or(Type::Top);
            let np = add_block_param(&mut m.funcs[caller_ix], nb, pty);
            vmap.insert(p, np);
        }
    }
    // Constants
    for v in &callee.values {
        if let ValueDef::Const(ref c) = v.def {
            let vid = push_value(&mut m.funcs[caller_ix], Some(const_type(c)), ValueDef::Const(c.clone()));
            vmap.insert(v.id, vid);
        }
    }

    // Clone instructions (Return -> Jump(cont, args))
    for sb in &callee.blocks {
        let nb = bmap[&sb.id];
        for &nid in &sb.insts {
            let node = &callee.nodes[nid.0 as usize];
            match &node.kind {
                Inst::Return(vals) => {
                    let args_map = vals.iter().map(|&v| map_value_id(v, &vmap)).collect::<Vec<_>>();
                    let _ = append_inst(&mut m.funcs[caller_ix], nb, Inst::Jump(cont_bid, args_map), None, 0);
                }
                _ => {
                    let mut kind = node.kind.clone();
                    rewrite_operands(&mut kind, &vmap, &bmap);
                    let (_nn, outs) = append_inst(&mut m.funcs[caller_ix], nb, kind, node.ty.clone(), node.results.len());
                    for (i, &ov) in node.results.iter().enumerate() { vmap.insert(ov, outs[i]); }
                }
            }
        }
    }

    // Replace the call with Jump(entry_clone, mapped args)
    {
        let entry_nb = bmap[ &callee.entry ];
        let entry_param_count = m.funcs[caller_ix].blocks[entry_nb.0 as usize].params.len();
        let mut entry_args = Vec::with_capacity(entry_param_count);
        for i in 0..entry_param_count {
            entry_args.push(args.get(i).copied().unwrap_or_else(|| {
                push_value(&mut m.funcs[caller_ix], Some(Type::Null), ValueDef::Const(Constant::Null))
            }));
        }
        let _ = insert_inst(&mut m.funcs[caller_ix], call_bid, call_pos, Inst::Jump(entry_nb, entry_args), None, 0);

        // Remove the original call (now shifted by one)
        let f = &mut m.funcs[caller_ix];
        let insts = &mut f.blocks[call_bid.0 as usize].insts;
        if call_pos + 1 < insts.len() && insts[call_pos + 1] == call_nid {
            insts.remove(call_pos + 1);
        } else if let Some(ix) = insts.iter().position(|&x| x == call_nid) {
            insts.remove(ix);
        }
    }

    true
}
