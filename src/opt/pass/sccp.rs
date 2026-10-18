#![allow(unused_imports)]
#![allow(unused_variables)]

use ahash::{AHashMap as HashMap, AHashSet as HashSet};
use smallvec::SmallVec;
use std::collections::VecDeque;
use std::mem::{Discriminant, discriminant};

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::wir::{
    BlockId, CmpKind, Constant, F64BinOp, Function, Inst, InstId, IntBinOp, Type, ValueDef, ValueId,
};

/// SCCP lattice (3-point): Undef < Const(c) < Overdef
#[derive(Clone, Debug)]
enum Lat {
    Undef,
    Const(Constant),
    Overdef,
}

// Manual PartialEq so we don't require Constant: PartialEq
impl PartialEq for Lat {
    fn eq(&self, other: &Self) -> bool {
        use Lat::*;
        match (self, other) {
            (Undef, Undef) => true,
            (Overdef, Overdef) => true,
            (Const(a), Const(b)) => const_eq(a, b),
            _ => false,
        }
    }
}

pub struct Sccp {
    last_func_ptr: Option<usize>,
}
impl Default for Sccp {
    fn default() -> Self {
        Self {
            last_func_ptr: None,
        }
    }
}
impl Sccp {
    pub fn new() -> Self {
        Self::default()
    }
}

impl OptimizationWIR for Sccp {
    /// Wake up on control-flow (so we discover CFG) and on common foldable ops.
    fn maybe_interesting(&self, tag: Discriminant<Inst>) -> bool {
        use Inst::*;
        let v0 = ValueId(0);
        let tags = [
            // Control
            discriminant(&Branch {
                cond: v0,
                then_b: BlockId(0),
                else_b: BlockId(0),
            }),
            discriminant(&Jump(BlockId(0), Vec::<ValueId>::new())),
            // (Skip Switch discriminant construction to avoid field-shape coupling)

            // Things we often fold/propagate
            discriminant(&Const(Constant::Null)),
            discriminant(&Mov(v0)),
            discriminant(&IntBin {
                op: IntBinOp::Add,
                a: v0,
                b: v0,
            }),
            discriminant(&F64Bin {
                op: F64BinOp::Add,
                a: v0,
                b: v0,
            }),
            discriminant(&NumAdd(v0, v0)),
            discriminant(&NumSub(v0, v0)),
            discriminant(&NumMul(v0, v0)),
            discriminant(&NumDiv(v0, v0)),
            discriminant(&NumRem(v0, v0)),
            discriminant(&CmpInt {
                kind: CmpKind::Eq,
                a: v0,
                b: v0,
            }),
            discriminant(&CmpF64 {
                kind: CmpKind::Eq,
                a: v0,
                b: v0,
            }),
            discriminant(&StrLen(v0)),
            discriminant(&StrCompare { a: v0, b: v0 }),
        ];
        tags.contains(&tag)
    }

    fn optimize_node(&mut self, cur: &mut InstCursor, q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| {
            let ptr = f as *mut Function as usize;
            if self.last_func_ptr != Some(ptr) {
                self.last_func_ptr = Some(ptr);
                let _ = run_on_function(f, q);
            }
        });
        false
    }
}

pub fn run_on_function(func: &Function, q: &mut WirEditQueue) -> bool {
    let n_blocks = func.blocks.len();
    let n_values = func.values.len();

    // --------- Fast indices and CFG ---------
    let bid_to_idx: HashMap<BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect();
    let idx_to_bid: Vec<BlockId> = func.blocks.iter().map(|b| b.id).collect();

    let (_succs, preds) = build_cfg(func, &bid_to_idx);

    // Precompute per-block terminator ids (Jump/Branch/Switch)
    let terms = collect_terminators(func);

    // InstId -> (block_ix,pos) map for O(1) block-of lookup
    let mut pos_of_inst: Vec<Option<(usize, usize)>> = vec![None; func.nodes.len()];
    for (bi, bb) in func.blocks.iter().enumerate() {
        for (i, &iid) in bb.insts.iter().enumerate() {
            pos_of_inst[iid.0 as usize] = Some((bi, i));
        }
    }
    let entry_idx = bid_to_idx[&func.entry];
    let block_of_inst = |iid: InstId| -> usize {
        pos_of_inst[iid.0 as usize]
            .map(|(bi, _)| bi)
            .unwrap_or(entry_idx)
    };

    // --------- Lattice & dataflow state ---------
    fn meet(a: &Lat, b: &Lat) -> Lat {
        use Lat::*;
        match (a, b) {
            (Undef, x) => x.clone(),
            (x, Undef) => x.clone(),
            (Const(c1), Const(c2)) => {
                if const_eq(c1, c2) {
                    Const(c1.clone())
                } else {
                    Overdef
                }
            }
            _ => Overdef,
        }
    }

    let mut val_lat: Vec<Lat> = vec![Lat::Undef; n_values];

    // Seed constants from value table
    for v in &func.values {
        if let ValueDef::Const(c) = &v.def {
            val_lat[v.id.0 as usize] = Lat::Const(c.clone());
        }
    }

    // Executable blocks / edges
    let mut exec_block: Vec<bool> = vec![false; n_blocks];
    let mut exec_edge: HashSet<(usize, usize)> = HashSet::new(); // (pred_idx, succ_idx)

    // Worklists
    let mut block_wl: VecDeque<usize> = VecDeque::new();
    let mut inst_wl: VecDeque<InstId> = VecDeque::new();
    let mut value_wl: VecDeque<ValueId> = VecDeque::new();

    // --------- Use lists (inst operands) ---------
    let (uses, jump_arg_uses) = build_use_lists(func);

    // --------- Initialization ---------
    if let Some(&entry_idx) = bid_to_idx.get(&func.entry) {
        mark_block_executable(
            entry_idx,
            func,
            &mut exec_block,
            &mut block_wl,
            &mut inst_wl,
        );
    }

    // --------- Main sparse propagation loop ---------
    while !block_wl.is_empty() || !inst_wl.is_empty() || !value_wl.is_empty() {
        // Process new executable blocks
        while let Some(bi) = block_wl.pop_front() {
            // Drive control decisions by visiting the terminator
            if let Some(tid) = terms[bi] {
                inst_wl.push_back(tid);
            }

            // If term is an unconditional Jump, mark edge & propagate params immediately
            if let Some(TerminatorInfo::Jump { to_idx, args, .. }) =
                terms_info(func, bi, &bid_to_idx)
            {
                if exec_edge.insert((bi, to_idx)) {
                    mark_block_executable(
                        to_idx,
                        func,
                        &mut exec_block,
                        &mut block_wl,
                        &mut inst_wl,
                    );
                    propagate_jump_params(func, to_idx, &args, &mut val_lat, &mut value_wl);
                }
            }
        }

        // Process pending insts
        while let Some(nid) = inst_wl.pop_front() {
            let bidx = block_of_inst(nid);
            if !exec_block[bidx] {
                continue;
            }
            let node = &func.nodes[nid.0 as usize];

            match &node.kind {
                // ---- Control flow ----
                Inst::Branch {
                    cond,
                    then_b,
                    else_b,
                } => {
                    let cl = val_lat[cond.0 as usize].clone();
                    match cl {
                        Lat::Const(Constant::Bool(true)) => {
                            let t = bid_to_idx[then_b];
                            if exec_edge.insert((bidx, t)) {
                                mark_block_executable(
                                    t,
                                    func,
                                    &mut exec_block,
                                    &mut block_wl,
                                    &mut inst_wl,
                                );
                            }
                        }
                        Lat::Const(Constant::Bool(false)) => {
                            let e = bid_to_idx[else_b];
                            if exec_edge.insert((bidx, e)) {
                                mark_block_executable(
                                    e,
                                    func,
                                    &mut exec_block,
                                    &mut block_wl,
                                    &mut inst_wl,
                                );
                            }
                        }
                        _ => {
                            let t = bid_to_idx[then_b];
                            let e = bid_to_idx[else_b];
                            if exec_edge.insert((bidx, t)) {
                                mark_block_executable(
                                    t,
                                    func,
                                    &mut exec_block,
                                    &mut block_wl,
                                    &mut inst_wl,
                                );
                            }
                            if exec_edge.insert((bidx, e)) {
                                mark_block_executable(
                                    e,
                                    func,
                                    &mut exec_block,
                                    &mut block_wl,
                                    &mut inst_wl,
                                );
                            }
                        }
                    }
                }
                Inst::Switch {
                    tag,
                    default_b,
                    table,
                } => {
                    let tl = val_lat[tag.0 as usize].clone();
                    match tl {
                        Lat::Const(Constant::Int32(tval)) => {
                            let mut target = *default_b;
                            for &(key, bb) in table {
                                if key as i32 == tval {
                                    target = bb;
                                    break;
                                }
                            }
                            let s = bid_to_idx[&target];
                            if exec_edge.insert((bidx, s)) {
                                mark_block_executable(
                                    s,
                                    func,
                                    &mut exec_block,
                                    &mut block_wl,
                                    &mut inst_wl,
                                );
                            }
                        }
                        _ => {
                            let d = bid_to_idx[default_b];
                            if exec_edge.insert((bidx, d)) {
                                mark_block_executable(
                                    d,
                                    func,
                                    &mut exec_block,
                                    &mut block_wl,
                                    &mut inst_wl,
                                );
                            }
                            for &(_, bb) in table {
                                let s = bid_to_idx[&bb];
                                if exec_edge.insert((bidx, s)) {
                                    mark_block_executable(
                                        s,
                                        func,
                                        &mut exec_block,
                                        &mut block_wl,
                                        &mut inst_wl,
                                    );
                                }
                            }
                        }
                    }
                }

                // ---- Data flow (single-result only) ----
                _ => {
                    if node.results.len() == 1 {
                        let res = node.results[0];
                        let new_lat = transfer_inst(&node.kind, &val_lat);
                        let old = val_lat[res.0 as usize].clone();
                        let joined = meet(&old, &new_lat);
                        if joined != old {
                            val_lat[res.0 as usize] = joined.clone();
                            on_value_change(
                                res,
                                func,
                                &uses,
                                &jump_arg_uses,
                                &exec_block,
                                &exec_edge,
                                &mut val_lat,
                                &mut value_wl,
                                &mut inst_wl,
                                &bid_to_idx,
                            );
                        }
                    }
                }
            }
        }

        // Process value updates (block params, etc.)
        while let Some(vid) = value_wl.pop_front() {
            on_value_change(
                vid,
                func,
                &uses,
                &jump_arg_uses,
                &exec_block,
                &exec_edge,
                &mut val_lat,
                &mut value_wl,
                &mut inst_wl,
                &bid_to_idx,
            );
        }
    }

    // --------- Rewrite IR based on final lattice (emit edits) ---------

    let mut changed = false;

    // 1) Branch/Switch -> Jump
    for (bi, b) in func.blocks.iter().enumerate() {
        if !exec_block[bi] {
            continue;
        }
        if let Some(&last) = b.insts.last() {
            let node = &func.nodes[last.0 as usize];
            match &node.kind {
                Inst::Branch {
                    cond,
                    then_b,
                    else_b,
                } => {
                    if let Lat::Const(Constant::Bool(c)) = &val_lat[cond.0 as usize] {
                        let to = if *c { *then_b } else { *else_b };
                        q.replace_kind(last, Inst::Jump(to, Vec::new()));
                        changed = true;
                    }
                }
                Inst::Switch {
                    tag,
                    default_b,
                    table,
                } => {
                    if let Lat::Const(Constant::Int32(tval)) = &val_lat[tag.0 as usize] {
                        let mut target = *default_b;
                        for &(key, bb) in table {
                            if key as i32 == *tval {
                                target = bb;
                                break;
                            }
                        }
                        q.replace_kind(last, Inst::Jump(target, Vec::new()));
                        changed = true;
                    }
                }
                _ => {}
            }
        }
    }

    // 2) Replace pure, non-effectful single-result with constants
    for (i, n) in func.nodes.iter().enumerate() {
        if n.results.len() == 1 && is_pure_non_effectful(&n.kind) {
            let res = n.results[0];
            if let Lat::Const(c) = &val_lat[res.0 as usize] {
                q.replace_kind(InstId(i as u32), Inst::Const(c.clone()));
                changed = true;
            }
        }
    }

    changed
}

/* ---------------- helper functions ---------------- */

#[derive(Copy, Clone)]
enum Terminator {
    Jump,
    Branch,
    Switch,
}

fn collect_terminators(func: &Function) -> Vec<Option<InstId>> {
    let mut out = vec![None; func.blocks.len()];
    for (i, b) in func.blocks.iter().enumerate() {
        if let Some(&nid) = b.insts.last() {
            match func.nodes[nid.0 as usize].kind {
                Inst::Jump(_, _) | Inst::Branch { .. } | Inst::Switch { .. } => out[i] = Some(nid),
                _ => {}
            }
        }
    }
    out
}

enum TerminatorInfo {
    Jump {
        pred_idx: usize,
        to_idx: usize,
        args: Vec<ValueId>,
    },
    Branch,
    Switch,
}

fn terms_info(
    func: &Function,
    bidx: usize,
    bid_to_idx: &HashMap<BlockId, usize>,
) -> Option<TerminatorInfo> {
    let b = &func.blocks[bidx];
    let &nid = b.insts.last()?;
    match &func.nodes[nid.0 as usize].kind {
        Inst::Jump(to, args) => Some(TerminatorInfo::Jump {
            pred_idx: bidx,
            to_idx: bid_to_idx[to],
            args: args.clone(),
        }),
        Inst::Branch { .. } => Some(TerminatorInfo::Branch),
        Inst::Switch { .. } => Some(TerminatorInfo::Switch),
        _ => None,
    }
}

fn build_cfg(
    func: &Function,
    bid_to_idx: &HashMap<BlockId, usize>,
) -> (Vec<Vec<usize>>, Vec<Vec<usize>>) {
    let n = func.blocks.len();
    let mut succs = vec![Vec::<usize>::new(); n];
    let mut preds = vec![Vec::<usize>::new(); n];

    for (i, b) in func.blocks.iter().enumerate() {
        if let Some(&last) = b.insts.last() {
            match &func.nodes[last.0 as usize].kind {
                Inst::Jump(tgt, _) => {
                    let j = bid_to_idx[tgt];
                    succs[i].push(j);
                    preds[j].push(i);
                }
                Inst::Branch { then_b, else_b, .. } => {
                    let j1 = bid_to_idx[then_b];
                    let j2 = bid_to_idx[else_b];
                    succs[i].push(j1);
                    preds[j1].push(i);
                    succs[i].push(j2);
                    preds[j2].push(i);
                }
                Inst::Switch {
                    default_b, table, ..
                } => {
                    let jd = bid_to_idx[default_b];
                    succs[i].push(jd);
                    preds[jd].push(i);
                    for &(_, bid) in table {
                        let j = bid_to_idx[&bid];
                        succs[i].push(j);
                        preds[j].push(i);
                    }
                }
                _ => {}
            }
        }
    }

    (succs, preds)
}

fn mark_block_executable(
    bi: usize,
    func: &Function,
    exec_block: &mut [bool],
    block_wl: &mut VecDeque<usize>,
    inst_wl: &mut VecDeque<InstId>,
) {
    if exec_block[bi] {
        return;
    }
    exec_block[bi] = true;
    // Enqueue whole block (so we can visit terminator immediately)
    block_wl.push_back(bi);
    // Also enqueue all insts (drives data flow regardless of control)
    for &nid in &func.blocks[bi].insts {
        inst_wl.push_back(nid);
    }
}

fn propagate_jump_params(
    func: &Function,
    succ_idx: usize,
    args: &[ValueId],
    val_lat: &mut [Lat],
    value_wl: &mut VecDeque<ValueId>,
) {
    let succ_params = &func.blocks[succ_idx].params;
    let n = std::cmp::min(args.len(), succ_params.len());
    for i in 0..n {
        let param = succ_params[i];
        let arg = args[i];
        let new_lat = {
            let a = &val_lat[param.0 as usize];
            let b = &val_lat[arg.0 as usize];
            match (a, b) {
                (Lat::Undef, x) => x.clone(),
                (x, Lat::Undef) => x.clone(),
                (Lat::Const(c1), Lat::Const(c2)) => {
                    if const_eq(c1, c2) {
                        Lat::Const(c1.clone())
                    } else {
                        Lat::Overdef
                    }
                }
                _ => Lat::Overdef,
            }
        };
        if new_lat != val_lat[param.0 as usize] {
            val_lat[param.0 as usize] = new_lat;
            value_wl.push_back(param);
        }
    }
}

fn on_value_change(
    vid: ValueId,
    func: &Function,
    uses: &HashMap<ValueId, Vec<InstId>>,
    jump_arg_uses: &HashMap<
        ValueId,
        Vec<(
            usize, /*pred_idx*/
            usize, /*succ_idx*/
            usize, /*param_i*/
        )>,
    >,

    exec_block: &[bool],
    exec_edge: &HashSet<(usize, usize)>,

    val_lat: &mut [Lat],
    value_wl: &mut VecDeque<ValueId>,
    inst_wl: &mut VecDeque<InstId>,

    bid_to_idx: &HashMap<BlockId, usize>,
) {
    if let Some(us) = uses.get(&vid) {
        for &nid in us {
            inst_wl.push_back(nid);
        }
    }
    if let Some(edges) = jump_arg_uses.get(&vid) {
        for &(pred_i, succ_i, param_i) in edges {
            if exec_block[pred_i] && exec_edge.contains(&(pred_i, succ_i)) {
                let param_vid = func.blocks[succ_i].params[param_i];
                // meet(param, arg)
                let new_lat = {
                    let a = &val_lat[param_vid.0 as usize];
                    let b = &val_lat[vid.0 as usize];
                    match (a, b) {
                        (Lat::Undef, x) => x.clone(),
                        (x, Lat::Undef) => x.clone(),
                        (Lat::Const(c1), Lat::Const(c2)) => {
                            if const_eq(c1, c2) {
                                Lat::Const(c1.clone())
                            } else {
                                Lat::Overdef
                            }
                        }
                        _ => Lat::Overdef,
                    }
                };
                if new_lat != val_lat[param_vid.0 as usize] {
                    val_lat[param_vid.0 as usize] = new_lat;
                    value_wl.push_back(param_vid);
                }
            }
        }
    }
}

fn inst_operands(k: &Inst) -> Vec<ValueId> {
    use Inst::*;
    match k {
        Mov(v) => vec![*v],
        Phi(vs) => vs.clone(),
        IntBin { a, b, .. } => vec![*a, *b],
        F64Bin { a, b, .. } => vec![*a, *b],
        NumAdd(a, b) | NumSub(a, b) | NumMul(a, b) | NumDiv(a, b) | NumRem(a, b) => vec![*a, *b],
        CmpInt { a, b, .. } => vec![*a, *b],
        CmpF64 { a, b, .. } => vec![*a, *b],
        StrLen(v) => vec![*v],
        StrConcat { a, b } => vec![*a, *b],
        StrSlice { s, start, end } => vec![*s, *start, *end],
        StrCompare { a, b } => vec![*a, *b],
        StrContains { s, sub } => vec![*s, *sub],
        Branch { cond, .. } => vec![*cond],
        Switch { tag, .. } => vec![*tag],
        _ => Vec::new(),
    }
}

fn build_use_lists(
    func: &Function,
) -> (
    HashMap<ValueId, Vec<InstId>>,
    HashMap<
        ValueId,
        Vec<(
            usize, /*pred_idx*/
            usize, /*succ_idx*/
            usize, /*param_i*/
        )>,
    >,
) {
    let mut uses: HashMap<ValueId, Vec<InstId>> = HashMap::new();
    let mut jump_arg_uses: HashMap<ValueId, Vec<(usize, usize, usize)>> = HashMap::new();

    let bid_to_idx: HashMap<BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect();

    for (bi, b) in func.blocks.iter().enumerate() {
        for &nid in &b.insts {
            let k = &func.nodes[nid.0 as usize].kind;
            for op in inst_operands(k) {
                uses.entry(op).or_default().push(nid);
            }
            if let Inst::Jump(to, args) = k {
                let succ_idx = bid_to_idx[to];
                for (i, &arg) in args.iter().enumerate() {
                    jump_arg_uses
                        .entry(arg)
                        .or_default()
                        .push((bi, succ_idx, i));
                }
            }
        }
    }

    (uses, jump_arg_uses)
}

fn is_pure_non_effectful(k: &Inst) -> bool {
    use Inst::*;
    match k {
        Const(_) | Mov(_) => true,
        IntBin { .. }
        | F64Bin { .. }
        | NumAdd(_, _)
        | NumSub(_, _)
        | NumMul(_, _)
        | NumDiv(_, _)
        | NumRem(_, _)
        | CmpInt { .. }
        | CmpF64 { .. }
        | StrLen(_)
        | StrConcat { .. }
        | StrCompare { .. }
        | StrContains { .. } => true,
        _ => false,
    }
}

#[allow(dead_code)]
fn const_type_hint(kind: &Inst) -> Type {
    match kind {
        Inst::Const(Constant::Int32(_)) => Type::Int32,
        Inst::Const(Constant::F64(_)) => Type::F64,
        Inst::Const(Constant::Bool(_)) => Type::Bool,
        Inst::Const(Constant::Null) => Type::Null,
        Inst::Const(Constant::Str(_)) => Type::Str,
        _ => Type::Top,
    }
}

fn const_eq(a: &Constant, b: &Constant) -> bool {
    use Constant::*;
    match (a, b) {
        (Int32(x), Int32(y)) => x == y,
        (F64(x), F64(y)) => x.to_bits() == y.to_bits(), // preserve -0.0 / NaN bits
        (Bool(x), Bool(y)) => x == y,
        (Null, Null) => true,
        (Str(sa), Str(sb)) => sa == sb,
        _ => false,
    }
}

fn transfer_inst(k: &Inst, lat: &Vec<Lat>) -> Lat {
    use Inst::*;
    let get = |v: ValueId| lat[v.0 as usize].clone();

    match k {
        Const(c) => Lat::Const(c.clone()),
        Mov(v) => get(*v),

        IntBin { op, a, b } => fold_int_bin(*op, get(*a), get(*b)),
        F64Bin { op, a, b } => fold_f64_bin(*op, get(*a), get(*b)),

        // Num* : if both ints -> int path; else if any f64 -> f64 path
        NumAdd(a, b) => fold_num_bin(IntBinOp::Add, get(*a), get(*b)),
        NumSub(a, b) => fold_num_bin(IntBinOp::Sub, get(*a), get(*b)),
        NumMul(a, b) => fold_num_bin(IntBinOp::Mul, get(*a), get(*b)),
        NumDiv(a, b) => fold_num_bin(IntBinOp::DivS, get(*a), get(*b)),
        NumRem(a, b) => fold_num_bin(IntBinOp::RemS, get(*a), get(*b)),

        CmpInt { kind, a, b } => fold_cmp_int(*kind, get(*a), get(*b)),
        CmpF64 { kind, a, b } => fold_cmp_f64(*kind, get(*a), get(*b)),

        StrLen(v) => match get(*v) {
            Lat::Const(Constant::Str(s)) => Lat::Const(Constant::Int32(s.len() as i32)),
            Lat::Overdef => Lat::Overdef,
            Lat::Undef => Lat::Undef,
            _ => Lat::Undef,
        },
        StrConcat { a, b } => match (get(*a), get(*b)) {
            (Lat::Const(Constant::Str(mut sa)), Lat::Const(Constant::Str(sb))) => {
                sa.push_str(&sb);
                Lat::Const(Constant::Str(sa))
            }
            (Lat::Overdef, _) | (_, Lat::Overdef) => Lat::Overdef,
            _ => Lat::Undef,
        },
        StrCompare { a, b } => match (get(*a), get(*b)) {
            (Lat::Const(Constant::Str(sa)), Lat::Const(Constant::Str(sb))) => {
                Lat::Const(Constant::Bool(sa == sb))
            }
            (Lat::Overdef, _) | (_, Lat::Overdef) => Lat::Overdef,
            _ => Lat::Undef,
        },
        StrContains { s, sub } => match (get(*s), get(*sub)) {
            (Lat::Const(Constant::Str(h)), Lat::Const(Constant::Str(n))) => {
                Lat::Const(Constant::Bool(h.contains(&n)))
            }
            (Lat::Overdef, _) | (_, Lat::Overdef) => Lat::Overdef,
            _ => Lat::Undef,
        },

        _ => Lat::Overdef,
    }
}

// ---- folders ----
fn fold_int_bin(op: IntBinOp, la: Lat, lb: Lat) -> Lat {
    use Lat::*;
    match (la, lb) {
        (Const(Constant::Int32(x)), Const(Constant::Int32(y))) => {
            crate::opt::helpers::fold_js_int_bin(op, x, y)
                .map(|v| Const(Constant::Int32(v)))
                .unwrap_or(Overdef)
        }
        (Overdef, _) | (_, Overdef) => Overdef,
        (Undef, _) | (_, Undef) => Undef,
        // Non-integer constants (strings, floats, ...) are evaluated at runtime.
        _ => Overdef,
    }
}

fn fold_f64_bin(op: F64BinOp, la: Lat, lb: Lat) -> Lat {
    use Lat::*;
    match (la, lb) {
        (Const(Constant::F64(x)), Const(Constant::F64(y))) => {
            let v = match op {
                F64BinOp::Add => x + y,
                F64BinOp::Sub => x - y,
                F64BinOp::Mul => x * y,
                F64BinOp::Div => x / y,
                F64BinOp::Rem => x % y,
            };
            Const(Constant::F64(v))
        }
        (Overdef, _) | (_, Overdef) => Overdef,
        _ => Undef,
    }
}

fn fold_num_bin(iop: IntBinOp, la: Lat, lb: Lat) -> Lat {
    use Lat::*;
    match (&la, &lb) {
        (Const(Constant::Int32(_)), Const(Constant::Int32(_))) => fold_int_bin(iop, la, lb),
        (Const(Constant::F64(x)), Const(Constant::F64(y))) => {
            let fop = match iop {
                IntBinOp::Add => F64BinOp::Add,
                IntBinOp::Sub => F64BinOp::Sub,
                IntBinOp::Mul => F64BinOp::Mul,
                IntBinOp::DivS => F64BinOp::Div,
                IntBinOp::RemS => F64BinOp::Rem,
                _ => return Overdef,
            };
            fold_f64_bin(
                fop,
                Lat::Const(Constant::F64(*x)),
                Lat::Const(Constant::F64(*y)),
            )
        }
        (Const(Constant::Int32(x)), Const(Constant::F64(y))) => {
            let fop = match iop {
                IntBinOp::Add => F64BinOp::Add,
                IntBinOp::Sub => F64BinOp::Sub,
                IntBinOp::Mul => F64BinOp::Mul,
                IntBinOp::DivS => F64BinOp::Div,
                IntBinOp::RemS => F64BinOp::Rem,
                _ => return Overdef,
            };
            fold_f64_bin(
                fop,
                Lat::Const(Constant::F64(*x as f64)),
                Lat::Const(Constant::F64(*y)),
            )
        }
        (Const(Constant::F64(x)), Const(Constant::Int32(y))) => {
            let fop = match iop {
                IntBinOp::Add => F64BinOp::Add,
                IntBinOp::Sub => F64BinOp::Sub,
                IntBinOp::Mul => F64BinOp::Mul,
                IntBinOp::DivS => F64BinOp::Div,
                IntBinOp::RemS => F64BinOp::Rem,
                _ => return Overdef,
            };
            fold_f64_bin(
                fop,
                Lat::Const(Constant::F64(*x)),
                Lat::Const(Constant::F64(*y as f64)),
            )
        }
        (Overdef, _) | (_, Overdef) => Overdef,
        _ => Undef,
    }
}

fn fold_cmp_int(kind: CmpKind, la: Lat, lb: Lat) -> Lat {
    use Lat::*;
    // Mirrors the JIT, which compares booleans as 0/1.
    let as_int = |c: &Constant| match c {
        Constant::Int32(x) => Some(*x as i64),
        Constant::Bool(b) => Some(*b as i64),
        _ => None,
    };
    match (la, lb) {
        (Const(ca), Const(cb)) => {
            let (Some(x), Some(y)) = (as_int(&ca), as_int(&cb)) else {
                return Overdef;
            };
            let r = match kind {
                CmpKind::Eq => x == y,
                CmpKind::Ne => x != y,
                CmpKind::Lt => x < y,
                CmpKind::Le => x <= y,
                CmpKind::Gt => x > y,
                CmpKind::Ge => x >= y,
            };
            Const(Constant::Bool(r))
        }
        (Overdef, _) | (_, Overdef) => Overdef,
        _ => Undef,
    }
}

fn fold_cmp_f64(kind: CmpKind, la: Lat, lb: Lat) -> Lat {
    use Lat::*;
    match (la, lb) {
        (Const(Constant::F64(x)), Const(Constant::F64(y))) => {
            let r = match kind {
                CmpKind::Eq => x == y,
                CmpKind::Ne => x != y,
                CmpKind::Lt => x < y,
                CmpKind::Le => x <= y,
                CmpKind::Gt => x > y,
                CmpKind::Ge => x >= y,
            };
            Const(Constant::Bool(r))
        }
        (Overdef, _) | (_, Overdef) => Overdef,
        _ => Undef,
    }
}
