// src/opts/cse.rs
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]

use std::collections::{HashMap, HashSet};

use crate::opt::{OptimizationWIR, WirEditQueue};
use crate::wir::{
    BlockId, Constant, Function, Inst, InstId, IntBinOp, F64BinOp, CmpKind, ValueDef, ValueId,
};

pub struct CommonSubexprElim {
    ran: bool,
}

impl Default for CommonSubexprElim {
    fn default() -> Self { Self { ran: false } }
}

impl CommonSubexprElim {
    pub fn new() -> Self { Self::default() }

    pub fn run(&mut self, func: &mut Function) {
        if self.ran { return; }
        self.ran = true;

        // --- CFG & dominators ---
        let (preds, succs) = build_cfg(func);
        let rpo = rpo_order(func.entry, &succs);
        let idom = compute_idom(func.entry, &preds, &rpo);
        let dom_children = build_dom_tree(&idom);

        let mut q = WirEditQueue::new();

        // Expression map with scope stack so we only reuse dominating leaders.
        let mut expr2leader: HashMap<ExprKey, ValueId> = HashMap::new();
        let mut expr_stack: Vec<ExprKey> = Vec::new();

        // Per-value representative (leader) mapping; follow this to canonicalize operands.
        let mut reps = RepCtx::new(func);

        visit_block(func, func.entry, &dom_children, &mut expr2leader, &mut expr_stack, &mut reps, &mut q);

        q.apply(func);
    }
}

impl OptimizationWIR for CommonSubexprElim {
    fn optimize_node(&mut self, cur: &mut crate::opt::InstCursor, _q: &mut WirEditQueue) -> bool {
        cur.with_func(|f| self.run(f));
        false
    }
}

// ======================================================================
// Internal machinery
// ======================================================================

#[derive(Default)]
struct RepCtx {
    // value -> representative leader value; None means "self is the leader"
    val2rep: Vec<Option<ValueId>>,
    // dedupe identical constants: ConstKey -> leader value
    const2leader: HashMap<ConstKey, ValueId>,
}

impl RepCtx {
    fn new(func: &Function) -> Self {
        Self {
            val2rep: vec![None; func.values.len()],
            const2leader: HashMap::new(),
        }
    }

    #[inline]
    fn grow_if_needed(&mut self, func: &Function) {
        if self.val2rep.len() < func.values.len() {
            self.val2rep.resize(func.values.len(), None);
        }
    }

    /// Find the current representative (leader) for `v`, following mappings.
    fn rep(&self, mut v: ValueId) -> ValueId {
        // Small bounded chase (paths are tiny in practice).
        for _ in 0..16 {
            match self.val2rep.get(v.0 as usize).and_then(|x| *x) {
                Some(nv) if nv != v => v = nv,
                _ => break,
            }
        }
        v
    }

    /// Declare that `v` is equal to leader `to`.
    fn union_to(&mut self, v: ValueId, to: ValueId) {
        let r = self.rep(to);
        let idx = v.0 as usize;
        if idx >= self.val2rep.len() { self.val2rep.resize(idx + 1, None); }
        self.val2rep[idx] = Some(r);
    }

    /// If `v` is (or produces) a constant, return/record a dominating leader for that constant.
    fn const_leader(&mut self, func: &Function, v: ValueId) -> Option<ValueId> {
        if let Some(ck) = constant_of_value(func, v) {
            if let Some(&ldr) = self.const2leader.get(&ck) {
                return Some(ldr);
            }
        }
        None
    }

    /// Record `dst` as the leader for constant `ck` (first time we see it in scope).
    fn remember_const_leader(&mut self, ck: ConstKey, dst: ValueId) {
        self.const2leader.entry(ck).or_insert(dst);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ConstKey {
    I32(i32),
    F64(u64), // exact bits to keep -0.0/NaNs distinct
    Bool(bool),
    Null,
    Str(String),
}

impl ConstKey {
    fn from_const(c: &Constant) -> Self {
        match c {
            Constant::Int32(x) => ConstKey::I32(*x),
            Constant::F64(x)   => ConstKey::F64(x.to_bits()),
            Constant::Bool(b)  => ConstKey::Bool(*b),
            Constant::Null     => ConstKey::Null,
            Constant::Str(s)   => ConstKey::Str(s.clone()),
        }
    }
}

fn constant_of_value(func: &Function, v: ValueId) -> Option<ConstKey> {
    match &func.values[v.0 as usize].def {
        ValueDef::Const(c) => Some(ConstKey::from_const(c)),
        ValueDef::InstResult(iid, _) => {
            if let Inst::Const(ref c) = func.nodes[iid.0 as usize].kind {
                Some(ConstKey::from_const(c))
            } else { None }
        }
        _ => None,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum NumOp { Add, Sub, Mul, Div, Rem }

fn num_op_of(k: &Inst) -> Option<NumOp> {
    use NumOp::*;
    match k {
        Inst::NumAdd(_,_) => Some(Add),
        Inst::NumSub(_,_) => Some(Sub),
        Inst::NumMul(_,_) => Some(Mul),
        Inst::NumDiv(_,_) => Some(Div),
        Inst::NumRem(_,_) => Some(Rem),
        _ => None,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ExprKey {
    // Constants
    Const(ConstKey),

    // Pure numeric ops
    IntBin { op: IntBinOp, a: ValueId, b: ValueId },
    F64Bin { op: F64BinOp, a: ValueId, b: ValueId },
    NumOp  { kind: NumOp,     a: ValueId, b: ValueId },

    // Comparisons
    CmpInt   { kind: CmpKind, a: ValueId, b: ValueId },
    CmpF64   { kind: CmpKind, a: CmpKinded<ValueId>, b: CmpKinded<ValueId> }, // handled via flip
    CmpF64N  { kind: CmpKind, a: ValueId, b: ValueId }, // (kept for symmetry; see canonicalize)
    CmpRefEq { a: ValueId, b: ValueId },

    // Simple queries
    ArrayLen { a: ValueId },
    StrLen   { a: ValueId },
    StrCompare { a: ValueId, b: ValueId },
}

// Helper wrapper to show intent in type; we still canonicalize below.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct CmpKinded<T>(T);

impl ExprKey {
    fn canonicalized(mut self) -> Self {
        use CmpKind::*;
        match &mut self {
            ExprKey::IntBin { op, a, b } => {
                if matches!(op, IntBinOp::Add | IntBinOp::Mul | IntBinOp::And | IntBinOp::Or | IntBinOp::Xor) {
                    if *a > *b { std::mem::swap(a, b); }
                }
            }
            ExprKey::F64Bin { op, a, b } => {
                if matches!(op, F64BinOp::Add | F64BinOp::Mul) {
                    if *a > *b { std::mem::swap(a, b); }
                }
            }
            ExprKey::NumOp { kind, a, b } => {
                if matches!(kind, NumOp::Add | NumOp::Mul) {
                    if *a > *b { std::mem::swap(a, b); }
                }
            }
            ExprKey::CmpInt { kind, a, b } => {
                if matches!(kind, Eq | Ne) {
                    if *a > *b { std::mem::swap(a, b); }
                } else if *a > *b {
                    *kind = flip_cmp(*kind);
                    std::mem::swap(a, b);
                }
            }
            ExprKey::CmpRefEq { a, b } |
            ExprKey::StrCompare { a, b } => {
                if *a > *b { std::mem::swap(a, b); }
            }
            _ => {}
        }
        self
    }
}

#[inline]
fn flip_cmp(k: CmpKind) -> CmpKind {
    use CmpKind::*;
    match k { Lt => Gt, Le => Ge, Gt => Lt, Ge => Le, Eq => Eq, Ne => Ne }
}

fn visit_block(
    func: &Function,
    bb: BlockId,
    dom_children: &HashMap<BlockId, Vec<BlockId>>,
    expr2leader: &mut HashMap<ExprKey, ValueId>,
    expr_stack: &mut Vec<ExprKey>,
    reps: &mut RepCtx,
    q: &mut WirEditQueue,
) {
    reps.grow_if_needed(func);
    let scope_mark = expr_stack.len();

    let block = func.blocks.iter().find(|b| b.id == bb).unwrap();

    // Prime reps for block params (self-leaders).
    for &p in &block.params {
        let r = reps.rep(p);
        reps.union_to(p, r);
    }

    // Walk instructions in order.
    for &nid in &block.insts {
        let node = &func.nodes[nid.0 as usize];

        // Helpers: canonical reps for operands
        let rep = |v: ValueId, reps: &RepCtx| -> ValueId { reps.rep(v) };

        match &node.kind {
            // Mov: tie the result to the source representative.
            Inst::Mov(src) => {
                if let Some(&dst) = node.results.get(0) {
                    let r = rep(*src, reps);
                    reps.union_to(dst, r);
                    // Optional: normalize Mov to Mov(rep(src)) for cleanliness.
                    if r != *src {
                        q.replace_kind(nid, Inst::Mov(r));
                    }
                }
            }

            // Const: dedupe identical constants in scope.
            Inst::Const(c) => {
                if let Some(&dst) = node.results.get(0) {
                    let ck = ConstKey::from_const(c);
                    if let Some(&ldr) = expr2leader.get(&ExprKey::Const(ck.clone())) {
                        q.replace_kind(nid, Inst::Mov(ldr));
                        reps.union_to(dst, reps.rep(ldr));
                    } else {
                        expr2leader.insert(ExprKey::Const(ck.clone()), dst);
                        expr_stack.push(ExprKey::Const(ck.clone()));
                        reps.remember_const_leader(ck, dst);
                        reps.union_to(dst, dst);
                    }
                }
            }

            // Pure numeric ops
            Inst::IntBin { op, a, b } => {
                if let Some(dst) = node.results.get(0).copied() {
                    let (a, b) = (rep(*a, reps), rep(*b, reps));
                    let key = ExprKey::IntBin { op: *op, a, b }.canonicalized();
                    cse_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, reps);
                }
            }
            Inst::F64Bin { op, a, b } => {
                if let Some(dst) = node.results.get(0).copied() {
                    let (a, b) = (rep(*a, reps), rep(*b, reps));
                    let key = ExprKey::F64Bin { op: *op, a, b }.canonicalized();
                    cse_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, reps);
                }
            }
            Inst::NumAdd(a,b) | Inst::NumSub(a,b) | Inst::NumMul(a,b) | Inst::NumDiv(a,b) | Inst::NumRem(a,b) => {
                if let Some(dst) = node.results.get(0).copied() {
                    let (a, b) = (rep(*a, reps), rep(*b, reps));
                    let key = ExprKey::NumOp { kind: num_op_of(&node.kind).unwrap(), a, b }.canonicalized();
                    cse_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, reps);
                }
            }

            // Comparisons
            Inst::CmpInt { kind, a, b } => {
                if let Some(dst) = node.results.get(0).copied() {
                    let (a, b) = (rep(*a, reps), rep(*b, reps));
                    let key = ExprKey::CmpInt { kind: *kind, a, b }.canonicalized();
                    cse_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, reps);
                }
            }
            Inst::CmpF64 { kind, a, b } => {
                if let Some(dst) = node.results.get(0).copied() {
                    let (a, b) = (rep(*a, reps), rep(*b, reps));
                    // We just reuse the same canonicalization as integer cmps.
                    let key = ExprKey::CmpInt { kind: *kind, a, b }.canonicalized(); // reuse logic
                    cse_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, reps);
                }
            }
            Inst::CmpRefEq { a, b } => {
                if let Some(dst) = node.results.get(0).copied() {
                    let (a, b) = (rep(*a, reps), rep(*b, reps));
                    let key = ExprKey::CmpRefEq { a, b }.canonicalized();
                    cse_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, reps);
                }
            }

            // Simple pure queries
            Inst::ArrayLen(arr) => {
                if let Some(dst) = node.results.get(0).copied() {
                    let a = rep(*arr, reps);
                    let key = ExprKey::ArrayLen { a };
                    cse_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, reps);
                }
            }
            Inst::StrLen(s) => {
                if let Some(dst) = node.results.get(0).copied() {
                    let a = rep(*s, reps);
                    let key = ExprKey::StrLen { a };
                    cse_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, reps);
                }
            }
            Inst::StrCompare { a, b } => {
                if let Some(dst) = node.results.get(0).copied() {
                    let (a, b) = (rep(*a, reps), rep(*b, reps));
                    let key = ExprKey::StrCompare { a, b }.canonicalized();
                    cse_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, reps);
                }
            }

            // Anything with effects / control / alloc / guards: do not CSE.
            _ => {
                // For completeness, make each produced value its own leader
                for &dst in &node.results {
                    reps.union_to(dst, dst);
                }
            }
        }
    }

    // Recurse into dominated children.
    if let Some(children) = dom_children.get(&bb) {
        for &c in children {
            visit_block(func, c, dom_children, expr2leader, expr_stack, reps, q);
        }
    }

    // Pop expressions defined in this subtree.
    while expr_stack.len() > scope_mark {
        if let Some(k) = expr_stack.pop() {
            expr2leader.remove(&k);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn cse_lookup_or_insert(
    key: ExprKey,
    dst: ValueId,
    expr2leader: &mut HashMap<ExprKey, ValueId>,
    expr_stack: &mut Vec<ExprKey>,
    q: &mut WirEditQueue,
    nid: InstId,
    reps: &mut RepCtx,
) {
    if let Some(&leader) = expr2leader.get(&key) {
        // Replace duplicate with Mov(leader) and union the result to leader.
        q.replace_kind(nid, Inst::Mov(leader));
        let l = reps.rep(leader);
        reps.union_to(dst, l);
    } else {
        expr2leader.insert(key.clone(), dst);
        expr_stack.push(key);
        reps.union_to(dst, dst);
    }
}

// =================== CFG & Dominators ===================

fn build_cfg(func: &Function) -> (HashMap<BlockId, Vec<BlockId>>, HashMap<BlockId, Vec<BlockId>>) {
    let mut succs: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::new();

    for b in &func.blocks {
        let mut list = Vec::new();
        if let Some(&last) = b.insts.last() {
            match &func.nodes[last.0 as usize].kind {
                Inst::Jump(tgt, _) => list.push(*tgt),
                Inst::Branch { then_b, else_b, .. } => { list.push(*then_b); list.push(*else_b); }
                Inst::Switch { default_b, table, .. } => {
                    list.push(*default_b);
                    for &(_, blk) in table { list.push(blk); }
                }
                Inst::Return(_) | Inst::Throw(_) => {}
                _ => {}
            }
        }
        succs.insert(b.id, list.clone());
        for s in list { preds.entry(s).or_default().push(b.id); }
        preds.entry(b.id).or_default();
    }
    (preds, succs)
}

fn rpo_order(entry: BlockId, succs: &HashMap<BlockId, Vec<BlockId>>) -> Vec<BlockId> {
    let mut seen: HashSet<BlockId> = HashSet::new();
    let mut out: Vec<BlockId> = Vec::new();

    fn dfs(u: BlockId, succs: &HashMap<BlockId, Vec<BlockId>>, seen: &mut HashSet<BlockId>, out: &mut Vec<BlockId>) {
        if !seen.insert(u) { return; }
        if let Some(vs) = succs.get(&u) {
            for &v in vs { dfs(v, succs, seen, out); }
        }
        out.push(u);
    }

    dfs(entry, succs, &mut seen, &mut out);
    out.reverse(); // RPO
    out
}

fn compute_idom(entry: BlockId, preds: &HashMap<BlockId, Vec<BlockId>>, rpo: &Vec<BlockId>) -> HashMap<BlockId, BlockId> {
    // Map block -> rpo index
    let mut index: HashMap<BlockId, usize> = HashMap::new();
    for (i, &b) in rpo.iter().enumerate() { index.insert(b, i); }

    let mut idom: HashMap<BlockId, BlockId> = HashMap::new();
    idom.insert(entry, entry);

    let mut changed = true;
    while changed {
        changed = false;
        for &b in rpo {
            if b == entry { continue; }
            let mut new_idom: Option<BlockId> = None;
            if let Some(ps) = preds.get(&b) {
                for &p in ps {
                    if idom.contains_key(&p) {
                        new_idom = Some(match new_idom {
                            None => p,
                            Some(cur) => intersect(cur, p, &idom, &index),
                        });
                    }
                }
            }
            if let Some(nid) = new_idom {
                if idom.get(&b).copied() != Some(nid) {
                    idom.insert(b, nid);
                    changed = true;
                }
            }
        }
    }

    idom
}

fn intersect(mut a: BlockId, mut b: BlockId, idom: &HashMap<BlockId, BlockId>, index: &HashMap<BlockId, usize>) -> BlockId {
    while a != b {
        while index[&a] > index[&b] { a = idom[&a]; }
        while index[&b] > index[&a] { b = idom[&b]; }
    }
    a
}

fn build_dom_tree(idom: &HashMap<BlockId, BlockId>) -> HashMap<BlockId, Vec<BlockId>> {
    let mut tree: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for (b, &id) in idom {
        if *b == id { continue; }
        tree.entry(id).or_default().push(*b);
        tree.entry(*b).or_default();
    }
    tree
}
