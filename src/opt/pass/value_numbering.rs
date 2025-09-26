// src/opts/gvn.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

use ahash::{AHashMap as HashMap, AHashSet as HashSet};
use smallvec::SmallVec;
use std::mem::{Discriminant, discriminant};

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::wir::{
    BlockId, CmpKind, Constant, F64BinOp, Function, Inst, InstId, IntBinOp, ValueDef, ValueId,
};

/// GVN runs lazily once per Function (per pass round).
/// We detect “first time for this function” via the function’s address.
pub struct GlobalValueNumbering {
    last_func_ptr: Option<usize>,
}

impl Default for GlobalValueNumbering {
    fn default() -> Self {
        Self {
            last_func_ptr: None,
        }
    }
}

#[derive(Default)]
struct VnCtx {
    val2vn: Vec<u32>,
    next_vn: u32,
    const2vn: HashMap<ConstKey, u32>,
}

impl VnCtx {
    fn new(func: &Function) -> Self {
        Self {
            val2vn: vec![0; func.values.len()],
            next_vn: 1,
            const2vn: HashMap::new(),
        }
    }

    #[inline]
    fn get_vn_of_const(&mut self, ck: ConstKey) -> u32 {
        if let Some(&vn) = self.const2vn.get(&ck) {
            return vn;
        }
        let vn = self.next_vn;
        self.next_vn += 1;
        self.const2vn.insert(ck, vn);
        vn
    }

    fn get_vn(&mut self, f: &Function, v: ValueId) -> u32 {
        let idx = v.0 as usize;
        if idx >= self.val2vn.len() {
            self.val2vn.resize(f.values.len(), 0);
        }
        let cached = self.val2vn[idx];
        if cached != 0 {
            return cached;
        }

        if let Some(ck) = constant_of_value(f, v) {
            let vn = self.get_vn_of_const(ck);
            self.val2vn[idx] = vn;
            return vn;
        }

        let vn = self.next_vn;
        self.next_vn += 1;
        self.val2vn[idx] = vn;
        vn
    }

    #[inline]
    fn set_vn(&mut self, v: ValueId, vn: u32) {
        let idx = v.0 as usize;
        if idx >= self.val2vn.len() {
            self.val2vn.resize(idx + 1, 0);
        }
        self.val2vn[idx] = vn;
    }
}

impl GlobalValueNumbering {
    pub fn new() -> Self {
        Self::default()
    }

    /// Run once over the whole function, emitting ReplaceKind edits into `q`.
    fn run_on_function(&mut self, func: &Function, q: &mut WirEditQueue) {
        let (preds, succs) = build_cfg(func);
        let rpo = rpo_order(func.entry, &succs);
        let idom = compute_idom(func.entry, &preds, &rpo);
        let dom_children = build_dom_tree(&idom);

        // BlockId -> index (O(1) lookups; avoid linear scans).
        let mut ix_of: HashMap<BlockId, usize> = HashMap::with_capacity(func.blocks.len());
        for (i, b) in func.blocks.iter().enumerate() {
            ix_of.insert(b.id, i);
        }

        let mut expr2leader: HashMap<ExprKey, ValueId> = HashMap::new();
        let mut expr_stack: SmallVec<[ExprKey; 32]> = SmallVec::new(); // per-scope keys
        let mut ctx = VnCtx::new(func);

        // Dominator tree preorder
        visit_block_ix(
            func,
            *ix_of.get(&func.entry).expect("missing entry block"),
            &dom_children,
            &ix_of,
            &mut expr2leader,
            &mut expr_stack,
            &mut ctx,
            q,
        );
    }
}

impl OptimizationWIR for GlobalValueNumbering {
    /// Only wake up on opcodes GVN can fold; helps the pass-level tag bucketing.
    fn maybe_interesting(&self, tag: Discriminant<Inst>) -> bool {
        use Inst::*;
        let v0 = ValueId(0);
        let tags = [
            discriminant(&Const(Constant::Null)),
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
            discriminant(&CmpRefEq { a: v0, b: v0 }),
            discriminant(&ArrayLen(v0)),
            discriminant(&StrLen(v0)),
            discriminant(&StrCompare { a: v0, b: v0 }),
        ];
        tags.contains(&tag)
    }

    /// Lazily run once per function; emit edits into `q` and let the framework apply them.
    fn optimize_node(&mut self, cur: &mut InstCursor, q: &mut WirEditQueue) -> bool {
        // Get a stable identity for the current Function (address)
        cur.with_func(|f| {
            let ptr = f as *mut Function as usize;
            if self.last_func_ptr != Some(ptr) {
                self.last_func_ptr = Some(ptr);
                // Run GVN *now* and queue edits; framework will apply incrementally.
                self.run_on_function(f, q);
            }
        });
        // Return false so other opts can still run on this instruction in this visit.
        false
    }
}

// =====================
// Internals
// =====================

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ConstKey {
    I32(i32),
    F64(u64), // bit-exact (handles -0.0, NaNs)
    Bool(bool),
    Null,
    Str(String),
}

impl ConstKey {
    fn from_const(c: &Constant) -> Self {
        match c {
            Constant::Int32(x) => ConstKey::I32(*x),
            Constant::F64(x) => ConstKey::F64(x.to_bits()),
            Constant::Bool(b) => ConstKey::Bool(*b),
            Constant::Null => ConstKey::Null,
            Constant::Str(s) => ConstKey::Str(s.clone()),
            Constant::Undefined => ConstKey::Null, // Treat undefined as null for GVN purposes
        }
    }
}

fn constant_of_value(func: &Function, v: ValueId) -> Option<ConstKey> {
    match &func.values[v.0 as usize].def {
        ValueDef::Const(c) => Some(ConstKey::from_const(c)),
        ValueDef::InstResult(iid, _) => {
            if let Inst::Const(ref c) = func.nodes[iid.0 as usize].kind {
                Some(ConstKey::from_const(c))
            } else {
                None
            }
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum NumOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

fn num_op_of(k: &Inst) -> Option<NumOp> {
    use NumOp::*;
    match k {
        Inst::NumAdd(_, _) => Some(Add),
        Inst::NumSub(_, _) => Some(Sub),
        Inst::NumMul(_, _) => Some(Mul),
        Inst::NumDiv(_, _) => Some(Div),
        Inst::NumRem(_, _) => Some(Rem),
        _ => None,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ExprKey {
    // Constants
    Const(ConstKey),

    // Pure numeric ops
    IntBin { op: IntBinOp, a: u32, b: u32 },
    F64Bin { op: F64BinOp, a: u32, b: u32 },
    NumOp { kind: NumOp, a: u32, b: u32 },

    // Comparisons
    CmpInt { kind: CmpKind, a: u32, b: u32 },
    CmpF64 { kind: CmpKind, a: u32, b: u32 },
    CmpRefEq { a: u32, b: u32 },

    // Simple queries
    ArrayLen { a: u32 },
    StrLen { a: u32 },
    StrCompare { a: u32, b: u32 },
}

impl ExprKey {
    fn canonicalized(mut self) -> Self {
        use CmpKind::*;
        match &mut self {
            ExprKey::IntBin { op, a, b } => {
                if matches!(
                    op,
                    IntBinOp::Add | IntBinOp::Mul | IntBinOp::And | IntBinOp::Or | IntBinOp::Xor
                ) {
                    if *a > *b {
                        std::mem::swap(a, b);
                    }
                }
            }
            ExprKey::F64Bin { op, a, b } => {
                if matches!(op, F64BinOp::Add | F64BinOp::Mul) {
                    if *a > *b {
                        std::mem::swap(a, b);
                    }
                }
            }
            ExprKey::NumOp { kind, a, b } => {
                if matches!(kind, NumOp::Add | NumOp::Mul) {
                    if *a > *b {
                        std::mem::swap(a, b);
                    }
                }
            }
            ExprKey::CmpInt { kind, a, b } => {
                if matches!(kind, Eq | Ne) {
                    if *a > *b {
                        std::mem::swap(a, b);
                    }
                } else if *a > *b {
                    *kind = flip_cmp(*kind);
                    std::mem::swap(a, b);
                }
            }
            ExprKey::CmpF64 { kind, a, b } => {
                if matches!(kind, Eq | Ne) {
                    if *a > *b {
                        std::mem::swap(a, b);
                    }
                } else if *a > *b {
                    *kind = flip_cmp(*kind);
                    std::mem::swap(a, b);
                }
            }
            ExprKey::CmpRefEq { a, b } => {
                if *a > *b {
                    std::mem::swap(a, b);
                }
            }
            ExprKey::StrCompare { a, b } => {
                if *a > *b {
                    std::mem::swap(a, b);
                }
            }
            _ => {}
        }
        self
    }
}

#[inline]
fn flip_cmp(k: CmpKind) -> CmpKind {
    use CmpKind::*;
    match k {
        Lt => Gt,
        Le => Ge,
        Gt => Lt,
        Ge => Le,
        Eq => Eq,
        Ne => Ne,
    }
}

#[allow(clippy::too_many_arguments)]
fn gvn_lookup_or_insert(
    key: ExprKey,
    dst: ValueId,
    expr2leader: &mut HashMap<ExprKey, ValueId>,
    expr_stack: &mut SmallVec<[ExprKey; 32]>,
    q: &mut WirEditQueue,
    nid: InstId,
    func: &Function,
    ctx: &mut VnCtx,
) {
    if let Some(&leader) = expr2leader.get(&key) {
        // Emit a global ReplaceKind (anchorless). Framework will apply/drain.
        q.replace_kind(nid, Inst::Mov(leader));
        let vn = ctx.get_vn(func, leader);
        ctx.set_vn(dst, vn);
    } else {
        expr2leader.insert(key.clone(), dst);
        expr_stack.push(key);
        let vn = ctx.get_vn(func, dst);
        ctx.set_vn(dst, vn);
    }
}

fn visit_block_ix(
    func: &Function,
    bix: usize,
    dom_children: &HashMap<BlockId, Vec<BlockId>>,
    ix_of: &HashMap<BlockId, usize>,
    expr2leader: &mut HashMap<ExprKey, ValueId>,
    expr_stack: &mut SmallVec<[ExprKey; 32]>,
    ctx: &mut VnCtx,
    q: &mut WirEditQueue,
) {
    let scope_mark = expr_stack.len();
    let block = &func.blocks[bix];

    for &param in &block.params {
        let _ = ctx.get_vn(func, param);
    }

    for &nid in &block.insts {
        let node = &func.nodes[nid.0 as usize];

        match &node.kind {
            Inst::Mov(src) => {
                if let Some(&dst) = node.results.get(0) {
                    let vn = ctx.get_vn(func, *src);
                    ctx.set_vn(dst, vn);
                }
            }
            Inst::Const(c) => {
                if let Some(&dst) = node.results.get(0) {
                    let ck = ConstKey::from_const(c);
                    let vn = ctx.get_vn_of_const(ck.clone());
                    let key = ExprKey::Const(ck);
                    if let Some(&leader) = expr2leader.get(&key) {
                        q.replace_kind(nid, Inst::Mov(leader));
                        let lvn = ctx.get_vn(func, leader);
                        ctx.set_vn(dst, lvn);
                    } else {
                        expr2leader.insert(key.clone(), dst);
                        expr_stack.push(key);
                        ctx.set_vn(dst, vn);
                    }
                }
            }

            Inst::IntBin { op, a, b } => {
                if let Some(dst) = node.results.get(0).copied() {
                    let va = ctx.get_vn(func, *a);
                    let vb = ctx.get_vn(func, *b);
                    let key = ExprKey::IntBin {
                        op: *op,
                        a: va,
                        b: vb,
                    }
                    .canonicalized();
                    gvn_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, func, ctx);
                }
            }

            Inst::F64Bin { op, a, b } => {
                if let Some(dst) = node.results.get(0).copied() {
                    let va = ctx.get_vn(func, *a);
                    let vb = ctx.get_vn(func, *b);
                    let key = ExprKey::F64Bin {
                        op: *op,
                        a: va,
                        b: vb,
                    }
                    .canonicalized();
                    gvn_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, func, ctx);
                }
            }

            Inst::NumAdd(a, b)
            | Inst::NumSub(a, b)
            | Inst::NumMul(a, b)
            | Inst::NumDiv(a, b)
            | Inst::NumRem(a, b) => {
                if let Some(dst) = node.results.get(0).copied() {
                    let va = ctx.get_vn(func, *a);
                    let vb = ctx.get_vn(func, *b);
                    let key = ExprKey::NumOp {
                        kind: num_op_of(&node.kind).unwrap(),
                        a: va,
                        b: vb,
                    }
                    .canonicalized();
                    gvn_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, func, ctx);
                }
            }

            Inst::CmpInt { kind, a, b } => {
                if let Some(dst) = node.results.get(0).copied() {
                    let va = ctx.get_vn(func, *a);
                    let vb = ctx.get_vn(func, *b);
                    let key = ExprKey::CmpInt {
                        kind: *kind,
                        a: va,
                        b: vb,
                    }
                    .canonicalized();
                    gvn_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, func, ctx);
                }
            }
            Inst::CmpF64 { kind, a, b } => {
                if let Some(dst) = node.results.get(0).copied() {
                    let va = ctx.get_vn(func, *a);
                    let vb = ctx.get_vn(func, *b);
                    let key = ExprKey::CmpF64 {
                        kind: *kind,
                        a: va,
                        b: vb,
                    }
                    .canonicalized();
                    gvn_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, func, ctx);
                }
            }
            Inst::CmpRefEq { a, b } => {
                if let Some(dst) = node.results.get(0).copied() {
                    let va = ctx.get_vn(func, *a);
                    let vb = ctx.get_vn(func, *b);
                    let key = ExprKey::CmpRefEq { a: va, b: vb }.canonicalized();
                    gvn_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, func, ctx);
                }
            }

            Inst::ArrayLen(arr) => {
                if let Some(dst) = node.results.get(0).copied() {
                    let va = ctx.get_vn(func, *arr);
                    let key = ExprKey::ArrayLen { a: va };
                    gvn_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, func, ctx);
                }
            }
            Inst::StrLen(s) => {
                if let Some(dst) = node.results.get(0).copied() {
                    let vs = ctx.get_vn(func, *s);
                    let key = ExprKey::StrLen { a: vs };
                    gvn_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, func, ctx);
                }
            }
            Inst::StrCompare { a, b } => {
                if let Some(dst) = node.results.get(0).copied() {
                    let va = ctx.get_vn(func, *a);
                    let vb = ctx.get_vn(func, *b);
                    let key = ExprKey::StrCompare { a: va, b: vb }.canonicalized();
                    gvn_lookup_or_insert(key, dst, expr2leader, expr_stack, q, nid, func, ctx);
                }
            }

            _ => {
                // Assign fresh VNs to any results we haven't seen.
                for &dst in &node.results {
                    if ctx.get_vn(func, dst) == 0 {
                        let vn = ctx.next_vn;
                        ctx.next_vn += 1;
                        ctx.set_vn(dst, vn);
                    }
                }
            }
        }
    }

    // Recurse into dominated children (by BlockId -> index)
    if let Some(children) = dom_children.get(&block.id) {
        for &c in children {
            if let Some(&cbix) = ix_of.get(&c) {
                visit_block_ix(
                    func,
                    cbix,
                    dom_children,
                    ix_of,
                    expr2leader,
                    expr_stack,
                    ctx,
                    q,
                );
            }
        }
    }

    // Pop expressions defined in this block’s scope.
    while expr_stack.len() > scope_mark {
        if let Some(k) = expr_stack.pop() {
            expr2leader.remove(&k);
        }
    }
}

// -------------------- CFG & Dom utils --------------------

fn build_cfg(
    func: &Function,
) -> (
    HashMap<BlockId, Vec<BlockId>>,
    HashMap<BlockId, Vec<BlockId>>,
) {
    let mut succs: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::new();

    for b in &func.blocks {
        let mut list = Vec::new();
        if let Some(&last) = b.insts.last() {
            match &func.nodes[last.0 as usize].kind {
                Inst::Jump(tgt, _) => list.push(*tgt),
                Inst::Branch { then_b, else_b, .. } => {
                    list.push(*then_b);
                    list.push(*else_b);
                }
                Inst::Switch {
                    default_b, table, ..
                } => {
                    list.push(*default_b);
                    for &(_, blk) in table {
                        list.push(blk);
                    }
                }
                Inst::Return(_) | Inst::Throw(_) => {}
                _ => {}
            }
        }
        succs.insert(b.id, list.clone());
        for s in list {
            preds.entry(s).or_default().push(b.id);
        }
        // Ensure entry for isolated nodes
        preds.entry(b.id).or_default();
    }
    (preds, succs)
}

fn rpo_order(entry: BlockId, succs: &HashMap<BlockId, Vec<BlockId>>) -> Vec<BlockId> {
    let mut seen: HashSet<BlockId> = HashSet::new();
    let mut out: Vec<BlockId> = Vec::new();

    fn dfs(
        u: BlockId,
        succs: &HashMap<BlockId, Vec<BlockId>>,
        seen: &mut HashSet<BlockId>,
        out: &mut Vec<BlockId>,
    ) {
        if !seen.insert(u) {
            return;
        }
        if let Some(vs) = succs.get(&u) {
            for &v in vs {
                dfs(v, succs, seen, out);
            }
        }
        out.push(u);
    }

    dfs(entry, succs, &mut seen, &mut out);
    out.reverse(); // RPO
    out
}

fn compute_idom(
    entry: BlockId,
    preds: &HashMap<BlockId, Vec<BlockId>>,
    rpo: &Vec<BlockId>,
) -> HashMap<BlockId, BlockId> {
    // Map block -> rpo index
    let mut index: HashMap<BlockId, usize> = HashMap::new();
    for (i, &b) in rpo.iter().enumerate() {
        index.insert(b, i);
    }

    let mut idom: HashMap<BlockId, BlockId> = HashMap::new();
    idom.insert(entry, entry);

    let mut changed = true;
    while changed {
        changed = false;
        for &b in rpo {
            if b == entry {
                continue;
            }
            // Pick one processed predecessor as seed
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

fn intersect(
    mut a: BlockId,
    mut b: BlockId,
    idom: &HashMap<BlockId, BlockId>,
    index: &HashMap<BlockId, usize>,
) -> BlockId {
    while a != b {
        while index[&a] > index[&b] {
            a = idom[&a];
        }
        while index[&b] > index[&a] {
            b = idom[&b];
        }
    }
    a
}

fn build_dom_tree(idom: &HashMap<BlockId, BlockId>) -> HashMap<BlockId, Vec<BlockId>> {
    let mut tree: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for (b, &id) in idom {
        if *b == id {
            continue;
        } // entry
        tree.entry(id).or_default().push(*b);
        tree.entry(*b).or_default(); // ensure key present
    }
    tree
}
