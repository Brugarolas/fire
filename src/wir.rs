// wir.rs
//! WIR — Wren IR (mid–high level, SSA, speculation-friendly)
//!
//! This is a single-file “real code” skeleton you can drop into a new Rust
//! crate (e.g., `lib.rs`). It defines the core IR data structures, types,
//! instruction set, effect tokens, guards & deopt snapshots, plus a minimal
//! builder API. It’s deliberately std-only and compiles as-is on stable Rust.
//!
//! Design highlights:
//! - SSA values and blocks with stable IDs (newtyped indices).
//! - Mid–high level instruction set with explicit Guards and Deopt.
//! - Precise heap effects modeled via an SSA “effect token” (E).
//! - Shape-based objects, arrays, strings, closures.
//! - Boxing/unboxing explicit; unboxed Int32/F64/Bools preferred.
//! - Abstract GC barriers (to be lowered to MMTk intrinsics).
//! - IC/PIC-friendly call forms; deopt snapshots for speculation.
//!
//! You’ll likely split this into modules later (types.rs, func.rs, builder.rs, …).
//!
//! SPDX-License-Identifier: MIT

#![allow(dead_code)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::too_many_arguments)]

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;

/// -------- Newtyped IDs for stable handles (indices into Vecs) --------

macro_rules! id_newtype {
    ($name:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
        pub struct $name(pub u32);
        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}#{}", stringify!($name), self.0)
            }
        }
    };
}

id_newtype!(ValueId);
id_newtype!(BlockId);
id_newtype!(InstId);
id_newtype!(ParamId);
id_newtype!(FuncId);
id_newtype!(ShapeId);
id_newtype!(FieldId);
id_newtype!(EnvShapeId);
id_newtype!(SiteId); // callsite / IC site id
id_newtype!(DeoptId);
id_newtype!(EffectId); // special: also a ValueId in practice

/// -------- Type lattice --------

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    Bottom,
    Top,

    // Primitives (unboxed preferred)
    Int32,
    F64,
    Bool,
    Null,

    // Boxed numeric (heap ref) & generic tagged numeric union
    NumRef,    // boxed number on heap (object/reference)
    Num,       // union of Int32|F64 (unboxed in registers unless boxed demanded)

    // References
    AnyRef,
    Obj(ShapeSet),              // hidden-class object; possibly union of shapes
    Array(Box<Option<Type>>),   // optional element type info (None = unknown)
    Str,
    Closure(Option<EnvShapeId>),
    Foreign, // host/FFI box (opaque)
    // Unions (compact but general). Keep small; normalize frequently.
    Union(Vec<Type>),
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Type::*;
        match self {
            Bottom => write!(f, "⊥"),
            Top => write!(f, "⊤"),
            Int32 => write!(f, "i32"),
            F64 => write!(f, "f64"),
            Bool => write!(f, "bool"),
            Null => write!(f, "null"),
            NumRef => write!(f, "NumRef"),
            Num => write!(f, "Num"),
            AnyRef => write!(f, "AnyRef"),
            Obj(s) => write!(f, "Obj<{:?}>", s),
            Array(t) => match t.as_ref() {
                Some(t) => write!(f, "Array<{:?}>", t),
                None => write!(f, "Array<?>"),
            },
            Str => write!(f, "Str"),
            Closure(s) => match s {
                Some(id) => write!(f, "Closure<Env#{:?}>", id),
                None => write!(f, "Closure<?>"),
            },
            Foreign => write!(f, "Foreign"),
            Union(v) => {
                write!(f, "Union(")?;
                for (i, t) in v.iter().enumerate() {
                    if i != 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{:?}", t)?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A compact set of shape IDs (hidden classes), kept small to encourage monomorphism.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ShapeSet {
    pub shapes: BTreeSet<ShapeId>,
}

impl fmt::Debug for ShapeSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.shapes.is_empty() {
            return write!(f, "S<?>");
        }
        write!(f, "S{{")?;
        for (i, s) in self.shapes.iter().enumerate() {
            if i != 0 {
                write!(f, ",")?;
            }
            write!(f, "{:?}", s)?;
        }
        write!(f, "}}")
    }
}

impl ShapeSet {
    pub fn singleton(s: ShapeId) -> Self {
        let mut set = BTreeSet::new();
        set.insert(s);
        ShapeSet { shapes: set }
    }
}

/// -------- Values & constants --------

#[derive(Clone, Debug)]
pub enum Constant {
    Int32(i32),
    F64(f64),
    Bool(bool),
    Null,
    Str(String),
    // Other literals can be added (symbols, interned strings, etc.)
}

/// -------- Deopt & Guards --------

/// Snapshot of interpreter/baseline-visible state for deoptimization.
/// Carries a mapping from "materialized" SSA values to VM stack slots / locals.
#[derive(Clone, Debug, Default)]
pub struct DeoptSnapshot {
    pub values: Vec<ValueId>,              // live SSA values to materialize
    pub slot_map: HashMap<usize, ValueId>, // VM-slot -> value
    pub meta: HashMap<String, i64>,        // optional metadata (pc, inlined-frame-id, ...)
}

/// A deopt target defines where to resume (e.g., baseline PC) and the snapshot to reconstruct state.
#[derive(Clone, Debug)]
pub struct DeoptPoint {
    pub id: DeoptId,
    pub target_label: String,     // runtime label / baseline PC key
    pub snapshot: DeoptSnapshot,  // reconstruction info
}

/// -------- Effects & purity model --------

/// Memory effect classes for side-effecting instructions.
/// We mostly need an ordering token; this is for analysis/printing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EffectKind {
    Entry,
    Alloc,
    Store,
    Call,
    Guard,
    Barrier,
    IO,
    Safepoint,
}

/// -------- Instructions (mid–high level) --------

/// Arithmetic kinds for convenience.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntBinOp { Add, Sub, Mul, DivS, RemS, And, Or, Xor, Shl, ShrU, Sar }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum F64BinOp { Add, Sub, Mul, Div, Rem }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpKind { Eq, Ne, Lt, Le, Gt, Ge }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumKind { Int32, F64, Num } // helper for mixed-num ops

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallConv {
    /// Fast internal calling convention (JIT-to-JIT).
    Fast,
    /// Host/native ABI (FFI).
    Native,
}

/// An inline cache entry (PIC) for a dynamic callsite.
#[derive(Clone, Debug)]
pub struct PicEntry {
    pub recv_shapes: ShapeSet,
    pub callee: FuncId,          // known target
    pub inlineable: bool,
    pub env_shape: Option<EnvShapeId>,
    pub arg_spec: Vec<Type>,     // observed arg types (narrowed)
}

/// Main instruction enum. SSA values are referenced by ValueId.
/// Effects: instructions that read/write heap have `effect_in` and may produce `effect_out`.
#[derive(Clone, Debug)]
pub enum Inst {
    // ---- Control ----
    Phi(Vec<ValueId>),                    // type is resolved by the type engine
    Jump(BlockId, Vec<ValueId>),
    Branch { cond: ValueId, then_b: BlockId, else_b: BlockId },
    Switch { tag: ValueId, default_b: BlockId, table: Vec<(i64, BlockId)> },
    Return(Vec<ValueId>),
    Throw(ValueId),

    // ---- Effect / bookkeeping ----
    EffectEntry,                          // E0 entry token
    Safepoint,                            // explicit safepoint (typically at backedges/calls)

    // ---- Constants / moves ----
    Const(Constant),
    Mov(ValueId),

    // ---- Guards (speculation) ----
    GuardType { val: ValueId, ty: Type, deopt: DeoptId },
    GuardShape { obj: ValueId, shapes: ShapeSet, deopt: DeoptId },
    GuardBounds { idx: ValueId, len: ValueId, deopt: DeoptId },
    GuardNotNull { val: ValueId, deopt: DeoptId },
    GuardIsInt { val: ValueId, deopt: DeoptId },   // returns unboxed Int32
    GuardIsF64 { val: ValueId, deopt: DeoptId },   // returns unboxed F64
    Bailout { reason: String, deopt: DeoptId },

    // ---- Objects (shape-based) ----
    AllocObj { shape: ShapeId },                     // returns Obj<shape>
    LoadField { obj: ValueId, field: FieldId, expected: Option<ShapeId> },
    StoreField { obj: ValueId, field: FieldId, val: ValueId, expected: Option<ShapeId> },
    TransitionShape { obj: ValueId, to: ShapeId },   // rare add/remove property

    // ---- Arrays ----
    AllocArray { elem_hint: Option<Type>, len: ValueId },
    ArrayLen(ValueId),
    LoadElem { arr: ValueId, idx: ValueId },
    StoreElem { arr: ValueId, idx: ValueId, val: ValueId },
    ArraySlice { arr: ValueId, start: ValueId, end: ValueId },

    // High-level array intrinsics (vectorizable lowering)
    ArrayMap { func: FuncId, arr: ValueId },
    ArrayReduce { func: FuncId, init: ValueId, arr: ValueId },
    ArrayFill { arr: ValueId, val: ValueId },
    ArrayCopy { dst: ValueId, src: ValueId, len: ValueId },

    // ---- Strings ----
    StrLen(ValueId),
    StrConcat { a: ValueId, b: ValueId },
    StrSlice { s: ValueId, start: ValueId, end: ValueId },
    StrCompare { a: ValueId, b: ValueId },
    StrContains { s: ValueId, sub: ValueId },
    StrToNumber(ValueId), // may deopt on failure (lowered with guard+bailout)

    // ---- Numerics ----
    IntBin { op: IntBinOp, a: ValueId, b: ValueId },
    F64Bin { op: F64BinOp, a: ValueId, b: ValueId },
    NumAdd(ValueId, ValueId), // generic numeric add (specialize via guards)
    NumSub(ValueId, ValueId),
    NumMul(ValueId, ValueId),
    NumDiv(ValueId, ValueId),
    NumRem(ValueId, ValueId),

    CmpInt { kind: CmpKind, a: ValueId, b: ValueId },
    CmpF64 { kind: CmpKind, a: ValueId, b: ValueId },
    CmpRefEq { a: ValueId, b: ValueId },

    // ---- Boxing / tagging ----
    BoxInt(ValueId),            // i32 -> NumRef
    BoxF64(ValueId),            // f64 -> NumRef
    BoxBool(ValueId),           // bool -> AnyRef (or a well-known singleton)
    UnboxToInt(ValueId),        // Num|Int32 -> Int32 (guard if needed)
    UnboxToF64(ValueId),        // Num|F64 -> F64 (guard if needed)

    // ---- Calls / closures ----
    CallDirect {
        conv: CallConv,
        callee: FuncId,
        args: Vec<ValueId>,
    },
    // Dynamic/method call that lowers into PIC checks + direct calls.
    CallIC {
        site: SiteId,
        recv: ValueId,
        args: Vec<ValueId>,
        // Optional pre-seeded PIC entries from profile
        seed_pic: Vec<PicEntry>,
    },
    MethodLookup { obj: ValueId, name: String }, // lowered away if shape is known

    AllocClosure { func: FuncId, env_shape: Option<EnvShapeId> },
    LoadEnv { clos: ValueId, index: u32 },
    StoreEnv { clos: ValueId, index: u32, val: ValueId },

    // ---- Natives / intrinsics ----
    CallNative {
        name: String,
        args: Vec<ValueId>,
        pure: bool,
        can_throw: bool,
    },

    // ---- GC barriers (abstract) ----
    PostWriteBarrier { obj: ValueId, val: ValueId },
    ReadBarrier { obj: ValueId },

    // ---- OSR points ----
    OSRPoint, // mark loop header for on-stack replacement
}

impl Inst {
    /// Whether the instruction *requires* an incoming effect token.
    pub fn needs_effect_in(&self) -> bool {
        use Inst::*;
        matches!(
            self,
            EffectEntry
                | Safepoint
                | GuardType { .. }
                | GuardShape { .. }
                | GuardBounds { .. }
                | GuardNotNull { .. }
                | GuardIsInt { .. }
                | GuardIsF64 { .. }
                | Bailout { .. }
                | AllocObj { .. }
                | StoreField { .. }
                | TransitionShape { .. }
                | AllocArray { .. }
                | StoreElem { .. }
                | ArrayFill { .. }
                | ArrayCopy { .. }
                | StrToNumber(_)
                | CallDirect { .. }
                | CallIC { .. }
                | AllocClosure { .. }
                | StoreEnv { .. }
                | CallNative { .. }
                | PostWriteBarrier { .. }
                | ReadBarrier { .. }
        )
    }
    /// Whether the instruction *produces* a new effect token.
    pub fn produces_effect_out(&self) -> bool {
        self.needs_effect_in()
    }
}

/// One IR node (instruction) with type/effect annotations.
#[derive(Clone, Debug)]
pub struct Node {
    pub id: InstId,
    pub kind: Inst,
    pub ty: Option<Type>,                 // result type (None for void)
    pub effect_in: Option<ValueId>,       // SSA effect token input
    pub effect_out: Option<ValueId>,      // SSA effect token output (if any)
    pub results: Vec<ValueId>,            // primary SSA result(s) (usually 0 or 1)
}

/// A basic block with parameter values (including optional effect token as first param).
#[derive(Clone, Debug)]
pub struct Block {
    pub id: BlockId,
    pub params: Vec<ValueId>,       // SSA block params (data + optional effect)
    pub insts: Vec<InstId>,
    pub sealed: bool,               // for SSA construction
}

/// Function signature metadata.
#[derive(Clone, Debug, Default)]
pub struct Signature {
    pub params: Vec<Type>,
    pub returns: Vec<Type>,
    pub name: String,
}

/// A function in WIR.
#[derive(Clone, Debug)]
pub struct Function {
    pub id: FuncId,
    pub sig: Signature,
    pub blocks: Vec<Block>,
    pub nodes: Vec<Node>,
    pub values: Vec<Value>,             // SSA value table
    pub entry: BlockId,
    pub deopts: Vec<DeoptPoint>,
    pub block_params: HashMap<BlockId, Vec<Type>>,
    pub profiles: ProfileData,
}

/// SSA Value descriptor.
#[derive(Clone, Debug)]
pub struct Value {
    pub id: ValueId,
    pub ty: Option<Type>,
    pub def: ValueDef,
}

#[derive(Clone, Debug)]
pub enum ValueDef {
    InstResult(InstId, u8), // (inst, result_index)
    BlockParam(BlockId, u8),
    Const(Constant),
    EffectToken(EffectKind), // Effect SSA token
}

/// Simple profile receptacle (extend with histograms later).
#[derive(Clone, Debug, Default)]
pub struct ProfileData {
    pub block_counters: HashMap<BlockId, u64>,
    pub callsite_shapes: HashMap<SiteId, Vec<ShapeSet>>,
    pub numeric_kinds: HashMap<InstId, (u64, u64)>, // (int_hits, f64_hits)
}

/// A Module groups functions and global metadata (shapes, fields, strings).
#[derive(Clone, Debug, Default)]
pub struct Module {
    pub funcs: Vec<Function>,
    pub next_shape: u32,
    pub next_field: u32,
    pub next_envshape: u32,
    pub next_site: u32,
    pub next_deopt: u32,
    pub strings: BTreeMap<String, ValueId>,
    pub shapes: BTreeMap<String, ShapeId>, // named shapes (for testing)
    pub fields: BTreeMap<String, FieldId>, // named fields (for testing)
}

impl Module {
    pub fn new() -> Self { Self::default() }
    pub fn fresh_shape(&mut self) -> ShapeId {
        let id = ShapeId(self.next_shape);
        self.next_shape += 1;
        id
    }
    pub fn fresh_field(&mut self) -> FieldId {
        let id = FieldId(self.next_field);
        self.next_field += 1;
        id
    }
    pub fn fresh_envshape(&mut self) -> EnvShapeId {
        let id = EnvShapeId(self.next_envshape);
        self.next_envshape += 1;
        id
    }
    pub fn fresh_site(&mut self) -> SiteId {
        let id = SiteId(self.next_site);
        self.next_site += 1;
        id
    }
    pub fn fresh_deopt(&mut self, target_label: impl Into<String>) -> DeoptPoint {
        let id = DeoptId(self.next_deopt);
        self.next_deopt += 1;
        DeoptPoint { id, target_label: target_label.into(), snapshot: DeoptSnapshot::default() }
    }
}

/// -------- IR Builder --------

pub struct Builder<'m> {
    pub module: &'m mut Module,
    func: Function,
    cur_block: BlockId,
}

impl<'m> Builder<'m> {
    pub fn new(module: &'m mut Module, name: &str, params: Vec<Type>, returns: Vec<Type>) -> Self {
        let entry_block = BlockId(0);
        let mut func = Function {
            id: FuncId(0),
            sig: Signature { params: params.clone(), returns, name: name.into() },
            blocks: vec![Block { id: entry_block, params: Vec::new(), insts: Vec::new(), sealed: false }],
            nodes: Vec::new(),
            values: Vec::new(),
            entry: entry_block,
            deopts: Vec::new(),
            block_params: HashMap::new(),
            profiles: ProfileData::default(),
        };
        // Create block params for function params
        let mut block_params = Vec::new();
        for (i, ty) in params.iter().enumerate() {
            let v = ValueId(i as u32);
            func.values.push(Value {
                id: v,
                ty: Some(ty.clone()),
                def: ValueDef::BlockParam(entry_block, i as u8),
            });
            block_params.push(v);
        }
        func.blocks[0].params = block_params;
        Self { module, func, cur_block: entry_block }
    }

    pub fn finish(mut self) -> Function {
        // assign instruction and value IDs
        for (i, n) in self.func.nodes.iter_mut().enumerate() {
            n.id = InstId(i as u32);
        }
        for (i, v) in self.func.values.iter_mut().enumerate() {
            v.id = ValueId(i as u32);
        }
        self.func
    }

    pub fn push_node(&mut self, kind: Inst, ty: Option<Type>, res_count: u8, effect_in: bool) -> (InstId, Vec<ValueId>) {
        let effect_in_val = if effect_in { Some(self.ensure_effect_in()) } else { None };
        let effect_out_val = if kind.produces_effect_out() {
            Some(self.new_effect_value(EffectKind::from_inst(&kind)))
        } else { None };

        // Now it’s safe to allocate this node’s ID
        let id = InstId(self.func.nodes.len() as u32);

        // Reserve result ValueIds *after* any effect_out was created,
        // so numbering lines up with `self.func.values.len()`.
        let mut results = Vec::new();
        for r in 0..res_count {
            let vid = ValueId(self.func.values.len() as u32 + r as u32);
            results.push(vid);
        }

        let node = Node {
            id,
            kind,
            ty: ty.clone(),
            effect_in: effect_in_val,
            effect_out: effect_out_val,
            results: results.clone(),
        };
        self.func.nodes.push(node);
        self.func.blocks.iter_mut().find(|b| b.id == self.cur_block).unwrap().insts.push(id);

        for (i, _) in results.iter().enumerate() {
            self.func.values.push(Value {
                id: ValueId(self.func.values.len() as u32),
                ty: ty.clone(),
                def: ValueDef::InstResult(id, i as u8),
            });
        }
        (id, results)
    }

    fn ensure_effect_in(&mut self) -> ValueId {
        // Convention: the first param of entry block is not effect; we create an effect token node when needed.
        // We add an EffectEntry once per block at the top if none exists yet.
        // Simplified: we emit EffectEntry on first effectful instruction in the function and reuse the last effect.
        // A more robust builder would thread effect SSA explicitly.
        if let Some(last_effect) = self.last_effect_value_in_block(self.cur_block) {
            return last_effect;
        }
        let (_nid, results) = self.push_node(Inst::EffectEntry, Some(Type::Top), 1, false);
        results[0]
    }

    fn last_effect_value_in_block(&self, b: BlockId) -> Option<ValueId> {
        let block = self.func.blocks.iter().find(|blk| blk.id == b).unwrap();
        for &nid in block.insts.iter().rev() {
            let n = &self.func.nodes[nid.0 as usize];
            if let Some(eff) = n.effect_out {
                return Some(eff);
            }
        }
        None
    }

    fn new_effect_value(&mut self, kind: EffectKind) -> ValueId {
        let vid = ValueId(self.func.values.len() as u32);
        self.func.values.push(Value {
            id: vid,
            ty: Some(Type::Top),
            def: ValueDef::EffectToken(kind),
        });
        vid
    }

    pub fn block(&mut self) -> BlockId {
        let id = BlockId(self.func.blocks.len() as u32);
        self.func.blocks.push(Block { id, params: Vec::new(), insts: Vec::new(), sealed: false });
        id
    }

    pub fn position_at(&mut self, b: BlockId) { self.cur_block = b; }

    pub fn param(&self, idx: usize) -> ValueId {
        self.func.blocks[0].params[idx]
    }

    pub fn const_i32(&mut self, x: i32) -> ValueId {
        let (_nid, res) = self.push_node(Inst::Const(Constant::Int32(x)), Some(Type::Int32), 1, false);
        res[0]
    }

    pub fn const_f64(&mut self, x: f64) -> ValueId {
        let (_nid, res) = self.push_node(Inst::Const(Constant::F64(x)), Some(Type::F64), 1, false);
        res[0]
    }

    pub fn int_bin(&mut self, op: IntBinOp, a: ValueId, b: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(Inst::IntBin { op, a, b }, Some(Type::Int32), 1, false);
        res[0]
    }

    pub fn f64_bin(&mut self, op: F64BinOp, a: ValueId, b: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(Inst::F64Bin { op, a, b }, Some(Type::F64), 1, false);
        res[0]
    }

    pub fn array_len(&mut self, arr: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(Inst::ArrayLen(arr), Some(Type::Int32), 1, false);
        res[0]
    }

    pub fn guard_bounds(&mut self, idx: ValueId, len: ValueId, deopt: DeoptId) {
        let _ = self.push_node(Inst::GuardBounds { idx, len, deopt }, Some(Type::Top), 1, true);
    }

    pub fn load_elem(&mut self, arr: ValueId, idx: ValueId, elem_ty: Option<Type>) -> ValueId {
        let (_nid, res) = self.push_node(Inst::LoadElem { arr, idx }, elem_ty, 1, false);
        res[0]
    }

    pub fn add_block_param(&mut self, b: BlockId, ty: Type) -> ValueId {
        let vid = ValueId(self.func.values.len() as u32);
        self.func.values.push(Value {
            id: vid,
            ty: Some(ty.clone()),
            def: ValueDef::BlockParam(b, self.func.blocks[b.0 as usize].params.len() as u8),
        });
        self.func.blocks[b.0 as usize].params.push(vid);
        self.func.block_params.entry(b).or_default().push(ty);
        vid
    }

    pub fn branch(&mut self, cond: ValueId, then_b: BlockId, else_b: BlockId) {
        let _ = self.push_node(Inst::Branch { cond, then_b, else_b }, None, 0, false);
    }

    pub fn jump(&mut self, to: BlockId, args: &[ValueId]) {
        let _ = self.push_node(Inst::Jump(to, args.to_vec()), None, 0, false);
    }

    pub fn ret(&mut self, vals: &[ValueId]) {
        let _ = self.push_node(Inst::Return(vals.to_vec()), None, 0, false);
    }

    pub fn deopt_point(&mut self, label: &str) -> DeoptId {
        let dp = self.module.fresh_deopt(label);
        let id = dp.id;
        self.func.deopts.push(dp);
        id
    }
}

impl EffectKind {
    fn from_inst(i: &Inst) -> EffectKind {
        match i {
            crate::wir::Inst::EffectEntry => EffectKind::Entry,
            crate::wir::Inst::Safepoint   => EffectKind::Safepoint,

            crate::wir::Inst::GuardType { .. }
            | crate::wir::Inst::GuardShape { .. }
            | crate::wir::Inst::GuardBounds { .. }
            | crate::wir::Inst::GuardNotNull { .. }
            | crate::wir::Inst::GuardIsInt { .. }
            | crate::wir::Inst::GuardIsF64 { .. }
            | crate::wir::Inst::Bailout { .. } => EffectKind::Guard,

            crate::wir::Inst::AllocObj { .. }
            | crate::wir::Inst::AllocArray { .. } => EffectKind::Alloc,

            crate::wir::Inst::StoreField { .. }
            | crate::wir::Inst::StoreElem { .. }
            | crate::wir::Inst::TransitionShape { .. } => EffectKind::Store,

            crate::wir::Inst::CallDirect { .. }
            | crate::wir::Inst::CallIC { .. }
            | crate::wir::Inst::CallNative { .. }
            | crate::wir::Inst::AllocClosure { .. }
            | crate::wir::Inst::StoreEnv { .. } => EffectKind::Call,

            crate::wir::Inst::PostWriteBarrier { .. }
            | crate::wir::Inst::ReadBarrier { .. } => EffectKind::Barrier,

            // May call into runtime:
            crate::wir::Inst::StrToNumber(_) => EffectKind::Call,

            // Default tag for pure ops:
            _ => EffectKind::Entry,
        }
    }
}

/// -------- Pretty printers (debug helpers) --------

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "func {}(", self.sig.name)?;
        for (i, t) in self.sig.params.iter().enumerate() {
            writeln!(f, "  %p{}: {:?}", i, t)?;
        }
        writeln!(f, ") -> {:?}", self.sig.returns)?;
        for b in &self.blocks {
            writeln!(f, "block {:?}(", b.id)?;
            for (i, p) in b.params.iter().enumerate() {
                let ty = self.values[p.0 as usize].ty.clone().unwrap_or(Type::Top);
                writeln!(f, "  %{:?} : {:?}", p, ty)?;
                if i + 1 == b.params.len() { writeln!(f, ")")?; }
            }
            for nid in &b.insts {
                let n = &self.nodes[nid.0 as usize];
                let res_list = n.results.iter().map(|v| format!("%{:?}", v)).collect::<Vec<_>>().join(", ");
                let ty = n.ty.as_ref().map(|t| format!("{:?}", t)).unwrap_or_else(|| "_".into());
                writeln!(f, "  {} = {:?} :: {}", res_list, n.kind, ty)?;
            }
        }
        Ok(())
    }
}

/// -------- Tiny smoke test (optional) --------
/// Run with `cargo test` to validate the builder compiles and IR prints.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_small_loop() {
        let mut m = Module::new();
        // Shapes/fields
        let shape_vec = m.fresh_shape();
        let _field_data = m.fresh_field();

        // function: sum(arr: Array<i32>) -> i32
        let mut b = Builder::new(&mut m, "sum", vec![Type::Array(Box::new(Some(Type::Int32)))], vec![Type::Int32]);
        let arr = b.param(0);
        let len = b.array_len(arr);
        let zero = b.const_i32(0);
        let one = b.const_i32(1);

        // header block params: i (i32), s (i32)
        let hdr = b.block();
        b.position_at(hdr);
        let i = b.add_block_param(hdr, Type::Int32);
        let s = b.add_block_param(hdr, Type::Int32);

        // Prologue: jump to hdr(0, 0)
        b.position_at(b.func.entry);
        b.jump(hdr, &[zero, zero]);

        // In header: guard bounds; load elem; accumulate; branch
        b.position_at(hdr);
        let de = b.deopt_point("sum@loop");
        b.guard_bounds(i, len, de);
        let x = b.load_elem(arr, i, Some(Type::Int32));
        let s1 = b.int_bin(IntBinOp::Add, s, x);
        let i1 = b.int_bin(IntBinOp::Add, i, one);

        // if (i1 < len) goto hdr(i1, s1) else return s1
        let cond = {
            let (_nid, res) = b.push_node(Inst::CmpInt { kind: CmpKind::Lt, a: i1, b: len }, Some(Type::Bool), 1, false);
            res[0]
        };
        let exit = b.block();
        b.branch(cond, hdr, exit);
        b.position_at(hdr);
        b.jump(hdr, &[i1, s1]); // backedge

        // exit
        b.position_at(exit);
        b.ret(&[s1]);

        let func = b.finish();
        // print for debug
        println!("{}", func);
        assert_eq!(func.sig.name, "sum");
    }
}
