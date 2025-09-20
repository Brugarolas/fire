// wir.rs
//! WIR — Wyvern IR (mid–high level, SSA, speculation-friendly)
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
//! - Type lattice with unions, for type inference/speculation.

#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::too_many_arguments)]

use std::collections::{BTreeMap, BTreeSet};
use ahash::AHashMap as HashMap;
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
id_newtype!(ClassId);
id_newtype!(BindingId); // ESM live binding cell

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

    Class(Option<ClassId>),
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
            Class(Some(id)) => write!(f, "Class#{:?}", id),
            Class(None) => write!(f, "Class<?>"),
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IntBinOp { Add, Sub, Mul, DivS, RemS, And, Or, Xor, Shl, ShrU, Sar }
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum F64BinOp { Add, Sub, Mul, Div, Rem }

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CmpKind { Eq, Ne, Lt, Le, Gt, Ge }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumKind { Int32, F64, Num } // helper for mixed-num ops

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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

#[derive(Clone, Debug)]
pub struct ClassMeta {
    pub id: ClassId,
    pub name: String,
    pub base: Option<ClassId>,
    pub instance_shape: ShapeId, // initial hidden-class for instances
    pub static_shape: ShapeId,   // hidden-class for the class object (statics)
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
    ArrayLen (ValueId),
    ArraySetLen { arr: ValueId, new_len: ValueId },
    LoadElem { arr: ValueId, idx: ValueId },
    StoreElem { arr: ValueId, idx: ValueId, val: ValueId },
    ArraySlice { arr: ValueId, start: ValueId, end: ValueId },

    // Array methods
    ArrayPush { arr: ValueId, val: ValueId }, // returns new length
    ArrayPop  (ValueId),                    // returns popped value or Null
    ArrayShift  (ValueId),                  // returns shifted value or Null
    ArrayUnshift { arr: ValueId, val: ValueId }, // returns new length

    // High-level array intrinsics (vectorizable lowering)
    ArrayMap { func: FuncId, arr: ValueId },
    ArrayReduce { func: FuncId, init: ValueId, arr: ValueId },
    ArrayFill { arr: ValueId, val: ValueId },
    ArrayCopy { dst: ValueId, src: ValueId, len: ValueId },

    // Extra high-level methods
    ArrayForEach   { func: FuncId, arr: ValueId }, // returns Null
    ArrayFind      { func: FuncId, arr: ValueId }, // returns element or Null
    ArrayFindIndex { func: FuncId, arr: ValueId }, // returns i32 (-1 if not found)
    ArrayFilter    { func: FuncId, arr: ValueId }, // returns Array<?>

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
    CallDirectMemoized {
        callee: FuncId,         // target function
        args: Vec<ValueId>,     // MUST be 1 arg to benefit, but we keep Vec for parity
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

    MakeClosure { callee: FuncId, env: ValueId },
    CallClosure { conv: CallConv, fun: ValueId, args: Vec<ValueId> },

    /// Register a class with the runtime. Prefer ids to strings for stability.
    RegisterClass {
        meta: ClassMeta,
        // Pre-resolved field ids (avoid string lookups at runtime)
        fields: Vec<FieldId>,                                  // instance fields
        statics: Vec<FieldId>,                                 // static fields
        methods: Vec<(FieldId, FuncId, /*is_static*/ bool)>,   // name, target, static?
        accessors: Vec<(FieldId, Option<FuncId>, Option<FuncId>, /*is_static*/ bool)>,
        // Optional known constructor (instance). If None, default ctor.
        ctor: Option<FuncId>,
    },

    /// Allocate a zeroed instance (does NOT run the constructor).
    AllocInstance { class: ClassId },

    /// Resolve a method by name on the receiver’s shape (non-super).
    /// Returns a callable value (lowered to closure or direct target).
    LoadMethod {
        obj: ValueId,
        method: FieldId,
        /// If present, we guard receiver’s shape before lookup.
        expected: Option<ShapeId>,
    },

    /// Resolve a method starting from the base (super) of `home_class`.
    /// Used exactly for `super.m`.
    LoadSuperMethod {
        recv: ValueId,
        home_class: ClassId,
        method: FieldId,
    },

    /// PIC-based method call: `recv.method(args...)` (no separate lookup result flows).
    CallMethodIC {
        site: SiteId,
        recv: ValueId,
        method: FieldId,           // the name at this callsite
        args: Vec<ValueId>,
        seed_pic: Vec<PicEntry>,
    },

    /// Direct `super.m(args...)` call. Can be lowered as LoadSuperMethod + CallDirect.
    CallSuper {
        home_class: ClassId,
        recv: ValueId,
        method: FieldId,
        args: Vec<ValueId>,
    },

    /// `obj instanceof C`
    InstanceOf {
        obj: ValueId,
        class: ClassId,
    },

    // ---- Natives / intrinsics ----
    CallNative {
        name: String,
        args: Vec<ValueId>,
        pure: bool,
        can_throw: bool,
    },

    // ---- Timers / event loop (JS-like) ----
    SetTimeout   { fun: ValueId, delay_ms: ValueId },   // -> Int32 (timer id)
    SetInterval  { fun: ValueId, period_ms: ValueId },  // -> Int32 (timer id)
    ClearTimeout { id: ValueId },                        // void
    ClearInterval{ id: ValueId },                        // void

    // Optional (tiny helper to run N ready tasks; useful for strategic pumping)
    EventLoopPump { budget: u32 },                       // -> Int32 (ran count)

    // ---- GC barriers (abstract) ----
    PostWriteBarrier { obj: ValueId, val: ValueId },
    ReadBarrier { obj: ValueId },

    // ---- OSR points ----
    OSRPoint, // mark loop header for on-stack replacement

    // ---- Modules / ESM live bindings ----
    /// Read from an ESM live binding cell. Throws on TDZ (uninitialized).
    LoadBinding { binding: BindingId },

    /// Write to an ESM live binding cell (used by the *owning* module for its exports).
    StoreBinding { binding: BindingId, val: ValueId },

    /// Build a frozen ESM namespace object with getters wired to live bindings.
    MakeNamespace { exports: Vec<(String, BindingId)> },

    /// Dynamic `import(spec)`: resolves/links/evaluates and returns a Promise for the namespace.
    ImportDynamic { spec: ValueId },
}

#[derive(Debug, Clone)]
pub struct MethodInfo {
    name: String,
    func: FuncId,
    is_static: bool,
}
#[derive(Debug, Clone)]
pub struct AccessorInfo {
    name: String,
    getter: Option<FuncId>,
    setter: Option<FuncId>,
    is_static: bool,
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
                // mutating array ops
                | ArrayPush { .. }
                | ArrayPop ( .. )
                | ArrayShift ( .. )
                | ArrayUnshift { .. }
                // higher-order ops (call user code / runtime)
                | ArrayMap { .. }
                | ArrayReduce { .. }
                | ArrayForEach { .. }
                | ArrayFind { .. }
                | ArrayFindIndex { .. }
                | ArrayFilter { .. }
                | ArrayReduce { .. }
                | StrToNumber(_)
                | CallDirect { .. }
                | CallDirectMemoized { .. }
                | CallIC { .. }
                | CallClosure { .. }
                | AllocClosure { .. }
                | StoreEnv { .. }
                | CallNative { .. }
                | PostWriteBarrier { .. }
                | ReadBarrier { .. }
                | RegisterClass { .. }  // mutates global class registry
                | AllocInstance { .. }
                | CallMethodIC { .. }
                | CallSuper { .. }
                // Modules / ESM
                | LoadBinding { .. }     // may throw TDZ → model as effectful guard
                | StoreBinding { .. }    // writes a live cell
                | MakeNamespace { .. }   // allocates a namespace object
                | ImportDynamic { .. }   // schedules async load/eval (calls runtime)
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
    pub next_class: u32,
    pub strings: BTreeMap<String, ValueId>,
    pub shapes: BTreeMap<String, ShapeId>, // named shapes (for testing)
    pub fields: BTreeMap<String, FieldId>, // named fields (for testing)
    pub next_binding: u32,
}

impl Module {
    pub fn new() -> Self { Self::default() }
    pub fn fresh_binding(&mut self) -> BindingId {
        let id = BindingId(self.next_binding);
        self.next_binding += 1;
        id
    }
    pub fn fresh_class(&mut self) -> ClassId {
        let id = ClassId(self.next_class);
        self.next_class += 1;
        id
    }
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
    pub fn push_function(&mut self, mut f: Function) -> FuncId {
        let id = FuncId(self.funcs.len() as u32);
        f.id = id;
        self.funcs.push(f);
        id
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

    pub fn current_block_terminated(&self) -> bool {
        let blk = self.func.blocks.iter().find(|b| b.id == self.cur_block).unwrap();
        if let Some(&last) = blk.insts.last() {
            use crate::wir::Inst;
            matches!(
                self.func.nodes[last.0 as usize].kind,
                Inst::Return(_)
                    | Inst::Branch { .. }
                    | Inst::Jump(_, _)
                    | Inst::Throw(_)
            )
        } else {
            false
        }
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

    // ---- classes ----
    pub fn register_class(
        &mut self,
        meta: ClassMeta,
        fields: Vec<FieldId>,
        statics: Vec<FieldId>,
        methods: Vec<(FieldId, FuncId, bool)>,
        accessors: Vec<(FieldId, Option<FuncId>, Option<FuncId>, bool)>,
        ctor: Option<FuncId>,
    ) {
        let _ = self.push_node(
            Inst::RegisterClass { meta, fields, statics, methods, accessors, ctor },
            Some(Type::Top),
            0,
            true,
        );
    }

    pub fn alloc_instance(&mut self, class: ClassId) -> ValueId {
        let (_nid, res) = self.push_node(
            Inst::AllocInstance { class },
            Some(Type::Obj(ShapeSet::default())), // precise shape comes from runtime/class meta
            1,
            true,
        );
        res[0]
    }

    pub fn load_method(&mut self, obj: ValueId, method: FieldId, expected: Option<ShapeId>) -> ValueId {
        let (_nid, res) = self.push_node(
            Inst::LoadMethod { obj, method, expected },
            Some(Type::Closure(None)),
            1,
            false,
        );
        res[0]
    }

    pub fn load_super_method(&mut self, recv: ValueId, home_class: ClassId, method: FieldId) -> ValueId {
        let (_nid, res) = self.push_node(
            Inst::LoadSuperMethod { recv, home_class, method },
            Some(Type::Closure(None)),
            1,
            false,
        );
        res[0]
    }

    pub fn call_method_ic(
        &mut self,
        site: SiteId,
        recv: ValueId,
        method: FieldId,
        args: Vec<ValueId>,
        seed_pic: Vec<PicEntry>,
    ) -> ValueId {
        let (_nid, res) = self.push_node(
            Inst::CallMethodIC { site, recv, method, args, seed_pic },
            Some(Type::Int32), // adjust per language return typing; keep Top/Union if unknown
            1,
            true,
        );
        res[0]
    }

    pub fn call_super(
        &mut self,
        home_class: ClassId,
        recv: ValueId,
        method: FieldId,
        args: Vec<ValueId>,
    ) -> ValueId {
        let (_nid, res) = self.push_node(
            Inst::CallSuper { home_class, recv, method, args },
            Some(Type::Int32),
            1,
            true,
        );
        res[0]
    }

    pub fn instanceof(&mut self, obj: ValueId, class: ClassId) -> ValueId {
        let (_nid, res) = self.push_node(
            Inst::InstanceOf { obj, class },
            Some(Type::Bool),
            1,
            false,
        );
        res[0]
    }

    /// Allocate a fresh ESM live-binding cell in the *current module*.
    /// The IR does not store names for bindings; the caller should keep the
    /// (name -> BindingId) mapping (e.g., in LinkInfo).
    pub fn define_binding_cell(&mut self) -> BindingId {
        self.module.fresh_binding()
    }

    /// Convenience alias used when creating cells for *exports*.
    /// `name` is only for the caller's bookkeeping/logging.
    pub fn define_export_cell(&mut self, _name: &str) -> BindingId {
        self.define_binding_cell()
    }

    /// Convenience alias used when creating cells to cache namespace objects.
    /// `name` is only for the caller's bookkeeping/logging.
    pub fn define_namespace_cell(&mut self, _name: &str) -> BindingId {
        self.define_binding_cell()
    }

    pub fn const_bool(&mut self, x: bool) -> ValueId {
        let (_nid, res) = self.push_node(Inst::Const(Constant::Bool(x)), Some(Type::Bool), 1, false);
        res[0]
    }
    pub fn const_null(&mut self) -> ValueId {
        let (_nid, res) = self.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
        res[0]
    }
    pub fn const_str(&mut self, s: &str) -> ValueId {
        let (_nid, res) = self.push_node(Inst::Const(Constant::Str(s.to_string())), Some(Type::Str), 1, false);
        res[0]
    }
}

impl EffectKind {
    fn from_inst(i: &Inst) -> EffectKind {
        match i {
            // treated as structural; group with Entry for ordering
            crate::wir::Inst::EffectEntry
            | crate::wir::Inst::LoadMethod { .. }
            | crate::wir::Inst::LoadSuperMethod { .. }
            | crate::wir::Inst::InstanceOf { .. } => EffectKind::Entry,

            crate::wir::Inst::Safepoint => EffectKind::Safepoint,

            // Guards / checks
            crate::wir::Inst::GuardType { .. }
            | crate::wir::Inst::GuardShape { .. }
            | crate::wir::Inst::GuardBounds { .. }
            | crate::wir::Inst::GuardNotNull { .. }
            | crate::wir::Inst::GuardIsInt { .. }
            | crate::wir::Inst::GuardIsF64 { .. }
            | crate::wir::Inst::Bailout { .. }
            // ESM: reading a binding may throw TDZ → clasifícalo como guard
            | crate::wir::Inst::LoadBinding { .. } => EffectKind::Guard,

            // Allocations
            crate::wir::Inst::AllocObj { .. }
            | crate::wir::Inst::AllocArray { .. }
            | crate::wir::Inst::RegisterClass { .. }
            | crate::wir::Inst::AllocInstance { .. }
            | crate::wir::Inst::MakeNamespace { .. } => EffectKind::Alloc,

            // Stores / mutations
            crate::wir::Inst::StoreField { .. }
            | crate::wir::Inst::StoreElem { .. }
            | crate::wir::Inst::TransitionShape { .. }
            | crate::wir::Inst::ArrayPush { .. }
            | crate::wir::Inst::ArrayPop ( .. )
            | crate::wir::Inst::ArrayShift ( .. )
            | crate::wir::Inst::ArrayUnshift { .. }
            | crate::wir::Inst::ArrayFill { .. }
            | crate::wir::Inst::ArrayCopy { .. }
            // ESM: write to an export cell
            | crate::wir::Inst::StoreBinding { .. } => EffectKind::Store,

            // Calls (user/runtime)
            crate::wir::Inst::CallDirect { .. }
            | crate::wir::Inst::CallDirectMemoized { .. }
            | crate::wir::Inst::CallIC { .. }
            | crate::wir::Inst::CallClosure { .. }
            | crate::wir::Inst::CallNative { .. }
            | crate::wir::Inst::AllocClosure { .. }
            | crate::wir::Inst::StoreEnv { .. }
            | crate::wir::Inst::ArrayMap { .. }
            | crate::wir::Inst::ArrayReduce { .. }
            | crate::wir::Inst::ArrayForEach { .. }
            | crate::wir::Inst::ArrayFind { .. }
            | crate::wir::Inst::ArrayFindIndex { .. }
            | crate::wir::Inst::ArrayFilter { .. }
            | crate::wir::Inst::StrToNumber(_)
            | crate::wir::Inst::CallMethodIC { .. }
            | crate::wir::Inst::CallSuper { .. }
            // ESM: dynamic import calls into the loader/runtime
            | crate::wir::Inst::ImportDynamic { .. } => EffectKind::Call,

            // Barriers
            crate::wir::Inst::PostWriteBarrier { .. }
            | crate::wir::Inst::ReadBarrier { .. } => EffectKind::Barrier,

            _ => EffectKind::from_inst_default(i),
        }
    }
}

impl EffectKind {
    fn from_inst_default(i: &Inst) -> EffectKind {
        match i {
            // paste your existing big match body here, EXCEPT the new cases handled above
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

impl<'m> Builder<'m> {
    pub fn make_closure(&mut self, callee: FuncId, env: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(
            Inst::MakeClosure { callee, env },
            Some(Type::Closure(None)),   // <-- fix
            1,
            false,
        );
        res[0]
    }
    pub fn call_closure(&mut self, fun: ValueId, args: Vec<ValueId>) -> ValueId {
        let (_nid, res) = self.push_node(
            Inst::CallClosure { conv: CallConv::Fast, fun, args },
            Some(Type::Int32),
            1,
            true,
        );
        res[0]
    }
}

impl<'m> Builder<'m> {
        /// Read from an ESM live binding cell. `ty` is optional; leave `None` and let the
    /// type engine infer/attach after linking if no static info is available.
    pub fn load_binding(&mut self, binding: BindingId, ty: Option<Type>) -> ValueId {
        let (_nid, res) = self.push_node(
            Inst::LoadBinding { binding },
            ty,        // often None; can be Some if the resolver knows it
            1,
            true,      // may throw TDZ → needs effect
        );
        res[0]
    }

    /// Write to an ESM live binding cell (only the *owning* module should emit this).
    pub fn store_binding(&mut self, binding: BindingId, val: ValueId) {
        let _ = self.push_node(
            Inst::StoreBinding { binding, val },
            Some(Type::Top), // no value result
            0,
            true,            // it mutates shared binding state
        );
    }

    /// Build a frozen namespace object backed by live getters to the given bindings.
    /// The resolver lowers `import * as ns from "..."` to this single op.
    pub fn make_namespace(&mut self, exports: Vec<(String, BindingId)>) -> ValueId {
        let (_nid, res) = self.push_node(
            Inst::MakeNamespace { exports },
            Some(Type::AnyRef), // could be a dedicated ModuleNamespace type later
            1,
            true,               // allocates
        );
        res[0]
    }

    /// Dynamic `import(spec)`: `spec` must be a string at runtime; returns a Promise of namespace.
    pub fn import_dynamic(&mut self, spec: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(
            Inst::ImportDynamic { spec },
            Some(Type::AnyRef), // Promise<any>; use a dedicated Promise<T> type later if desired
            1,
            true,               // calls into loader/runtime
        );
        res[0]
    }

    pub fn array_push(&mut self, arr: ValueId, val: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(Inst::ArrayPush { arr, val }, Some(Type::Int32), 1, true);
        res[0]
    }
    pub fn array_pop(&mut self, arr: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(Inst::ArrayPop(arr), None, 1, true);
        res[0]
    }
    pub fn array_shift(&mut self, arr: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(Inst::ArrayShift(arr), None, 1, true);
        res[0]
    }
    pub fn array_unshift(&mut self, arr: ValueId, val: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(Inst::ArrayUnshift { arr, val }, Some(Type::Int32), 1, true);
        res[0]
    }

    pub fn array_map(&mut self, func: FuncId, arr: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(Inst::ArrayMap { func, arr }, Some(Type::Array(Box::new(None))), 1, true);
        res[0]
    }
    pub fn array_for_each(&mut self, func: FuncId, arr: ValueId) {
        let _ = self.push_node(Inst::ArrayForEach { func, arr }, Some(Type::Null), 0, true);
    }
    pub fn array_find(&mut self, func: FuncId, arr: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(Inst::ArrayFind { func, arr }, None, 1, true);
        res[0]
    }
    pub fn array_find_index(&mut self, func: FuncId, arr: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(Inst::ArrayFindIndex { func, arr }, Some(Type::Int32), 1, true);
        res[0]
    }
    pub fn array_filter(&mut self, func: FuncId, arr: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(Inst::ArrayFilter { func, arr }, Some(Type::Array(Box::new(None))), 1, true);
        res[0]
    }
    pub fn array_reduce(&mut self, func: FuncId, init: ValueId, arr: ValueId) -> ValueId {
        let (_nid, res) = self.push_node(
            Inst::ArrayReduce { func, init, arr },
            Some(Type::Int32),
            1,
            true,
        );
        res[0]
    }
}
