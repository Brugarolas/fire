// src/lowerer.rs
#![allow(unused_variables)]

use crate::helpers::collections::{HashMap, HashSet};
use logos::Logos;
use smallbox::SmallBox;
use std::cell::Cell;
use std::collections::hash_map::Entry;
use std::{collections::BTreeSet, ops::Deref};

// Bring in the WIR types from your other file/module.
use crate::wir::{
    AccessorInfo, BindingId, BlockId, Builder, Constant, FieldId, FuncId, Inst, IntBinOp,
    MethodInfo, Module, TryExitKind, TryHandler, TryRegion, TryRegionId, Type, ValueId, next_id,
};

use crate::diag::Node;
use crate::front::{
    BinOp, Block, CatchClause, ClassDecl, ClassMember, DeferKind, ExportDecl, Expr, ExprKind,
    FuncDecl, ImportDecl, ImportItem, LValue, LValueKind, ListenDecl, ObjItem, ObjPattern,
    OptionalAccess, Program, PropKey, RouteDecl, RtCheck, Stmt, StmtKind, TypedOp, UnOp,
};

use crate::hoister::hoist_fn_lits_program;

#[inline]
fn stmt_unknown(kind: StmtKind) -> Stmt {
    Node::unknown(kind)
}

#[inline]
fn expr_unknown(kind: ExprKind) -> Expr {
    Node::unknown(kind)
}

#[inline]
fn lvalue_unknown(kind: LValueKind) -> LValue {
    Node::unknown(kind)
}

#[inline]
fn stmt_with_meta(template: &Stmt, kind: StmtKind) -> Stmt {
    Node::new(template.meta.clone(), kind)
}

#[inline]
fn expr_with_meta(template: &Expr, kind: ExprKind) -> Expr {
    Node::new(template.meta.clone(), kind)
}

#[inline]
fn lvalue_with_meta(template: &LValue, kind: LValueKind) -> LValue {
    Node::new(template.meta.clone(), kind)
}

#[derive(Clone)]
struct TryScope {
    region: TryRegionId,
    continuation: BlockId,
    finally: Option<BlockId>,
    locals: Vec<String>,
}

#[derive(Clone, Debug)]
struct TryLeaveInfo {
    region: TryRegionId,
    continuation: BlockId,
    finally: Option<BlockId>,
    locals: Vec<ValueId>,
}

fn emit_try_leave_chain<'m>(
    b: &mut Builder<'m>,
    stack: &[TryScope],
    locals: &HashMap<String, ValueId>,
    exit: TryExitKind,
) -> Vec<TryLeaveInfo> {
    let mut out: Vec<TryLeaveInfo> = Vec::with_capacity(stack.len());
    for scope in stack.iter().rev() {
        let mut captured: Vec<ValueId> = Vec::with_capacity(scope.locals.len());
        for name in &scope.locals {
            let val = *locals
                .get(name)
                .unwrap_or_else(|| panic!("missing local '{}' for try scope", name));
            captured.push(val);
        }

        let locals_vec = captured.clone();
        let _ = b.push_node(
            Inst::TryLeave {
                region: scope.region,
                exit,
                locals: locals_vec,
            },
            None,
            0,
            true,
        );
        out.push(TryLeaveInfo {
            region: scope.region,
            continuation: scope.continuation,
            finally: scope.finally,
            locals: captured,
        });
    }
    out
}

fn snapshot_try_locals(b: &mut Builder<'_>, locals: &HashMap<String, ValueId>) {
    if b.current_block_terminated() {
        return;
    }
    for (region, names) in b.try_local_scopes.clone() {
        let values = names.iter().map(|name| locals[name]).collect();
        b.push_node(
            Inst::TryLeave {
                region,
                exit: TryExitKind::Snapshot,
                locals: values,
            },
            None,
            0,
            true,
        );
    }
}

fn lower_try_stmt_generic<'m, F>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    try_block: &Block,
    catch: Option<&CatchClause>,
    finally_block: Option<&Block>,
    lowering_ctx: &LoweringContext,
    active_try: &mut Vec<TryScope>,
    mut lower_block: F,
) -> LResult<()>
where
    F: FnMut(
        &mut Builder<'m>,
        &mut HashMap<String, ValueId>,
        &mut HashMap<String, FieldId>,
        &mut u32,
        &Block,
        &LoweringContext,
        &mut Vec<TryScope>,
    ) -> LResult<()>,
{
    let stack_depth_before = active_try.len();

    let mut mutated_names: Vec<String> = locals.keys().cloned().collect();
    mutated_names.extend(collect_mut_locals_in_block(try_block));
    if let Some(c) = catch {
        mutated_names.extend(collect_mut_locals_in_block(&c.body));
    }
    if let Some(fin) = finally_block {
        mutated_names.extend(collect_mut_locals_in_block(fin));
    }
    let try_entry = b.block();
    let continuation = b.block();
    let finally_entry = finally_block.map(|_| b.block());
    let catch_entry = catch.map(|_| b.block());

    mutated_names.sort();
    mutated_names.dedup();
    mutated_names.retain(|name| locals.contains_key(name));
    #[cfg(debug_assertions)]
    eprintln!(
        "[lower_try] try_entry={:?} continuation={:?} mutated={:?}",
        try_entry, continuation, mutated_names
    );

    let mut mutated_types: HashMap<String, Type> = HashMap::new();
    for name in &mutated_names {
        if let Some(&vid) = locals.get(name) {
            if let Some(ty) = b.value_ty(vid) {
                mutated_types.insert(name.clone(), ty);
            } else {
                mutated_types.insert(name.clone(), Type::Top);
            }
        }
    }

    let mut cont_params: HashMap<String, ValueId> = HashMap::new();
    for name in &mutated_names {
        let ty = mutated_types.get(name).cloned().unwrap_or(Type::Top);
        let param = b.add_block_param(continuation, ty);
        cont_params.insert(name.clone(), param);
    }

    let mut finally_params: Vec<(String, ValueId)> = Vec::new();
    if let Some(fin_id) = finally_entry {
        for name in &mutated_names {
            let ty = mutated_types.get(name).cloned().unwrap_or(Type::Top);
            let param = b.add_block_param(fin_id, ty);
            finally_params.push((name.clone(), param));
        }
    }

    let catches_meta = if let (Some(catch_clause), Some(handler)) = (catch, catch_entry) {
        vec![TryHandler {
            handler,
            binds_exception: catch_clause.binding.is_some(),
        }]
    } else {
        Vec::new()
    };

    let region_id = b.add_try_region(TryRegion {
        id: TryRegionId(0),
        try_entry,
        continuation,
        catches: catches_meta,
        finally_entry,
        body_blocks: Vec::new(),
        catch_blocks: Vec::new(),
    });

    let _ = b.push_node(Inst::TryEnter { region: region_id }, None, 0, true);
    b.jump(try_entry, &[]);

    active_try.push(TryScope {
        region: region_id,
        continuation,
        finally: finally_entry,
        locals: mutated_names.clone(),
    });
    b.try_local_scopes.push((region_id, mutated_names.clone()));
    let mut region_popped = false;

    let incoming_locals = locals.clone();
    let gather_args = |map: &HashMap<String, ValueId>| -> Vec<ValueId> {
        mutated_names
            .iter()
            .map(|name| {
                *map.get(name)
                    .or_else(|| incoming_locals.get(name))
                    .expect("mutated local missing in scope")
            })
            .collect()
    };

    let mut cont_has_path = false;

    // Lower try body
    b.position_at(try_entry);
    let body_start = b.block_count();
    let mut locals_try = incoming_locals.clone();
    snapshot_try_locals(b, &locals_try);
    lower_block(
        b,
        &mut locals_try,
        fields,
        next_field,
        try_block,
        lowering_ctx,
        active_try,
    )?;
    let mut body_blocks = vec![try_entry];
    body_blocks.extend((body_start..b.block_count()).map(|i| BlockId(i as u32)));
    if !b.current_block_terminated() {
        #[cfg(debug_assertions)]
        eprintln!(
            "[lower_try] after try-body mutated={:?} keys={:?}",
            mutated_names,
            locals_try.keys().collect::<Vec<_>>()
        );
        let args = gather_args(&locals_try);
        let locals_vec = args.clone();
        let _ = b.push_node(
            Inst::TryLeave {
                region: region_id,
                exit: TryExitKind::Normal,
                locals: locals_vec.clone(),
            },
            None,
            0,
            true,
        );
        if let Some(fin_id) = finally_entry {
            let _ = b.push_node(
                Inst::TryFinallyEnter {
                    region: region_id,
                    locals: locals_vec,
                    error: None,
                },
                None,
                0,
                true,
            );
            b.jump(fin_id, &args);
        } else {
            b.jump(continuation, &args);
            cont_has_path = true;
        }
    }

    // Lower catch, if present
    let mut catch_blocks = Vec::new();
    if let (Some(catch_clause), Some(catch_id)) = (catch, catch_entry) {
        b.position_at(catch_id);
        let catch_start = b.block_count();
        let mut locals_catch = incoming_locals.clone();
        let exception = catch_clause.binding.as_ref()
            .map(|_| b.add_block_param(catch_id, Type::Top));
        for name in &mutated_names {
            let ty = mutated_types.get(name).cloned().unwrap_or(Type::Top);
            let param = b.add_block_param(catch_id, ty);
            locals_catch.insert(name.clone(), param);
        }
        let saved_snapshot_scopes = b.try_local_scopes.clone();
        let saved_try_scopes = active_try.clone();
        let shadow = catch_clause.binding.as_ref().and_then(|binding| {
            locals_catch.get(binding).copied().map(|value| {
                let saved = format!("\0catch_{}_{}", region_id.0, binding);
                locals_catch.insert(saved.clone(), value);
                for (_, names) in &mut b.try_local_scopes {
                    for name in names {
                        if name == binding {
                            *name = saved.clone();
                        }
                    }
                }
                for scope in active_try.iter_mut() {
                    for name in &mut scope.locals {
                        if name == binding {
                            *name = saved.clone();
                        }
                    }
                }
                (binding.clone(), saved)
            })
        });
        if let (Some(binding), Some(exception)) = (&catch_clause.binding, exception) {
            locals_catch.insert(binding.clone(), exception);
        }
        lower_block(
            b,
            &mut locals_catch,
            fields,
            next_field,
            &catch_clause.body,
            lowering_ctx,
            active_try,
        )?;
        b.try_local_scopes = saved_snapshot_scopes;
        *active_try = saved_try_scopes;
        if let Some((binding, saved)) = shadow {
            let value = locals_catch[&saved];
            locals_catch.insert(binding, value);
        }
        catch_blocks.push(catch_id);
        catch_blocks.extend((catch_start..b.block_count()).map(|i| BlockId(i as u32)));
        if !b.current_block_terminated() {
            #[cfg(debug_assertions)]
            eprintln!(
                "[lower_try] catch path mutated={:?} keys={:?}",
                mutated_names,
                locals_catch.keys().collect::<Vec<_>>()
            );
            let args = gather_args(&locals_catch);
            let locals_vec = args.clone();
            let _ = b.push_node(
                Inst::TryLeave {
                    region: region_id,
                    exit: TryExitKind::Normal,
                    locals: locals_vec.clone(),
                },
                None,
                0,
                true,
            );
            if let Some(fin_id) = finally_entry {
                let _ = b.push_node(
                    Inst::TryFinallyEnter {
                        region: region_id,
                        locals: locals_vec,
                        error: None,
                    },
                    None,
                    0,
                    true,
                );
                b.jump(fin_id, &args);
            } else {
                b.jump(continuation, &args);
                cont_has_path = true;
            }
        }
    }

    // Lower finally, if present
    b.try_local_scopes.pop();
    if let Some(fin_id) = finally_entry {
        let popped = active_try
            .pop()
            .expect("try scope should be active before finally");
        debug_assert_eq!(popped.region, region_id);
        region_popped = true;

        b.position_at(fin_id);
        let mut locals_finally = incoming_locals.clone();
        for (name, param) in &finally_params {
            locals_finally.insert(name.clone(), *param);
        }
        lower_block(
            b,
            &mut locals_finally,
            fields,
            next_field,
            finally_block.expect("finally block"),
            lowering_ctx,
            active_try,
        )?;
        if !b.current_block_terminated() {
            #[cfg(debug_assertions)]
            eprintln!(
                "[lower_try] finally path mutated={:?} keys={:?}",
                mutated_names,
                locals_finally.keys().collect::<Vec<_>>()
            );
            let args = gather_args(&locals_finally);
            let _ = b.push_node(Inst::TryFinallyExit { region: region_id }, None, 0, true);
            b.jump(continuation, &args);
            cont_has_path = true;
        }
    }

    if !region_popped {
        let popped = active_try.pop().expect("try scope should still be active");
        debug_assert_eq!(popped.region, region_id);
    }
    debug_assert_eq!(active_try.len(), stack_depth_before);
    b.set_try_blocks(region_id, body_blocks, catch_blocks);

    b.position_at(continuation);
    if cont_has_path {
        for name in &mutated_names {
            if let Some(&param) = cont_params.get(name) {
                locals.insert(name.clone(), param);
            }
        }
    } else {
        for name in &mutated_names {
            if let Some(val) = incoming_locals.get(name) {
                locals.insert(name.clone(), *val);
            }
        }
    }

    Ok(())
}
// -------------------------
/// LOWERING (AST â†’ WIR)
/// -------------------------

#[derive(Debug, Clone)]
struct ClassInfo {
    name: String,
    base: Option<String>,
    has_ctor: bool,
    has_dtor: bool,
    instance_fields: Vec<(String, Option<Expr>)>,
    props: Vec<(String, Option<Block>, Option<(String, Block)>)>, // name, getter, setter
    methods: Vec<(String, Vec<String>, Block, bool)>,             // instance methods
    static_vars: Vec<(String, Option<Expr>)>,
    static_methods: Vec<(String, Vec<String>, Block, bool)>,
}

#[derive(Debug)]
pub enum LowerError {
    UnknownVar(String),
    /// Identifier that is not in scope, with the source location of the use.
    Undefined {
        name: String,
        meta: crate::diag::Meta,
    },
    UnknownFunc(String),
    NotLowerable(&'static str),
}

type LResult<T> = Result<T, LowerError>;

thread_local! {
    static AWAIT_SCOPE_DEPTH: Cell<u32> = Cell::new(0);
}

struct AwaitScopeGuard;

impl AwaitScopeGuard {
    fn enter() -> Self {
        AWAIT_SCOPE_DEPTH.with(|depth| {
            let cur = depth.get();
            depth.set(cur.saturating_add(1));
        });
        AwaitScopeGuard
    }
}

impl Drop for AwaitScopeGuard {
    fn drop(&mut self) {
        AWAIT_SCOPE_DEPTH.with(|depth| {
            let cur = depth.get();
            if cur > 0 {
                depth.set(cur - 1);
            }
        });
    }
}

fn await_allowed() -> bool {
    AWAIT_SCOPE_DEPTH.with(|depth| depth.get() > 0)
}

#[derive(Debug, Clone, Copy)]
pub struct EnumBinding {
    /// Distinguishes a module declaration from a same-named local enum.
    pub declaration: BindingId,
    pub cell: BindingId,
}

#[derive(Debug, Clone, Default)]
pub struct LinkInfo {
    /// Private and exported module variables share live cells across functions.
    pub module_bindings: HashMap<String, (Vec<crate::diag::Span>, BindingId)>,
    /// Module-level enum bindings, including private declarations.
    pub enum_bindings: HashMap<String, EnumBinding>,
    /// import { a as x } from "m"   â†’   "x" -> binding(m,a)
    pub import_bindings: HashMap<String, BindingId>,
    /// import * as ns from "m"      â†’   "ns" -> [ ("a", binding(m,a)), ... ]
    pub namespace_imports: HashMap<String, Vec<(String, BindingId)>>,
    /// export { local as name } / export function f / export const x ...
    /// nombre local en este mÃ³dulo â†’ binding(this,name)
    pub export_bindings: HashMap<String, BindingId>,
    /// celda local (live binding) donde cachearemos el objeto namespace en __modinit__
    /// Si no estÃ¡, caemos al camino â€œMVP por usoâ€ para compat.
    pub namespace_cells: HashMap<String, BindingId>,
    /// nombres locales que corresponden a `export class` del proveedor (para saber que son clase)
    pub imported_class_bindings: HashSet<BindingId>,
}

#[derive(Debug, Clone)]
pub struct LoweringContext {
    pub funcs: HashMap<String, FuncId>,
    pub lam_captures: HashMap<String, Vec<String>>,
    classes: HashMap<String, ClassInfo>,
    pub links: LinkInfo,
}

impl LoweringContext {
    pub fn new() -> Self {
        Self {
            funcs: Default::default(),
            lam_captures: Default::default(),
            classes: Default::default(),
            links: Default::default(),
        }
    }

    fn is_class_ident(&self, name: &str) -> bool {
        // Local classes win
        if self.classes.contains_key(name) {
            return true;
        }
        // Only treat as imported class if we can prove it by BindingId
        if let Some(bid) = self.links.import_bindings.get(name) {
            return self.links.imported_class_bindings.contains(bid);
        }
        false // fall back to generic value lowering
    }
}

#[derive(Debug)]
pub struct Lowerer<'m> {
    module: &'m mut Module,
    lowering_ctx: LoweringContext,
}

impl<'m> Lowerer<'m> {
    pub fn new(module: &'m mut Module) -> Self {
        Self {
            module,
            lowering_ctx: LoweringContext::new(),
        }
    }

    pub fn set_links(&mut self, links: LinkInfo) -> &mut Self {
        self.lowering_ctx.links = links;
        self
    }

    pub fn lower_program(&mut self, prog: &Program) -> LResult<Vec<FuncId>> {
        self.lowering_ctx.links.module_bindings.clear();
        if let Some(toplevel) = prog.functions.iter().find(|f| f.name == "__toplevel__") {
            for statement in &toplevel.body.stmts {
                let names: Vec<&String> = match statement.kind() {
                    StmtKind::Var { name, .. } => vec![name],
                    StmtKind::VarDestruct { pattern, .. } => pattern
                        .fields
                        .iter()
                        .map(|field| &field.binding)
                        .chain(pattern.rest.iter())
                        .collect(),
                    _ => continue,
                };
                for name in names {
                    if let Some((declarations, _)) =
                        self.lowering_ctx.links.module_bindings.get_mut(name)
                    {
                        declarations.push(statement.meta.span.clone());
                        continue;
                    }
                    let cell = self.lowering_ctx.links.export_bindings.get(name)
                        .copied()
                        .unwrap_or_else(|| self.module.fresh_binding());
                    self.lowering_ctx.links.module_bindings.insert(
                        name.clone(),
                        (vec![statement.meta.span.clone()], cell),
                    );
                }
            }
        }
        self.lowering_ctx.links.enum_bindings.clear();
        if let Some(toplevel) = prog.functions.iter().find(|f| f.name == "__toplevel__") {
            for statement in &toplevel.body.stmts {
                if let StmtKind::Enum { name, binding, .. } = statement.kind() {
                    let cell = self
                        .lowering_ctx
                        .links
                        .export_bindings
                        .get(name)
                        .copied()
                        .unwrap_or(*binding);
                    let enum_binding = EnumBinding {
                        declaration: *binding,
                        cell,
                    };
                    if self
                        .lowering_ctx
                        .links
                        .enum_bindings
                        .insert(name.clone(), enum_binding)
                        .is_some()
                    {
                        return Err(LowerError::NotLowerable("duplicate enum declaration"));
                    }
                }
            }
        }

        // -------- Stage 1: collect classes & their metadata --------
        self.lowering_ctx.classes.clear();

        for c in &prog.classes {
            // gather accessors by name so we can form (getter,setter)
            let mut prop_map: HashMap<String, (Option<Block>, Option<(String, Block)>)> =
                HashMap::new();

            let mut ci = ClassInfo {
                name: c.name.clone(),
                base: c.base.clone(),
                has_ctor: false,
                has_dtor: false,
                instance_fields: Vec::new(),
                props: Vec::new(),
                methods: Vec::new(),
                static_vars: Vec::new(),
                static_methods: Vec::new(),
            };

            for m in &c.members {
                match m {
                    ClassMember::Stored {
                        is_static,
                        name,
                        init,
                        ..
                    } => {
                        if *is_static {
                            ci.static_vars.push((name.clone(), init.clone()));
                        } else {
                            ci.instance_fields.push((name.clone(), init.clone()));
                        }
                    }
                    ClassMember::Accessor {
                        is_static,
                        name,
                        getter,
                        setter_param,
                        setter_body,
                        ..
                    } => {
                        if *is_static {
                            continue;
                        }
                        let entry = prop_map.entry(name.clone()).or_insert((None, None));
                        if let Some(gb) = getter.clone() {
                            entry.0 = Some(gb);
                        }
                        if let (Some(p), Some(sb)) = (setter_param.clone(), setter_body.clone()) {
                            entry.1 = Some((p, sb));
                        }
                    }
                    ClassMember::Method {
                        is_static,
                        name,
                        params,
                        body,
                        is_async,
                        ..
                    } => {
                        if *is_static {
                            ci.static_methods.push((
                                name.clone(),
                                params.clone(),
                                body.clone(),
                                *is_async,
                            ));
                        } else {
                            ci.methods.push((
                                name.clone(),
                                params.clone(),
                                body.clone(),
                                *is_async,
                            ));
                        }
                    }
                    ClassMember::Constructor { params, body, .. } => {
                        ci.has_ctor = true;
                        ci.methods.insert(
                            0,
                            (
                                String::from("constructor"),
                                params.clone(),
                                body.clone(),
                                false,
                            ),
                        );
                    }
                    ClassMember::Destructor { body } => {
                        ci.has_dtor = true;
                        ci.methods.push((
                            String::from("destructor"),
                            Vec::new(),
                            body.clone(),
                            false,
                        ));
                    }
                }
            }

            ci.props = prop_map.into_iter().map(|(n, (g, s))| (n, g, s)).collect();
            self.lowering_ctx.classes.insert(c.name.clone(), ci);
        }

        // -------- Stage 2: hoist lambdas (produces __lam_* functions) --------
        let (prog, lam_caps) = hoist_fn_lits_program(prog);
        self.lowering_ctx.lam_captures = lam_caps;

        // -------- Stage 3: RESERVE FuncId for ALL functions post-hoist --------
        self.lowering_ctx.funcs.clear();

        // 3.1 Reserve for free/hoisted functions first (includes __lam_* and __toplevel__)
        for f in &prog.functions {
            let fid = self.module.reserve_func_id();
            #[cfg(debug_assertions)]
            eprintln!("[reserve func] {} -> {:?}", f.name, fid);
            self.lowering_ctx.funcs.insert(f.name.clone(), fid);
        }

        // 3.2 Reserve for class-generated functions in the SAME order lower_one_class emits them
        let mut extra_names: Vec<String> = Vec::new();
        for c in &prog.classes {
            let fid_raw = c.name.clone();
            let ci = self
                .lowering_ctx
                .classes
                .get(&fid_raw)
                .expect("class collected");

            // Accessors
            for (pname, get, set) in &ci.props {
                if get.is_some() {
                    extra_names.push(format!("__get_{}_{}", fid_raw, pname));
                }
                if set.is_some() {
                    extra_names.push(format!("__set_{}_{}", fid_raw, pname));
                }
            }

            // Instance methods (skip ctor/dtor)
            for (mname, _, _, _) in &ci.methods {
                if *mname != "constructor" && *mname != "destructor" {
                    extra_names.push(format!("__method_{}_{}", fid_raw, mname));
                }
            }

            // Statics
            for (mname, _, _, _) in &ci.static_methods {
                extra_names.push(format!("__static_{}_{}", fid_raw, mname));
            }

            // Ctor / Dtor
            if ci.has_ctor {
                extra_names.push(format!("__ctor_{}", fid_raw));
            }
            if ci.has_dtor {
                extra_names.push(format!("__dtor_{}", fid_raw));
            }

            // Allocator
            extra_names.push(format!("__class_new_{}", fid_raw));
        }

        for nm in extra_names {
            let fid = self.module.reserve_func_id();
            self.lowering_ctx.funcs.insert(nm, fid);
        }

        // -------- Stage 4: lower free/hoisted functions --------
        let mut out = Vec::new();
        for f in &prog.functions {
            let id = self.lower_fn(f)?;
            out.push(id);
        }

        // -------- Stage 5: lower ALL CLASSES (emiten en el mismo orden predeclarado) --------
        self.lower_all_classes(&prog)?;

        // -------- Stage 6: ahora SÃ, __modinit__ AL FINAL --------
        let modinit = self.lower_modinit(&prog, &self.lowering_ctx.links.clone())?;
        out.push(modinit);

        Ok(out)
    }

    fn lower_fn(&mut self, fdecl: &FuncDecl) -> LResult<FuncId> {
        use crate::wir::{Inst, Type};

        // Capture list for this (hoisted) function, if any.
        let lam_caps_for_this = self
            .lowering_ctx
            .lam_captures
            .get(&fdecl.name)
            .cloned()
            .unwrap_or_default();

        // Param types: default i32; if the first param is "__env", treat it as an Array (env).
        let mut param_tys: Vec<Type> = fdecl.params.iter().map(|_| Type::Int32).collect();
        if matches!(fdecl.params.first().map(|s| s.as_str()), Some("__env")) {
            param_tys[0] = Type::Array(Box::new(None));
        }

        // We model returns uniformly as a single Int32 slot (your dynamic value).
        let ret_tys = vec![Type::Int32];

        // Snapshot the function table so we can resolve direct calls without borrowing &mut self.
        let funcs_snapshot = self.lowering_ctx.funcs.clone();
        let func_name = fdecl.name.clone();
        let is_async = fdecl.is_async;

        // Build the function body.
        let mut func = {
            let mut b = Builder::new(self.module, &func_name, param_tys, ret_tys);

            // Bind parameters as locals.
            let mut locals: HashMap<String, ValueId> = Default::default();
            for (i, name) in fdecl.params.iter().enumerate() {
                locals.insert(name.clone(), b.param(i));
            }

            // If this is a hoisted lambda, param 0 is "__env" and we must bind each captured name
            // to its corresponding box (array slot) from the env.
            if !lam_caps_for_this.is_empty() {
                let env_arr = *locals
                    .get("__env")
                    .expect("__env param must be present for hoisted lambdas");
                for (i, cap) in lam_caps_for_this.iter().enumerate() {
                    let idx = b.const_i32(i as i32);
                    let (_nid, boxv) = b.push_node(
                        Inst::CallNative {
                            name: "wir_array_get".into(),
                            args: vec![env_arr, idx],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    locals.insert(cap.clone(), boxv[0]);
                    locals.insert(boxed_key(cap), boxv[0]);
                }
            }

            // Per-function table for "fast field" interning.
            let mut fields: HashMap<String, FieldId> = Default::default();
            let mut next_field: u32 = 0;
            let mut active_try: Vec<TryScope> = Vec::new();

            if is_async {
                b.set_async(true);
                // --- Async prologue: d = Deferred()
                let (_nid, d_res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_deferred_new".into(),
                        args: vec![],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                let d = d_res[0];
                locals.insert("__deferred".to_string(), d);

                // Lower body with async-aware lowering.
                lower_block_free_async(
                    &mut b,
                    &mut locals,
                    &mut fields,
                    &mut next_field,
                    &fdecl.body,
                    &self.lowering_ctx,
                    true, // in_async
                    &mut active_try,
                )?;

                // Promise settlement happens after all finalizers in the JIT epilogue.
                if !b.current_block_terminated() {
                    let zero = b.const_i32(0);
                    b.ret(&[zero]);
                }
            } else {
                // --- Sync function: old path
                lower_block_free(
                    &mut b,
                    &mut locals,
                    &mut fields,
                    &mut next_field,
                    &fdecl.body,
                    &self.lowering_ctx,
                    &mut active_try,
                )?;

                // Fallthrough return 0 (matches previous convention).
                if !b.current_block_terminated() {
                    let zero = b.const_i32(0);
                    b.ret(&[zero]);
                }
            }

            b.finish()
        };

        // Set the reserved ID before pushing
        let reserved_fid = *self.lowering_ctx.funcs.get(&fdecl.name).expect("reserved");
        func.id = reserved_fid;

        // Publish into the module preserving the reserved ID
        let fid = self.module.push_function_preserve_id(func);
        assert_eq!(fid, reserved_fid, "push preserved ID");
        Ok(fid)
    }
}

fn lower_block_free<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    blk: &Block,
    lowering_ctx: &LoweringContext,
    active_try: &mut Vec<TryScope>,
) -> LResult<()> {
    lower_cleanup_scope(
        b,
        locals,
        fields,
        next_field,
        blk,
        lowering_ctx,
        active_try,
        &mut lower_stmt_free,
    )
}

fn lower_cleanup_scope<'m, F>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    blk: &Block,
    lowering_ctx: &LoweringContext,
    active_try: &mut Vec<TryScope>,
    lower_stmt: &mut F,
) -> LResult<()>
where
    F: FnMut(
        &mut Builder<'m>,
        &mut HashMap<String, ValueId>,
        &mut HashMap<String, FieldId>,
        &mut u32,
        &Stmt,
        &LoweringContext,
        &mut Vec<TryScope>,
    ) -> LResult<()>,
{
    for (index, s) in blk.stmts.iter().enumerate() {
        if b.current_block_terminated() {
            break;
        }
        if let StmtKind::Defer {
            kind,
            binding,
            body,
        } = s.kind()
        {
            // Only the remaining statements are protected, so an unreached
            // registration never runs. Nesting supplies LIFO cleanup order.
            let remaining = Block {
                stmts: blk.stmts[index + 1..].to_vec(),
            };
            let catch = if *kind == DeferKind::ErrDefer {
                let original = format!("\0errdefer_{}", crate::wir::next_id());
                let error = expr_unknown(ExprKind::Ident(original.clone()));
                let mut stmts = Vec::new();
                if let Some(binding) = binding {
                    stmts.push(stmt_with_meta(
                        s,
                        StmtKind::Var {
                            name: original.clone(),
                            init: Some(expr_unknown(ExprKind::Ident(binding.clone()))),
                            ty: None,
                        },
                    ));
                }
                // The original throw resumes outside the cleanup body's scope;
                // inner errdefers must not mistake it for a cleanup failure.
                stmts.push(stmt_with_meta(
                    s,
                    StmtKind::Try {
                        try_block: body.clone(),
                        catch: None,
                        finally_block: Some(Block { stmts: Vec::new() }),
                    },
                ));
                stmts.push(stmt_with_meta(s, StmtKind::Throw(error)));
                Some(CatchClause {
                    binding: Some(binding.clone().unwrap_or(original)),
                    body: Block { stmts },
                    meta: s.meta.clone(),
                })
            } else {
                None
            };
            lower_try_stmt_generic(
                b,
                locals,
                fields,
                next_field,
                &remaining,
                catch.as_ref(),
                (*kind == DeferKind::Defer).then_some(body),
                lowering_ctx,
                active_try,
                |b, locals, fields, next_field, block, lowering_ctx, active_try| {
                    lower_cleanup_scope(
                        b,
                        locals,
                        fields,
                        next_field,
                        block,
                        lowering_ctx,
                        active_try,
                        lower_stmt,
                    )
                },
            )?;
            return Ok(());
        }
        lower_stmt(b, locals, fields, next_field, s, lowering_ctx, active_try)?;
    }
    Ok(())
}

/// Whether `recv` names a namespace import (`import * as ns`) not shadowed by a local.
fn is_namespace_ident(recv: &Expr, locals: &HashMap<String, ValueId>, ctx: &LoweringContext) -> bool {
    let ExprKind::Ident(ns) = recv.kind() else {
        return false;
    };
    let links = &ctx.links;
    if links.namespace_cells.contains_key(ns) {
        !locals.contains_key(ns)
    } else {
        // Path 7 of identifier lowering memoizes the namespace into `locals`.
        links.namespace_imports.contains_key(ns)
    }
}

/// Whether `recv` is a namespace import that exports `name`.
fn namespace_exports(
    recv: &Expr,
    name: &str,
    locals: &HashMap<String, ValueId>,
    ctx: &LoweringContext,
) -> bool {
    let ExprKind::Ident(ns) = recv.kind() else {
        return false;
    };
    is_namespace_ident(recv, locals, ctx)
        && ctx
            .links
            .namespace_imports
            .get(ns)
            .is_some_and(|members| members.iter().any(|(n, _)| n == name))
}

/// `ns.name(args)` as a plain call; the parser turns calls of builtin collection
/// method names (`add`, `get`, `keys`, ...) into builtin nodes regardless of receiver.
fn namespace_member_call(e: &Expr, recv: &Expr, name: &str, args: Vec<Expr>) -> Expr {
    let callee = expr_with_meta(e, ExprKind::GetProp {
        recv: SmallBox::new(recv.clone()),
        name: name.to_string(),
    });
    expr_with_meta(e, ExprKind::Call { callee: SmallBox::new(callee), args })
}

fn initialize_variable(
    b: &mut Builder<'_>,
    locals: &mut HashMap<String, ValueId>,
    name: &str,
    value: ValueId,
    statement: &Stmt,
    ctx: &LoweringContext,
) {
    if let Some((declarations, cell)) = ctx.links.module_bindings.get(name) {
        if declarations.contains(&statement.meta.span) {
            b.store_binding(*cell, value);
            // A block-scoped local of the same name (e.g. a `for (var i ...)` init)
            // would otherwise keep shadowing the module binding on later reads.
            locals.remove(name);
            locals.remove(&boxed_key(name));
            return;
        }
    }
    locals.insert(name.to_string(), value);
}

fn lower_stmt_free<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    s: &Stmt,
    lowering_ctx: &LoweringContext,
    active_try: &mut Vec<TryScope>,
) -> LResult<()> {
    prebox_captures_for_stmt(b, locals, s, lowering_ctx);
    snapshot_try_locals(b, locals);
    match s.kind() {
        StmtKind::Enum {
            name,
            binding,
            init,
        } => {
            let value = lower_expr_free(b, locals, fields, next_field, init, lowering_ctx)?;
            locals.insert(name.clone(), value);
            if let Some(module_binding) = lowering_ctx.links.enum_bindings.get(name) {
                if module_binding.declaration == *binding {
                    b.store_binding(module_binding.cell, value);
                }
            }
        }
        StmtKind::Var { name, init, .. } => {
            let val = if let Some(e) = init {
                lower_expr_free(b, locals, fields, next_field, e, lowering_ctx)? // <-- pass
            } else {
                b.const_i32(0)
            };
            initialize_variable(b, locals, name, val, s, lowering_ctx);

            #[cfg(debug_assertions)]
            {
                eprintln!("lower_stmt_free() StmtKind::Var {{ {} }}", name);
                eprintln!(
                    "[links] exports        : {:?}",
                    lowering_ctx
                        .links
                        .export_bindings
                        .keys()
                        .collect::<Vec<_>>()
                );
                eprintln!(
                    "[links] imports        : {:?}",
                    lowering_ctx
                        .links
                        .import_bindings
                        .keys()
                        .collect::<Vec<_>>()
                );
                eprintln!(
                    "[links] namespace_imps : {:?}",
                    lowering_ctx
                        .links
                        .namespace_imports
                        .keys()
                        .collect::<Vec<_>>()
                );
                eprintln!(
                    "[links] namespace_cells: {:?}",
                    lowering_ctx.links.namespace_cells
                );
            }
        }
        StmtKind::VarDestruct { pattern, init } => {
            let obj_val = lower_expr_free(b, locals, fields, next_field, init, lowering_ctx)?;

            for field in &pattern.fields {
                let prop_name = match &field.key {
                    PropKey::Ident(name) => name.as_str(),
                    PropKey::Str(name) => name.as_str(),
                };
                let value = lower_general_getprop(b, obj_val, prop_name, fields, next_field);
                initialize_variable(b, locals, &field.binding, value, s, lowering_ctx);
            }

            if let Some(rest_name) = &pattern.rest {
                let (_nid_clone, clone_res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_obj_clone".into(),
                        args: vec![obj_val],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                let rest_obj = clone_res[0];

                for field in &pattern.fields {
                    match &field.key {
                        PropKey::Ident(name) => {
                            let field_id = intern_field_local(fields, next_field, name);
                            let fid_smi = b.const_i32(field_id.0 as i32);
                            let _ = b.push_node(
                                Inst::CallNative {
                                    name: "wir_obj_del_field".into(),
                                    args: vec![rest_obj, fid_smi],
                                    pure: false,
                                    can_throw: false,
                                },
                                Some(Type::Bool),
                                1,
                                true,
                            );

                            let (_nid_sc, ks) = b.push_node(
                                Inst::Const(Constant::Str(name.clone())),
                                Some(Type::Str),
                                1,
                                false,
                            );
                            let _ = b.push_node(
                                Inst::CallNative {
                                    name: "wir_obj_del_str".into(),
                                    args: vec![rest_obj, ks[0]],
                                    pure: false,
                                    can_throw: false,
                                },
                                Some(Type::Bool),
                                1,
                                true,
                            );
                        }
                        PropKey::Str(name) => {
                            let (_nid_sc, ks) = b.push_node(
                                Inst::Const(Constant::Str(name.clone())),
                                Some(Type::Str),
                                1,
                                false,
                            );
                            let _ = b.push_node(
                                Inst::CallNative {
                                    name: "wir_obj_del_str".into(),
                                    args: vec![rest_obj, ks[0]],
                                    pure: false,
                                    can_throw: false,
                                },
                                Some(Type::Bool),
                                1,
                                true,
                            );
                        }
                    }
                }

                initialize_variable(b, locals, rest_name, rest_obj, s, lowering_ctx);
            }
        }
        StmtKind::If {
            cond,
            then_b,
            else_b,
        } => {
            let c = lower_expr_free(b, locals, fields, next_field, cond, lowering_ctx)?; // <-- pass
            let then_id = b.block();
            let else_id = b.block();
            let then_end = b.block();
            let else_end = b.block();
            let cont_id = b.block();

            b.branch(c, then_id, else_id);

            let incoming = locals.clone();

            b.position_at(then_id);
            let mut locals_then = incoming.clone();
            lower_block_free(
                b,
                &mut locals_then,
                fields,
                next_field,
                then_b,
                lowering_ctx,
                active_try,
            )?; // <-- pass
            if !b.current_block_terminated() {
                b.jump(then_end, &[]);
            }
            b.position_at(then_end);

            b.position_at(else_id);
            let mut locals_else = incoming.clone();
            if let Some(eb) = else_b {
                lower_block_free(
                    b,
                    &mut locals_else,
                    fields,
                    next_field,
                    eb,
                    lowering_ctx,
                    active_try,
                )?; // <-- pass
            }
            if !b.current_block_terminated() {
                b.jump(else_end, &[]);
            }
            b.position_at(else_end);

            let mut phi_vars: Vec<String> = Vec::new();
            for (name, &vin) in incoming.iter() {
                let vt = *locals_then.get(name).unwrap_or(&vin);
                let ve = *locals_else.get(name).unwrap_or(&vin);
                if vt != ve {
                    phi_vars.push(name.clone());
                }
            }
            phi_vars.sort();

            let mut phi_params = Vec::with_capacity(phi_vars.len());
            for _ in &phi_vars {
                phi_params.push(b.add_block_param(cont_id, Type::Int32));
            }

            let mut args_then = Vec::with_capacity(phi_vars.len());
            let mut args_else = Vec::with_capacity(phi_vars.len());
            for name in &phi_vars {
                let vin = *incoming.get(name).unwrap();
                args_then.push(*locals_then.get(name).unwrap_or(&vin));
                args_else.push(*locals_else.get(name).unwrap_or(&vin));
            }

            b.position_at(then_end);
            b.jump(cont_id, &args_then);
            b.position_at(else_end);
            b.jump(cont_id, &args_else);

            b.position_at(cont_id);
            for (i, name) in phi_vars.iter().enumerate() {
                locals.insert(name.clone(), phi_params[i]);
            }
        }
        StmtKind::While { cond, body } => {
            let head = b.block();
            let body_b = b.block();
            let exit = b.block();

            let mut_names = collect_mut_locals_in_block(body)
                .into_iter()
                .filter(|n| locals.contains_key(n))
                .collect::<Vec<_>>();

            let init_args: Vec<ValueId> =
                mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
            let phi_vals: Vec<ValueId> = mut_names
                .iter()
                .map(|_| b.add_block_param(head, Type::Int32))
                .collect();

            b.jump(head, &init_args);

            b.position_at(head);
            for (nm, p) in mut_names.iter().zip(phi_vals.iter()) {
                locals.insert(nm.clone(), *p);
            }
            let c = lower_expr_free(b, locals, fields, next_field, cond, lowering_ctx)?; // <-- pass
            b.branch(c, body_b, exit);

            let exit_locals = locals.clone();
            b.position_at(body_b);
            lower_block_free(
                b,
                locals,
                fields,
                next_field,
                body,
                lowering_ctx,
                active_try,
            )?; // <-- pass
            let back_args: Vec<ValueId> =
                mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
            b.jump(head, &back_args);

            b.position_at(exit);
            *locals = exit_locals;
            for (nm, p) in mut_names.into_iter().zip(phi_vals.into_iter()) {
                locals.insert(nm, p);
            }
        }
        StmtKind::For {
            init,
            cond,
            step,
            body,
        } => {
            if let Some(i) = init.as_deref() {
                lower_stmt_free(b, locals, fields, next_field, i, lowering_ctx, active_try)?;
                // The init may have declared a captured loop variable.
                prebox_captures_for_stmt(b, locals, s, lowering_ctx);
            }

            let head = b.block();
            let body_b = b.block();
            let exit = b.block();

            let mut mutated_set: BTreeSet<String> = BTreeSet::new();
            for st in &body.stmts {
                collect_mut_locals_in_stmt(st, &mut mutated_set);
            }
            if let Some(se) = step {
                collect_mut_locals_in_expr(se, &mut mutated_set);
            }
            let mut_names: Vec<String> = mutated_set
                .into_iter()
                .filter(|n| locals.contains_key(n))
                .collect();

            let init_args: Vec<ValueId> =
                mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
            let phi_vals: Vec<ValueId> = mut_names
                .iter()
                .map(|_| b.add_block_param(head, Type::Int32))
                .collect();

            b.jump(head, &init_args);

            b.position_at(head);
            for (nm, p) in mut_names.iter().zip(phi_vals.iter()) {
                locals.insert(nm.clone(), *p);
            }
            let c = if let Some(e) = cond {
                lower_expr_free(b, locals, fields, next_field, e, lowering_ctx)? // <-- pass
            } else {
                let (_nid, res) = b.push_node(
                    Inst::Const(Constant::Bool(true)),
                    Some(Type::Bool),
                    1,
                    false,
                );
                res[0]
            };
            b.branch(c, body_b, exit);

            let exit_locals = locals.clone();
            b.position_at(body_b);
            lower_block_free(
                b,
                locals,
                fields,
                next_field,
                body,
                lowering_ctx,
                active_try,
            )?; // <-- pass
            if let Some(se) = step {
                let _ = lower_expr_free(b, locals, fields, next_field, se, lowering_ctx)?;
            } // <-- pass
            let back_args: Vec<ValueId> =
                mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
            b.jump(head, &back_args);

            b.position_at(exit);
            *locals = exit_locals;
            for (nm, p) in mut_names.into_iter().zip(phi_vals.into_iter()) {
                locals.insert(nm, p);
            }
        }
        StmtKind::Try {
            try_block,
            catch,
            finally_block,
        } => {
            lower_try_stmt_generic(
                b,
                locals,
                fields,
                next_field,
                try_block,
                catch.as_ref(),
                finally_block.as_ref(),
                lowering_ctx,
                active_try,
                |b, locals, fields, next_field, block, lowering_ctx, active_try| {
                    lower_block_free(
                        b,
                        locals,
                        fields,
                        next_field,
                        block,
                        lowering_ctx,
                        active_try,
                    )
                },
            )?;
        }
        StmtKind::Throw(expr) => {
            let val = lower_expr_free(b, locals, fields, next_field, expr, lowering_ctx)?;
            let _ = emit_try_leave_chain(b, active_try, locals, TryExitKind::Exception);
            let _ = b.push_node(Inst::Throw(val), None, 0, true);
        }
        StmtKind::Defer { .. } => {
            return Err(LowerError::NotLowerable(
                "defer declaration must belong to a cleanup scope",
            ));
        }
        StmtKind::Return(e) => {
            if let Some(e) = e {
                let v = lower_expr_free(b, locals, fields, next_field, e, lowering_ctx)?;
                let _ = emit_try_leave_chain(b, active_try, locals, TryExitKind::Normal);
                b.ret(&[v]);
            } else {
                let z = b.const_i32(0);
                let _ = emit_try_leave_chain(b, active_try, locals, TryExitKind::Normal);
                b.ret(&[z]);
            }
        }
        StmtKind::Listen(ld) => {
            // server id = wir_server_create(addr)
            let (_nid_addr, addr_r) = b.push_node(
                Inst::Const(Constant::Str(ld.addr.clone())),
                Some(Type::Str),
                1,
                false,
            );
            let addr_v = addr_r[0];
            let (_nid_sid, sid_r) = b.push_node(
                Inst::CallNative {
                    name: "wir_server_create".into(),
                    args: vec![addr_v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32), // server id
                1,
                true,
            );
            let sid = sid_r[0];

            // add routes
            for rt in &ld.routes {
                let pat_v =
                    lower_expr_free(b, locals, fields, next_field, &rt.pattern, lowering_ctx)?;
                let hnd_v =
                    lower_expr_free(b, locals, fields, next_field, &rt.handler, lowering_ctx)?;
                let (_mid, mr) = b.push_node(
                    Inst::Const(Constant::Str(rt.method.clone())),
                    Some(Type::Str),
                    1,
                    false,
                );
                let m_str = mr[0];

                let _ = b.push_node(
                    Inst::CallNative {
                        name: "wir_server_add_route".into(),
                        args: vec![sid, m_str, pat_v, hnd_v], // <-- pass the string pointer
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
            }

            // listen
            let _ = b.push_node(
                Inst::CallNative {
                    name: "wir_server_listen".into(),
                    args: vec![sid],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );
        }

        StmtKind::Expr(e) => {
            let _ = lower_expr_free(b, locals, fields, next_field, e, lowering_ctx)?;
        } // <-- pass
    }

    Ok(())
}

fn lower_general_getprop<'m>(
    b: &mut Builder<'m>,
    obj: ValueId,
    name: &str,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
) -> ValueId {
    let name_string = name.to_string();

    let (_nid_sc, ks) = b.push_node(
        Inst::Const(Constant::Str(name_string.clone())),
        Some(Type::Str),
        1,
        false,
    );

    let field = intern_field_local(fields, next_field, &name_string);
    let fid_smi = b.const_i32(field.0 as i32);

    let _ = b.push_node(
        Inst::CallNative {
            name: "wir_field_register_name".into(),
            args: vec![fid_smi, ks[0]],
            pure: false,
            can_throw: false,
        },
        Some(Type::Int32),
        1,
        true,
    );

    let (_nid_is_proxy, is_proxy) = b.push_node(
        Inst::CallNative {
            name: "wir_is_proxy".into(),
            args: vec![obj],
            pure: true,
            can_throw: false,
        },
        Some(Type::Bool),
        1,
        false,
    );

    let proxy_block = b.block();
    let normal_block = b.block();
    let cont = b.block();
    let out_val = b.add_block_param(cont, Type::Int32);

    b.branch(is_proxy[0], proxy_block, normal_block);

    b.position_at(proxy_block);
    let (_nid_proxy_get, proxy_res) = b.push_node(
        Inst::CallNative {
            name: "wir_obj_get_str".into(),
            args: vec![obj, ks[0]],
            pure: false,
            can_throw: false,
        },
        None,
        1,
        true,
    );
    b.jump(cont, &[proxy_res[0]]);

    b.position_at(normal_block);
    // Arrays and other non-object values do not have the BoxedObj layout.
    let (_, is_object) = b.push_node(
        Inst::CallNative {
            name: "wir_is_obj".into(),
            args: vec![obj],
            pure: true,
            can_throw: false,
        },
        Some(Type::Bool),
        1,
        false,
    );
    let object_block = b.block();
    let missing_block = b.block();
    b.branch(is_object[0], object_block, missing_block);
    b.position_at(missing_block);
    let missing = b.const_null();
    b.jump(cont, &[missing]);
    b.position_at(object_block);
    let (_nid_hs, has_str) = b.push_node(
        Inst::CallNative {
            name: "wir_obj_has_str".into(),
            args: vec![obj, ks[0]],
            pure: false,
            can_throw: false,
        },
        Some(Type::Bool),
        1,
        true,
    );

    let str_hit = b.block();
    let try_fast = b.block();
    b.branch(has_str[0], str_hit, try_fast);

    b.position_at(str_hit);
    let (_nid_gs, sv) = b.push_node(
        Inst::CallNative {
            name: "wir_obj_get_str".into(),
            args: vec![obj, ks[0]],
            pure: false,
            can_throw: false,
        },
        None,
        1,
        true,
    );
    b.jump(cont, &[sv[0]]);

    b.position_at(try_fast);
    let (_nid_hf, hasf) = b.push_node(
        Inst::CallNative {
            name: "wir_obj_has_field".into(),
            args: vec![obj, fid_smi],
            pure: false,
            can_throw: false,
        },
        Some(Type::Bool),
        1,
        true,
    );

    let fast_b = b.block();
    let try_gettr = b.block();
    b.branch(hasf[0], fast_b, try_gettr);

    b.position_at(fast_b);
    let (_nid_f, fv) = b.push_node(
        Inst::LoadField {
            obj,
            field,
            expected: None,
        },
        None,
        1,
        false,
    );
    b.jump(cont, &[fv[0]]);

    b.position_at(try_gettr);
    let getter_key = format!("__get__{}", name);
    let (_nid_gk, gk) = b.push_node(
        Inst::Const(Constant::Str(getter_key)),
        Some(Type::Str),
        1,
        false,
    );
    let (_nid_hg, has_g) = b.push_node(
        Inst::CallNative {
            name: "wir_obj_has_str".into(),
            args: vec![obj, gk[0]],
            pure: false,
            can_throw: false,
        },
        Some(Type::Bool),
        1,
        true,
    );

    let call_g = b.block();
    let miss = b.block();
    b.branch(has_g[0], call_g, miss);

    b.position_at(call_g);
    let (_nid_gv, gv) = b.push_node(
        Inst::CallNative {
            name: "wir_obj_get_str".into(),
            args: vec![obj, gk[0]],
            pure: false,
            can_throw: false,
        },
        None,
        1,
        true,
    );
    let (_nid_call, gres) = b.push_node(
        Inst::CallClosure {
            conv: crate::wir::CallConv::Fast,
            fun: gv[0],
            args: vec![obj],
        },
        Some(Type::Int32),
        1,
        true,
    );
    b.jump(cont, &[gres[0]]);

    b.position_at(miss);
    let z = b.const_i32(0);
    b.jump(cont, &[z]);

    b.position_at(cont);
    out_val
}

fn collect_mut_locals_in_expr(e: &Expr, out: &mut BTreeSet<String>) {
    match e.kind() {
        ExprKind::Assign(lv, rhs) => {
            if let LValueKind::Ident(name) = lv.kind() {
                out.insert(name.clone());
            }
            collect_mut_locals_in_expr(rhs, out);
        }
        ExprKind::Conditional {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_mut_locals_in_expr(cond, out);
            collect_mut_locals_in_expr(then_branch, out);
            collect_mut_locals_in_expr(else_branch, out);
        }
        ExprKind::Binary { a, b, .. } => {
            collect_mut_locals_in_expr(a, out);
            collect_mut_locals_in_expr(b, out);
        }
        ExprKind::Unary { e: inner, .. } => collect_mut_locals_in_expr(inner, out),
        ExprKind::Call { callee, args } => {
            collect_mut_locals_in_expr(callee, out);
            for a in args {
                collect_mut_locals_in_expr(a, out);
            }
        }
        ExprKind::Typed { args, .. } => {
            for a in args {
                collect_mut_locals_in_expr(a, out);
            }
        }
        ExprKind::GetProp { recv, .. } => collect_mut_locals_in_expr(recv, out),
        ExprKind::Index { recv, index } => {
            collect_mut_locals_in_expr(recv, out);
            collect_mut_locals_in_expr(index, out);
        }
        ExprKind::Group(inner) => collect_mut_locals_in_expr(inner, out),
        ExprKind::ObjLit(items) => {
            for item in items {
                match item {
                    ObjItem::Prop(_, value) => collect_mut_locals_in_expr(value, out),
                    ObjItem::Spread(expr) => collect_mut_locals_in_expr(expr, out),
                }
            }
        }
        ExprKind::OptionalChain { base, access } => {
            collect_mut_locals_in_expr(base, out);
            match access {
                OptionalAccess::Prop(_) => {}
                OptionalAccess::Index(expr) => collect_mut_locals_in_expr(expr, out),
                OptionalAccess::Call(args) => {
                    for a in args {
                        collect_mut_locals_in_expr(a, out);
                    }
                }
            }
        }
        ExprKind::CallBuiltinMapMethod { recv, args, .. } => {
            collect_mut_locals_in_expr(recv, out);
            for a in args {
                collect_mut_locals_in_expr(a, out);
            }
        }
        ExprKind::CallBuiltinSetMethod { recv, args, .. } => {
            collect_mut_locals_in_expr(recv, out);
            for a in args {
                collect_mut_locals_in_expr(a, out);
            }
        }
        ExprKind::CallBuiltinCommonMethod { recv, .. } => {
            collect_mut_locals_in_expr(recv, out);
        }
        ExprKind::GetBuiltinSize(recv) => collect_mut_locals_in_expr(recv, out),
        _ => {}
    }
}

fn collect_mut_locals_in_stmt(s: &Stmt, out: &mut BTreeSet<String>) {
    match s.kind() {
        StmtKind::Expr(e) => collect_mut_locals_in_expr(e, out),
        StmtKind::Enum { .. } => {}
        StmtKind::Var { .. } => {} // vars declared inside the loop are not loop-carried
        StmtKind::VarDestruct { .. } => {}
        StmtKind::If {
            cond,
            then_b,
            else_b,
        } => {
            collect_mut_locals_in_expr(cond, out);
            for st in &then_b.stmts {
                collect_mut_locals_in_stmt(st, out);
            }
            if let Some(eb) = else_b {
                for st in &eb.stmts {
                    collect_mut_locals_in_stmt(st, out);
                }
            }
        }
        StmtKind::While { cond, body } => {
            collect_mut_locals_in_expr(cond, out);
            for st in &body.stmts {
                collect_mut_locals_in_stmt(st, out);
            }
        }
        StmtKind::For {
            init,
            cond,
            step,
            body,
        } => {
            if let Some(i) = init.as_deref() {
                collect_mut_locals_in_stmt(i, out);
            }
            if let Some(c) = cond {
                collect_mut_locals_in_expr(c, out);
            }
            if let Some(s) = step {
                collect_mut_locals_in_expr(s, out);
            }
            for st in &body.stmts {
                collect_mut_locals_in_stmt(st, out);
            }
        }
        StmtKind::Return(e) => {
            if let Some(e) = e {
                collect_mut_locals_in_expr(e, out);
            }
        }
        StmtKind::Try {
            try_block,
            catch,
            finally_block,
        } => {
            for st in &try_block.stmts {
                collect_mut_locals_in_stmt(st, out);
            }
            if let Some(c) = catch {
                for st in &c.body.stmts {
                    collect_mut_locals_in_stmt(st, out);
                }
            }
            if let Some(fin) = finally_block {
                for st in &fin.stmts {
                    collect_mut_locals_in_stmt(st, out);
                }
            }
        }
        StmtKind::Throw(expr) => collect_mut_locals_in_expr(expr, out),
        StmtKind::Defer { body, .. } => {
            out.extend(collect_mut_locals_in_block(body));
        }
        StmtKind::Listen(ld) => {
            for r in &ld.routes {
                collect_mut_locals_in_expr(&r.pattern, out);
                collect_mut_locals_in_expr(&r.handler, out);
            }
        }
    }
}

/// Box a local into a one-element array so closures can share and mutate it.
fn box_local(b: &mut Builder<'_>, locals: &mut HashMap<String, ValueId>, name: &str) -> bool {
    if locals.contains_key(&boxed_key(name)) {
        return true;
    }
    let Some(&cur) = locals.get(name) else {
        return false;
    };
    let one = b.const_i32(1);
    let (_nid, box_res) = b.push_node(
        Inst::CallNative {
            name: "wir_array_new".into(),
            args: vec![one],
            pure: false,
            can_throw: false,
        },
        Some(Type::Array(Box::new(None))),
        1,
        true,
    );
    let box_arr = box_res[0];
    let zero = b.const_i32(0);
    let _ = b.push_node(
        Inst::CallNative {
            name: "wir_array_set".into(),
            args: vec![box_arr, zero, cur],
            pure: false,
            can_throw: false,
        },
        Some(Type::Int32),
        1,
        true,
    );
    locals.insert(name.to_string(), box_arr);
    locals.insert(boxed_key(name), box_arr);
    true
}

/// Box every in-scope local that a closure created inside `s` captures *before*
/// lowering `s`. Boxing lazily at the closure site would rebind the local only
/// on that control-flow path, so loop back-edges and branch merges would mix
/// the box with the raw value.
fn prebox_captures_for_stmt(
    b: &mut Builder<'_>,
    locals: &mut HashMap<String, ValueId>,
    s: &Stmt,
    ctx: &LoweringContext,
) {
    if ctx.lam_captures.is_empty() {
        return;
    }
    let mut caps = BTreeSet::new();
    collect_captures_in_stmt(s, ctx, &mut caps);
    for cap in caps {
        box_local(b, locals, &cap);
    }
}

fn collect_captures_in_block(blk: &Block, ctx: &LoweringContext, out: &mut BTreeSet<String>) {
    for s in &blk.stmts {
        collect_captures_in_stmt(s, ctx, out);
    }
}

fn collect_captures_in_stmt(s: &Stmt, ctx: &LoweringContext, out: &mut BTreeSet<String>) {
    match s.kind() {
        StmtKind::Enum { init, .. } => collect_captures_in_expr(init, ctx, out),
        StmtKind::Var { init, .. } => {
            if let Some(e) = init {
                collect_captures_in_expr(e, ctx, out);
            }
        }
        StmtKind::VarDestruct { init, .. } => collect_captures_in_expr(init, ctx, out),
        StmtKind::If {
            cond,
            then_b,
            else_b,
        } => {
            collect_captures_in_expr(cond, ctx, out);
            collect_captures_in_block(then_b, ctx, out);
            if let Some(eb) = else_b {
                collect_captures_in_block(eb, ctx, out);
            }
        }
        StmtKind::While { cond, body } => {
            collect_captures_in_expr(cond, ctx, out);
            collect_captures_in_block(body, ctx, out);
        }
        StmtKind::For {
            init,
            cond,
            step,
            body,
        } => {
            if let Some(i) = init.as_deref() {
                collect_captures_in_stmt(i, ctx, out);
            }
            if let Some(c) = cond {
                collect_captures_in_expr(c, ctx, out);
            }
            if let Some(st) = step {
                collect_captures_in_expr(st, ctx, out);
            }
            collect_captures_in_block(body, ctx, out);
        }
        StmtKind::Try {
            try_block,
            catch,
            finally_block,
        } => {
            collect_captures_in_block(try_block, ctx, out);
            if let Some(c) = catch {
                collect_captures_in_block(&c.body, ctx, out);
            }
            if let Some(fin) = finally_block {
                collect_captures_in_block(fin, ctx, out);
            }
        }
        StmtKind::Throw(e) | StmtKind::Expr(e) => collect_captures_in_expr(e, ctx, out),
        StmtKind::Return(e) => {
            if let Some(e) = e {
                collect_captures_in_expr(e, ctx, out);
            }
        }
        StmtKind::Defer { body, .. } => collect_captures_in_block(body, ctx, out),
        StmtKind::Listen(ld) => {
            for r in &ld.routes {
                collect_captures_in_expr(&r.pattern, ctx, out);
                collect_captures_in_expr(&r.handler, ctx, out);
            }
        }
    }
}

fn collect_captures_in_exprs(es: &[Expr], ctx: &LoweringContext, out: &mut BTreeSet<String>) {
    for e in es {
        collect_captures_in_expr(e, ctx, out);
    }
}

fn collect_captures_in_expr(e: &Expr, ctx: &LoweringContext, out: &mut BTreeSet<String>) {
    match e.kind() {
        ExprKind::FnRef { name } => {
            if let Some(caps) = ctx.lam_captures.get(name) {
                out.extend(caps.iter().cloned());
            }
        }
        ExprKind::FnLit { body, .. } => collect_captures_in_block(body, ctx, out),
        ExprKind::LitInt(_)
        | ExprKind::LitF64(_)
        | ExprKind::LitBool(_)
        | ExprKind::LitNull
        | ExprKind::Str(_)
        | ExprKind::Ident(_)
        | ExprKind::This
        | ExprKind::SuperProp(_) => {}
        ExprKind::Assign(lv, rhs) => {
            match lv.kind() {
                LValueKind::Ident(_) => {}
                LValueKind::GetProp { recv, .. } => collect_captures_in_expr(recv, ctx, out),
                LValueKind::Index { recv, index } => {
                    collect_captures_in_expr(recv, ctx, out);
                    collect_captures_in_expr(index, ctx, out);
                }
            }
            collect_captures_in_expr(rhs, ctx, out);
        }
        ExprKind::Conditional {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_captures_in_expr(cond, ctx, out);
            collect_captures_in_expr(then_branch, ctx, out);
            collect_captures_in_expr(else_branch, ctx, out);
        }
        ExprKind::Binary { a, b, .. } => {
            collect_captures_in_expr(a, ctx, out);
            collect_captures_in_expr(b, ctx, out);
        }
        ExprKind::Unary { e: inner, .. }
        | ExprKind::Group(inner)
        | ExprKind::Await(inner)
        | ExprKind::GetProp { recv: inner, .. }
        | ExprKind::GetPropObj { obj: inner, .. }
        | ExprKind::DeleteProp { obj: inner, .. }
        | ExprKind::CallBuiltinCommonMethod { recv: inner, .. }
        | ExprKind::GetBuiltinSize(inner) => collect_captures_in_expr(inner, ctx, out),
        ExprKind::Call { callee, args } => {
            collect_captures_in_expr(callee, ctx, out);
            collect_captures_in_exprs(args, ctx, out);
        }
        ExprKind::Index { recv: x, index: y }
        | ExprKind::In { key: x, obj: y }
        | ExprKind::DeleteIndex { obj: x, index: y }
        | ExprKind::SetPropObj { obj: x, value: y, .. } => {
            collect_captures_in_expr(x, ctx, out);
            collect_captures_in_expr(y, ctx, out);
        }
        ExprKind::ArrayLit(args)
        | ExprKind::SuperCall(args)
        | ExprKind::New { args, .. }
        | ExprKind::CreateBuiltin { args, .. }
        | ExprKind::Typed { args, .. } => collect_captures_in_exprs(args, ctx, out),
        ExprKind::ObjLit(items) => {
            for item in items {
                match item {
                    ObjItem::Prop(_, v) | ObjItem::Spread(v) => collect_captures_in_expr(v, ctx, out),
                }
            }
        }
        ExprKind::OptionalChain { base, access } => {
            collect_captures_in_expr(base, ctx, out);
            match access {
                OptionalAccess::Prop(_) => {}
                OptionalAccess::Index(i) => collect_captures_in_expr(i, ctx, out),
                OptionalAccess::Call(args) => collect_captures_in_exprs(args, ctx, out),
            }
        }
        ExprKind::CallBuiltinMapMethod { recv, args, .. }
        | ExprKind::CallBuiltinSetMethod { recv, args, .. } => {
            collect_captures_in_expr(recv, ctx, out);
            collect_captures_in_exprs(args, ctx, out);
        }
    }
}

fn collect_mut_locals_in_block(b: &Block) -> Vec<String> {
    let mut set = BTreeSet::new();
    for s in &b.stmts {
        collect_mut_locals_in_stmt(s, &mut set);
    }
    set.into_iter().collect() // stable order
}

fn lower_block_free_async<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    blk: &Block,
    lowering_ctx: &LoweringContext,
    in_async: bool,
    active_try: &mut Vec<TryScope>,
) -> LResult<()> {
    lower_cleanup_scope(
        b,
        locals,
        fields,
        next_field,
        blk,
        lowering_ctx,
        active_try,
        &mut |b, locals, fields, next_field, s, lowering_ctx, active_try| {
            lower_stmt_free_async(
                b, locals, fields, next_field, s, lowering_ctx, in_async, active_try,
            )
        },
    )
}

fn lower_stmt_free_async<'m>(
    mut b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    s: &Stmt,
    lowering_ctx: &LoweringContext,
    in_async: bool,
    active_try: &mut Vec<TryScope>,
) -> LResult<()> {
    prebox_captures_for_stmt(b, locals, s, lowering_ctx);
    match s.kind() {
        StmtKind::Return(eopt) if in_async => {
            let ret_val = if let Some(e) = eopt {
                lower_expr_free_async(b, locals, fields, next_field, e, lowering_ctx, in_async)?
            } else {
                b.const_i32(0)
            };
            let _ = emit_try_leave_chain(b, active_try, locals, TryExitKind::Normal);
            b.ret(&[ret_val]);
            Ok(())
        }
        StmtKind::Listen(ld) => {
            // server id = wir_server_create(addr)
            let (_nid_addr, addr_r) = b.push_node(
                Inst::Const(Constant::Str(ld.addr.clone())),
                Some(Type::Str),
                1,
                false,
            );
            let addr_v = addr_r[0];
            let (_nid_sid, sid_r) = b.push_node(
                Inst::CallNative {
                    name: "wir_server_create".into(),
                    args: vec![addr_v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32), // server id
                1,
                true,
            );
            let sid = sid_r[0];

            // add routes
            for rt in &ld.routes {
                let pat_v = lower_expr_free_async(
                    b,
                    locals,
                    fields,
                    next_field,
                    &rt.pattern,
                    lowering_ctx,
                    in_async,
                )?;
                let hnd_v = lower_expr_free_async(
                    b,
                    locals,
                    fields,
                    next_field,
                    &rt.handler,
                    lowering_ctx,
                    in_async,
                )?;
                let (_mid, mr) = b.push_node(
                    Inst::Const(Constant::Str(rt.method.clone())),
                    Some(Type::Str),
                    1,
                    false,
                );
                let m_str = mr[0];

                let _ = b.push_node(
                    Inst::CallNative {
                        name: "wir_server_add_route".into(),
                        args: vec![sid, m_str, pat_v, hnd_v], // <-- pass the string pointer
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
            }

            // listen
            let _ = b.push_node(
                Inst::CallNative {
                    name: "wir_server_listen".into(),
                    args: vec![sid],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );

            Ok(())
        }
        _ => {
            // Forward to the old lowering, but via the *_async versions
            match s.kind() {
                StmtKind::Try {
                    try_block,
                    catch,
                    finally_block,
                } => lower_try_stmt_generic(
                    b,
                    locals,
                    fields,
                    next_field,
                    try_block,
                    catch.as_ref(),
                    finally_block.as_ref(),
                    lowering_ctx,
                    active_try,
                    |b, locals, fields, next_field, block, lowering_ctx, active_try| {
                        lower_block_free_async(
                            b,
                            locals,
                            fields,
                            next_field,
                            block,
                            lowering_ctx,
                            in_async,
                            active_try,
                        )
                    },
                ),
                StmtKind::Throw(expr) => {
                    let val = lower_expr_free_async(
                        b,
                        locals,
                        fields,
                        next_field,
                        expr,
                        lowering_ctx,
                        in_async,
                    )?;
                    let _ = emit_try_leave_chain(b, active_try, locals, TryExitKind::Exception);
                    let _ = b.push_node(Inst::Throw(val), None, 0, true);
                    Ok(())
                }
                StmtKind::Defer { .. } => Err(LowerError::NotLowerable(
                    "defer declaration must belong to a cleanup scope",
                )),
                StmtKind::Enum { .. } => {
                    lower_stmt_free(b, locals, fields, next_field, s, lowering_ctx, active_try)
                }
                StmtKind::Var { name, init, .. } => {
                    let val = if let Some(e) = init {
                        lower_expr_free_async(
                            b,
                            locals,
                            fields,
                            next_field,
                            e,
                            lowering_ctx,
                            in_async,
                        )?
                    } else {
                        b.const_i32(0)
                    };
                    initialize_variable(b, locals, name, val, s, lowering_ctx);
                    Ok(())
                }
                StmtKind::VarDestruct { pattern, init } => {
                    let obj_val = lower_expr_free_async(
                        b,
                        locals,
                        fields,
                        next_field,
                        init,
                        lowering_ctx,
                        in_async,
                    )?;

                    for field in &pattern.fields {
                        let prop_name = match &field.key {
                            PropKey::Ident(name) => name.as_str(),
                            PropKey::Str(name) => name.as_str(),
                        };
                        let value =
                            lower_general_getprop(b, obj_val, prop_name, fields, next_field);
                        initialize_variable(b, locals, &field.binding, value, s, lowering_ctx);
                    }

                    if let Some(rest_name) = &pattern.rest {
                        let (_nid_clone, clone_res) = b.push_node(
                            Inst::CallNative {
                                name: "wir_obj_clone".into(),
                                args: vec![obj_val],
                                pure: false,
                                can_throw: false,
                            },
                            None,
                            1,
                            true,
                        );
                        let rest_obj = clone_res[0];

                        for field in &pattern.fields {
                            match &field.key {
                                PropKey::Ident(name) => {
                                    let field_id = intern_field_local(fields, next_field, name);
                                    let fid_smi = b.const_i32(field_id.0 as i32);
                                    let _ = b.push_node(
                                        Inst::CallNative {
                                            name: "wir_obj_del_field".into(),
                                            args: vec![rest_obj, fid_smi],
                                            pure: false,
                                            can_throw: false,
                                        },
                                        Some(Type::Bool),
                                        1,
                                        true,
                                    );

                                    let (_nid_sc, ks) = b.push_node(
                                        Inst::Const(Constant::Str(name.clone())),
                                        Some(Type::Str),
                                        1,
                                        false,
                                    );
                                    let _ = b.push_node(
                                        Inst::CallNative {
                                            name: "wir_obj_del_str".into(),
                                            args: vec![rest_obj, ks[0]],
                                            pure: false,
                                            can_throw: false,
                                        },
                                        Some(Type::Bool),
                                        1,
                                        true,
                                    );
                                }
                                PropKey::Str(name) => {
                                    let (_nid_sc, ks) = b.push_node(
                                        Inst::Const(Constant::Str(name.clone())),
                                        Some(Type::Str),
                                        1,
                                        false,
                                    );
                                    let _ = b.push_node(
                                        Inst::CallNative {
                                            name: "wir_obj_del_str".into(),
                                            args: vec![rest_obj, ks[0]],
                                            pure: false,
                                            can_throw: false,
                                        },
                                        Some(Type::Bool),
                                        1,
                                        true,
                                    );
                                }
                            }
                        }

                        initialize_variable(b, locals, rest_name, rest_obj, s, lowering_ctx);
                    }
                    Ok(())
                }
                StmtKind::If {
                    cond,
                    then_b,
                    else_b,
                } => {
                    let c = lower_expr_free_async(
                        b,
                        locals,
                        fields,
                        next_field,
                        cond,
                        lowering_ctx,
                        in_async,
                    )?;
                    // (rest identical to your If lowering, but using lower_block_free_async)
                    // ...
                    // Keep your existing structure, just swap the called helpers:
                    let then_id = b.block();
                    let else_id = b.block();
                    let then_end = b.block();
                    let else_end = b.block();
                    let cont_id = b.block();

                    b.branch(c, then_id, else_id);

                    let incoming = locals.clone();

                    b.position_at(then_id);
                    let mut locals_then = incoming.clone();
                    lower_block_free_async(
                        &mut b,
                        &mut locals_then,
                        fields,
                        next_field,
                        then_b,
                        lowering_ctx,
                        in_async,
                        active_try,
                    )?;
                    if !b.current_block_terminated() {
                        b.jump(then_end, &[]);
                    }
                    b.position_at(then_end);

                    b.position_at(else_id);
                    let mut locals_else = incoming.clone();
                    if let Some(eb) = else_b {
                        lower_block_free_async(
                            &mut b,
                            &mut locals_else,
                            fields,
                            next_field,
                            eb,
                            lowering_ctx,
                            in_async,
                            active_try,
                        )?;
                    }
                    if !b.current_block_terminated() {
                        b.jump(else_end, &[]);
                    }
                    b.position_at(else_end);

                    let mut phi_vars: Vec<String> = Vec::new();
                    for (name, &vin) in incoming.iter() {
                        let vt = *locals_then.get(name).unwrap_or(&vin);
                        let ve = *locals_else.get(name).unwrap_or(&vin);
                        if vt != ve {
                            phi_vars.push(name.clone());
                        }
                    }
                    phi_vars.sort();

                    let mut phi_params = Vec::with_capacity(phi_vars.len());
                    for _ in &phi_vars {
                        phi_params.push(b.add_block_param(cont_id, Type::Int32));
                    }

                    let mut args_then = Vec::with_capacity(phi_vars.len());
                    let mut args_else = Vec::with_capacity(phi_vars.len());
                    for name in &phi_vars {
                        let vin = *incoming.get(name).unwrap();
                        args_then.push(*locals_then.get(name).unwrap_or(&vin));
                        args_else.push(*locals_else.get(name).unwrap_or(&vin));
                    }

                    b.position_at(then_end);
                    b.jump(cont_id, &args_then);
                    b.position_at(else_end);
                    b.jump(cont_id, &args_else);

                    b.position_at(cont_id);
                    for (i, name) in phi_vars.iter().enumerate() {
                        locals.insert(name.clone(), phi_params[i]);
                    }

                    Ok(())
                }
                // While / For / Expr â€¦ call lower_*_async respectively
                StmtKind::While { cond, body } => {
                    // same as your While, but using lower_expr_free_async / lower_block_free_async
                    let head = b.block();
                    let body_b = b.block();
                    let exit = b.block();

                    let mut_names = collect_mut_locals_in_block(body)
                        .into_iter()
                        .filter(|n| locals.contains_key(n))
                        .collect::<Vec<_>>();

                    let init_args: Vec<ValueId> =
                        mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
                    let phi_vals: Vec<ValueId> = mut_names
                        .iter()
                        .map(|_| b.add_block_param(head, Type::Int32))
                        .collect();

                    b.jump(head, &init_args);

                    b.position_at(head);
                    for (nm, p) in mut_names.iter().zip(phi_vals.iter()) {
                        locals.insert(nm.clone(), *p);
                    }
                    let c = lower_expr_free_async(
                        b,
                        locals,
                        fields,
                        next_field,
                        cond,
                        lowering_ctx,
                        in_async,
                    )?;
                    b.branch(c, body_b, exit);

                    let exit_locals = locals.clone();
                    b.position_at(body_b);
                    lower_block_free_async(
                        b,
                        locals,
                        fields,
                        next_field,
                        body,
                        lowering_ctx,
                        in_async,
                        active_try,
                    )?;
                    let back_args: Vec<ValueId> =
                        mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
                    b.jump(head, &back_args);

                    b.position_at(exit);
                    *locals = exit_locals;
                    for (nm, p) in mut_names.into_iter().zip(phi_vals.into_iter()) {
                        locals.insert(nm, p);
                    }
                    Ok(())
                }
                StmtKind::For {
                    init,
                    cond,
                    step,
                    body,
                } => {
                    if let Some(i) = init {
                        lower_stmt_free_async(
                            b,
                            locals,
                            fields,
                            next_field,
                            i,
                            lowering_ctx,
                            in_async,
                            active_try,
                        )?;
                        // The init may have declared a captured loop variable.
                        prebox_captures_for_stmt(b, locals, s, lowering_ctx);
                    }

                    let head = b.block();
                    let body_b = b.block();
                    let exit = b.block();

                    let mut mutated_set: BTreeSet<String> = BTreeSet::new();
                    for st in &body.stmts {
                        collect_mut_locals_in_stmt(st, &mut mutated_set);
                    }
                    if let Some(se) = step {
                        collect_mut_locals_in_expr(se, &mut mutated_set);
                    }
                    let mut_names: Vec<String> = mutated_set
                        .into_iter()
                        .filter(|n| locals.contains_key(n))
                        .collect();

                    let init_args: Vec<ValueId> =
                        mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
                    let phi_vals: Vec<ValueId> = mut_names
                        .iter()
                        .map(|_| b.add_block_param(head, Type::Int32))
                        .collect();

                    b.jump(head, &init_args);

                    b.position_at(head);
                    for (nm, p) in mut_names.iter().zip(phi_vals.iter()) {
                        locals.insert(nm.clone(), *p);
                    }
                    let c = if let Some(e) = cond {
                        lower_expr_free_async(
                            b,
                            locals,
                            fields,
                            next_field,
                            e,
                            lowering_ctx,
                            in_async,
                        )?
                    } else {
                        let (_nid, res) = b.push_node(
                            Inst::Const(Constant::Bool(true)),
                            Some(Type::Bool),
                            1,
                            false,
                        );
                        res[0]
                    };
                    b.branch(c, body_b, exit);

                    let exit_locals = locals.clone();
                    b.position_at(body_b);
                    lower_block_free_async(
                        b,
                        locals,
                        fields,
                        next_field,
                        body,
                        lowering_ctx,
                        in_async,
                        active_try,
                    )?;
                    if let Some(se) = step {
                        let _ = lower_expr_free_async(
                            b,
                            locals,
                            fields,
                            next_field,
                            se,
                            lowering_ctx,
                            in_async,
                        )?;
                    }
                    let back_args: Vec<ValueId> =
                        mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
                    b.jump(head, &back_args);

                    b.position_at(exit);
                    *locals = exit_locals;
                    for (nm, p) in mut_names.into_iter().zip(phi_vals.into_iter()) {
                        locals.insert(nm, p);
                    }
                    Ok(())
                }
                StmtKind::Expr(e) => {
                    let _ = lower_expr_free_async(
                        b,
                        locals,
                        fields,
                        next_field,
                        e,
                        lowering_ctx,
                        in_async,
                    )?;
                    Ok(())
                }

                StmtKind::Listen(_) => unreachable!(), // handled in the outer match arm
                StmtKind::Return(_) => unreachable!(), // handled above when in_async
            }
        }
    }
}

fn lower_expr_free_async<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    e: &Expr,
    lowering_ctx: &LoweringContext,
    in_async: bool,
) -> LResult<ValueId> {
    if in_async {
        let _guard = AwaitScopeGuard::enter();
        lower_expr_free(b, locals, fields, next_field, e, lowering_ctx)
    } else {
        lower_expr_free(b, locals, fields, next_field, e, lowering_ctx)
    }
}

/// Whether `name(args...)` with `argc` arguments matches a builtin string or
/// array method lowered by `lower_string_method_call` / `lower_array_method_call`.
fn builtin_method_arity_ok(name: &str, argc: usize) -> bool {
    match name {
        "length" | "pop" | "shift" | "toUpperCase" | "toLowerCase" | "trim" | "trimEnd"
        | "trimStart" => argc == 0,
        "setLength" | "push" | "unshift" | "fill" | "map" | "filter" | "forEach" | "find"
        | "findIndex" | "concat" | "repeat" | "endsWith" => argc == 1,
        "reduce" | "indexOf" | "includes" | "lastIndexOf" | "padEnd" | "padStart" | "startsWith" => {
            argc == 1 || argc == 2
        }
        "replace" | "replaceAll" => argc == 2,
        "split" | "slice" | "substring" => argc <= 2,
        _ => false,
    }
}

fn require_callable(b: &mut Builder<'_>, fun_v: ValueId, message: &str) {
    let (_, callable) = b.push_node(
        Inst::CallNative {
            name: "wir_is_closure".into(),
            args: vec![fun_v],
            pure: true,
            can_throw: false,
        },
        Some(Type::Bool),
        1,
        false,
    );
    let call = b.block();
    let invalid = b.block();
    b.branch(callable[0], call, invalid);
    b.position_at(invalid);
    let error = b.const_str(message);
    b.push_node(Inst::Throw(error), None, 0, true);
    b.position_at(call);
}

/// `recv.name(args...)` through a property lookup, passing `recv` as `this`.
fn lower_dynamic_method_call<'m>(
    b: &mut Builder<'m>,
    recv_v: ValueId,
    name: &str,
    args: Vec<ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
) -> ValueId {
    let fun_v = lower_general_getprop(b, recv_v, name, fields, next_field);
    require_callable(
        b, fun_v, &format!("TypeError: method '{name}' is not callable"),
    );
    let mut argv = Vec::with_capacity(args.len() + 1);
    argv.push(recv_v);
    argv.extend(args);
    let (_nid, res) = b.push_node(
        Inst::CallClosure {
            conv: crate::wir::CallConv::Fast,
            fun: fun_v,
            args: argv,
        },
        Some(Type::Int32),
        1,
        true,
    );
    res[0]
}

/// Map/Set builtin call (`m.get(k)`, `s.add(v)`, ...). Objects and proxies may
/// define methods with these names, so they are dispatched dynamically instead.
fn lower_collection_method_call<'m>(
    b: &mut Builder<'m>,
    recv_v: ValueId,
    method_name: &str,
    native_name: &str,
    is_chainable: bool,
    args: Vec<ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
) -> ValueId {
    use crate::wir::{Inst, Type};
    let (join, out) = begin_builtin_method_dispatch(b, recv_v, method_name, &args, fields, next_field);
    let mut call_args = Vec::with_capacity(args.len() + 1);
    call_args.push(recv_v);
    call_args.extend(args.iter().copied());
    let (_nid, res) = b.push_node(
        Inst::CallNative {
            name: native_name.into(),
            args: call_args,
            pure: false,
            can_throw: false,
        },
        None,
        1,
        true,
    );
    // Chainable builtins (`map.set`, `set.add`) evaluate to the collection itself.
    let builtin = if is_chainable { recv_v } else { res[0] };
    b.jump(join, &[builtin]);
    b.position_at(join);
    out
}

/// Starts a `recv.name(args)` call whose name matches a builtin method. Objects and
/// proxies that actually have a `name` property call it (with `this`); everything
/// else (strings, arrays, maps, objects without such a property, ...) falls through
/// to the builtin. Leaves the builder positioned in the builtin block: the caller
/// emits the builtin, jumps to the returned join block with its result and then
/// positions at the join, whose parameter is the returned value.
fn begin_builtin_method_dispatch<'m>(
    b: &mut Builder<'m>,
    recv_v: ValueId,
    name: &str,
    args: &[ValueId],
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
) -> (crate::wir::BlockId, ValueId) {
    use crate::wir::{Inst, Type};
    let native_bool = |b: &mut Builder<'m>, native: &str, v: ValueId| {
        let (_n, r) = b.push_node(
            Inst::CallNative {
                name: native.into(),
                args: vec![v],
                pure: true,
                can_throw: false,
            },
            Some(Type::Bool),
            1,
            false,
        );
        r[0]
    };
    let is_obj = native_bool(b, "wir_is_obj", recv_v);
    let lookup_blk = b.block();
    let check_proxy_blk = b.block();
    let call_blk = b.block();
    let builtin_blk = b.block();
    let join = b.block();
    let out = b.add_block_param(join, Type::Int32);
    b.branch(is_obj, lookup_blk, check_proxy_blk);

    b.position_at(check_proxy_blk);
    let is_proxy = native_bool(b, "wir_is_proxy", recv_v);
    b.branch(is_proxy, lookup_blk, builtin_blk);

    b.position_at(lookup_blk);
    let fun_v = lower_general_getprop(b, recv_v, name, fields, next_field);
    // Missing properties read as SMI 0, so test for an actual closure.
    let callable = native_bool(b, "wir_is_closure", fun_v);
    b.branch(callable, call_blk, builtin_blk);

    b.position_at(call_blk);
    let mut argv = Vec::with_capacity(args.len() + 1);
    argv.push(recv_v);
    argv.extend_from_slice(args);
    let (_nid, res) = b.push_node(
        Inst::CallClosure {
            conv: crate::wir::CallConv::Fast,
            fun: fun_v,
            args: argv,
        },
        Some(Type::Int32),
        1,
        true,
    );
    b.jump(join, &[res[0]]);

    b.position_at(builtin_blk);
    (join, out)
}

fn lower_array_method_call<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    _fields: &mut HashMap<String, FieldId>,
    _next_field: &mut u32,
    recv_v: ValueId,
    name: &str,
    args: &[ValueId],
    lowering_ctx: &LoweringContext,
) -> LResult<Option<ValueId>> {
    use crate::wir::{Inst, Type};

    let arr = recv_v;

    // Small helper to call a simple native
    macro_rules! cn {
        ($fname:expr, [$($argv:expr),*], $ty:expr) => {{
            let (_nid, res) = b.push_node(
                Inst::CallNative {
                    name: $fname.into(),
                    args: vec![$($argv),*],
                    pure: false,
                    can_throw: false,
                },
                $ty,
                1,
                true,
            );
            Ok(Some(res[0]))
        }};
    }

    match name {
        // ---- property-like method kept for back-compat
        "length" => {
            if !args.is_empty() {
                return Err(LowerError::NotLowerable("length() expects 0 args"));
            }
            return cn!("wir_array_len", [arr], Some(Type::Int32));
        }

        // ---- basic mutators that already worked via natives
        "setLength" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("setLength expects 1 arg"));
            }
            let n = args[0];
            return cn!("wir_array_set_len", [arr, n], Some(Type::Int32));
        }
        "push" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("push expects 1 arg"));
            }
            let v = args[0];
            return cn!("wir_array_push", [arr, v], Some(Type::Int32));
        }
        "pop" => {
            if !args.is_empty() {
                return Err(LowerError::NotLowerable("pop expects 0 args"));
            }
            return cn!("wir_array_pop", [arr], Some(Type::Int32));
        }
        "shift" => {
            if !args.is_empty() {
                return Err(LowerError::NotLowerable("shift expects 0 args"));
            }
            return cn!("wir_array_shift", [arr], Some(Type::Int32));
        }
        "unshift" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("unshift expects 1 arg"));
            }
            let v = args[0];
            return cn!("wir_array_unshift", [arr, v], Some(Type::Int32));
        }
        "fill" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("fill expects 1 arg"));
            }
            let v = args[0];
            return cn!("wir_array_fill", [arr, v], None);
        }

        // ---- map: build loop in WIR, call the closure for each element
        "map" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("map expects 1 arg"));
            }
            let fun = args[0];

            // len
            let (_nid, len_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_len".into(),
                    args: vec![arr],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );
            let len = len_res[0];

            // out = new array len
            let (_nid, out_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_new".into(),
                    args: vec![len],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Array(Box::new(None))),
                1,
                true,
            );
            let out = out_res[0];

            let zero = b.const_i32(0);
            let one = b.const_i32(1);

            let head = b.block();
            let body = b.block();
            let exit = b.block();

            let i_phi = b.add_block_param(head, Type::Int32);

            b.jump(head, &[zero]);
            b.position_at(head);

            let (_nid, cnd) = b.push_node(
                Inst::CmpInt {
                    kind: crate::wir::CmpKind::Lt,
                    a: i_phi,
                    b: len,
                },
                Some(Type::Bool),
                1,
                false,
            );
            b.branch(cnd[0], body, exit);

            b.position_at(body);
            let (_nid, elr) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_get".into(),
                    args: vec![arr, i_phi],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            let el = elr[0];

            let (_nid, mapped) = b.push_node(
                Inst::CallClosure {
                    conv: crate::wir::CallConv::Fast,
                    fun,
                    args: vec![el],
                },
                Some(Type::Int32),
                1,
                true,
            );

            let (_nid, _s) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_set".into(),
                    args: vec![out, i_phi, mapped[0]],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );

            let next = b.int_bin(IntBinOp::Add, i_phi, one);
            b.jump(head, &[next]);

            b.position_at(exit);
            return Ok(Some(out));
        }

        // ---- filter: out = []; if pred(el) push(out, el)
        "filter" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("filter expects 1 arg"));
            }
            let fun = args[0];

            let (_nid, len_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_len".into(),
                    args: vec![arr],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );
            let len = len_res[0];

            let zero = b.const_i32(0);
            let one = b.const_i32(1);

            // out = list(0)
            let (_nid, out_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_new".into(),
                    args: vec![zero],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Array(Box::new(None))),
                1,
                true,
            );
            let out = out_res[0];

            let head = b.block();
            let body = b.block();
            let exit = b.block();

            let i_phi = b.add_block_param(head, Type::Int32);
            b.jump(head, &[zero]);
            b.position_at(head);
            let (_nid, cnd) = b.push_node(
                Inst::CmpInt {
                    kind: crate::wir::CmpKind::Lt,
                    a: i_phi,
                    b: len,
                },
                Some(Type::Bool),
                1,
                false,
            );
            b.branch(cnd[0], body, exit);

            b.position_at(body);
            let (_nid, elr) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_get".into(),
                    args: vec![arr, i_phi],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            let el = elr[0];

            let (_nid, pred) = b.push_node(
                Inst::CallClosure {
                    conv: crate::wir::CallConv::Fast,
                    fun,
                    args: vec![el],
                },
                Some(Type::Bool),
                1,
                true,
            );

            let then_b = b.block();
            let cont_b = b.block();
            b.branch(pred[0], then_b, cont_b);

            b.position_at(then_b);
            let (_nid, _pushed) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_push".into(),
                    args: vec![out, el],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );
            b.jump(cont_b, &[]);

            b.position_at(cont_b);
            let next = b.int_bin(IntBinOp::Add, i_phi, one);
            b.jump(head, &[next]);

            b.position_at(exit);
            return Ok(Some(out));
        }

        // ---- forEach: just invoke, return 0
        "forEach" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("forEach expects 1 arg"));
            }
            let fun = args[0];

            let (_nid, len_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_len".into(),
                    args: vec![arr],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );
            let len = len_res[0];

            let zero = b.const_i32(0);
            let one = b.const_i32(1);

            let head = b.block();
            let body = b.block();
            let exit = b.block();

            let i_phi = b.add_block_param(head, Type::Int32);
            b.jump(head, &[zero]);
            b.position_at(head);
            let (_nid, cnd) = b.push_node(
                Inst::CmpInt {
                    kind: crate::wir::CmpKind::Lt,
                    a: i_phi,
                    b: len,
                },
                Some(Type::Bool),
                1,
                false,
            );
            b.branch(cnd[0], body, exit);

            b.position_at(body);
            let (_nid, elr) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_get".into(),
                    args: vec![arr, i_phi],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            let el = elr[0];

            let (_nid, _ignored) = b.push_node(
                Inst::CallClosure {
                    conv: crate::wir::CallConv::Fast,
                    fun,
                    args: vec![el],
                },
                Some(Type::Int32),
                1,
                true,
            );

            let next = b.int_bin(IntBinOp::Add, i_phi, one);
            b.jump(head, &[next]);

            b.position_at(exit);
            let z = b.const_i32(0);
            return Ok(Some(z));
        }

        // ---- reduce: closure(acc, el)
        "reduce" => {
            use crate::wir::{CallConv, CmpKind, Inst, IntBinOp, Type};

            if !(args.len() == 1 || args.len() == 2) {
                return Err(LowerError::NotLowerable(
                    "reduce expects (fn) or (fn, init)",
                ));
            }

            let fun = args[0];

            let (_nid, len_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_len".into(),
                    args: vec![arr],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );
            let len = len_res[0];

            let zero = b.const_i32(0);
            let one = b.const_i32(1);

            // --- Seed (i0, acc0)
            // Use init if provided, else: if len==0 -> (0,0), else -> (1, arr[0])
            let seed_join = b.block();
            let seed_i = b.add_block_param(seed_join, Type::Int32);
            let seed_acc = b.add_block_param(seed_join, Type::Int32);

            if args.len() == 2 {
                let init =
                    args[1];
                b.jump(seed_join, &[zero, init]);
            } else {
                let empty_b = b.block();
                let nonempty_b = b.block();

                let (_nid, is_empty) = b.push_node(
                    Inst::CmpInt {
                        kind: CmpKind::Eq,
                        a: len,
                        b: zero,
                    },
                    Some(Type::Bool),
                    1,
                    false,
                );
                b.branch(is_empty[0], empty_b, nonempty_b);

                b.position_at(empty_b);
                b.jump(seed_join, &[zero, zero]);

                b.position_at(nonempty_b);
                let (_nid, first_r) = b.push_node(
                    Inst::CallNative {
                        name: "wir_array_get".into(),
                        args: vec![arr, zero],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                b.jump(seed_join, &[one, first_r[0]]);
            }

            // --- Main loop: phis (i, acc)
            b.position_at(seed_join);

            let head = b.block();
            let body = b.block();
            let exit = b.block();
            let cont = b.block();
            let res = b.add_block_param(cont, Type::Int32);

            let i_phi = b.add_block_param(head, Type::Int32);
            let acc_phi = b.add_block_param(head, Type::Int32);
            b.jump(head, &[seed_i, seed_acc]);

            b.position_at(head);
            let (_nid, cnd) = b.push_node(
                Inst::CmpInt {
                    kind: CmpKind::Lt,
                    a: i_phi,
                    b: len,
                },
                Some(Type::Bool),
                1,
                false,
            );
            b.branch(cnd[0], body, exit); // <-- no direct branch to cont

            b.position_at(body);
            let (_nid, el_r) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_get".into(),
                    args: vec![arr, i_phi],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            let el = el_r[0];

            let (_nid, acc2) = b.push_node(
                Inst::CallClosure {
                    conv: CallConv::Fast,
                    fun,
                    args: vec![acc_phi, el],
                },
                Some(Type::Int32),
                1,
                true,
            );

            let next_i = b.int_bin(IntBinOp::Add, i_phi, one);
            b.jump(head, &[next_i, acc2[0]]);

            b.position_at(exit);
            b.jump(cont, &[acc_phi]); // <-- pass the phi into cont

            b.position_at(cont);
            return Ok(Some(res));
        }

        // ---- find: return first matching element, else 0
        "find" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("find expects 1 arg"));
            }
            let fun = args[0];

            let (_nid, len_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_len".into(),
                    args: vec![arr],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );
            let len = len_res[0];

            let zero = b.const_i32(0);
            let one = b.const_i32(1);

            let head = b.block();
            let body = b.block();
            let exit = b.block();
            let cont = b.block();
            let resp = b.add_block_param(cont, Type::Int32);

            let i_phi = b.add_block_param(head, Type::Int32);
            b.jump(head, &[zero]);

            b.position_at(head);
            let (_nid, cnd) = b.push_node(
                Inst::CmpInt {
                    kind: crate::wir::CmpKind::Lt,
                    a: i_phi,
                    b: len,
                },
                Some(Type::Bool),
                1,
                false,
            );
            b.branch(cnd[0], body, exit);

            b.position_at(body);
            let (_nid, elr) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_get".into(),
                    args: vec![arr, i_phi],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            let el = elr[0];

            let (_nid, hit) = b.push_node(
                Inst::CallClosure {
                    conv: crate::wir::CallConv::Fast,
                    fun,
                    args: vec![el],
                },
                Some(Type::Bool),
                1,
                true,
            );

            let then_b = b.block();
            let cont_b = b.block();
            b.branch(hit[0], then_b, cont_b);

            b.position_at(then_b);
            b.jump(cont, &[el]);

            b.position_at(cont_b);
            let next = b.int_bin(IntBinOp::Add, i_phi, one);
            b.jump(head, &[next]);

            b.position_at(exit);
            b.jump(cont, &[zero]);

            b.position_at(cont);
            return Ok(Some(resp));
        }

        // ---- findIndex: return index or -1
        "findIndex" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("findIndex expects 1 arg"));
            }
            let fun = args[0];

            let (_nid, len_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_len".into(),
                    args: vec![arr],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );
            let len = len_res[0];

            let zero = b.const_i32(0);
            let one = b.const_i32(1);
            let neg1 = b.const_i32(-1);

            let head = b.block();
            let body = b.block();
            let exit = b.block();
            let cont = b.block();
            let resp = b.add_block_param(cont, Type::Int32);

            let i_phi = b.add_block_param(head, Type::Int32);
            b.jump(head, &[zero]);

            b.position_at(head);
            let (_nid, cnd) = b.push_node(
                Inst::CmpInt {
                    kind: crate::wir::CmpKind::Lt,
                    a: i_phi,
                    b: len,
                },
                Some(Type::Bool),
                1,
                false,
            );
            b.branch(cnd[0], body, exit);

            b.position_at(body);
            let (_nid, elr) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_get".into(),
                    args: vec![arr, i_phi],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            let el = elr[0];

            let (_nid, hit) = b.push_node(
                Inst::CallClosure {
                    conv: crate::wir::CallConv::Fast,
                    fun,
                    args: vec![el],
                },
                Some(Type::Bool),
                1,
                true,
            );

            let then_b = b.block();
            let cont_b = b.block();
            b.branch(hit[0], then_b, cont_b);

            b.position_at(then_b);
            b.jump(cont, &[i_phi]);

            b.position_at(cont_b);
            let next = b.int_bin(IntBinOp::Add, i_phi, one);
            b.jump(head, &[next]);

            b.position_at(exit);
            b.jump(cont, &[neg1]);

            b.position_at(cont);
            return Ok(Some(resp));
        }

        _ => Ok(None),
    }
}

fn lower_string_method_call<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    _fields: &mut HashMap<String, FieldId>,
    _next_field: &mut u32,
    recv_v: ValueId,
    name: &str,
    args: &[ValueId],
    lowering_ctx: &LoweringContext,
) -> LResult<Option<ValueId>> {
    use crate::wir::{Inst, Type};

    // Helper macro for creating `CallNative` instructions.
    macro_rules! cn {
        ($fname:expr, [$($argv:expr),*], $ty:expr) => {{
            let (_nid, res) = b.push_node(
                Inst::CallNative {
                    name: $fname.into(),
                    args: vec![$($argv),*],
                    pure: false, // String operations can allocate, so they are not pure.
                    can_throw: false,
                },
                $ty,
                1,
                true,
            );
            Ok(Some(res[0]))
        }};
    }

    // List of all string methods we are implementing.
    let is_string_method = matches!(
        name,
        "concat"
            | "split"
            | "indexOf"
            | "lastIndexOf"
            | "padEnd"
            | "padStart"
            | "repeat"
            | "replace"
            | "replaceAll"
            | "slice"
            | "substring"
            | "startsWith"
            | "endsWith"
            | "includes"
            | "toLowerCase"
            | "toUpperCase"
            | "trim"
            | "trimEnd"
            | "trimStart"
    );

    if !is_string_method {
        return Ok(None); // Not a string method, do nothing.
    }

    // All string methods require lowering the receiver `s`.
    let s = recv_v;

    match name {
        "concat" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("concat expects 1 argument"));
            }
            let other = args[0];
            cn!("wir_string_concat", [s, other], Some(Type::Str))
        }
        "split" => {
            let separator = if let Some(sep_expr) = args.get(0) {
                *sep_expr
            } else {
                b.const_undef() // `undefined` separator splits by nothing.
            };
            cn!(
                "wir_string_split",
                [s, separator],
                Some(Type::Array(Box::new(Some(Type::Str))))
            )
        }
        "indexOf" => {
            if args.is_empty() || args.len() > 2 {
                return Err(LowerError::NotLowerable("indexOf expects 1 or 2 arguments"));
            }
            let search = args[0];
            let pos = if let Some(pos_expr) = args.get(1) {
                *pos_expr
            } else {
                b.const_i32(0) // Default start position is 0
            };
            cn!("wir_string_index_of", [s, search, pos], Some(Type::Int32))
        }
        "lastIndexOf" => {
            if args.is_empty() || args.len() > 2 {
                return Err(LowerError::NotLowerable(
                    "lastIndexOf expects 1 or 2 arguments",
                ));
            }
            let search = args[0];
            let pos = if let Some(pos_expr) = args.get(1) {
                *pos_expr
            } else {
                b.const_i32(-1) // Sentinel for "from the end"
            };
            cn!(
                "wir_string_last_index_of",
                [s, search, pos],
                Some(Type::Int32)
            )
        }
        "padEnd" | "padStart" => {
            if args.is_empty() || args.len() > 2 {
                return Err(LowerError::NotLowerable(
                    "padEnd/padStart expect 1 or 2 arguments",
                ));
            }
            let max_len = args[0];
            let fill_str = if let Some(fill_expr) = args.get(1) {
                *fill_expr
            } else {
                b.const_str(" ") // Default fill is a space
            };
            let native_name = if name == "padEnd" {
                "wir_string_pad_end"
            } else {
                "wir_string_pad_start"
            };
            cn!(native_name, [s, max_len, fill_str], Some(Type::Str))
        }
        "repeat" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("repeat expects 1 argument"));
            }
            let count = args[0];
            cn!("wir_string_repeat", [s, count], Some(Type::Str))
        }
        "replace" => {
            if args.len() != 2 {
                return Err(LowerError::NotLowerable("replace expects 2 arguments"));
            }
            let search = args[0];
            let replacement =
                args[1];
            cn!(
                "wir_string_replace",
                [s, search, replacement],
                Some(Type::Str)
            )
        }
        "replaceAll" => {
            if args.len() != 2 {
                return Err(LowerError::NotLowerable("replaceAll expects 2 arguments"));
            }
            let search = args[0];
            let replacement =
                args[1];
            cn!(
                "wir_string_replace_all",
                [s, search, replacement],
                Some(Type::Str)
            )
        }
        "slice" | "substring" => {
            let start = if let Some(start_expr) = args.get(0) {
                *start_expr
            } else {
                b.const_i32(0)
            };
            let end = if let Some(end_expr) = args.get(1) {
                *end_expr
            } else {
                b.const_i32(-1) // Use -1 SMI as a sentinel for "to the end".
            };
            let native_name = if name == "slice" {
                "wir_string_slice"
            } else {
                "wir_string_substring"
            };
            cn!(native_name, [s, start, end], Some(Type::Str))
        }
        "toUpperCase" => {
            if !args.is_empty() {
                return Err(LowerError::NotLowerable("toUpperCase expects 0 arguments"));
            }
            cn!("wir_string_to_upper_case", [s], Some(Type::Str))
        }
        "toLowerCase" => {
            if !args.is_empty() {
                return Err(LowerError::NotLowerable("toLowerCase expects 0 arguments"));
            }
            cn!("wir_string_to_lower_case", [s], Some(Type::Str))
        }
        "startsWith" => {
            if args.is_empty() || args.len() > 2 {
                return Err(LowerError::NotLowerable(
                    "startsWith expects 1 or 2 arguments",
                ));
            }
            let search = args[0];
            cn!("wir_string_starts_with", [s, search], Some(Type::Bool))
        }
        "endsWith" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("endsWith expects 1 argument"));
            }
            let search = args[0];
            cn!("wir_string_ends_with", [s, search], Some(Type::Bool))
        }
        "includes" => {
            if args.is_empty() || args.len() > 2 {
                return Err(LowerError::NotLowerable("includes expects 1 or 2 arguments"));
            }
            let search = args[0];
            if args.len() == 1 {
                cn!("wir_string_includes", [s, search], Some(Type::Bool))
            } else {
                let index = typed_native(b, "wir_string_index_of", vec![s, search, args[1]], Type::Int32, false);
                let zero = b.const_i32(0);
                let (_, found) = b.push_node(
                    Inst::CmpInt { kind: crate::wir::CmpKind::Ge, a: index, b: zero },
                    Some(Type::Bool), 1, false,
                );
                Ok(Some(found[0]))
            }
        }
        "trim" => {
            if !args.is_empty() {
                return Err(LowerError::NotLowerable("trim expects 0 arguments"));
            }
            cn!("wir_string_trim", [s], Some(Type::Str))
        }
        "trimEnd" | "trimStart" => {
            if !args.is_empty() {
                return Err(LowerError::NotLowerable(
                    "trimEnd/trimStart expects 0 arguments",
                ));
            }
            let native_name = if name == "trimEnd" {
                "wir_string_trim_end"
            } else {
                "wir_string_trim_start"
            };
            cn!(native_name, [s], Some(Type::Str))
        }
        _ => Ok(None),
    }
}

fn lower_expr_free<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    e: &Expr,
    lowering_ctx: &LoweringContext,
) -> LResult<ValueId> {
    snapshot_try_locals(b, locals);
    let value = lower_expr_free_impl(b, locals, fields, next_field, e, lowering_ctx)?;
    snapshot_try_locals(b, locals);
    Ok(value)
}

fn lower_expr_free_impl<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    e: &Expr,
    lowering_ctx: &LoweringContext,
) -> LResult<ValueId> {
    use BinOp::*;

    match e.kind() {
        ExprKind::LitInt(i) => Ok(b.const_i32(*i)),
        ExprKind::LitF64(f) => Ok(b.const_f64(*f)),
        ExprKind::LitBool(v) => {
            let (_nid, res) =
                b.push_node(Inst::Const(Constant::Bool(*v)), Some(Type::Bool), 1, false);
            Ok(res[0])
        }
        ExprKind::LitNull => {
            let (_nid, res) = b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
            Ok(res[0])
        }
        ExprKind::Str(s) => {
            let (_nid, res) = b.push_node(
                Inst::Const(Constant::Str(s.clone())),
                Some(Type::Str),
                1,
                false,
            );
            Ok(res[0])
        }

        ExprKind::Conditional {
            cond,
            then_branch,
            else_branch,
        } => {
            let cond_v = lower_expr_free(b, locals, fields, next_field, cond, lowering_ctx)?;
            let then_b = b.block();
            let else_b = b.block();
            let cont = b.block();
            let res_param = b.add_block_param(cont, Type::Int32);
            b.branch(cond_v, then_b, else_b);

            b.position_at(then_b);
            let tval = lower_expr_free(b, locals, fields, next_field, then_branch, lowering_ctx)?;
            b.jump(cont, &[tval]);

            b.position_at(else_b);
            let fval = lower_expr_free(b, locals, fields, next_field, else_branch, lowering_ctx)?;
            b.jump(cont, &[fval]);

            b.position_at(cont);
            Ok(res_param)
        }

        // Allow await when inside an async lowering scope.
        ExprKind::Await(inner) => {
            if !await_allowed() {
                return Err(LowerError::NotLowerable("await outside async function"));
            }
            let pv = lower_expr_free(b, locals, fields, next_field, inner, lowering_ctx)?;
            let (_nid, res) = b.push_node(
                Inst::CallNative {
                    name: "wir_await".into(),
                    args: vec![pv],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            return Ok(res[0]);
        }
        // Unhoisted function literal shouldn't reach the lowerer
        ExprKind::FnLit { .. } => {
            return Err(LowerError::NotLowerable(
                "unhoisted function literal reached lowerer",
            ));
        }

        // locals first, else known function -> a closure with null env
        ExprKind::Ident(name) => {
            // 1) Captured/boxed local (read box[0])
            //    If you use a specific key format for boxed locals, keep it here.
            if locals.get(&boxed_key(name)).is_some() {
                let box_arr = *locals
                    .get(name)
                    .ok_or_else(|| LowerError::UnknownVar(name.clone()))?;
                let zero = b.const_i32(0);
                let (_nid, res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_array_get".into(),
                        args: vec![box_arr, zero],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                return Ok(res[0]);
            }

            // 2) Plain local
            if let Some(&v) = locals.get(name) {
                return Ok(v);
            }

            if let Some((_, cell)) = lowering_ctx.links.module_bindings.get(name) {
                return Ok(b.load_binding(*cell, None));
            }

            if let Some(binding) = lowering_ctx.links.enum_bindings.get(name) {
                return Ok(b.load_binding(binding.cell, None));
            }

            // 3) Known global function name â†’ make a closure with null env
            if let Some(&fid) = lowering_ctx.funcs.get(name) {
                let (_nid, env_null) =
                    b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                let (_nid, clos) = b.push_node(
                    Inst::MakeClosure {
                        callee: fid,
                        env: env_null[0],
                    },
                    Some(Type::Closure(None)),
                    1,
                    false,
                );
                return Ok(clos[0]);
            }

            // 4) Named import: read provider's live binding (must be linked beforehand).
            //    `links.import_bindings` maps local name -> provider BindingId.
            if let Some(&bid) = lowering_ctx.links.import_bindings.get(name) {
                let v = b.load_binding(bid, None);
                return Ok(v);
            }

            // 5) Own export: read our own live binding cell.
            //    `links.export_bindings` maps our local export name -> our BindingId.
            if let Some(&bid) = lowering_ctx.links.export_bindings.get(name) {
                let v = b.load_binding(bid, None);
                return Ok(v);
            }

            // 6) Namespace import cached in `__modinit__` (fast path).
            if let Some(&cell) = lowering_ctx.links.namespace_cells.get(name) {
                let ns_obj = b.load_binding(cell, None);
                return Ok(ns_obj);
            }

            // 7) Compatibility path: declared namespace import but not cached yet.
            //    If the namespace alias is known, we can synthesize/return a namespace
            //    object lazily and memoize it into `locals` to avoid rebuilding it.
            if let Some(exports) = lowering_ctx.links.namespace_imports.get(name) {
                if let Some(&cached) = locals.get(name) {
                    return Ok(cached);
                }
                let ns_obj = b.make_namespace(exports.clone());
                locals.insert(name.clone(), ns_obj);
                return Ok(ns_obj);
            }

            // Miss: unresolved identifier
            Err(LowerError::Undefined {
                name: name.clone(),
                meta: e.meta.clone(),
            })
        }

        ExprKind::OptionalChain { base, access } => {
            let base_v = lower_expr_free(b, locals, fields, next_field, base, lowering_ctx)?;
            let cont = b.block();
            let res_param = b.add_block_param(cont, Type::Top);
            let null_v = b.const_null();
            let null_block = b.block();
            let value_block = b.block();
            let (_nid, is_null) = b.push_node(
                Inst::CallNative {
                    name: "wir_is_nullish".into(),
                    args: vec![base_v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Bool),
                1,
                true,
            );
            b.branch(is_null[0], null_block, value_block);

            b.position_at(null_block);
            b.jump(cont, &[null_v]);

            b.position_at(value_block);
            let value = match access {
                OptionalAccess::Prop(name) => {
                    lower_general_getprop(b, base_v, name, fields, next_field)
                }
                OptionalAccess::Index(idx_expr) => {
                    let idx_val =
                        lower_expr_free(b, locals, fields, next_field, idx_expr, lowering_ctx)?;
                    let (_nid_is, is_str) = b.push_node(
                        Inst::CallNative {
                            name: "wir_is_str".into(),
                            args: vec![idx_val],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    let str_b = b.block();
                    let arr_b = b.block();
                    let idx_cont = b.block();
                    let idx_res = b.add_block_param(idx_cont, Type::Top);
                    b.branch(is_str[0], str_b, arr_b);

                    b.position_at(str_b);
                    let (_nid_get, sv) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_get_str".into(),
                            args: vec![base_v, idx_val],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    b.jump(idx_cont, &[sv[0]]);

                    b.position_at(arr_b);
                    let (_nid_arr, av) = b.push_node(
                        Inst::CallNative {
                            name: "wir_array_get".into(),
                            args: vec![base_v, idx_val],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    b.jump(idx_cont, &[av[0]]);

                    b.position_at(idx_cont);
                    idx_res
                }
                OptionalAccess::Call(args) => {
                    let mut argv = Vec::with_capacity(args.len() + 1);
                    let mut this_source: Option<Expr> = None;
                    match base.kind() {
                        ExprKind::GetProp { recv, .. } => {
                            this_source = Some((**recv).clone());
                        }
                        ExprKind::Index { recv, index }
                            if matches!(index.kind(), ExprKind::Str(_)) =>
                        {
                            this_source = Some((**recv).clone());
                        }
                        ExprKind::OptionalChain {
                            base: inner,
                            access: OptionalAccess::Prop(_),
                        } => {
                            this_source = Some((**inner).clone());
                        }
                        _ => {}
                    }
                    if let Some(expr) = this_source {
                        let this_v =
                            lower_expr_free(b, locals, fields, next_field, &expr, lowering_ctx)?;
                        argv.push(this_v);
                    }
                    for arg in args {
                        argv.push(lower_expr_free(
                            b,
                            locals,
                            fields,
                            next_field,
                            arg,
                            lowering_ctx,
                        )?);
                    }
                    let (_nid, res) = b.push_node(
                        Inst::CallClosure {
                            conv: crate::wir::CallConv::Fast,
                            fun: base_v,
                            args: argv,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    res[0]
                }
            };
            b.jump(cont, &[value]);

            b.position_at(cont);
            Ok(res_param)
        }

        ExprKind::Group(inner) => {
            lower_expr_free(b, locals, fields, next_field, inner, lowering_ctx)
        }

        ExprKind::Unary { op, e } => {
            let v = lower_expr_free(b, locals, fields, next_field, e, lowering_ctx)?;
            match op {
                UnOp::Neg => {
                    let zero = b.const_i32(0);
                    Ok(b.int_bin(IntBinOp::Sub, zero, v))
                }
                UnOp::Pos => Ok(v),
                UnOp::BitwiseNot => {
                    // handle `~`
                    let neg_one = b.const_i32(-1);
                    Ok(b.int_bin(IntBinOp::Xor, v, neg_one))
                }
                UnOp::Not => {
                    let (_nid, falsev) = b.push_node(
                        Inst::Const(Constant::Bool(false)),
                        Some(Type::Bool),
                        1,
                        false,
                    );
                    let (_nid, res) = b.push_node(
                        Inst::CmpInt {
                            kind: crate::wir::CmpKind::Eq,
                            a: v,
                            b: falsev[0],
                        },
                        Some(Type::Bool),
                        1,
                        false,
                    );
                    Ok(res[0])
                }
            }
        }

        ExprKind::Binary { op, a, b: bb } => {
            let left_is_str_lit = matches!(a.kind(), ExprKind::Str(_));
            let right_is_str_lit = matches!(bb.kind(), ExprKind::Str(_));
            let va = lower_expr_free(b, locals, fields, next_field, a, lowering_ctx)?;
            match op {
                Add => {
                    let vb = lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    if left_is_str_lit || right_is_str_lit {
                        // `"lit" + x` concatenates with `x` converted to a string.
                        let (_nid, res) = b.push_node(
                            Inst::CallNative {
                                name: "wir_string_concat_coerce".into(),
                                args: vec![va, vb],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Str),
                            1,
                            true,
                        );
                        Ok(res[0])
                    } else {
                        Ok(b.int_bin(IntBinOp::Add, va, vb))
                    }
                }
                Sub => {
                    let vb = lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::Sub, va, vb))
                }
                Mul => {
                    let vb = lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::Mul, va, vb))
                }
                Div => {
                    let vb = lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::DivS, va, vb))
                }
                Rem => {
                    let vb = lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::RemS, va, vb))
                }
                Shl => {
                    // a << b
                    let vb = lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::Shl, va, vb))
                }
                BitOr => {
                    let vb = lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::Or, va, vb))
                }
                Shr => {
                    // a >> b  (arithmetic right shift, sign-propagating)
                    let vb = lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::Sar, va, vb))
                }
                ShrU => {
                    // handle `>>>`
                    let vb = lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::ShrU, va, vb)) // ShrU = Unsigned (Logical) Shift Right
                }
                StrConcat => {
                    // handle `__`
                    let vb = lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;

                    // We need to ensure both operands are strings before concatenating.
                    // For simplicity, we'll use a native helper that does the conversion.
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_string_concat_coerce".into(),
                            args: vec![va, vb],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Str),
                        1,
                        true,
                    );
                    Ok(res[0])
                }
                Eq | Ne | Lt | Le | Gt | Ge => {
                    let vb = lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;

                    if *op == BinOp::Eq || *op == BinOp::Ne {
                        let (_nid1, is_a_str) = b.push_node(
                            Inst::CallNative {
                                name: "wir_is_str".into(),
                                args: vec![va],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Bool),
                            1,
                            true,
                        );
                        let (_nid2, is_b_str) = b.push_node(
                            Inst::CallNative {
                                name: "wir_is_str".into(),
                                args: vec![vb],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Bool),
                            1,
                            true,
                        );
                        let is_either_str = build_bool_or(b, is_a_str[0], is_b_str[0]);

                        let string_path = b.block();
                        let int_path = b.block();
                        let cont = b.block();
                        let result_phi = b.add_block_param(cont, Type::Bool);

                        b.branch(is_either_str, string_path, int_path);

                        b.position_at(string_path);
                        let (_nid_streq, str_eq_res) = b.push_node(
                            Inst::CallNative {
                                name: "wir_string_equals".into(),
                                args: vec![va, vb],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Bool),
                            1,
                            true,
                        );
                        let str_res = if *op == BinOp::Ne {
                            let falsev = b.const_bool(false);
                            let (_nid, negated) = b.push_node(
                                Inst::CmpInt {
                                    kind: crate::wir::CmpKind::Eq,
                                    a: str_eq_res[0],
                                    b: falsev,
                                },
                                Some(Type::Bool),
                                1,
                                false,
                            );
                            negated[0]
                        } else {
                            str_eq_res[0]
                        };
                        b.jump(cont, &[str_res]);

                        b.position_at(int_path);
                        let kind = if *op == BinOp::Eq {
                            crate::wir::CmpKind::Eq
                        } else {
                            crate::wir::CmpKind::Ne
                        };
                        let (_nid_int, int_res) = b.push_node(
                            Inst::CmpInt { kind, a: va, b: vb },
                            Some(Type::Bool),
                            1,
                            false,
                        );
                        b.jump(cont, &[int_res[0]]);

                        b.position_at(cont);
                        return Ok(result_phi);
                    } else {
                        let kind = match *op {
                            BinOp::Lt => crate::wir::CmpKind::Lt,
                            BinOp::Le => crate::wir::CmpKind::Le,
                            BinOp::Gt => crate::wir::CmpKind::Gt,
                            BinOp::Ge => crate::wir::CmpKind::Ge,
                            _ => unreachable!(),
                        };
                        let (_nid, res) = b.push_node(
                            Inst::CmpInt { kind, a: va, b: vb },
                            Some(Type::Bool),
                            1,
                            false,
                        );
                        Ok(res[0])
                    }
                }
                And | Or => {
                    let then_b = b.block();
                    let else_b = b.block();
                    let cont = b.block();
                    let res_param = b.add_block_param(cont, Type::Bool);

                    if *op == And {
                        b.branch(va, then_b, else_b);
                    } else {
                        b.branch(va, else_b, then_b);
                    }

                    b.position_at(then_b);
                    let tval = if *op == And {
                        lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?
                    } else {
                        let (_nid, res) = b.push_node(
                            Inst::Const(Constant::Bool(true)),
                            Some(Type::Bool),
                            1,
                            false,
                        );
                        res[0]
                    };
                    b.jump(cont, &[tval]);

                    b.position_at(else_b);
                    let fval = if *op == And {
                        let (_nid, res) = b.push_node(
                            Inst::Const(Constant::Bool(false)),
                            Some(Type::Bool),
                            1,
                            false,
                        );
                        res[0]
                    } else {
                        lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?
                    };
                    b.jump(cont, &[fval]);

                    b.position_at(cont);
                    Ok(res_param)
                }
                Nullish => {
                    let cont = b.block();
                    let res_param = b.add_block_param(cont, Type::Top);
                    let null_block = b.block();
                    let value_block = b.block();
                    let (_nid, is_nullish) = b.push_node(
                        Inst::CallNative {
                            name: "wir_is_nullish".into(),
                            args: vec![va],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );
                    b.branch(is_nullish[0], null_block, value_block);

                    b.position_at(null_block);
                    let vb = lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    b.jump(cont, &[vb]);

                    b.position_at(value_block);
                    b.jump(cont, &[va]);

                    b.position_at(cont);
                    Ok(res_param)
                }
            }
        }

        ExprKind::Assign(lv, rhs) => {
            let rv = lower_expr_free(b, locals, fields, next_field, rhs, lowering_ctx)?;
            match lv.kind() {
                // o.a = rv      (dot write)
                LValueKind::GetProp { recv, name } => {
                    let obj = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;

                    // Special-case: arr.length = n (only for real arrays; other values
                    // get a regular property store below).
                    let mut length_join = None;
                    if name == "length" {
                        let (_nid, is_arr) = b.push_node(
                            Inst::CallNative {
                                name: "wir_is_array".into(),
                                args: vec![obj],
                                pure: true,
                                can_throw: false,
                            },
                            Some(Type::Bool),
                            1,
                            false,
                        );
                        let arr_b = b.block();
                        let prop_b = b.block();
                        let join = b.block();
                        b.branch(is_arr[0], arr_b, prop_b);
                        b.position_at(arr_b);
                        let (_nid, _r) = b.push_node(
                            Inst::CallNative {
                                name: "wir_array_set_len".into(),
                                args: vec![obj, rv],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                        b.jump(join, &[]);
                        b.position_at(prop_b);
                        length_join = Some(join);
                    }

                    // 1) Store fast field
                    let field = intern_field_local(fields, next_field, name);
                    let _ = b.push_node(
                        Inst::StoreField {
                            obj,
                            field,
                            val: rv,
                            expected: None,
                        },
                        Some(Type::Top),
                        1,
                        true,
                    );

                    // 2) Mirror into string table
                    let (_nid_sconst, ks) = b.push_node(
                        Inst::Const(Constant::Str(name.clone())),
                        Some(Type::Str),
                        1,
                        false,
                    );
                    let _ = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_set_str".into(),
                            args: vec![obj, ks[0], rv],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );

                    if let Some(join) = length_join {
                        b.jump(join, &[]);
                        b.position_at(join);
                    }
                    Ok(rv)
                }

                // o["a"] = rv     (bracket write with string)
                LValueKind::Index { recv, index } if matches!(index.kind(), ExprKind::Str(_)) => {
                    let obj = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
                    let s = if let ExprKind::Str(s) = index.kind() {
                        s
                    } else {
                        unreachable!()
                    };

                    // 1) Store fast field
                    let field = intern_field_local(fields, next_field, s);
                    let _ = b.push_node(
                        Inst::StoreField {
                            obj,
                            field,
                            val: rv,
                            expected: None,
                        },
                        Some(Type::Top),
                        1,
                        true,
                    );

                    // 2) Mirror into string table
                    let (_nid, ks) = b.push_node(
                        Inst::Const(Constant::Str(s.clone())),
                        Some(Type::Str),
                        1,
                        false,
                    );
                    let _ = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_set_str".into(),
                            args: vec![obj, ks[0], rv],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );

                    Ok(rv)
                }

                // --- inside ExprKind::Assign(lv, rhs) match ---
                LValueKind::Index { recv, index } if !matches!(index.kind(), ExprKind::Str(_)) => {
                    let obj = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
                    let idxv = lower_expr_free(b, locals, fields, next_field, index, lowering_ctx)?;

                    let (_nid_is, is_str) = b.push_node(
                        Inst::CallNative {
                            name: "wir_is_str".into(),
                            args: vec![idxv],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    let str_b = b.block();
                    let arr_b = b.block();
                    let cont = b.block();

                    b.branch(is_str[0], str_b, arr_b);

                    b.position_at(str_b);
                    let (_nid_set_s, _r_s) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_set_str".into(),
                            args: vec![obj, idxv, rv],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    b.jump(cont, &[]);

                    b.position_at(arr_b);
                    let (_nid_set_a, _r_a) = b.push_node(
                        Inst::CallNative {
                            name: "wir_array_set".into(),
                            args: vec![obj, idxv, rv],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    b.jump(cont, &[]);

                    b.position_at(cont);
                    Ok(rv)
                }

                // x = rv          (local write, with capture boxing support)
                LValueKind::Ident(name) => {
                    if !locals.contains_key(name) {
                        if let Some((_, cell)) = lowering_ctx.links.module_bindings.get(name) {
                            b.store_binding(*cell, rv);
                            return Ok(rv);
                        }
                    }
                    #[cfg(debug_assertions)]
                    {
                        eprintln!("lower_expr_free() LValue::Ident({})", name);
                        eprintln!(
                            "[links] exports        : {:?}",
                            lowering_ctx
                                .links
                                .export_bindings
                                .keys()
                                .collect::<Vec<_>>()
                        );
                        eprintln!(
                            "[links] imports        : {:?}",
                            lowering_ctx
                                .links
                                .import_bindings
                                .keys()
                                .collect::<Vec<_>>()
                        );
                        eprintln!(
                            "[links] namespace_imps : {:?}",
                            lowering_ctx
                                .links
                                .namespace_imports
                                .keys()
                                .collect::<Vec<_>>()
                        );
                        eprintln!(
                            "[links] namespace_cells: {:?}",
                            lowering_ctx.links.namespace_cells
                        );
                    }

                    // a) no se puede asignar a un import
                    if lowering_ctx.links.import_bindings.contains_key(name) {
                        return Err(LowerError::NotLowerable(
                            "cannot assign to imported binding",
                        ));
                    }
                    // b) tampoco a un namespace import
                    if lowering_ctx.links.namespace_cells.contains_key(name)
                        || lowering_ctx.links.namespace_imports.contains_key(name)
                    {
                        return Err(LowerError::NotLowerable(
                            "cannot assign to namespace import",
                        ));
                    }
                    // c) export propio: live update
                    if !locals.contains_key(name) {
                        if let Some(&bid) = lowering_ctx.links.export_bindings.get(name) {
                            b.store_binding(bid, rv);
                            return Ok(rv);
                        }
                    }

                    // import x from "m";  x = ...  â†’ error de compilaciÃ³n
                    if lowering_ctx.links.import_bindings.contains_key(name) {
                        return Err(LowerError::NotLowerable(
                            "cannot assign to imported binding",
                        ));
                    }

                    // export let x;  x = rv  â†’ StoreBinding(binding(this,x), rv)
                    if !locals.contains_key(name) {
                        if let Some(&bid) = lowering_ctx.links.export_bindings.get(name) {
                            b.store_binding(bid, rv);
                            return Ok(rv);
                        }
                    }

                    // resto: igual que tenÃ­as (boxed locals / locals normales / error)
                    if locals.get(&boxed_key(name)).is_some() {
                        let box_arr = *locals
                            .get(name)
                            .ok_or_else(|| LowerError::UnknownVar(name.clone()))?;
                        let zero = b.const_i32(0);
                        let (_nid, _res) = b.push_node(
                            Inst::CallNative {
                                name: "wir_array_set".into(),
                                args: vec![box_arr, zero, rv],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                        Ok(rv)
                    } else {
                        if locals.contains_key(name) {
                            locals.insert(name.clone(), rv);
                            Ok(rv)
                        } else {
                            Err(LowerError::Undefined {
                                name: name.clone(),
                                meta: e.meta.clone(),
                            })
                        }
                    }
                }

                _ => Err(LowerError::NotLowerable("invalid lvalue")),
            }
        }

        // obj.<propKey>  where propKey is an identifier or string
        ExprKind::GetProp { recv, name } => {
            // `ns.member` of a namespace import reads the exporter's live binding cell.
            if let ExprKind::Ident(ns) = recv.kind() {
                if is_namespace_ident(recv, locals, lowering_ctx) {
                    let binding = lowering_ctx
                        .links
                        .namespace_imports
                        .get(ns)
                        .and_then(|members| members.iter().find(|(n, _)| n == name))
                        .map(|(_, bid)| *bid);
                    if let Some(bid) = binding {
                        return Ok(b.load_binding(bid, None));
                    }
                }
            }

            // Static class method read: Class.static â†’ closure with null env
            if let ExprKind::Ident(cn) = recv.kind() {
                if let Some(&mfid) = lowering_ctx.funcs.get(&format!("__static_{}_{}", cn, name)) {
                    let (_nid, env_null) =
                        b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                    let (_nid, clos) = b.push_node(
                        Inst::MakeClosure {
                            callee: mfid,
                            env: env_null[0],
                        },
                        Some(Type::Closure(None)),
                        1,
                        false,
                    );
                    return Ok(clos[0]);
                }
            }

            // Lower receiver once
            let recv_v = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;

            // --- Special case: "length" ---
            if name == "length" {
                // Proxies must delegate to generic getprop to honor traps
                let (_nid_is_proxy, is_proxy_res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_is_proxy".into(),
                        args: vec![recv_v],
                        pure: true,
                        can_throw: false,
                    },
                    Some(Type::Bool),
                    1,
                    false,
                );

                let proxy_b = b.block();
                let normal_b = b.block();
                let cont = b.block();
                let out = b.add_block_param(cont, Type::Int32);

                b.branch(is_proxy_res[0], proxy_b, normal_b);

                // Proxy path â†’ generic (may be trapped/overridden)
                b.position_at(proxy_b);
                let pv = lower_general_getprop(b, recv_v, name, fields, next_field);
                b.jump(cont, &[pv]);

                // Non-proxy: first branch on STRING (never call obj_* on strings!)
                b.position_at(normal_b);
                let (_nid_is_s, is_s) = b.push_node(
                    Inst::CallNative {
                        name: "wir_is_str".into(),
                        args: vec![recv_v],
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::Bool),
                    1,
                    true,
                );

                let string_b = b.block();
                let not_string_b = b.block();
                b.branch(is_s[0], string_b, not_string_b);

                // String path â†’ builtin length
                b.position_at(string_b);
                let (_nid_len, len_res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_string_len".into(),
                        args: vec![recv_v],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                b.jump(cont, &[len_res[0]]);

                // Not a string: arrays use the builtin length; anything else is a
                // regular property read (never reinterpret an array as an object).
                b.position_at(not_string_b);
                let (_nid_is_arr, is_arr) = b.push_node(
                    Inst::CallNative {
                        name: "wir_is_array".into(),
                        args: vec![recv_v],
                        pure: true,
                        can_throw: false,
                    },
                    Some(Type::Bool),
                    1,
                    false,
                );
                let arr_b = b.block();
                let other_b = b.block();
                b.branch(is_arr[0], arr_b, other_b);

                b.position_at(arr_b);
                let (_nid_a, arr_res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_array_len".into(),
                        args: vec![recv_v],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                b.jump(cont, &[arr_res[0]]);

                b.position_at(other_b);
                let ov = lower_general_getprop(b, recv_v, name, fields, next_field);
                b.jump(cont, &[ov]);

                b.position_at(cont);
                return Ok(out);
            }

            // --- Special case: "size" (Map/Set) ---
            if name == "size" {
                // Proxies â†’ generic
                let (_nid_is_proxy, is_proxy_res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_is_proxy".into(),
                        args: vec![recv_v],
                        pure: true,
                        can_throw: false,
                    },
                    Some(Type::Bool),
                    1,
                    false,
                );

                let proxy_b = b.block();
                let normal_b = b.block();
                let join = b.block();
                let out = b.add_block_param(join, Type::Int32);
                b.branch(is_proxy_res[0], proxy_b, normal_b);

                b.position_at(proxy_b);
                let v = lower_general_getprop(b, recv_v, name, fields, next_field);
                b.jump(join, &[v]);

                b.position_at(normal_b);
                let (_nid_map, is_map) = b.push_node(
                    Inst::CallNative {
                        name: "wir_is_map".into(),
                        args: vec![recv_v],
                        pure: true,
                        can_throw: false,
                    },
                    Some(Type::Bool),
                    1,
                    false,
                );
                let map_b = b.block();
                let check_set_b = b.block();
                b.branch(is_map[0], map_b, check_set_b);

                b.position_at(map_b);
                let (_nid_ms, ms) = b.push_node(
                    Inst::CallNative {
                        name: "wir_map_size".into(),
                        args: vec![recv_v],
                        pure: true,
                        can_throw: false,
                    },
                    Some(Type::Int32),
                    1,
                    false,
                );
                b.jump(join, &[ms[0]]);

                b.position_at(check_set_b);
                let (_nid_set, is_set) = b.push_node(
                    Inst::CallNative {
                        name: "wir_is_set".into(),
                        args: vec![recv_v],
                        pure: true,
                        can_throw: false,
                    },
                    Some(Type::Bool),
                    1,
                    false,
                );
                let set_b = b.block();
                let other_b = b.block();
                b.branch(is_set[0], set_b, other_b);

                b.position_at(set_b);
                let (_nid_ss, ss) = b.push_node(
                    Inst::CallNative {
                        name: "wir_set_size".into(),
                        args: vec![recv_v],
                        pure: true,
                        can_throw: false,
                    },
                    Some(Type::Int32),
                    1,
                    false,
                );
                b.jump(join, &[ss[0]]);

                b.position_at(other_b);
                let v = lower_general_getprop(b, recv_v, name, fields, next_field);
                b.jump(join, &[v]);

                b.position_at(join);
                return Ok(out);
            }

            // Fallback to the generic property getter for all other property names.
            let value = lower_general_getprop(b, recv_v, name, fields, next_field);
            Ok(value)
        }

        // obj.<propKey> = value   (identifier or string propKey)
        ExprKind::SetPropObj { obj, key, value } => {
            let o = lower_expr_free(b, locals, fields, next_field, obj, lowering_ctx)?;
            let v = lower_expr_free(b, locals, fields, next_field, value, lowering_ctx)?;
            let field_name = match key {
                PropKey::Ident(s) => s.clone(),
                PropKey::Str(s) => s.clone(),
            };

            let field = intern_field_local(fields, next_field, &field_name);
            let fid_smi = b.const_i32(field.0 as i32);
            let (_nid_field_str, field_str) = b.push_node(
                Inst::Const(Constant::Str(field_name.clone())),
                Some(Type::Str),
                1,
                false,
            );

            let _ = b.push_node(
                Inst::CallNative {
                    name: "wir_field_register_name".into(),
                    args: vec![fid_smi, field_str[0]],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );

            let (_nid_is_proxy, is_proxy) = b.push_node(
                Inst::CallNative {
                    name: "wir_is_proxy".into(),
                    args: vec![o],
                    pure: true,
                    can_throw: false,
                },
                Some(Type::Bool),
                1,
                false,
            );

            let proxy_block = b.block();
            let non_proxy_block = b.block();
            let cont = b.block();
            let result_phi = b.add_block_param(cont, Type::Int32);

            b.branch(is_proxy[0], proxy_block, non_proxy_block);

            b.position_at(proxy_block);
            let (_nid_proxy_set, _) = b.push_node(
                Inst::CallNative {
                    name: "wir_obj_set_str".into(),
                    args: vec![o, field_str[0], v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );
            b.jump(cont, &[v]);

            b.position_at(non_proxy_block);

            let setter_key = format!("__set__{}", field_name);
            let (_nid_sk, sk) = b.push_node(
                Inst::Const(Constant::Str(setter_key)),
                Some(Type::Str),
                1,
                false,
            );
            let (_nid_sv, sv) = b.push_node(
                Inst::CallNative {
                    name: "wir_obj_get_str".into(),
                    args: vec![o, sk[0]],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );

            let zero = b.const_i32(0);
            let (_nid_has_set, has_set) = b.push_node(
                Inst::CmpInt {
                    kind: crate::wir::CmpKind::Ne,
                    a: sv[0],
                    b: zero,
                },
                Some(Type::Bool),
                1,
                false,
            );

            let call_set_b = b.block();
            let store_b = b.block();
            let join = b.block();

            b.branch(has_set[0], call_set_b, store_b);

            b.position_at(call_set_b);
            let (_nid_call, _r) = b.push_node(
                Inst::CallClosure {
                    conv: crate::wir::CallConv::Fast,
                    fun: sv[0],
                    args: vec![o, v],
                },
                Some(Type::Int32),
                1,
                true,
            );
            b.jump(join, &[]);

            b.position_at(store_b);
            let _ = b.push_node(
                Inst::StoreField {
                    obj: o,
                    field,
                    val: v,
                    expected: None,
                },
                Some(Type::Top),
                1,
                true,
            );

            let _ = b.push_node(
                Inst::CallNative {
                    name: "wir_obj_set_str".into(),
                    args: vec![o, field_str[0], v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );
            b.jump(join, &[]);

            b.position_at(join);
            b.jump(cont, &[v]);

            b.position_at(cont);
            Ok(result_phi)
        }

        // Calls / builtins
        ExprKind::Call { callee, args } => {
            // Literal bracket calls have the same dispatch and evaluation order
            // as property calls, including array/string builtins and type errors.
            if let ExprKind::Index { recv, index } = callee.kind() {
                if let ExprKind::Str(name) = index.kind() {
                    let property = expr_with_meta(callee, ExprKind::GetProp {
                        recv: recv.clone(), name: name.clone(),
                    });
                    let call = expr_with_meta(e, ExprKind::Call {
                        callee: SmallBox::new(property), args: args.clone(),
                    });
                    return lower_expr_free(b, locals, fields, next_field, &call, lowering_ctx);
                }
            }

            // --- Property-call fast paths ---
            if let ExprKind::GetProp { recv, name } = callee.kind() {
                // 0-) Namespace import member: `ns.f(args)` calls the exported value as a
                //     plain function; a namespace object is never passed as `this`.
                if let ExprKind::Ident(ns) = recv.kind() {
                    if is_namespace_ident(recv, locals, lowering_ctx) {
                        let funv =
                            lower_expr_free(b, locals, fields, next_field, callee, lowering_ctx)?;
                        let mut argv = Vec::with_capacity(args.len());
                        for a in args {
                            argv.push(lower_expr_free(
                                b,
                                locals,
                                fields,
                                next_field,
                                a,
                                lowering_ctx,
                            )?);
                        }
                        let message = format!("TypeError: {ns}.{name} is not a function");
                        require_callable(b, funv, &message);
                        let (_nid, res) = b.push_node(
                            Inst::CallClosure {
                                conv: crate::wir::CallConv::Fast,
                                fun: funv,
                                args: argv,
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                        return Ok(res[0]);
                    }
                }

                // 0a) Promise-style instance methods
                if name == "then" {
                    let p = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
                    let z = b.const_i32(0); // sentinel "no callback"
                    let onf = if args.len() >= 1 {
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?
                    } else {
                        z
                    };
                    let onr = if args.len() >= 2 {
                        lower_expr_free(b, locals, fields, next_field, &args[1], lowering_ctx)?
                    } else {
                        z
                    };
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_promise_then".into(),
                            args: vec![p, onf, onr],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "catch" {
                    let p = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
                    let z = b.const_i32(0);
                    let onr = if args.len() >= 1 {
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?
                    } else {
                        z
                    };
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_promise_catch".into(),
                            args: vec![p, onr],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "resolve" {
                    // deferred.resolve(value?)
                    let p = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
                    let (_nid, nul) =
                        b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                    let val = if args.len() >= 1 {
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?
                    } else {
                        nul[0]
                    };
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_deferred_resolve".into(),
                            args: vec![p, val],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "reject" {
                    // deferred.reject(reason?)
                    let p = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
                    let (_nid, nul) =
                        b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                    let reason = if args.len() >= 1 {
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?
                    } else {
                        nul[0]
                    };
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_deferred_reject".into(),
                            args: vec![p, reason],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }

                // 0b) http.* helpers â€” IMPORTANT: this branch does NOT lower `recv`
                if let ExprKind::Ident(obj) = recv.kind() {
                    if obj == "http" {
                        match name.as_str() {
                            "startStream" => {
                                if args.len() != 3 {
                                    return Err(LowerError::NotLowerable(
                                        "http.startStream(req, status, headers)",
                                    ));
                                }
                                let req = lower_expr_free(
                                    b,
                                    locals,
                                    fields,
                                    next_field,
                                    &args[0],
                                    lowering_ctx,
                                )?;
                                let status = lower_expr_free(
                                    b,
                                    locals,
                                    fields,
                                    next_field,
                                    &args[1],
                                    lowering_ctx,
                                )?;
                                let hdrs = lower_expr_free(
                                    b,
                                    locals,
                                    fields,
                                    next_field,
                                    &args[2],
                                    lowering_ctx,
                                )?;
                                let (_nid, res) = b.push_node(
                                    Inst::CallNative {
                                        name: "wir_http_start_stream_from_req".into(),
                                        args: vec![req, status, hdrs],
                                        pure: false,
                                        can_throw: false,
                                    },
                                    Some(Type::Int32),
                                    1,
                                    true,
                                );
                                return Ok(res[0]);
                            }
                            "streamWrite" => {
                                if args.len() != 3 {
                                    return Err(LowerError::NotLowerable(
                                        "http.streamWrite(serverId, reqId, chunk)",
                                    ));
                                }
                                let sid = lower_expr_free(
                                    b,
                                    locals,
                                    fields,
                                    next_field,
                                    &args[0],
                                    lowering_ctx,
                                )?;
                                let rid = lower_expr_free(
                                    b,
                                    locals,
                                    fields,
                                    next_field,
                                    &args[1],
                                    lowering_ctx,
                                )?;
                                let chunk = lower_expr_free(
                                    b,
                                    locals,
                                    fields,
                                    next_field,
                                    &args[2],
                                    lowering_ctx,
                                )?;
                                let (_nid, res) = b.push_node(
                                    Inst::CallNative {
                                        name: "wir_http_stream_write".into(),
                                        args: vec![sid, rid, chunk],
                                        pure: false,
                                        can_throw: false,
                                    },
                                    Some(Type::Int32),
                                    1,
                                    true,
                                );
                                return Ok(res[0]);
                            }
                            "streamEnd" => {
                                if args.len() != 2 {
                                    return Err(LowerError::NotLowerable(
                                        "http.streamEnd(serverId, reqId)",
                                    ));
                                }
                                let sid = lower_expr_free(
                                    b,
                                    locals,
                                    fields,
                                    next_field,
                                    &args[0],
                                    lowering_ctx,
                                )?;
                                let rid = lower_expr_free(
                                    b,
                                    locals,
                                    fields,
                                    next_field,
                                    &args[1],
                                    lowering_ctx,
                                )?;
                                let (_nid, res) = b.push_node(
                                    Inst::CallNative {
                                        name: "wir_http_stream_end".into(),
                                        args: vec![sid, rid],
                                        pure: false,
                                        can_throw: false,
                                    },
                                    Some(Type::Int32),
                                    1,
                                    true,
                                );
                                return Ok(res[0]);
                            }
                            _ => {}
                        }
                    }
                }

                // 0c) STATIC CLASS METHODS â€” check BEFORE anything that would lower `recv`
                if let ExprKind::Ident(cn) = recv.kind() {
                    if let Some(&fid) = lowering_ctx.funcs.get(&format!("__static_{}_{}", cn, name))
                    {
                        #[cfg(debug_assertions)]
                        {
                            eprintln!("[static] candidate {}.{}", cn, name);
                        }

                        let mut argv = Vec::with_capacity(args.len());
                        for a in args {
                            argv.push(lower_expr_free(
                                b,
                                locals,
                                fields,
                                next_field,
                                a,
                                lowering_ctx,
                            )?);
                        }
                        let (_nid, res) = b.push_node(
                            Inst::CallDirect {
                                conv: crate::wir::CallConv::Fast,
                                callee: fid,
                                args: argv,
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                        return Ok(res[0]);
                    }
                }

                let is_static_call = if let ExprKind::Ident(id_name) = recv.kind() {
                    lowering_ctx.is_class_ident(id_name)
                } else {
                    false
                };

                if is_static_call {
                    // Static call: `Counter.times3(7)` -> args are just `[7]`
                    let fun_v =
                        lower_expr_free(b, locals, fields, next_field, callee, lowering_ctx)?;
                    let mut argv = Vec::with_capacity(args.len());
                    for a in args {
                        argv.push(lower_expr_free(
                            b,
                            locals,
                            fields,
                            next_field,
                            a,
                            lowering_ctx,
                        )?);
                    }
                    let (_nid, res) = b.push_node(
                        Inst::CallClosure {
                            conv: crate::wir::CallConv::Fast,
                            fun: fun_v,
                            args: argv,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }

                // Instance call: evaluate the receiver exactly once, then the arguments.
                let recv_v = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
                let mut arg_vals = Vec::with_capacity(args.len());
                for a in args {
                    arg_vals.push(lower_expr_free(
                        b,
                        locals,
                        fields,
                        next_field,
                        a,
                        lowering_ctx,
                    )?);
                }

                // 0d/0e) Builtin string/array methods. Objects (class instances, object
                // literals, proxies) may define methods with the same names, so those
                // receivers are dispatched dynamically at runtime.
                if builtin_method_arity_ok(name, args.len()) {
                    let (join, out) = begin_builtin_method_dispatch(
                        b, recv_v, name, &arg_vals, fields, next_field,
                    );
                    if matches!(name.as_str(), "indexOf" | "includes") {
                        let (_, is_array) = b.push_node(
                            Inst::CallNative {
                                name: "wir_is_array".into(), args: vec![recv_v],
                                pure: true, can_throw: false,
                            }, Some(Type::Bool), 1, false,
                        );
                        let array_block = b.block();
                        let string_block = b.block();
                        b.branch(is_array[0], array_block, string_block);
                        b.position_at(array_block);
                        let from = arg_vals.get(1).copied().unwrap_or_else(|| b.const_i32(0));
                        let (_, result) = b.push_node(
                            Inst::CallNative {
                                name: if name == "includes" { "wir_array_includes" } else { "wir_array_index_of" }.into(),
                                args: vec![recv_v, arg_vals[0], from], pure: false, can_throw: false,
                            }, Some(if name == "includes" { Type::Bool } else { Type::Int32 }), 1, true,
                        );
                        b.jump(join, &[result[0]]);
                        b.position_at(string_block);
                    }
                    let builtin = match lower_string_method_call(
                        b,
                        locals,
                        fields,
                        next_field,
                        recv_v,
                        name,
                        &arg_vals,
                        lowering_ctx,
                    )? {
                        Some(v) => v,
                        None => lower_array_method_call(
                            b,
                            locals,
                            fields,
                            next_field,
                            recv_v,
                            name,
                            &arg_vals,
                            lowering_ctx,
                        )?
                        .ok_or(LowerError::NotLowerable("builtin method"))?,
                    };
                    b.jump(join, &[builtin]);
                    b.position_at(join);
                    return Ok(out);
                }

                // 0e) Generic property call with `this`.
                return Ok(lower_dynamic_method_call(
                    b, recv_v, name, arg_vals, fields, next_field,
                ));
            }

            // 0f) Bracket-call: o["m"](...)
            // - If recv is a class ident and key is a string matching a static, direct-call it.
            // - Else, if key is a string at runtime, inject `this`.
            // - Otherwise treat as array[index] function call (no `this`).
            if let ExprKind::Index { recv, index } = callee.kind() {
                // Static: Class["M"](...)
                if let (ExprKind::Ident(cn), ExprKind::Str(m)) = (recv.kind(), index.kind()) {
                    if let Some(&fid) = lowering_ctx.funcs.get(&format!("__static_{}_{}", cn, m)) {
                        let mut argv = Vec::with_capacity(args.len());
                        for a in args {
                            argv.push(lower_expr_free(
                                b,
                                locals,
                                fields,
                                next_field,
                                a,
                                lowering_ctx,
                            )?);
                        }
                        let (_nid, res) = b.push_node(
                            Inst::CallDirect {
                                conv: crate::wir::CallConv::Fast,
                                callee: fid,
                                args: argv,
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                        return Ok(res[0]);
                    }
                }

                // General bracket-call
                let obj = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
                let idxv = lower_expr_free(b, locals, fields, next_field, index, lowering_ctx)?;
                let mut argvals = Vec::with_capacity(args.len());
                for a in args {
                    argvals.push(lower_expr_free(
                        b,
                        locals,
                        fields,
                        next_field,
                        a,
                        lowering_ctx,
                    )?);
                }

                // Is the key a string? -> method call (inject `this`)
                let (_nid_is, is_str) = b.push_node(
                    Inst::CallNative {
                        name: "wir_is_str".into(),
                        args: vec![idxv],
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::Bool),
                    1,
                    true,
                );

                let str_b = b.block();
                let arr_b = b.block();
                let cont = b.block();
                let out = b.add_block_param(cont, Type::Int32);

                b.branch(is_str[0], str_b, arr_b);

                // String-key path: fun = obj[key]; CallClosure(fun, this, args...)
                b.position_at(str_b);
                let (_nid_gs, sv) = b.push_node(
                    Inst::CallNative {
                        name: "wir_obj_get_str".into(),
                        args: vec![obj, idxv],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                require_callable(b, sv[0], "TypeError: indexed value is not callable");
                let mut with_this = Vec::with_capacity(1 + argvals.len());
                with_this.push(obj);
                with_this.extend_from_slice(&argvals);
                let (_nid_call_s, sret) = b.push_node(
                    Inst::CallClosure {
                        conv: crate::wir::CallConv::Fast,
                        fun: sv[0],
                        args: with_this,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
                b.jump(cont, &[sret[0]]);

                // Non-string index: fun = arr[index]; CallClosure(fun, args...)
                b.position_at(arr_b);
                let (_nid_ga, av) = b.push_node(
                    Inst::CallNative {
                        name: "wir_array_get".into(),
                        args: vec![obj, idxv],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                require_callable(b, av[0], "TypeError: indexed value is not callable");
                let (_nid_call_a, aret) = b.push_node(
                    Inst::CallClosure {
                        conv: crate::wir::CallConv::Fast,
                        fun: av[0],
                        args: argvals,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
                b.jump(cont, &[aret[0]]);

                b.position_at(cont);
                return Ok(out);
            }

            // --- Bare identifier callee & other cases ---
            if let ExprKind::Ident(name) = callee.kind() {
                // Timers
                if name == "setTimeout" {
                    if args.len() != 2 {
                        return Err(LowerError::NotLowerable("setTimeout(fn, ms)"));
                    }
                    let fun =
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
                    let ms =
                        lower_expr_free(b, locals, fields, next_field, &args[1], lowering_ctx)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_set_timeout".into(),
                            args: vec![fun, ms],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "setInterval" {
                    if args.len() != 2 {
                        return Err(LowerError::NotLowerable("setInterval(fn, ms)"));
                    }
                    let fun =
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
                    let ms =
                        lower_expr_free(b, locals, fields, next_field, &args[1], lowering_ctx)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_set_interval".into(),
                            args: vec![fun, ms],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "clearTimeout" {
                    if args.len() != 1 {
                        return Err(LowerError::NotLowerable("clearTimeout(id)"));
                    }
                    let id =
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_clear_timeout".into(),
                            args: vec![id],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "clearInterval" {
                    if args.len() != 1 {
                        return Err(LowerError::NotLowerable("clearInterval(id)"));
                    }
                    let id =
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_clear_interval".into(),
                            args: vec![id],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }

                // Builtins: Array/Promise/Deferred
                if name == "Array" {
                    if args.len() != 1 {
                        return Err(LowerError::NotLowerable("Array(len) expects 1 arg"));
                    }
                    let len =
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_array_new".into(),
                            args: vec![len],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Array(Box::new(None))),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "Promise" {
                    if args.len() != 1 {
                        return Err(LowerError::NotLowerable("Promise(executor) expects 1 arg"));
                    }
                    let exec =
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_promise_new".into(),
                            args: vec![exec],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "Deferred" {
                    if !args.is_empty() {
                        return Err(LowerError::NotLowerable("Deferred() expects 0 args"));
                    }
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_deferred_new".into(),
                            args: vec![],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }

                // HTTP helpers (global)
                if name == "get" {
                    if args.len() != 1 {
                        return Err(LowerError::NotLowerable("get(url) expects 1 arg"));
                    }
                    let url =
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_http_get".into(),
                            args: vec![url],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "getJSON" {
                    if args.len() != 1 {
                        return Err(LowerError::NotLowerable("getJSON(url) expects 1 arg"));
                    }
                    let url =
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_http_get_json".into(),
                            args: vec![url],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "postJSON" {
                    if !(args.len() == 2 || args.len() == 3) {
                        return Err(LowerError::NotLowerable("postJSON(url, body, headers?)"));
                    }
                    let url =
                        lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
                    let body =
                        lower_expr_free(b, locals, fields, next_field, &args[1], lowering_ctx)?;
                    let (_nid, nul) =
                        b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                    let headers = if args.len() == 3 {
                        lower_expr_free(b, locals, fields, next_field, &args[2], lowering_ctx)?
                    } else {
                        nul[0]
                    };
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_http_post_json".into(),
                            args: vec![url, body, headers],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "json" {
                    // json(body) OR json(status, body[, headers])
                    let (_nid_null, nul) =
                        b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                    let (status_v, body_v, headers_v) = match args.len() {
                        1 => {
                            let body = lower_expr_free(
                                b,
                                locals,
                                fields,
                                next_field,
                                &args[0],
                                lowering_ctx,
                            )?;
                            let status = b.const_i32(200);
                            (status, body, nul[0])
                        }
                        2 => {
                            let status = lower_expr_free(
                                b,
                                locals,
                                fields,
                                next_field,
                                &args[0],
                                lowering_ctx,
                            )?;
                            let body = lower_expr_free(
                                b,
                                locals,
                                fields,
                                next_field,
                                &args[1],
                                lowering_ctx,
                            )?;
                            (status, body, nul[0])
                        }
                        3 => {
                            let status = lower_expr_free(
                                b,
                                locals,
                                fields,
                                next_field,
                                &args[0],
                                lowering_ctx,
                            )?;
                            let body = lower_expr_free(
                                b,
                                locals,
                                fields,
                                next_field,
                                &args[1],
                                lowering_ctx,
                            )?;
                            let headers = lower_expr_free(
                                b,
                                locals,
                                fields,
                                next_field,
                                &args[2],
                                lowering_ctx,
                            )?;
                            (status, body, headers)
                        }
                        _ => {
                            return Err(LowerError::NotLowerable(
                                "json expects (body) or (status, body[, headers])",
                            ));
                        }
                    };
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_http_send_json".into(),
                            args: vec![status_v, body_v, headers_v],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }

                // print(value)
                if name == "print" {
                    if args.len() != 1 {
                        return Err(LowerError::NotLowerable("print(value) expects 1 arg"));
                    }

                    // Fast string-literal path
                    // Fast path for string literals: avoid allocation/inspection.
                    if matches!(args[0].kind(), ExprKind::Str(_)) {
                        let v =
                            lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
                        let (_nid, res) = b.push_node(
                            Inst::CallNative {
                                name: "wir_print_str".into(),
                                args: vec![v],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                        return Ok(res[0]);
                    }

                    // General case: let the runtime pretty-print *any* value.
                    let v = lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_print_any".into(),
                            args: vec![v],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }

                // Direct call to a known (hoisted/declared) function
                if let Some(&fid) = lowering_ctx.funcs.get(name) {
                    let mut argv = Vec::with_capacity(args.len());
                    for a in args {
                        argv.push(lower_expr_free(
                            b,
                            locals,
                            fields,
                            next_field,
                            a,
                            lowering_ctx,
                        )?);
                    }
                    let (_nid, res) = b.push_node(
                        Inst::CallDirect {
                            conv: crate::wir::CallConv::Fast,
                            callee: fid,
                            args: argv,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
            }

            // --- 2) Fallback: general function value + CallClosure ---
            let funv = lower_expr_free(b, locals, fields, next_field, callee, lowering_ctx)?;
            let mut argv = Vec::with_capacity(args.len());
            for a in args {
                argv.push(lower_expr_free(
                    b,
                    locals,
                    fields,
                    next_field,
                    a,
                    lowering_ctx,
                )?);
            }
            let (_nid, res) = b.push_node(
                Inst::CallClosure {
                    conv: crate::wir::CallConv::Fast,
                    fun: funv,
                    args: argv,
                },
                Some(Type::Int32),
                1,
                true,
            );
            Ok(res[0])
        }

        ExprKind::This => {
            if let Some(&v) = locals.get("this") {
                Ok(v)
            } else {
                Err(LowerError::UnknownVar("this".into()))
            }
        }

        ExprKind::SuperProp(_) => {
            return Err(LowerError::NotLowerable(
                "`super.prop` is only valid when called: use `super.prop(...)`",
            ));
        }
        ExprKind::SuperCall(_) => {
            return Err(LowerError::NotLowerable(
                "`super(...)` is only valid in a derived constructor",
            ));
        }

        ExprKind::New { class, args } => {
            #[cfg(debug_assertions)]
            {
                eprintln!(
                    "[new] trying to resolve class {:?} via import/export/namespace",
                    class
                );
            }

            // `new ns.Class(args)`: the namespace member is a class object exposing `new`.
            if let Some((ns, member)) = class.split_once('.') {
                let recv = expr_with_meta(e, ExprKind::Ident(ns.to_string()));
                let class_ref = expr_with_meta(e, ExprKind::GetProp {
                    recv: SmallBox::new(recv),
                    name: member.to_string(),
                });
                let clazz =
                    lower_expr_free(b, locals, fields, next_field, &class_ref, lowering_ctx)?;
                let key = b.const_str("new");
                let (_ng, fun) = b.push_node(
                    Inst::CallNative {
                        name: "wir_obj_get_str".into(),
                        args: vec![clazz, key],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                require_callable(b, fun[0], &format!("TypeError: {class} is not a constructor"));
                let mut argv = Vec::with_capacity(args.len());
                for a in args {
                    argv.push(lower_expr_free(b, locals, fields, next_field, a, lowering_ctx)?);
                }
                let (_nid, res) = b.push_node(
                    Inst::CallClosure {
                        conv: crate::wir::CallConv::Fast,
                        fun: fun[0],
                        args: argv,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
                return Ok(res[0]);
            }

            // Handle `new Map()` and `new Set()` as special builtins
            let native_ctor = match class.as_str() {
                "Map" => Some("wir_map_new"),
                "Set" => Some("wir_set_new"),
                _ => None,
            };

            if let Some(ctor_name) = native_ctor {
                // For now, we don't support initial values like `new Map([...])`.
                if !args.is_empty() {
                    return Err(LowerError::NotLowerable(
                        "Map/Set constructors with arguments not yet supported",
                    ));
                }

                let (_nid, res) = b.push_node(
                    Inst::CallNative {
                        name: ctor_name.into(),
                        args: vec![],
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::AnyRef),
                    1,
                    true,
                );
                return Ok(res[0]);
            }

            // 1) ruta local
            let fname = format!("__class_new_{}", class);
            if let Some(&fid) = lowering_ctx.funcs.get(&fname) {
                let mut argv = Vec::with_capacity(args.len());
                for a in args {
                    argv.push(lower_expr_free(
                        b,
                        locals,
                        fields,
                        next_field,
                        a,
                        lowering_ctx,
                    )?);
                }
                let (_nid, res) = b.push_node(
                    Inst::CallDirect {
                        conv: crate::wir::CallConv::Fast,
                        callee: fid,
                        args: argv,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
                return Ok(res[0]);
            }

            #[cfg(debug_assertions)]
            {
                eprintln!(
                    "lower_expr_free() ExprKind::Call(...) ExprKind::New({})",
                    class
                );
                eprintln!(
                    "[links] exports        : {:?}",
                    lowering_ctx
                        .links
                        .export_bindings
                        .keys()
                        .collect::<Vec<_>>()
                );
                eprintln!(
                    "[links] imports        : {:?}",
                    lowering_ctx
                        .links
                        .import_bindings
                        .keys()
                        .collect::<Vec<_>>()
                );
                eprintln!(
                    "[links] namespace_imps : {:?}",
                    lowering_ctx
                        .links
                        .namespace_imports
                        .keys()
                        .collect::<Vec<_>>()
                );
                eprintln!(
                    "[links] namespace_cells: {:?}",
                    lowering_ctx.links.namespace_cells
                );
            }

            // 2) ruta IMPORTADA/EXPORTADA: el identificador 'class' es un binding a un "class object"
            if let Some(&bid) = lowering_ctx
                .links
                .import_bindings
                .get(class)
                .or_else(|| lowering_ctx.links.export_bindings.get(class))
                .or_else(|| lowering_ctx.links.namespace_cells.get(class))
            {
                #[cfg(debug_assertions)]
                {
                    eprintln!(
                        "[new] class {:?} -> binding {:?}; invoking 'new'",
                        class, bid
                    );
                }

                let clazz = b.load_binding(bid, Some(Type::AnyRef));
                // convention: el "class object" expone 'new' que apunta al allocator
                let (_nk, k) = b.push_node(
                    Inst::Const(Constant::Str("new".into())),
                    Some(Type::Str),
                    1,
                    false,
                );
                let (_ng, fun) = b.push_node(
                    Inst::CallNative {
                        name: "wir_obj_get_str".into(),
                        args: vec![clazz, k[0]],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                let mut argv = Vec::with_capacity(args.len());
                for a in args {
                    argv.push(lower_expr_free(
                        b,
                        locals,
                        fields,
                        next_field,
                        a,
                        lowering_ctx,
                    )?);
                }
                let (_nid, res) = b.push_node(
                    Inst::CallClosure {
                        conv: crate::wir::CallConv::Fast,
                        fun: fun[0],
                        args: argv,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
                return Ok(res[0]);
            }

            return Err(LowerError::UnknownFunc(fname));
        }

        ExprKind::Index { recv, index } => {
            // Path A: The index is a compile-time string literal, e.g., obj["key"].
            // This is the most common case for object property access and can be optimized.
            if let ExprKind::Str(s) = index.kind() {
                // Your existing, correct logic for this case is perfect.
                let obj = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
                let value = lower_general_getprop(b, obj, s, fields, next_field);
                return Ok(value);
            }

            // Path B: The index is a dynamic expression, e.g., obj[i] or obj[key_b].
            // We need to generate code that handles all possibilities at runtime.
            let recv_v = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
            let idx_v = lower_expr_free(b, locals, fields, next_field, index, lowering_ctx)?;

            // Runtime Decision Point 1: Is the INDEX a string?
            let (_nid_is_idx_str, is_idx_string_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_is_str".into(),
                    args: vec![idx_v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Bool),
                1,
                true,
            );
            let is_idx_string = is_idx_string_res[0];

            let obj_key_path = b.block(); // Path for obj[string_key]
            let numeric_key_path = b.block(); // Path for string[i] or array[i]
            let cont = b.block();
            let result_phi = b.add_block_param(cont, Type::Int32);

            b.branch(is_idx_string, obj_key_path, numeric_key_path);

            // --- Logic for when the index is a string ---
            b.position_at(obj_key_path);
            // This is a dynamic property access on an object.
            let (_nid_get, obj_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_obj_get_str".into(),
                    args: vec![recv_v, idx_v],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            b.jump(cont, &[obj_res[0]]);

            // --- Logic for when the index is NOT a string (i.e., numeric) ---
            b.position_at(numeric_key_path);
            // Runtime Decision Point 2: Is the RECEIVER a string?
            let (_nid_is_recv_str, is_recv_string_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_is_str".into(),
                    args: vec![recv_v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Bool),
                1,
                true,
            );
            let is_recv_string = is_recv_string_res[0];

            let string_recv_path = b.block(); // Path for "string"[i]
            let array_recv_path = b.block(); // Path for array[i]

            // We need a nested join block here.
            let numeric_cont = b.block();
            let numeric_phi = b.add_block_param(numeric_cont, Type::Int32);

            b.branch(is_recv_string, string_recv_path, array_recv_path);

            b.position_at(string_recv_path);
            let (_nid_char, char_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_string_get_char".into(),
                    args: vec![recv_v, idx_v],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            b.jump(numeric_cont, &[char_res[0]]);

            b.position_at(array_recv_path);
            let (_nid_object, object) = b.push_node(
                Inst::CallNative {
                    name: "wir_is_obj".into(),
                    args: vec![recv_v],
                    pure: true,
                    can_throw: false,
                },
                Some(Type::Bool),
                1,
                false,
            );
            let object_recv_path = b.block();
            let indexed_array_path = b.block();
            b.branch(object[0], object_recv_path, indexed_array_path);

            // Numeric enum reverse mappings are ordinary string-keyed properties.
            b.position_at(object_recv_path);
            let empty = b.const_str("");
            let (_nid_key, key) = b.push_node(
                Inst::CallNative {
                    name: "wir_string_concat_coerce".into(),
                    args: vec![empty, idx_v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Str),
                1,
                true,
            );
            let (_nid_value, value) = b.push_node(
                Inst::CallNative {
                    name: "wir_obj_get_str".into(),
                    args: vec![recv_v, key[0]],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            b.jump(numeric_cont, &[value[0]]);

            b.position_at(indexed_array_path);
            let (_nid_arr, arr_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_get".into(),
                    args: vec![recv_v, idx_v],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            b.jump(numeric_cont, &[arr_res[0]]);

            b.position_at(numeric_cont);
            b.jump(cont, &[numeric_phi]); // Forward the result to the final join block.

            // Final join block for all paths.
            b.position_at(cont);
            Ok(result_phi)
        }

        ExprKind::ArrayLit(elems) => {
            // Allocate array
            let len_v = b.const_i32(elems.len() as i32);
            let (_nid_new, new_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_new".into(),
                    args: vec![len_v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Array(Box::new(None))),
                1,
                true,
            );
            let arr_v = new_res[0];
            // Back-compat alias in case older code still uses `arr`
            let arr = arr_v;

            // Fill it
            for (i, el) in elems.iter().enumerate() {
                let v = lower_expr_free(b, locals, fields, next_field, el, lowering_ctx)?;
                let idx = b.const_i32(i as i32);
                let _ = b.push_node(
                    Inst::CallNative {
                        name: "wir_array_set".into(),
                        args: vec![arr, idx, v],
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
            }

            Ok(arr)
        }

        // Closure creation from hoisted lambda
        ExprKind::FnRef { name } => {
            let fid = *lowering_ctx
                .funcs
                .get(name)
                .ok_or_else(|| LowerError::UnknownFunc(name.clone()))?;
            let caps = lowering_ctx
                .lam_captures
                .get(name)
                .cloned()
                .unwrap_or_default();

            // For each capture, if it is not boxed yet in this scope, box it now:
            //   box = Array(1); box[0] = current_value; rebind local to box; mark boxed.
            for cap in &caps {
                if !box_local(b, locals, cap) {
                    return Err(LowerError::UnknownVar(cap.into()));
                }
            }

            // Build env array out of *boxes* (so inner lambda can mutate them)
            let len = b.const_i32(caps.len() as i32);
            let (_nid, env_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_new".into(),
                    args: vec![len],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Array(Box::new(None))),
                1,
                true,
            );
            let env = env_res[0];
            for (i, cap) in caps.iter().enumerate() {
                let idx = b.const_i32(i as i32);
                let box_arr = *locals.get(cap).expect("boxed local present");
                let _ = b.push_node(
                    Inst::CallNative {
                        name: "wir_array_set".into(),
                        args: vec![env, idx, box_arr],
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
            }

            let (_nid, clos) = b.push_node(
                Inst::MakeClosure { callee: fid, env },
                Some(Type::Closure(None)),
                1,
                false,
            );
            Ok(clos[0])
        }

        ExprKind::ObjLit(items) => {
            // obj = wir_obj_new()
            let (_nid, obj_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_obj_new".into(),
                    args: vec![],
                    pure: false,
                    can_throw: false,
                },
                None, // dynamic object
                1,
                true,
            );
            let obj = obj_res[0];

            for item in items {
                match item {
                    ObjItem::Prop(key, val_e) => {
                        let v =
                            lower_expr_free(b, locals, fields, next_field, val_e, lowering_ctx)?;

                        // First, get the property name as a string, regardless of how it was defined.
                        let name_str = match key {
                            PropKey::Ident(name) => name.clone(),
                            PropKey::Str(s) => s.clone(),
                        };

                        // --- CORRECT TWO-WAY STORE ---
                        // 1. Store in the "fast path" using its FieldId.
                        let field = intern_field_local(fields, next_field, &name_str);
                        let _ = b.push_node(
                            Inst::StoreField {
                                obj,
                                field,
                                val: v,
                                expected: None,
                            },
                            Some(Type::Top),
                            1, // StoreField is effectful and produces a token
                            true,
                        );

                        // 2. Mirror the store in the "dynamic path" using its string key.
                        let (_nid_sconst, ks) = b.push_node(
                            Inst::Const(Constant::Str(name_str)),
                            Some(Type::Str),
                            1,
                            false,
                        );
                        let _ = b.push_node(
                            Inst::CallNative {
                                name: "wir_obj_set_str".into(),
                                args: vec![obj, ks[0], v],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Int32), // Returns a status code
                            1,
                            true,
                        );
                    }
                    ObjItem::Spread(expr) => {
                        // Your spread logic is already correct.
                        let spread_obj =
                            lower_expr_free(b, locals, fields, next_field, expr, lowering_ctx)?;
                        let _ = b.push_node(
                            Inst::CallNative {
                                name: "wir_obj_assign".into(),
                                args: vec![obj, spread_obj],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                    }
                }
            }

            Ok(obj)
        }

        ExprKind::DeleteProp { obj, key } => {
            let o = lower_expr_free(b, locals, fields, next_field, obj, lowering_ctx)?;

            match key {
                // delete o.a  â€” delete both field and string
                PropKey::Ident(name) => {
                    let field = intern_field_local(fields, next_field, name);
                    let fid_smi = b.const_i32(field.0 as i32);

                    let (_nid_sc, ks) = b.push_node(
                        Inst::Const(Constant::Str(name.clone())),
                        Some(Type::Str),
                        1,
                        false,
                    );
                    let _ = b.push_node(
                        Inst::CallNative {
                            name: "wir_field_register_name".into(),
                            args: vec![fid_smi, ks[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );

                    // del fast field
                    let (_nid_f, _rf) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_del_field".into(),
                            args: vec![o, fid_smi],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    // del string key (mirror)
                    let (_nid_s, rs) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_del_str".into(),
                            args: vec![o, ks[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    Ok(rs[0]) // return last result (truthy if deleted)
                }

                // delete o["a"] â€” delete both string and field
                PropKey::Str(s) => {
                    // del string key
                    let (_nid_sc, ks) = b.push_node(
                        Inst::Const(Constant::Str(s.clone())),
                        Some(Type::Str),
                        1,
                        false,
                    );
                    let (_nid_s, rs) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_del_str".into(),
                            args: vec![o, ks[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    // del fast field mirror (safe even if not an identifier originally)
                    let field = intern_field_local(fields, next_field, s);
                    let fid_smi = b.const_i32(field.0 as i32);
                    let (_nid_f, _rf) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_del_field".into(),
                            args: vec![o, fid_smi],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    Ok(rs[0])
                }
            }
        }

        ExprKind::In { key, obj } => {
            let o = lower_expr_free(b, locals, fields, next_field, obj, lowering_ctx)?;

            // Dynamic key (`k in o` with a bound variable `k`, or any other expression).
            let dynamic_key = match key.kind() {
                ExprKind::Str(_) => None,
                ExprKind::Ident(_) => {
                    match lower_expr_free(b, locals, fields, next_field, key, lowering_ctx) {
                        Ok(kv) => Some(kv),
                        // Unbound identifier: legacy `name in o` meaning the literal name.
                        Err(LowerError::UnknownVar(_) | LowerError::Undefined { .. }) => None,
                        Err(e) => return Err(e),
                    }
                }
                _ => Some(lower_expr_free(b, locals, fields, next_field, key, lowering_ctx)?),
            };
            if let Some(kv) = dynamic_key {
                let (_nid_s, hs) = b.push_node(
                    Inst::CallNative {
                        name: "wir_obj_has_str".into(),
                        args: vec![o, kv],
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::Bool),
                    1,
                    true,
                );
                return Ok(hs[0]);
            }

            match key.kind() {
                // identifier key:  a in o
                ExprKind::Ident(name) => {
                    let field = intern_field_local(fields, next_field, name);
                    let fid_smi = b.const_i32(field.0 as i32);

                    let (_nid_sc, ks) = b.push_node(
                        Inst::Const(Constant::Str(name.clone())),
                        Some(Type::Str),
                        1,
                        false,
                    );
                    let _ = b.push_node(
                        Inst::CallNative {
                            name: "wir_field_register_name".into(),
                            args: vec![fid_smi, ks[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );

                    // fast-slot check
                    let (_nid_f, hf) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_has_field".into(),
                            args: vec![o, fid_smi],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    // string-table check
                    let (_nid_s, hs) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_has_str".into(),
                            args: vec![o, ks[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    Ok(build_bool_or(b, hf[0], hs[0]))
                }

                // string-literal key:  "a" in o
                ExprKind::Str(s) => {
                    let field = intern_field_local(fields, next_field, s);
                    let fid_smi = b.const_i32(field.0 as i32);

                    let (_nid_f, hf) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_has_field".into(),
                            args: vec![o, fid_smi],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    let (_nid_sc, ks) = b.push_node(
                        Inst::Const(Constant::Str(s.clone())),
                        Some(Type::Str),
                        1,
                        false,
                    );
                    let (_nid_s, hs) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_has_str".into(),
                            args: vec![o, ks[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    Ok(build_bool_or(b, hf[0], hs[0]))
                }

                _ => unreachable!(),
            }
        }

        ExprKind::CreateBuiltin { kind, args } => match kind {
            crate::front::BuiltinType::Map => {
                if !args.is_empty() {
                    return Err(LowerError::NotLowerable(
                        "Map constructors do not accept arguments",
                    ));
                }
                let (_nid, res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_map_new".into(),
                        args: vec![],
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::AnyRef),
                    1,
                    true,
                );
                Ok(res[0])
            }
            crate::front::BuiltinType::Set => {
                if !args.is_empty() {
                    return Err(LowerError::NotLowerable(
                        "Set constructors do not accept arguments",
                    ));
                }
                let (_nid, res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_set_new".into(),
                        args: vec![],
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::AnyRef),
                    1,
                    true,
                );
                Ok(res[0])
            }
            crate::front::BuiltinType::Proxy => {
                if args.len() != 2 {
                    return Err(LowerError::NotLowerable(
                        "Proxy constructor expects exactly 2 arguments",
                    ));
                }
                let target =
                    lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
                let handler =
                    lower_expr_free(b, locals, fields, next_field, &args[1], lowering_ctx)?;
                let (_nid, res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_proxy_new".into(),
                        args: vec![target, handler],
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::AnyRef),
                    1,
                    true,
                );
                Ok(res[0])
            }
        },

        ExprKind::CallBuiltinMapMethod { recv, method, args } => {
            let (native_name, method_name, is_chainable) = match method {
                crate::front::BuiltinMapMethod::Get => ("wir_map_get", "get", false),
                crate::front::BuiltinMapMethod::Set => ("wir_map_set", "set", true),
                crate::front::BuiltinMapMethod::Has => ("wir_map_has", "has", false),
                crate::front::BuiltinMapMethod::Delete => ("wir_map_delete", "delete", false),
                crate::front::BuiltinMapMethod::Clear => ("wir_map_clear", "clear", false),
                crate::front::BuiltinMapMethod::Keys => ("wir_builtin_keys", "keys", false),
                crate::front::BuiltinMapMethod::Values => ("wir_builtin_values", "values", false),
                crate::front::BuiltinMapMethod::Entries => {
                    ("wir_builtin_entries", "entries", false)
                }
            };
            if namespace_exports(recv, method_name, locals, lowering_ctx) {
                let call = namespace_member_call(e, recv, method_name, args.clone());
                return lower_expr_free(b, locals, fields, next_field, &call, lowering_ctx);
            }
            let recv_v = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;

            let mut arg_vals = Vec::with_capacity(args.len());
            for arg_expr in args {
                arg_vals.push(lower_expr_free(
                    b,
                    locals,
                    fields,
                    next_field,
                    arg_expr,
                    lowering_ctx,
                )?);
            }
            Ok(lower_collection_method_call(
                b,
                recv_v,
                method_name,
                native_name,
                is_chainable,
                arg_vals,
                fields,
                next_field,
            ))
        }

        ExprKind::CallBuiltinSetMethod { recv, method, args } => {
            let (native_name, method_name, is_chainable) = match method {
                crate::front::BuiltinSetMethod::Add => ("wir_set_add", "add", true),
                crate::front::BuiltinSetMethod::Has => ("wir_set_has", "has", false),
                crate::front::BuiltinSetMethod::Delete => ("wir_set_delete", "delete", false),
                crate::front::BuiltinSetMethod::Clear => ("wir_set_clear", "clear", false),
                crate::front::BuiltinSetMethod::Values => ("wir_builtin_values", "values", false),
            };
            if namespace_exports(recv, method_name, locals, lowering_ctx) {
                let call = namespace_member_call(e, recv, method_name, args.clone());
                return lower_expr_free(b, locals, fields, next_field, &call, lowering_ctx);
            }
            let recv_v = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;

            let mut arg_vals = Vec::with_capacity(args.len());
            for arg_expr in args {
                arg_vals.push(lower_expr_free(
                    b,
                    locals,
                    fields,
                    next_field,
                    arg_expr,
                    lowering_ctx,
                )?);
            }
            Ok(lower_collection_method_call(
                b,
                recv_v,
                method_name,
                native_name,
                is_chainable,
                arg_vals,
                fields,
                next_field,
            ))
        }

        ExprKind::CallBuiltinCommonMethod { recv, method } => {
            let (native_name, method_name) = match method {
                crate::front::BuiltinCommonMethod::Keys => ("wir_builtin_keys", "keys"),
                crate::front::BuiltinCommonMethod::Values => ("wir_builtin_values", "values"),
                crate::front::BuiltinCommonMethod::Entries => ("wir_builtin_entries", "entries"),
            };
            if namespace_exports(recv, method_name, locals, lowering_ctx) {
                let call = namespace_member_call(e, recv, method_name, Vec::new());
                return lower_expr_free(b, locals, fields, next_field, &call, lowering_ctx);
            }
            let recv_v = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
            Ok(lower_collection_method_call(
                b,
                recv_v,
                method_name,
                native_name,
                false,
                Vec::new(),
                fields,
                next_field,
            ))
        }

        ExprKind::GetBuiltinSize(recv) => {
            let recv_v = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
            let (_nid_object, object) = b.push_node(
                Inst::CallNative {
                    name: "wir_is_obj".into(),
                    args: vec![recv_v],
                    pure: true,
                    can_throw: false,
                },
                Some(Type::Bool),
                1,
                false,
            );
            let check_property = b.block();
            let property = b.block();
            let builtin = b.block();
            let done = b.block();
            let result = b.add_block_param(done, Type::Top);
            b.branch(object[0], check_property, builtin);

            b.position_at(check_property);
            let key = b.const_str("size");
            let (_nid_has, has) = b.push_node(
                Inst::CallNative {
                    name: "wir_obj_has_str".into(),
                    args: vec![recv_v, key],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Bool),
                1,
                true,
            );
            b.branch(has[0], property, builtin);
            b.position_at(property);
            let value = lower_general_getprop(b, recv_v, "size", fields, next_field);
            b.jump(done, &[value]);

            b.position_at(builtin);
            let (_nid, res) = b.push_node(
                Inst::CallNative {
                    name: "wir_builtin_size".into(),
                    args: vec![recv_v],
                    pure: true,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                false,
            );
            b.jump(done, &[res[0]]);
            b.position_at(done);
            Ok(result)
        }

        ExprKind::Typed { op, args } => {
            lower_typed(b, locals, fields, next_field, op, args, lowering_ctx)
        }

        _ => Err(LowerError::NotLowerable("expression type not supported")),
    }
}

fn typed_native(b: &mut Builder<'_>, name: &str, args: Vec<ValueId>, ty: Type, pure: bool) -> ValueId {
    let (_nid, res) = b.push_node(
        Inst::CallNative {
            name: name.into(),
            args,
            pure,
            can_throw: false,
        },
        Some(ty),
        1,
        !pure,
    );
    res[0]
}

fn const_bool(b: &mut Builder<'_>, value: bool) -> ValueId {
    let (_nid, res) = b.push_node(Inst::Const(Constant::Bool(value)), Some(Type::Bool), 1, false);
    res[0]
}

/// Selects between two boolean constants; keeps tagged booleans canonical.
fn bool_select(b: &mut Builder<'_>, cond: ValueId, if_true: bool) -> ValueId {
    let yes = b.block();
    let no = b.block();
    let done = b.block();
    let result = b.add_block_param(done, Type::Bool);
    b.branch(cond, yes, no);
    b.position_at(yes);
    let value = const_bool(b, if_true);
    b.jump(done, &[value]);
    b.position_at(no);
    let value = const_bool(b, !if_true);
    b.jump(done, &[value]);
    b.position_at(done);
    result
}

/// Compiled runtime test for a type-checker boundary guard.
fn lower_rt_check(
    b: &mut Builder<'_>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    value: ValueId,
    check: &RtCheck,
) -> ValueId {
    let predicate = match check {
        RtCheck::Number => "wir_is_number",
        RtCheck::Str => "wir_is_str",
        RtCheck::Bool => "wir_is_bool",
        RtCheck::Null => "wir_is_null",
        RtCheck::Array => "wir_is_array",
        RtCheck::Function => "wir_is_closure",
        RtCheck::Map => "wir_is_map",
        RtCheck::Set => "wir_is_set",
        RtCheck::AnyOf(checks) => {
            let mut result = None;
            for check in checks {
                let next = lower_rt_check(b, fields, next_field, value, check);
                result = Some(match result {
                    Some(previous) => build_bool_or(b, previous, next),
                    None => next,
                });
            }
            return result.unwrap_or_else(|| const_bool(b, false));
        }
        RtCheck::Shape(names) => {
            let is_object = typed_native(b, "wir_is_obj", vec![value], Type::Bool, true);
            if names.is_empty() {
                return is_object;
            }
            let done = b.block();
            let result = b.add_block_param(done, Type::Bool);
            let missing = b.block();
            let mut next = b.block();
            b.branch(is_object, next, missing);
            for name in names {
                b.position_at(next);
                // Probe by name: function-local field ids are not globally unique.
                let key = b.const_str(name);
                let has = typed_native(b, "wir_obj_has_str", vec![value, key], Type::Bool, false);
                next = b.block();
                b.branch(has, next, missing);
            }
            b.position_at(next);
            let pass = const_bool(b, true);
            b.jump(done, &[pass]);
            b.position_at(missing);
            let fail = const_bool(b, false);
            b.jump(done, &[fail]);
            b.position_at(done);
            return result;
        }
        other => {
            let schema = b.const_str(&serde_json::to_string(other).expect("serializable type schema"));
            return typed_native(b, "wir_type_matches", vec![value, schema], Type::Bool, false);
        }
    };
    typed_native(b, predicate, vec![value], Type::Bool, true)
}

fn lower_typed<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    op: &TypedOp,
    args: &[Expr],
    lowering_ctx: &LoweringContext,
) -> LResult<ValueId> {
    if let TypedOp::ArraySet = op {
        // Same evaluation order as untyped `a[i] = v`: value first.
        let value = lower_expr_free(b, locals, fields, next_field, &args[2], lowering_ctx)?;
        let array = lower_expr_free(b, locals, fields, next_field, &args[0], lowering_ctx)?;
        let index = lower_expr_free(b, locals, fields, next_field, &args[1], lowering_ctx)?;
        typed_native(b, "wir_array_set", vec![array, index, value], Type::Top, false);
        return Ok(value);
    }
    let mut values = Vec::with_capacity(args.len());
    for arg in args {
        values.push(lower_expr_free(b, locals, fields, next_field, arg, lowering_ctx)?);
    }
    Ok(match op {
        TypedOp::Assert { check, message } => {
            let value = values[0];
            let ok = lower_rt_check(b, fields, next_field, value, check);
            let pass = b.block();
            let fail = b.block();
            b.branch(ok, pass, fail);
            b.position_at(fail);
            snapshot_try_locals(b, locals);
            let error = b.const_str(message);
            let _ = b.push_node(Inst::Throw(error), None, 0, true);
            b.position_at(pass);
            value
        }
        TypedOp::StrConcat => {
            typed_native(b, "wir_string_concat", vec![values[0], values[1]], Type::Str, false)
        }
        TypedOp::StrEq { negate } => {
            let equal =
                typed_native(b, "wir_string_equals", vec![values[0], values[1]], Type::Bool, false);
            if *negate { bool_select(b, equal, false) } else { equal }
        }
        TypedOp::PrimEq { negate } => {
            let kind = if *negate { crate::wir::CmpKind::Ne } else { crate::wir::CmpKind::Eq };
            let (_nid, res) = b.push_node(
                Inst::CmpInt { kind, a: values[0], b: values[1] },
                Some(Type::Bool),
                1,
                false,
            );
            res[0]
        }
        TypedOp::ArrayLen => typed_native(b, "wir_array_len", vec![values[0]], Type::Int32, false),
        TypedOp::StrLen => typed_native(b, "wir_string_len", vec![values[0]], Type::Int32, false),
        TypedOp::ArrayGet => {
            typed_native(b, "wir_array_get", vec![values[0], values[1]], Type::Top, false)
        }
        TypedOp::TypeArgs(_) | TypedOp::Cast(_) => values[0],
        TypedOp::ArraySet => unreachable!("handled above"),
    })
}

impl<'m> Lowerer<'m> {
    fn lower_modinit(&mut self, _prog: &Program, links: &LinkInfo) -> LResult<FuncId> {
        use crate::wir::{Inst, Type};

        #[cfg(debug_assertions)]
        {
            eprintln!("lower_modinit() [pre]");
            eprintln!(
                "[links] exports        : {:?}",
                links.export_bindings.keys().collect::<Vec<_>>()
            );
            eprintln!(
                "[links] imports        : {:?}",
                links.import_bindings.keys().collect::<Vec<_>>()
            );
            eprintln!(
                "[links] namespace_imps : {:?}",
                links.namespace_imports.keys().collect::<Vec<_>>()
            );
            eprintln!("[links] namespace_cells: {:?}", links.namespace_cells);
        }

        // ---- Plan de exports desde link info ----
        let mut fn_exports: Vec<(BindingId, FuncId)> = Vec::new();
        let mut class_exports: Vec<(BindingId, Option<FuncId>, Vec<(String, FuncId)>)> = Vec::new();

        for (name, &bid) in links.export_bindings.get_internals() {
            if let Some(&fid) = self.lowering_ctx.funcs.get(name) {
                #[cfg(debug_assertions)]
                eprintln!(
                    "[modinit] export function {} -> fid {:?} binding {:?}",
                    name, fid, bid
                );
                // export function <name>
                fn_exports.push((bid, fid));
                continue;
            }
            if let Some(ci) = self.lowering_ctx.classes.get(name) {
                // export class <name>
                let alloc = self
                    .lowering_ctx
                    .funcs
                    .get(&format!("__class_new_{}", name))
                    .copied();
                let mut statics = Vec::new();
                for (mname, _, _, _) in &ci.static_methods {
                    if let Some(&sfid) = self
                        .lowering_ctx
                        .funcs
                        .get(&format!("__static_{}_{}", name, mname))
                    {
                        statics.push((mname.clone(), sfid));
                    }
                }
                class_exports.push((bid, alloc, statics));
                continue;
            }
            #[cfg(debug_assertions)]
            eprintln!(
                "[modinit] export {:?}: no es func/clase local (vars se materializan via StmtKind::Var en __toplevel__)",
                name
            );
        }

        // ---- Cuerpo de la funciÃ³n (sÃ³lo muta self.module) ----
        let func = {
            let mut b = Builder::new(self.module, "__modinit__", vec![], vec![Type::Int32]);

            // 0) Inicializa SOLO las celdas de export de este mÃ³dulo a `undefined` (TDZ-safe).
            //    NO tocar import_bindings: son celdas del proveedor.
            let undef = b.const_undef();
            for (_, cell) in links.module_bindings.values() {
                b.store_binding(*cell, undef);
            }
            for &bid in links.export_bindings.values() {
                b.store_binding(bid, undef);
            }
            for binding in links.enum_bindings.values() {
                let bid = binding.cell;
                if !links.export_bindings.values().any(|export| *export == bid) {
                    b.store_binding(bid, undef);
                }
            }

            // null env para closures
            let (_nid, nul) = b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);

            // 1) Materializa funciones exportadas como closures sin entorno
            for (bid, fid) in fn_exports {
                let (_nid, clos) = b.push_node(
                    Inst::MakeClosure {
                        callee: fid,
                        env: nul[0],
                    },
                    Some(Type::Closure(None)),
                    1,
                    false,
                );
                b.store_binding(bid, clos[0]);
            }

            // 2) Materializa clases exportadas: objeto con 'new' + estÃ¡ticos; luego publÃ­calo
            for (bid, alloc_opt, statics) in class_exports {
                let (_nid, obj) = b.push_node(
                    Inst::CallNative {
                        name: "wir_obj_new".into(),
                        args: vec![],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                let objv = obj[0];

                if let Some(afid) = alloc_opt {
                    let (_nid, clo) = b.push_node(
                        Inst::MakeClosure {
                            callee: afid,
                            env: nul[0],
                        },
                        Some(Type::Closure(None)),
                        1,
                        false,
                    );
                    let (_nk, k) = b.push_node(
                        Inst::Const(Constant::Str("new".into())),
                        Some(Type::Str),
                        1,
                        false,
                    );
                    let _ = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_set_str".into(),
                            args: vec![objv, k[0], clo[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                }

                for (mname, sfid) in statics {
                    let (_nid, clo) = b.push_node(
                        Inst::MakeClosure {
                            callee: sfid,
                            env: nul[0],
                        },
                        Some(Type::Closure(None)),
                        1,
                        false,
                    );
                    let (_nk, k) =
                        b.push_node(Inst::Const(Constant::Str(mname)), Some(Type::Str), 1, false);
                    let _ = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_set_str".into(),
                            args: vec![objv, k[0], clo[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                }

                // publica el "class object"
                b.store_binding(bid, objv);
            }

            // 3) Cachea namespaces importados (si existen celdas locales para ellos)
            //    Esto sÃ³lo escribe en nuestras celdas de namespace (locales), no en el proveedor.
            for (ns, exports) in links.namespace_imports.get_internals() {
                if let Some(&cell) = links.namespace_cells.get(ns) {
                    let ns_obj = b.make_namespace(exports.clone());
                    b.store_binding(cell, ns_obj);
                }
            }

            let zero = b.const_i32(0);
            b.ret(&[zero]);
            b.finish()
        };

        let fid = self.module.push_function(func);
        Ok(fid)
    }

    fn lower_all_classes(&mut self, prog: &Program) -> LResult<()> {
        // Emit in the same order we predeclared
        for c in &prog.classes {
            self.lower_one_class(c)?;
        }
        Ok(())
    }

    fn lower_one_class(&mut self, c: &ClassDecl) -> LResult<()> {
        let cname = &c.name;

        // Own the collected class info (props/method lists, flags)
        let ci = self
            .lowering_ctx
            .classes
            .get(cname)
            .expect("class collected")
            .clone();

        // ---- IMPORTANT: one shared field-id table per class ----
        let mut cls_fields: HashMap<String, FieldId> = HashMap::new();
        let mut cls_next_field: u32 = 0;

        // 1) Accessors
        for (pname, get, set) in &ci.props {
            if let Some(gb) = get {
                let fname = format!("__get_{}_{}", cname, pname);
                self.lower_instance_fun(
                    cname,
                    &fname,
                    &[],
                    gb,
                    false,
                    &mut cls_fields,
                    &mut cls_next_field,
                )?;
            }
            if let Some((p, sb)) = set {
                let fname = format!("__set_{}_{}", cname, pname);
                let params: Vec<String> = vec![p.clone()];
                self.lower_instance_fun(
                    cname,
                    &fname,
                    &params,
                    sb,
                    false,
                    &mut cls_fields,
                    &mut cls_next_field,
                )?;
            }
        }

        // 2) Instance methods (skip ctor/dtor pseudo entries)
        for (mname, params, body, is_async) in &ci.methods {
            if *mname == "constructor" || *mname == "destructor" {
                continue;
            }
            let fname = format!("__method_{}_{}", cname, mname);
            self.lower_instance_fun(
                cname,
                &fname,
                params,
                body,
                *is_async,
                &mut cls_fields,
                &mut cls_next_field,
            )?;
        }

        // 3) Static methods (unchanged)
        for (mname, params, body, is_async) in &ci.static_methods {
            let fname = format!("__static_{}_{}", cname, mname);
            self.lower_free_like_fun(&fname, params, body, *is_async)?;
        }

        // 4) Ctor (optional) â€” must share the same field-id map
        if let Some((_, ctor_params, ctor_body, _)) =
            ci.methods.iter().find(|(n, _, _, _)| *n == "constructor")
        {
            let fname = format!("__ctor_{}", cname);
            self.lower_instance_fun(
                cname,
                &fname,
                ctor_params,
                ctor_body,
                false,
                &mut cls_fields,
                &mut cls_next_field,
            )?;
        }

        // 5) Dtor (optional)
        if ci.has_dtor {
            if let Some((_, _, dtor_body, _)) =
                ci.methods.iter().find(|(n, _, _, _)| *n == "destructor")
            {
                let fname = format!("__dtor_{}", cname);
                self.lower_instance_fun(
                    cname,
                    &fname,
                    &[],
                    dtor_body,
                    false,
                    &mut cls_fields,
                    &mut cls_next_field,
                )?;
            }
        }

        // 6) Allocator â€” also installs method closures onto the instance
        self.lower_allocator(&ci, &mut cls_fields, &mut cls_next_field)?;
        Ok(())
    }

    fn lower_free_like_fun(
        &mut self,
        fname: &str,
        params: &[String],
        body: &Block,
        is_async: bool,
    ) -> LResult<()> {
        use crate::wir::{Inst, Type};

        let mut f = {
            let mut b = Builder::new(
                self.module,
                fname,
                vec![Type::Int32; params.len()],
                vec![Type::Int32],
            );

            // Bind params
            let mut locals: HashMap<String, ValueId> = Default::default();
            for (i, p) in params.iter().enumerate() {
                locals.insert(p.clone(), b.param(i));
            }

            let mut fields: HashMap<String, FieldId> = Default::default();
            let mut next_field: u32 = 0;
            let mut active_try: Vec<TryScope> = Vec::new();

            if is_async {
                b.set_async(true);
                // Deferred prologue
                let (_nid, d_res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_deferred_new".into(),
                        args: vec![],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                let d = d_res[0];
                locals.insert("__deferred".to_string(), d);

                lower_block_free_async(
                    &mut b,
                    &mut locals,
                    &mut fields,
                    &mut next_field,
                    body,
                    &self.lowering_ctx,
                    true,
                    &mut active_try,
                )?;

                if !b.current_block_terminated() {
                    let zero = b.const_i32(0);
                    b.ret(&[zero]);
                }
            } else {
                lower_block_free(
                    &mut b,
                    &mut locals,
                    &mut fields,
                    &mut next_field,
                    body,
                    &self.lowering_ctx,
                    &mut active_try,
                )?;
                if !b.current_block_terminated() {
                    let zero = b.const_i32(0);
                    b.ret(&[zero]);
                }
            }

            b.finish()
        };

        // Set the reserved ID before pushing
        let reserved_fid = *self.lowering_ctx.funcs.get(fname).expect("reserved");
        f.id = reserved_fid;

        // Publish into the module preserving the reserved ID
        let fid = self.module.push_function_preserve_id(f);
        assert_eq!(fid, reserved_fid, "push preserved ID");
        Ok(())
    }

    fn rewrite_privates_in_block(&self, class_name: &str, body: &Block) -> Block {
        // Resolve base class name once (if any). Weâ€™ll still rewrite even if there is none;
        // in that case unknown-func errors will be raised later if user wrote `super`.
        let base_opt = self
            .lowering_ctx
            .classes
            .get(class_name)
            .and_then(|ci| ci.base.clone());

        fn rw_block<F: Fn(&Expr) -> Expr + Copy>(b: &Block, f: F) -> Block {
            Block {
                stmts: b.stmts.iter().map(|s| rw_stmt(s, f)).collect(),
            }
        }
        fn rw_stmt<F: Fn(&Expr) -> Expr + Copy>(s: &Stmt, f: F) -> Stmt {
            match s.kind() {
                StmtKind::Enum {
                    name,
                    binding,
                    init,
                } => stmt_with_meta(
                    s,
                    StmtKind::Enum {
                        name: name.clone(),
                        binding: *binding,
                        init: rw_expr(init, f),
                    },
                ),
                StmtKind::Var { name, init, ty } => stmt_with_meta(
                    s,
                    StmtKind::Var {
                        name: name.clone(),
                        init: init.as_ref().map(|e| rw_expr(e, f)),
                        ty: ty.clone(),
                    },
                ),
                StmtKind::VarDestruct { pattern, init } => stmt_with_meta(
                    s,
                    StmtKind::VarDestruct {
                        pattern: pattern.clone(),
                        init: rw_expr(init, f),
                    },
                ),
                StmtKind::If {
                    cond,
                    then_b,
                    else_b,
                } => stmt_with_meta(
                    s,
                    StmtKind::If {
                        cond: rw_expr(cond, f),
                        then_b: rw_block(then_b, f),
                        else_b: else_b.as_ref().map(|b| rw_block(b, f)),
                    },
                ),
                StmtKind::While { cond, body } => stmt_with_meta(
                    s,
                    StmtKind::While {
                        cond: rw_expr(cond, f),
                        body: rw_block(body, f),
                    },
                ),
                StmtKind::For {
                    init,
                    cond,
                    step,
                    body,
                } => stmt_with_meta(
                    s,
                    StmtKind::For {
                        init: init.as_deref().map(|i| SmallBox::new(rw_stmt(i, f))),
                        cond: cond.as_ref().map(|e| rw_expr(e, f)),
                        step: step.as_ref().map(|e| rw_expr(e, f)),
                        body: rw_block(body, f),
                    },
                ),
                StmtKind::Try {
                    try_block,
                    catch,
                    finally_block,
                } => stmt_with_meta(
                    s,
                    StmtKind::Try {
                        try_block: rw_block(try_block, f),
                        catch: catch.as_ref().map(|clause| CatchClause {
                            binding: clause.binding.clone(),
                            body: rw_block(&clause.body, f),
                            meta: clause.meta.clone(),
                        }),
                        finally_block: finally_block.as_ref().map(|blk| rw_block(blk, f)),
                    },
                ),
                StmtKind::Throw(expr) => stmt_with_meta(s, StmtKind::Throw(rw_expr(expr, f))),
                StmtKind::Defer {
                    kind,
                    binding,
                    body,
                } => stmt_with_meta(
                    s,
                    StmtKind::Defer {
                        kind: *kind,
                        binding: binding.clone(),
                        body: rw_block(body, f),
                    },
                ),
                StmtKind::Return(e) => {
                    stmt_with_meta(s, StmtKind::Return(e.as_ref().map(|x| rw_expr(x, f))))
                }
                StmtKind::Expr(e) => stmt_with_meta(s, StmtKind::Expr(rw_expr(e, f))),
                StmtKind::Listen(ld) => {
                    let routes = ld
                        .routes
                        .iter()
                        .map(|r| RouteDecl {
                            method: r.method.clone(),
                            pattern: rw_expr(&r.pattern, f),
                            handler: rw_expr(&r.handler, f),
                        })
                        .collect();
                    stmt_with_meta(
                        s,
                        StmtKind::Listen(ListenDecl {
                            addr: ld.addr.clone(),
                            routes,
                        }),
                    )
                }
            }
        }
        fn rw_expr<F: Fn(&Expr) -> Expr + Copy>(e: &Expr, f: F) -> Expr {
            let m = f(e);
            if std::mem::discriminant(m.kind()) != std::mem::discriminant(e.kind()) {
                return m;
            }

            match m.kind() {
                ExprKind::Assign(lv, rhs) => expr_with_meta(
                    &m,
                    ExprKind::Assign(
                        SmallBox::new(rw_lvalue(lv, f)),
                        SmallBox::new(rw_expr(rhs, f)),
                    ),
                ),
                ExprKind::Binary { op, a, b } => expr_with_meta(
                    &m,
                    ExprKind::Binary {
                        op: *op,
                        a: SmallBox::new(rw_expr(a, f)),
                        b: SmallBox::new(rw_expr(b, f)),
                    },
                ),
                ExprKind::Unary { op, e: inner } => expr_with_meta(
                    &m,
                    ExprKind::Unary {
                        op: *op,
                        e: SmallBox::new(rw_expr(inner, f)),
                    },
                ),
                ExprKind::Call { callee, args } => expr_with_meta(
                    &m,
                    ExprKind::Call {
                        callee: SmallBox::new(rw_expr(callee, f)),
                        args: args.iter().map(|x| rw_expr(x, f)).collect(),
                    },
                ),
                ExprKind::Typed { op, args } => expr_with_meta(
                    &m,
                    ExprKind::Typed {
                        op: op.clone(),
                        args: args.iter().map(|x| rw_expr(x, f)).collect(),
                    },
                ),
                ExprKind::GetProp { recv, name } => expr_with_meta(
                    &m,
                    ExprKind::GetProp {
                        recv: SmallBox::new(rw_expr(recv, f)),
                        name: name.clone(),
                    },
                ),
                ExprKind::Index { recv, index } => expr_with_meta(
                    &m,
                    ExprKind::Index {
                        recv: SmallBox::new(rw_expr(recv, f)),
                        index: SmallBox::new(rw_expr(index, f)),
                    },
                ),
                ExprKind::Group(inner) => {
                    expr_with_meta(&m, ExprKind::Group(SmallBox::new(rw_expr(inner, f))))
                }
                ExprKind::ArrayLit(items) => expr_with_meta(
                    &m,
                    ExprKind::ArrayLit(items.iter().map(|x| rw_expr(x, f)).collect()),
                ),
                ExprKind::ObjLit(list) => expr_with_meta(
                    &m,
                    ExprKind::ObjLit(
                        list.iter()
                            .map(|item| match item {
                                ObjItem::Prop(k, v) => ObjItem::Prop(k.clone(), rw_expr(v, f)),
                                ObjItem::Spread(expr) => ObjItem::Spread(rw_expr(expr, f)),
                            })
                            .collect(),
                    ),
                ),
                ExprKind::GetPropObj { obj, key } => expr_with_meta(
                    &m,
                    ExprKind::GetPropObj {
                        obj: SmallBox::new(rw_expr(obj, f)),
                        key: key.clone(),
                    },
                ),
                ExprKind::SetPropObj { obj, key, value } => expr_with_meta(
                    &m,
                    ExprKind::SetPropObj {
                        obj: SmallBox::new(rw_expr(obj, f)),
                        key: key.clone(),
                        value: SmallBox::new(rw_expr(value, f)),
                    },
                ),
                ExprKind::In { key, obj } => expr_with_meta(
                    &m,
                    ExprKind::In {
                        key: SmallBox::new(rw_expr(key, f)),
                        obj: SmallBox::new(rw_expr(obj, f)),
                    },
                ),
                ExprKind::DeleteProp { obj, key } => expr_with_meta(
                    &m,
                    ExprKind::DeleteProp {
                        obj: SmallBox::new(rw_expr(obj, f)),
                        key: key.clone(),
                    },
                ),
                ExprKind::Await(inner) => {
                    expr_with_meta(&m, ExprKind::Await(SmallBox::new(rw_expr(inner, f))))
                }
                _ => m,
            }
        }

        fn rw_lvalue<F: Fn(&Expr) -> Expr + Copy>(lv: &LValue, f: F) -> LValue {
            match lv.kind() {
                LValueKind::GetProp { recv, name } => lvalue_with_meta(
                    lv,
                    LValueKind::GetProp {
                        recv: rw_expr(recv, f),
                        name: name.clone(),
                    },
                ),
                LValueKind::Index { recv, index } => lvalue_with_meta(
                    lv,
                    LValueKind::Index {
                        recv: rw_expr(recv, f),
                        index: rw_expr(index, f),
                    },
                ),
                _ => lv.clone(),
            }
        }

        // Rewriter: (super(...)) and (super.m)(...) â†’ direct calls with implicit `this`
        let class_name = class_name.to_string();

        let f = |e: &Expr| -> Expr {
            match e.kind() {
                // super(args...)  â†’  __ctor_Base(this, args...)  (only if there *is* a base)
                ExprKind::SuperCall(args) => {
                    if let Some(ref base) = base_opt {
                        let mut new_args = Vec::with_capacity(args.len() + 1);
                        new_args.push(expr_unknown(ExprKind::This));
                        new_args.extend(args.iter().cloned());
                        expr_unknown(ExprKind::Call {
                            callee: SmallBox::new(expr_unknown(ExprKind::Ident(format!(
                                "__ctor_{}",
                                base
                            )))),
                            args: new_args,
                        })
                    } else {
                        e.clone() // leave for lowerer to complain
                    }
                }

                // (super.m)(args...)  â†’  __method_Base_m(this, args...)  (only if base exists)
                ExprKind::Call { callee, args } => {
                    if let ExprKind::SuperProp(m) = callee.kind() {
                        if let Some(ref base) = base_opt {
                            let mut new_args = Vec::with_capacity(args.len() + 1);
                            new_args.push(expr_unknown(ExprKind::This));
                            new_args.extend(args.iter().cloned());
                            expr_unknown(ExprKind::Call {
                                callee: SmallBox::new(expr_unknown(ExprKind::Ident(format!(
                                    "__method_{}_{}",
                                    base, m
                                )))),
                                args: new_args,
                            })
                        } else {
                            e.clone()
                        }
                    } else {
                        e.clone()
                    }
                }

                // Value-position super.m stays as-is so the lowerer raises your existing error.
                ExprKind::SuperProp(_) => e.clone(),

                _ => e.clone(),
            }
        };

        rw_block(body, f)
    }

    fn lower_instance_fun(
        &mut self,
        class_name: &str,
        fname: &str,
        params: &[String],
        body: &Block,
        is_async: bool,
        // class-shared field-id table (important!)
        fields: &mut HashMap<String, FieldId>,
        next_field: &mut u32,
    ) -> LResult<()> {
        use crate::wir::{Inst, Type};

        // Keep your private/super rewriter
        let body_rw = self.rewrite_privates_in_block(class_name, body);

        // Build function: hidden `this` + user params
        let mut f = {
            let argc = params.len() + 1;
            let mut b = Builder::new(
                self.module,
                fname,
                vec![Type::Int32; argc],
                vec![Type::Int32],
            );

            // Bind locals
            let mut locals: HashMap<String, ValueId> = Default::default();
            locals.insert("this".to_string(), b.param(0));
            for (i, name) in params.iter().enumerate() {
                locals.insert(name.clone(), b.param(i + 1));
            }
            let mut active_try: Vec<TryScope> = Vec::new();

            if is_async {
                b.set_async(true);
                // --- Async prologue: d = Deferred()
                let (_nid, d_res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_deferred_new".into(),
                        args: vec![],
                        pure: false,
                        can_throw: false,
                    },
                    None,
                    1,
                    true,
                );
                let d = d_res[0];
                locals.insert("__deferred".to_string(), d);

                // Lower body with async-aware lowering.
                lower_block_free_async(
                    &mut b,
                    &mut locals,
                    fields,
                    next_field,
                    &body_rw,
                    &self.lowering_ctx,
                    true,
                    &mut active_try,
                )?;

                // Promise settlement happens after all finalizers in the JIT epilogue.
                if !b.current_block_terminated() {
                    let zero = b.const_i32(0);
                    b.ret(&[zero]);
                }
            } else {
                // --- Sync path (what you already had), but sharing the CLASS field-id map
                lower_block_free(
                    &mut b,
                    &mut locals,
                    fields,
                    next_field,
                    &body_rw,
                    &self.lowering_ctx,
                    &mut active_try,
                )?;
                if !b.current_block_terminated() {
                    let zero = b.const_i32(0);
                    b.ret(&[zero]);
                }
            }

            b.finish()
        };

        // Set the reserved ID before pushing
        let reserved_fid = *self.lowering_ctx.funcs.get(fname).expect("reserved");
        f.id = reserved_fid;

        // Publish into the module preserving the reserved ID
        let fid = self.module.push_function_preserve_id(f);
        assert_eq!(fid, reserved_fid, "push preserved ID");
        Ok(())
    }

    fn lower_allocator(
        &mut self,
        ci: &ClassInfo,
        fields: &mut HashMap<String, FieldId>,
        next_field: &mut u32,
    ) -> LResult<()> {
        use crate::wir::{Inst, Type};

        let fname = format!("__class_new_{}", ci.name);

        // Collect base chain names from root â†’ ... â†’ direct base (so overrides later will win)
        let mut base_chain: Vec<String> = Vec::new();
        let mut cur = ci.base.clone();
        while let Some(bn) = cur {
            base_chain.push(bn.clone());
            cur = self
                .lowering_ctx
                .classes
                .get(&bn)
                .and_then(|x| x.base.clone());
        }
        base_chain.reverse();

        // helper closures inside this fn
        let mut f = {
            let ctor_params: Vec<String> = ci
                .methods
                .iter()
                .find(|(n, _, _, _)| *n == "constructor")
                .map(|(_, ps, _, _)| ps.clone())
                .unwrap_or_default();

            let mut b = Builder::new(
                self.module,
                &fname,
                vec![Type::Int32; ctor_params.len()],
                vec![Type::Int32],
            );

            // obj = wir_obj_new()
            let (_nid, obj_r) = b.push_node(
                Inst::CallNative {
                    name: "wir_obj_new".into(),
                    args: vec![],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            let obj = obj_r[0];

            // null for closures
            let (_nid, nul) = b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);

            // ---- Install inherited methods/accessors (root base first) ----
            for bn in &base_chain {
                if let Some(bci) = self.lowering_ctx.classes.get(bn) {
                    // methods (skip ctor/dtor)
                    for (mname, _ps, _body, _ia) in &bci.methods {
                        if *mname == "constructor" || *mname == "destructor" {
                            continue;
                        }
                        if let Some(&mfid) = self
                            .lowering_ctx
                            .funcs
                            .get(&format!("__method_{}_{}", bn, mname))
                        {
                            let (_nid_clo, clos) = b.push_node(
                                Inst::MakeClosure {
                                    callee: mfid,
                                    env: nul[0],
                                },
                                Some(Type::Closure(None)),
                                1,
                                false,
                            );
                            let (_nid_k, ks) = b.push_node(
                                Inst::Const(Constant::Str(mname.clone())),
                                Some(Type::Str),
                                1,
                                false,
                            );
                            let _ = b.push_node(
                                Inst::CallNative {
                                    name: "wir_obj_set_str".into(),
                                    args: vec![obj, ks[0], clos[0]],
                                    pure: false,
                                    can_throw: false,
                                },
                                Some(Type::Int32),
                                1,
                                true,
                            );
                        }
                    }
                    // accessors: "__get__p" / "__set__p"
                    for (pname, getb, setb) in &bci.props {
                        if getb.is_some() {
                            if let Some(&gid) = self
                                .lowering_ctx
                                .funcs
                                .get(&format!("__get_{}_{}", bn, pname))
                            {
                                let (_nid_clo, clos) = b.push_node(
                                    Inst::MakeClosure {
                                        callee: gid,
                                        env: nul[0],
                                    },
                                    Some(Type::Closure(None)),
                                    1,
                                    false,
                                );
                                let key = format!("__get__{}", pname);
                                let (_nid_k, ks) = b.push_node(
                                    Inst::Const(Constant::Str(key)),
                                    Some(Type::Str),
                                    1,
                                    false,
                                );
                                let _ = b.push_node(
                                    Inst::CallNative {
                                        name: "wir_obj_set_str".into(),
                                        args: vec![obj, ks[0], clos[0]],
                                        pure: false,
                                        can_throw: false,
                                    },
                                    Some(Type::Int32),
                                    1,
                                    true,
                                );
                            }
                        }
                        if setb.is_some() {
                            if let Some(&sid) = self
                                .lowering_ctx
                                .funcs
                                .get(&format!("__set_{}_{}", bn, pname))
                            {
                                let (_nid_clo, clos) = b.push_node(
                                    Inst::MakeClosure {
                                        callee: sid,
                                        env: nul[0],
                                    },
                                    Some(Type::Closure(None)),
                                    1,
                                    false,
                                );
                                let key = format!("__set__{}", pname);
                                let (_nid_k, ks) = b.push_node(
                                    Inst::Const(Constant::Str(key)),
                                    Some(Type::Str),
                                    1,
                                    false,
                                );
                                let _ = b.push_node(
                                    Inst::CallNative {
                                        name: "wir_obj_set_str".into(),
                                        args: vec![obj, ks[0], clos[0]],
                                        pure: false,
                                        can_throw: false,
                                    },
                                    Some(Type::Int32),
                                    1,
                                    true,
                                );
                            }
                        }
                    }
                }
            }

            // ---- Install own methods/accessors (override base if name matches) ----
            for (mname, _ps, _body, _ia) in &ci.methods {
                if *mname == "constructor" || *mname == "destructor" {
                    continue;
                }
                if let Some(&mfid) = self
                    .lowering_ctx
                    .funcs
                    .get(&format!("__method_{}_{}", ci.name, mname))
                {
                    let (_nid_clo, clos) = b.push_node(
                        Inst::MakeClosure {
                            callee: mfid,
                            env: nul[0],
                        },
                        Some(Type::Closure(None)),
                        1,
                        false,
                    );
                    let (_nid_k, ks) = b.push_node(
                        Inst::Const(Constant::Str(mname.clone())),
                        Some(Type::Str),
                        1,
                        false,
                    );
                    let _ = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_set_str".into(),
                            args: vec![obj, ks[0], clos[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                }
            }
            for (pname, getb, setb) in &ci.props {
                if getb.is_some() {
                    if let Some(&gid) = self
                        .lowering_ctx
                        .funcs
                        .get(&format!("__get_{}_{}", ci.name, pname))
                    {
                        let (_nid_clo, clos) = b.push_node(
                            Inst::MakeClosure {
                                callee: gid,
                                env: nul[0],
                            },
                            Some(Type::Closure(None)),
                            1,
                            false,
                        );
                        let key = format!("__get__{}", pname);
                        let (_nid_k, ks) =
                            b.push_node(Inst::Const(Constant::Str(key)), Some(Type::Str), 1, false);
                        let _ = b.push_node(
                            Inst::CallNative {
                                name: "wir_obj_set_str".into(),
                                args: vec![obj, ks[0], clos[0]],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                    }
                }
                if setb.is_some() {
                    if let Some(&sid) = self
                        .lowering_ctx
                        .funcs
                        .get(&format!("__set_{}_{}", ci.name, pname))
                    {
                        let (_nid_clo, clos) = b.push_node(
                            Inst::MakeClosure {
                                callee: sid,
                                env: nul[0],
                            },
                            Some(Type::Closure(None)),
                            1,
                            false,
                        );
                        let key = format!("__set__{}", pname);
                        let (_nid_k, ks) =
                            b.push_node(Inst::Const(Constant::Str(key)), Some(Type::Str), 1, false);
                        let _ = b.push_node(
                            Inst::CallNative {
                                name: "wir_obj_set_str".into(),
                                args: vec![obj, ks[0], clos[0]],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                    }
                }
            }

            // ---- Initialize fields that have literal initializers (MVP) ----
            for (fname, init_opt) in &ci.instance_fields {
                if let Some(init_e) = init_opt {
                    // We best-effort lower, but only pure/literal inits will succeed (no `this`/params).
                    // Use the same field-id table as methods so fast-field loads match.
                    if let Ok(v) = lower_expr_free(
                        &mut b,
                        &mut Default::default(),
                        fields,
                        next_field,
                        init_e,
                        &self.lowering_ctx,
                    ) {
                        let field = intern_field_local(fields, next_field, fname);
                        let _ = b.push_node(
                            Inst::StoreField {
                                obj,
                                field,
                                val: v,
                                expected: None,
                            },
                            Some(Type::Top),
                            1,
                            true,
                        );
                        // Also mirror into string table for consistency
                        let (_nid_k, ks) = b.push_node(
                            Inst::Const(Constant::Str(fname.clone())),
                            Some(Type::Str),
                            1,
                            false,
                        );
                        let _ = b.push_node(
                            Inst::CallNative {
                                name: "wir_obj_set_str".into(),
                                args: vec![obj, ks[0], v],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                    }
                }
            }

            // ---- Call derived ctor if present ----
            if ci.has_ctor {
                if let Some(&fid) = self.lowering_ctx.funcs.get(&format!("__ctor_{}", ci.name)) {
                    let mut argv = Vec::with_capacity(1 + ctor_params.len());
                    argv.push(obj);
                    for i in 0..ctor_params.len() {
                        argv.push(b.param(i));
                    }
                    let (_nid, _res) = b.push_node(
                        Inst::CallDirect {
                            conv: crate::wir::CallConv::Fast,
                            callee: fid,
                            args: argv,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                }
            }

            b.ret(&[obj]);
            b.finish()
        };

        // Set the reserved ID before pushing
        let reserved_fid = *self.lowering_ctx.funcs.get(&fname).expect("reserved");
        f.id = reserved_fid;

        // Publish into the module preserving the reserved ID
        let fid = self.module.push_function_preserve_id(f);
        assert_eq!(fid, reserved_fid, "push preserved ID");
        Ok(())
    }
}

fn intern_field_local(
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    name: &str,
) -> FieldId {
    if let Some(&fid) = fields.get(name) {
        return fid;
    }
    let fid = FieldId(*next_field);
    *next_field += 1;
    fields.insert(name.to_string(), fid);
    fid
}

fn build_bool_or(b: &mut Builder, lhs: ValueId, rhs: ValueId) -> ValueId {
    // if lhs then true else rhs
    let then_b = b.block();
    let else_b = b.block();
    let cont = b.block();
    let out = b.add_block_param(cont, Type::Bool);

    b.branch(lhs, then_b, else_b);

    b.position_at(then_b);
    let (_nid_t, t) = b.push_node(
        Inst::Const(Constant::Bool(true)),
        Some(Type::Bool),
        1,
        false,
    );
    b.jump(cont, &[t[0]]);

    b.position_at(else_b);
    b.jump(cont, &[rhs]);

    b.position_at(cont);
    out
}

fn http_method_smi(method: &str) -> i32 {
    match method {
        "GET" | "get" => 1,
        "POST" | "post" => 2,
        "PUT" | "put" => 3,
        "DELETE" | "delete" => 4,
        "PATCH" | "patch" => 5,
        "OPTIONS" | "options" => 6,
        "HEAD" | "head" => 7,
        "*" | "ANY" | "any" => 0,
        _ => 0, // default ANY
    }
}

fn boxed_key(name: &str) -> String {
    format!("__boxed:{}", name)
}
