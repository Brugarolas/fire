// src/lowerer.rs
#![allow(unused_variables)]

use ahash::{AHashMap as HashMap, AHashSet as HashSet};
use logos::Logos;
use smallbox::SmallBox;
use std::cell::Cell;
use std::collections::hash_map::Entry;
use std::{collections::BTreeSet, ops::Deref};

// Bring in the WIR types from your other file/module.
use crate::wir::{
    AccessorInfo, BindingId, Builder, Constant, FieldId, FuncId, Inst, IntBinOp, MethodInfo,
    Module, Type, ValueId,
};

use crate::front::{
    BinOp, Block, ClassDecl, ClassMember, ExportDecl, Expr, FuncDecl, ImportDecl, ImportItem,
    LValue, ListenDecl, ObjItem, ObjPattern, OptionalAccess, Program, PropKey, RouteDecl, Stmt,
    UnOp,
};

use crate::hoister::hoist_fn_lits_program;

// -------------------------
/// LOWERING (AST → WIR)
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

#[derive(Debug, Clone, Default)]
pub struct LinkInfo {
    /// import { a as x } from "m"   →   "x" -> binding(m,a)
    pub import_bindings: HashMap<String, BindingId>,
    /// import * as ns from "m"      →   "ns" -> [ ("a", binding(m,a)), ... ]
    pub namespace_imports: HashMap<String, Vec<(String, BindingId)>>,
    /// export { local as name } / export function f / export const x ...
    /// nombre local en este módulo → binding(this,name)
    pub export_bindings: HashMap<String, BindingId>,
    /// celda local (live binding) donde cachearemos el objeto namespace en __modinit__
    /// Si no está, caemos al camino “MVP por uso” para compat.
    pub namespace_cells: HashMap<String, BindingId>,
    /// nombres locales que corresponden a `export class` del proveedor (para saber que son clase)
    pub imported_class_bindings: HashSet<BindingId>,
}

#[derive(Debug, Clone)]
pub struct LoweringContext {
    pub funcs: HashMap<String, FuncId>,
    pub lam_captures: HashMap<String, Vec<String>>,
    pub classes: HashMap<String, ClassInfo>,
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
            let ci = self.lowering_ctx.classes.get(&fid_raw).expect("class collected");

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

        // -------- Stage 6: ahora SÍ, __modinit__ AL FINAL --------
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

            if is_async {
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
                )?;

                // Fallthrough: if the body didn’t explicitly return, resolve with 0 and return d.
                if !b.current_block_terminated() {
                    let zero = b.const_i32(0);
                    let dloc = *locals.get("__deferred").expect("__deferred present");
                    let (_nid, _) = b.push_node(
                        Inst::CallNative {
                            name: "wir_deferred_resolve".into(),
                            args: vec![dloc, zero],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    b.ret(&[dloc]);
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
) -> LResult<()> {
    for s in &blk.stmts {
        lower_stmt_free(b, locals, fields, next_field, s, lowering_ctx)?; // <-- pass
    }
    Ok(())
}

fn lower_stmt_free<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    s: &Stmt,
    lowering_ctx: &LoweringContext,
) -> LResult<()> {
    match s {
        Stmt::Var { name, init } => {
            let val = if let Some(e) = init {
                lower_expr_free(b, locals, fields, next_field, e, lowering_ctx)? // <-- pass
            } else {
                b.const_i32(0)
            };
            locals.insert(name.clone(), val);

            #[cfg(debug_assertions)]
            {
                eprintln!("lower_stmt_free() Stmt::Var {{ {} }}", name);
                eprintln!(
                    "[links] exports        : {:?}",
                    lowering_ctx.links.export_bindings.keys().collect::<Vec<_>>()
                );
                eprintln!(
                    "[links] imports        : {:?}",
                    lowering_ctx.links.import_bindings.keys().collect::<Vec<_>>()
                );
                eprintln!(
                    "[links] namespace_imps : {:?}",
                    lowering_ctx.links.namespace_imports.keys().collect::<Vec<_>>()
                );
                eprintln!("[links] namespace_cells: {:?}", lowering_ctx.links.namespace_cells);
            }
            if let Some(&bid) = lowering_ctx.links.export_bindings.get(name) {
                b.store_binding(bid, val);
            }
        }
        Stmt::VarDestruct { pattern, init } => {
            let obj_val =
                lower_expr_free(b, locals, fields, next_field, init, lowering_ctx)?;

            for field in &pattern.fields {
                let prop_name = match &field.key {
                    PropKey::Ident(name) => name.as_str(),
                    PropKey::Str(name) => name.as_str(),
                };
                let value = lower_general_getprop(b, obj_val, prop_name, fields, next_field);
                locals.insert(field.binding.clone(), value);
                if let Some(&bid) = lowering_ctx.links.export_bindings.get(&field.binding) {
                    b.store_binding(bid, value);
                }
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

                locals.insert(rest_name.clone(), rest_obj);
                if let Some(&bid) = lowering_ctx.links.export_bindings.get(rest_name) {
                    b.store_binding(bid, rest_obj);
                }
            }
        }
        Stmt::If {
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
                lowering_ctx
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
                    lowering_ctx
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
        Stmt::While { cond, body } => {
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

            b.position_at(body_b);
            lower_block_free(b, locals, fields, next_field, body, lowering_ctx)?; // <-- pass
            let back_args: Vec<ValueId> =
                mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
            b.jump(head, &back_args);

            b.position_at(exit);
            for (nm, p) in mut_names.into_iter().zip(phi_vals.into_iter()) {
                locals.insert(nm, p);
            }
        }
        Stmt::For {
            init,
            cond,
            step,
            body,
        } => {
            if let Some(i) = init.as_deref() {
                lower_stmt_free(b, locals, fields, next_field, i, lowering_ctx)?;
            } // <-- pass

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

            b.position_at(body_b);
            lower_block_free(b, locals, fields, next_field, body, lowering_ctx)?; // <-- pass
            if let Some(se) = step {
                let _ = lower_expr_free(b, locals, fields, next_field, se, lowering_ctx)?;
            } // <-- pass
            let back_args: Vec<ValueId> =
                mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
            b.jump(head, &back_args);

            b.position_at(exit);
            for (nm, p) in mut_names.into_iter().zip(phi_vals.into_iter()) {
                locals.insert(nm, p);
            }
        }
        Stmt::Return(e) => {
            if let Some(e) = e {
                let v = lower_expr_free(b, locals, fields, next_field, e, lowering_ctx)?;
                b.ret(&[v]);
            } else {
                let z = b.const_i32(0);
                b.ret(&[z]);
            }
        }
        Stmt::Listen(ld) => {
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
                let pat_v = lower_expr_free(
                    b,
                    locals,
                    fields,
                    next_field,
                    &rt.pattern,
                    lowering_ctx
                )?;
                let hnd_v = lower_expr_free(
                    b,
                    locals,
                    fields,
                    next_field,
                    &rt.handler,
                    lowering_ctx
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
        }

        Stmt::Expr(e) => {
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
    let cont = b.block();
    let out_ptr = cont;
    let out_val = b.add_block_param(cont, Type::Int32);

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
    let field = intern_field_local(fields, next_field, &name_string);
    let fid_smi = b.const_i32(field.0 as i32);
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
    match e {
        Expr::Assign(lv, rhs) => {
            if let LValue::Ident(name) = &**lv {
                out.insert(name.clone());
            }
            collect_mut_locals_in_expr(rhs, out);
        }
        Expr::Conditional {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_mut_locals_in_expr(cond, out);
            collect_mut_locals_in_expr(then_branch, out);
            collect_mut_locals_in_expr(else_branch, out);
        }
        Expr::Binary { a, b, .. } => {
            collect_mut_locals_in_expr(a, out);
            collect_mut_locals_in_expr(b, out);
        }
        Expr::Unary { e, .. } => collect_mut_locals_in_expr(e, out),
        Expr::Call { callee, args } => {
            collect_mut_locals_in_expr(callee, out);
            for a in args {
                collect_mut_locals_in_expr(a, out);
            }
        }
        Expr::GetProp { recv, .. } => collect_mut_locals_in_expr(recv, out),
        Expr::Index { recv, index } => {
            collect_mut_locals_in_expr(recv, out);
            collect_mut_locals_in_expr(index, out);
        }
        Expr::Group(e) => collect_mut_locals_in_expr(e, out),
        Expr::ObjLit(items) => {
            for item in items {
                match item {
                    ObjItem::Prop(_, value) => collect_mut_locals_in_expr(value, out),
                    ObjItem::Spread(expr) => collect_mut_locals_in_expr(expr, out),
                }
            }
        }
        Expr::OptionalChain { base, access } => {
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
        _ => {}
    }
}

fn collect_mut_locals_in_stmt(s: &Stmt, out: &mut BTreeSet<String>) {
    match s {
        Stmt::Expr(e) => collect_mut_locals_in_expr(e, out),
        Stmt::Var { .. } => {} // vars declared inside the loop are not loop-carried
        Stmt::VarDestruct { .. } => {}
        Stmt::If {
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
        Stmt::While { cond, body } => {
            collect_mut_locals_in_expr(cond, out);
            for st in &body.stmts {
                collect_mut_locals_in_stmt(st, out);
            }
        }
        Stmt::For {
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
        Stmt::Return(e) => {
            if let Some(e) = e {
                collect_mut_locals_in_expr(e, out);
            }
        }

        Stmt::Listen(ld) => {
            for r in &ld.routes {
                collect_mut_locals_in_expr(&r.pattern, out);
                collect_mut_locals_in_expr(&r.handler, out);
            }
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
) -> LResult<()> {
    for s in &blk.stmts {
        lower_stmt_free_async(
            b, locals, fields, next_field, s, lowering_ctx, in_async,
        )?;
    }
    Ok(())
}

fn lower_stmt_free_async<'m>(
    mut b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    s: &Stmt,
    lowering_ctx: &LoweringContext,
    in_async: bool,
) -> LResult<()> {
    match s {
        Stmt::Return(eopt) if in_async => {
            let d = *locals.get("__deferred").expect("__deferred present");
            let v = if let Some(e) = eopt {
                lower_expr_free_async(
                    b, locals, fields, next_field, e, lowering_ctx, in_async,
                )?
            } else {
                b.const_i32(0)
            };
            let (_nid, _r) = b.push_node(
                Inst::CallNative {
                    name: "wir_deferred_resolve".into(),
                    args: vec![d, v],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            b.ret(&[d]);
            Ok(())
        }
        Stmt::Listen(ld) => {
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
            match s {
                Stmt::Var { name, init } => {
                    let val = if let Some(e) = init {
                        lower_expr_free_async(
                            b, locals, fields, next_field, e, lowering_ctx, in_async,
                        )?
                    } else {
                        b.const_i32(0)
                    };
                    locals.insert(name.clone(), val);
                    if let Some(&bid) = lowering_ctx.links.export_bindings.get(name) {
                        b.store_binding(bid, val);
                    }
                    Ok(())
                }
                Stmt::VarDestruct { pattern, init } => {
                    let obj_val = lower_expr_free_async(
                        b, locals, fields, next_field, init, lowering_ctx, in_async,
                    )?;

                    for field in &pattern.fields {
                        let prop_name = match &field.key {
                            PropKey::Ident(name) => name.as_str(),
                            PropKey::Str(name) => name.as_str(),
                        };
                        let value =
                            lower_general_getprop(b, obj_val, prop_name, fields, next_field);
                        locals.insert(field.binding.clone(), value);
                        if let Some(&bid) = lowering_ctx.links.export_bindings.get(&field.binding) {
                            b.store_binding(bid, value);
                        }
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

                        locals.insert(rest_name.clone(), rest_obj);
                        if let Some(&bid) = lowering_ctx.links.export_bindings.get(rest_name) {
                            b.store_binding(bid, rest_obj);
                        }
                    }
                    Ok(())
                }
                Stmt::If {
                    cond,
                    then_b,
                    else_b,
                } => {
                    let c = lower_expr_free_async(
                        b, locals, fields, next_field, cond, lowering_ctx, in_async,
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
                // While / For / Expr … call lower_*_async respectively
                Stmt::While { cond, body } => {
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
                        b, locals, fields, next_field, cond, lowering_ctx, in_async,
                    )?;
                    b.branch(c, body_b, exit);

                    b.position_at(body_b);
                    lower_block_free_async(
                        b, locals, fields, next_field, body, lowering_ctx, in_async,
                    )?;
                    let back_args: Vec<ValueId> =
                        mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
                    b.jump(head, &back_args);

                    b.position_at(exit);
                    for (nm, p) in mut_names.into_iter().zip(phi_vals.into_iter()) {
                        locals.insert(nm, p);
                    }
                    Ok(())
                }
                Stmt::For {
                    init,
                    cond,
                    step,
                    body,
                } => {
                    if let Some(i) = init {
                        lower_stmt_free_async(
                            b, locals, fields, next_field, i, lowering_ctx, in_async,
                        )?;
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
                            b, locals, fields, next_field, e, lowering_ctx, in_async,
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

                    b.position_at(body_b);
                    lower_block_free_async(
                        b, locals, fields, next_field, body, lowering_ctx, in_async,
                    )?;
                    if let Some(se) = step {
                        let _ = lower_expr_free_async(
                            b, locals, fields, next_field, se, lowering_ctx, in_async,
                        )?;
                    }
                    let back_args: Vec<ValueId> =
                        mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
                    b.jump(head, &back_args);

                    b.position_at(exit);
                    for (nm, p) in mut_names.into_iter().zip(phi_vals.into_iter()) {
                        locals.insert(nm, p);
                    }
                    Ok(())
                }
                Stmt::Expr(e) => {
                    let _ = lower_expr_free_async(
                        b, locals, fields, next_field, e, lowering_ctx, in_async,
                    )?;
                    Ok(())
                }

                Stmt::Listen(_) => unreachable!(), // handled in the outer match arm
                Stmt::Return(_) => unreachable!(), // handled above when in_async
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

fn lower_array_method_call<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    _fields: &mut HashMap<String, FieldId>,
    _next_field: &mut u32,
    recv: &Expr,
    name: &str,
    args: &[Expr],
    lowering_ctx: &LoweringContext,
) -> LResult<Option<ValueId>> {
    use crate::wir::{Inst, Type};

    let arr = lower_expr_free(
        b,
        locals,
        _fields,
        _next_field,
        recv,
        lowering_ctx,
    )?;

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
            let n = lower_expr_free(
                b,
                locals,
                _fields,
                _next_field,
                &args[0],
                lowering_ctx
            )?;
            return cn!("wir_array_set_len", [arr, n], Some(Type::Int32));
        }
        "push" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("push expects 1 arg"));
            }
            let v = lower_expr_free(
                b,
                locals,
                _fields,
                _next_field,
                &args[0],
                lowering_ctx
            )?;
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
            let v = lower_expr_free(
                b,
                locals,
                _fields,
                _next_field,
                &args[0],
                lowering_ctx
            )?;
            return cn!("wir_array_unshift", [arr, v], Some(Type::Int32));
        }

        // ---- map: build loop in WIR, call the closure for each element
        "map" => {
            if args.len() != 1 {
                return Err(LowerError::NotLowerable("map expects 1 arg"));
            }
            let fun = lower_expr_free(
                b,
                locals,
                _fields,
                _next_field,
                &args[0],
                lowering_ctx
            )?;

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
            let fun = lower_expr_free(
                b,
                locals,
                _fields,
                _next_field,
                &args[0],
                lowering_ctx
            )?;

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
            let fun = lower_expr_free(
                b,
                locals,
                _fields,
                _next_field,
                &args[0],
                lowering_ctx
            )?;

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

            let fun = lower_expr_free(
                b,
                locals,
                _fields,
                _next_field,
                &args[0],
                lowering_ctx
            )?;

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
                let init = lower_expr_free(
                    b,
                    locals,
                    _fields,
                    _next_field,
                    &args[1],
                    lowering_ctx
                )?;
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
            let fun = lower_expr_free(
                b,
                locals,
                _fields,
                _next_field,
                &args[0],
                lowering_ctx
            )?;

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
            let fun = lower_expr_free(
                b,
                locals,
                _fields,
                _next_field,
                &args[0],
                lowering_ctx
            )?;

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

fn lower_expr_free<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    e: &Expr,
    lowering_ctx: &LoweringContext,
) -> LResult<ValueId> {
    use BinOp::*;

    match e {
        Expr::LitInt(i) => Ok(b.const_i32(*i)),
        Expr::LitF64(f) => Ok(b.const_f64(*f)),
        Expr::LitBool(v) => {
            let (_nid, res) =
                b.push_node(Inst::Const(Constant::Bool(*v)), Some(Type::Bool), 1, false);
            Ok(res[0])
        }
        Expr::LitNull => {
            let (_nid, res) = b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
            Ok(res[0])
        }
        Expr::Str(s) => {
            let (_nid, res) = b.push_node(
                Inst::Const(Constant::Str(s.clone())),
                Some(Type::Str),
                1,
                false,
            );
            Ok(res[0])
        }

        Expr::Conditional {
            cond,
            then_branch,
            else_branch,
        } => {
            let cond_v =
                lower_expr_free(b, locals, fields, next_field, cond, lowering_ctx)?;
            let then_b = b.block();
            let else_b = b.block();
            let cont = b.block();
            let res_param = b.add_block_param(cont, Type::Int32);
            b.branch(cond_v, then_b, else_b);

            b.position_at(then_b);
            let tval = lower_expr_free(
                b,
                locals,
                fields,
                next_field,
                then_branch,
                lowering_ctx
            )?;
            b.jump(cont, &[tval]);

            b.position_at(else_b);
            let fval = lower_expr_free(
                b,
                locals,
                fields,
                next_field,
                else_branch,
                lowering_ctx
            )?;
            b.jump(cont, &[fval]);

            b.position_at(cont);
            Ok(res_param)
        }

        // Allow await when inside an async lowering scope.
        Expr::Await(inner) => {
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
        Expr::FnLit { .. } => {
            return Err(LowerError::NotLowerable(
                "unhoisted function literal reached lowerer",
            ));
        }

        // locals first, else known function -> a closure with null env
        Expr::Ident(name) => {
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

            // 3) Known global function name → make a closure with null env
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
            if lowering_ctx.links.namespace_imports.contains_key(name) {
                if let Some(&cached) = locals.get(name) {
                    return Ok(cached);
                }
                // NOTE: We only have the alias here (no member BindingIds).
                //       `make_namespace` should create an object that reads provider
                //       bindings on demand (implementation-specific). If your current
                //       `make_namespace` needs the (name, BindingId) list, you'll want
                //       to run a linking pass that populates `namespace_imports[alias]`.
                let ns_obj = b.make_namespace(Vec::new());
                locals.insert(name.clone(), ns_obj);
                return Ok(ns_obj);
            }

            // Miss: unresolved identifier
            Err(LowerError::UnknownVar(name.clone()))
        }

        Expr::OptionalChain { base, access } => {
            let base_v =
                lower_expr_free(b, locals, fields, next_field, base, lowering_ctx)?;
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
                    let idx_val = lower_expr_free(
                        b, locals, fields, next_field, idx_expr, lowering_ctx,
                    )?;
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
                    match &**base {
                        Expr::GetProp { recv, .. } => {
                            this_source = Some((**recv).clone());
                        }
                        Expr::Index { recv, index } if matches!(&**index, Expr::Str(_)) => {
                            this_source = Some((**recv).clone());
                        }
                        Expr::OptionalChain {
                            base: inner,
                            access: OptionalAccess::Prop(_),
                        } => {
                            this_source = Some((**inner).clone());
                        }
                        _ => {}
                    }
                    if let Some(expr) = this_source {
                        let this_v = lower_expr_free(
                            b, locals, fields, next_field, &expr, lowering_ctx,
                        )?;
                        argv.push(this_v);
                    }
                    for arg in args {
                        argv.push(lower_expr_free(
                            b, locals, fields, next_field, arg, lowering_ctx,
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

        Expr::Group(inner) => {
            lower_expr_free(b, locals, fields, next_field, inner, lowering_ctx)
        }

        Expr::Unary { op, e } => {
            let v = lower_expr_free(b, locals, fields, next_field, e, lowering_ctx)?;
            match op {
                UnOp::Neg => {
                    let zero = b.const_i32(0);
                    Ok(b.int_bin(IntBinOp::Sub, zero, v))
                }
                UnOp::Pos => Ok(v),
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

        Expr::Binary { op, a, b: bb } => {
            let va = lower_expr_free(b, locals, fields, next_field, a, lowering_ctx)?;
            match op {
                Add => {
                    let vb =
                        lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::Add, va, vb))
                }
                Sub => {
                    let vb =
                        lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::Sub, va, vb))
                }
                Mul => {
                    let vb =
                        lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::Mul, va, vb))
                }
                Div => {
                    let vb =
                        lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::DivS, va, vb))
                }
                Rem => {
                    let vb =
                        lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    Ok(b.int_bin(IntBinOp::RemS, va, vb))
                }
                Eq | Ne | Lt | Le | Gt | Ge => {
                    let vb =
                        lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    let kind = match *op {
                        BinOp::Eq => crate::wir::CmpKind::Eq,
                        BinOp::Ne => crate::wir::CmpKind::Ne,
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
                    let vb =
                        lower_expr_free(b, locals, fields, next_field, bb, lowering_ctx)?;
                    b.jump(cont, &[vb]);

                    b.position_at(value_block);
                    b.jump(cont, &[va]);

                    b.position_at(cont);
                    Ok(res_param)
                }
            }
        }

        Expr::Assign(lv, rhs) => {
            let rv = lower_expr_free(b, locals, fields, next_field, rhs, lowering_ctx)?;
            match &**lv {
                // o.a = rv      (dot write)
                LValue::GetProp { recv, name } => {
                    let obj = lower_expr_free(
                        b, locals, fields, next_field, recv, lowering_ctx,
                    )?;

                    // Special-case: arr.length = n
                    if name == "length" {
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
                        return Ok(rv);
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

                    Ok(rv)
                }

                // o["a"] = rv     (bracket write with string)
                LValue::Index { recv, index } if matches!(index, Expr::Str(_)) => {
                    let obj = lower_expr_free(
                        b, locals, fields, next_field, recv, lowering_ctx,
                    )?;
                    let s = if let Expr::Str(s) = index {
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

                // --- inside Expr::Assign(lv, rhs) match ---
                LValue::Index { recv, index } if !matches!(index, Expr::Str(_)) => {
                    let obj = lower_expr_free(
                        b, locals, fields, next_field, recv, lowering_ctx,
                    )?;
                    let idxv = lower_expr_free(
                        b, locals, fields, next_field, index, lowering_ctx,
                    )?;

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
                LValue::Ident(name) => {
                    // Primero resuelve RHS
                    let rv = lower_expr_free(
                        b, locals, fields, next_field, rhs, lowering_ctx,
                    )?;

                    #[cfg(debug_assertions)]
                    {
                        eprintln!("lower_expr_free() LValue::Ident({})", name);
                        eprintln!(
                            "[links] exports        : {:?}",
                            lowering_ctx.links.export_bindings.keys().collect::<Vec<_>>()
                        );
                        eprintln!(
                            "[links] imports        : {:?}",
                            lowering_ctx.links.import_bindings.keys().collect::<Vec<_>>()
                        );
                        eprintln!(
                            "[links] namespace_imps : {:?}",
                            lowering_ctx.links.namespace_imports.keys().collect::<Vec<_>>()
                        );
                        eprintln!("[links] namespace_cells: {:?}", lowering_ctx.links.namespace_cells);
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
                    if let Some(&bid) = lowering_ctx.links.export_bindings.get(name) {
                        b.store_binding(bid, rv);
                        return Ok(rv);
                    }

                    // import x from "m";  x = ...  → error de compilación
                    if lowering_ctx.links.import_bindings.contains_key(name) {
                        return Err(LowerError::NotLowerable(
                            "cannot assign to imported binding",
                        ));
                    }

                    // export let x;  x = rv  → StoreBinding(binding(this,x), rv)
                    if let Some(&bid) = lowering_ctx.links.export_bindings.get(name) {
                        b.store_binding(bid, rv);
                        return Ok(rv);
                    }

                    // resto: igual que tenías (boxed locals / locals normales / error)
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
                            Err(LowerError::UnknownVar(name.clone()))
                        }
                    }
                }

                _ => Err(LowerError::NotLowerable("invalid lvalue")),
            }
        }

        // obj.<propKey>  where propKey is an identifier or string
        Expr::GetProp { recv, name } => {
            if let Expr::Ident(cn) = &**recv {
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

            // Special-case: arr.length
            if name == "length" {
                let arr =
                    lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
                let (_nid, res) = b.push_node(
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
                return Ok(res[0]);
            }

            let obj = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
            let value = lower_general_getprop(b, obj, name, fields, next_field);
            Ok(value)
        }

        // obj.<propKey> = value   (identifier or string propKey)
        Expr::SetPropObj { obj, key, value } => {
            // Normalize inputs
            let o = lower_expr_free(b, locals, fields, next_field, obj, lowering_ctx)?;
            let v = lower_expr_free(b, locals, fields, next_field, value, lowering_ctx)?;
            let field_name = match key {
                PropKey::Ident(s) => s.clone(),
                PropKey::Str(s) => s.clone(),
            };

            // If a setter "__set__<name>" exists on the object, call it as setter(obj, value)
            // and return the assigned value. Otherwise, perform default store (fast+string mirror).
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

            let z = b.const_i32(0);
            let (_nid_has_set, has_set) = b.push_node(
                Inst::CmpInt {
                    kind: crate::wir::CmpKind::Ne,
                    a: sv[0],
                    b: z,
                },
                Some(Type::Bool),
                1,
                false,
            );

            let call_set_b = b.block();
            let store_b = b.block();
            let cont = b.block();

            b.branch(has_set[0], call_set_b, store_b);

            // Use custom setter
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
            b.jump(cont, &[]);

            // Default storage path (fast field + mirror into string table)
            b.position_at(store_b);
            let field = intern_field_local(fields, next_field, &field_name);
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

            let (_nid_sc, ks) = b.push_node(
                Inst::Const(Constant::Str(field_name)),
                Some(Type::Str),
                1,
                false,
            );
            let _ = b.push_node(
                Inst::CallNative {
                    name: "wir_obj_set_str".into(),
                    args: vec![o, ks[0], v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );
            b.jump(cont, &[]);

            b.position_at(cont);
            // The expression value of an assignment is the assigned value.
            Ok(v)
        }

        // Calls / builtins
        Expr::Call { callee, args } => {
            // --- Bracket-literal method call: o["m"](... ) -> inject receiver as first arg ---
            if let Expr::Index { recv, index } = &**callee {
                if matches!(&**index, Expr::Str(_)) {
                    let this_v = lower_expr_free(
                        b, locals, fields, next_field, recv, lowering_ctx,
                    )?;
                    let fun_v = lower_expr_free(
                        b, locals, fields, next_field, callee, lowering_ctx,
                    )?;
                    let mut argv = Vec::with_capacity(args.len() + 1);
                    argv.push(this_v);
                    for a in args {
                        argv.push(lower_expr_free(
                            b, locals, fields, next_field, a, lowering_ctx,
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
            }

            // --- Property-call fast paths ---
            if let Expr::GetProp { recv, name } = &**callee {
                if let Expr::Ident(name) = &**callee {
                    if name == "import" {
                        if args.len() != 1 {
                            return Err(LowerError::NotLowerable("import(spec) expects 1 arg"));
                        }
                        let spec = lower_expr_free(
                            b, locals, fields, next_field, &args[0], lowering_ctx,
                        )?;
                        let v = b.import_dynamic(spec);
                        return Ok(v);
                    }
                }

                // 0a) Promise-style instance methods
                if name == "then" {
                    let p = lower_expr_free(
                        b, locals, fields, next_field, recv, lowering_ctx,
                    )?;
                    let z = b.const_i32(0); // sentinel "no callback"
                    let onf = if args.len() >= 1 {
                        lower_expr_free(
                            b, locals, fields, next_field, &args[0], lowering_ctx,
                        )?
                    } else {
                        z
                    };
                    let onr = if args.len() >= 2 {
                        lower_expr_free(
                            b, locals, fields, next_field, &args[1], lowering_ctx,
                        )?
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
                    let p = lower_expr_free(
                        b, locals, fields, next_field, recv, lowering_ctx,
                    )?;
                    let z = b.const_i32(0);
                    let onr = if args.len() >= 1 {
                        lower_expr_free(
                            b, locals, fields, next_field, &args[0], lowering_ctx,
                        )?
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
                    let p = lower_expr_free(
                        b, locals, fields, next_field, recv, lowering_ctx,
                    )?;
                    let (_nid, nul) =
                        b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                    let val = if args.len() >= 1 {
                        lower_expr_free(
                            b, locals, fields, next_field, &args[0], lowering_ctx,
                        )?
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
                    let p = lower_expr_free(
                        b, locals, fields, next_field, recv, lowering_ctx
                    )?;
                    let (_nid, nul) =
                        b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                    let reason = if args.len() >= 1 {
                        lower_expr_free(
                            b, locals, fields, next_field, &args[0], lowering_ctx
                        )?
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

                // 0b) http.* helpers — IMPORTANT: this branch does NOT lower `recv`
                if let Expr::Ident(obj) = &**recv {
                    if obj == "http" {
                        match name.as_str() {
                            "startStream" => {
                                if args.len() != 3 {
                                    return Err(LowerError::NotLowerable(
                                        "http.startStream(req, status, headers)",
                                    ));
                                }
                                let req = lower_expr_free(
                                    b, locals, fields, next_field, &args[0], lowering_ctx 
                                )?;
                                let status = lower_expr_free(
                                    b, locals, fields, next_field, &args[1], lowering_ctx 
                                )?;
                                let hdrs = lower_expr_free(
                                    b, locals, fields, next_field, &args[2], lowering_ctx 
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
                                    b, locals, fields, next_field, &args[0], lowering_ctx 
                                )?;
                                let rid = lower_expr_free(
                                    b, locals, fields, next_field, &args[1], lowering_ctx 
                                )?;
                                let chunk = lower_expr_free(
                                    b, locals, fields, next_field, &args[2], lowering_ctx 
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
                                    b, locals, fields, next_field, &args[0], lowering_ctx 
                                )?;
                                let rid = lower_expr_free(
                                    b, locals, fields, next_field, &args[1], lowering_ctx 
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

                // 0c) STATIC CLASS METHODS — check BEFORE anything that would lower `recv`
                if let Expr::Ident(cn) = &**recv {
                    if let Some(&fid) = lowering_ctx.funcs.get(&format!("__static_{}_{}", cn, name)) {
                        #[cfg(debug_assertions)]
                        {
                            eprintln!("[static] candidate {}.{}", cn, name);
                        }

                        let mut argv = Vec::with_capacity(args.len());
                        for a in args {
                            argv.push(lower_expr_free(
                                b, locals, fields, next_field, a, lowering_ctx 
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

                // 0d) Array instance methods (map/filter/etc.) — AFTER static check (this lowers `recv`)
                if let Some(v) = lower_array_method_call(
                    b, locals, fields, next_field, recv, name, args, lowering_ctx 
                )? {
                    return Ok(v);
                }

                // 0e) Generic property call: inject receiver as implicit first arg ("this")
                let this_v =
                    lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
                let fun_v = lower_expr_free(
                    b, locals, fields, next_field, callee, lowering_ctx 
                )?;
                let mut argv = Vec::with_capacity(args.len() + 1);
                argv.push(this_v);
                for a in args {
                    argv.push(lower_expr_free(
                        b, locals, fields, next_field, a, lowering_ctx 
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

            // 0f) Bracket-call: o["m"](...)
            // - If recv is a class ident and key is a string matching a static, direct-call it.
            // - Else, if key is a string at runtime, inject `this`.
            // - Otherwise treat as array[index] function call (no `this`).
            if let Expr::Index { recv, index } = &**callee {
                // Static: Class["M"](...)
                if let (Expr::Ident(cn), Expr::Str(m)) = (&**recv, &**index) {
                    if let Some(&fid) = lowering_ctx.funcs.get(&format!("__static_{}_{}", cn, m)) {
                        let mut argv = Vec::with_capacity(args.len());
                        for a in args {
                            argv.push(lower_expr_free(
                                b, locals, fields, next_field, a, lowering_ctx 
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
                let obj =
                    lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
                let idxv =
                    lower_expr_free(b, locals, fields, next_field, index, lowering_ctx)?;
                let mut argvals = Vec::with_capacity(args.len());
                for a in args {
                    argvals.push(lower_expr_free(
                        b, locals, fields, next_field, a, lowering_ctx 
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
            if let Expr::Ident(name) = &**callee {
                // Timers
                if name == "setTimeout" {
                    if args.len() != 2 {
                        return Err(LowerError::NotLowerable("setTimeout(fn, ms)"));
                    }
                    let fun = lower_expr_free(
                        b, locals, fields, next_field, &args[0], lowering_ctx,
                    )?;
                    let ms = lower_expr_free(
                        b, locals, fields, next_field, &args[1], lowering_ctx,
                    )?;
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
                    let fun = lower_expr_free(
                        b, locals, fields, next_field, &args[0], lowering_ctx,
                    )?;
                    let ms = lower_expr_free(
                        b, locals, fields, next_field, &args[1], lowering_ctx,
                    )?;
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
                    let id = lower_expr_free(
                        b, locals, fields, next_field, &args[0], lowering_ctx,
                    )?;
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
                    let id = lower_expr_free(
                        b, locals, fields, next_field, &args[0], lowering_ctx,
                    )?;
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
                    let len = lower_expr_free(
                        b, locals, fields, next_field, &args[0], lowering_ctx,
                    )?;
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
                    let exec = lower_expr_free(
                        b, locals, fields, next_field, &args[0], lowering_ctx,
                    )?;
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
                    let url = lower_expr_free(
                        b, locals, fields, next_field, &args[0], lowering_ctx,
                    )?;
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
                    let url = lower_expr_free(
                        b, locals, fields, next_field, &args[0], lowering_ctx,
                    )?;
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
                    let url = lower_expr_free(
                        b, locals, fields, next_field, &args[0], lowering_ctx,
                    )?;
                    let body = lower_expr_free(
                        b, locals, fields, next_field, &args[1], lowering_ctx,
                    )?;
                    let (_nid, nul) =
                        b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                    let headers = if args.len() == 3 {
                        lower_expr_free(
                            b, locals, fields, next_field, &args[2], lowering_ctx,
                        )?
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
                                b, locals, fields, next_field, &args[0], lowering_ctx,
                            )?;
                            let status = b.const_i32(200);
                            (status, body, nul[0])
                        }
                        2 => {
                            let status = lower_expr_free(
                                b, locals, fields, next_field, &args[0], lowering_ctx,
                            )?;
                            let body = lower_expr_free(
                                b, locals, fields, next_field, &args[1], lowering_ctx,
                            )?;
                            (status, body, nul[0])
                        }
                        3 => {
                            let status = lower_expr_free(
                                b, locals, fields, next_field, &args[0], lowering_ctx,
                            )?;
                            let body = lower_expr_free(
                                b, locals, fields, next_field, &args[1], lowering_ctx,
                            )?;
                            let headers = lower_expr_free(
                                b, locals, fields, next_field, &args[2], lowering_ctx,
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
                    if matches!(args[0], Expr::Str(_)) {
                        let v = lower_expr_free(
                            b, locals, fields, next_field, &args[0], lowering_ctx,
                        )?;
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
                    let v = lower_expr_free(
                        b, locals, fields, next_field, &args[0], lowering_ctx,
                    )?;
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
                            b, locals, fields, next_field, a, lowering_ctx,
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
            let funv = lower_expr_free(
                b, locals, fields, next_field, callee, lowering_ctx,
            )?;
            let mut argv = Vec::with_capacity(args.len());
            for a in args {
                argv.push(lower_expr_free(
                    b, locals, fields, next_field, a, lowering_ctx,
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

        Expr::This => {
            if let Some(&v) = locals.get("this") {
                Ok(v)
            } else {
                Err(LowerError::UnknownVar("this".into()))
            }
        }

        Expr::SuperProp(_) => {
            return Err(LowerError::NotLowerable(
                "`super.prop` is only valid when called: use `super.prop(...)`",
            ));
        }
        Expr::SuperCall(_) => {
            return Err(LowerError::NotLowerable(
                "`super(...)` is only valid in a derived constructor",
            ));
        }

        Expr::New { class, args } => {
            #[cfg(debug_assertions)]
            {
                eprintln!(
                    "[new] trying to resolve class {:?} via import/export/namespace",
                    class
                );
            }

            // 1) ruta local (como ya tenías)
            let fname = format!("__class_new_{}", class);
            if let Some(&fid) = lowering_ctx.funcs.get(&fname) {
                let mut argv = Vec::with_capacity(args.len());
                for a in args {
                    argv.push(lower_expr_free(
                        b, locals, fields, next_field, a, lowering_ctx 
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
                eprintln!("lower_expr_free() Expr::Call(...) Expr::New({})", class);
                eprintln!(
                    "[links] exports        : {:?}",
                    lowering_ctx.links.export_bindings.keys().collect::<Vec<_>>()
                );
                eprintln!(
                    "[links] imports        : {:?}",
                    lowering_ctx.links.import_bindings.keys().collect::<Vec<_>>()
                );
                eprintln!(
                    "[links] namespace_imps : {:?}",
                    lowering_ctx.links.namespace_imports.keys().collect::<Vec<_>>()
                );
                eprintln!("[links] namespace_cells: {:?}", lowering_ctx.links.namespace_cells);
            }

            // 2) ruta IMPORTADA/EXPORTADA: el identificador 'class' es un binding a un "class object"
            if let Some(&bid) = lowering_ctx.links
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
                        b, locals, fields, next_field, a, lowering_ctx 
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

        Expr::Index { recv, index } => {
            // If index is a string literal, prefer string-table FIRST, then fast-field as a fallback.
            if let Expr::Str(s) = &**index {
                let obj =
                    lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;

                // string path first
                let (_nid_sc, ks) = b.push_node(
                    Inst::Const(Constant::Str(s.clone())),
                    Some(Type::Str),
                    1,
                    false,
                );
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
                let cont = b.block();
                let out = b.add_block_param(cont, Type::Int32);

                b.branch(has_str[0], str_hit, try_fast);

                b.position_at(str_hit);
                let (_nid_s, sv) = b.push_node(
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

                // fallback: fast field (works when literal and same lowering context)
                b.position_at(try_fast);
                let field = intern_field_local(fields, next_field, s);
                let fid_smi = b.const_i32(field.0 as i32);
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
                let miss = b.block();
                b.branch(hasf[0], fast_b, miss);

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

                b.position_at(miss);
                let z = b.const_i32(0);
                b.jump(cont, &[z]);

                b.position_at(cont);
                return Ok(out);
            }

            // Generic path: decide at runtime. If index is a string → object["key"]; else → array[index].
            let obj = lower_expr_free(b, locals, fields, next_field, recv, lowering_ctx)?;
            let idxv =
                lower_expr_free(b, locals, fields, next_field, index, lowering_ctx)?;

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

            // object["key"]  — dynamic string path (no fast-field here; we can't safely pick a FieldId)
            b.position_at(str_b);
            let (_nid_hs, sv) = b.push_node(
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
            b.jump(cont, &[sv[0]]);

            // array[index]
            b.position_at(arr_b);
            let (_nid_a, av) = b.push_node(
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
            b.jump(cont, &[av[0]]);

            b.position_at(cont);
            Ok(out)
        }

        Expr::ArrayLit(elems) => {
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
        Expr::FnRef { name } => {
            let fid = *lowering_ctx.funcs
                .get(name)
                .ok_or_else(|| LowerError::UnknownFunc(name.clone()))?;
            let caps = lowering_ctx.lam_captures.get(name).cloned().unwrap_or_default();

            // For each capture, if it is not boxed yet in this scope, box it now:
            //   box = Array(1); box[0] = current_value; rebind local to box; mark boxed.
            for cap in &caps {
                if locals.get(&boxed_key(cap)).is_none() {
                    let cur = *locals
                        .get(cap)
                        .ok_or_else(|| LowerError::UnknownVar(cap.into()))?;
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
                    locals.insert(cap.clone(), box_arr);
                    locals.insert(boxed_key(cap), box_arr);
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

        Expr::ObjLit(items) => {
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
                        let v = lower_expr_free(
                            b, locals, fields, next_field, val_e, lowering_ctx 
                        )?;
                        match key {
                            PropKey::Ident(name) => {
                                let field = intern_field_local(fields, next_field, &name);
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
                            }
                            PropKey::Str(s) => {
                                let (_nid, ks) = b.push_node(
                                    Inst::Const(Constant::Str(s.clone())),
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
                    ObjItem::Spread(expr) => {
                        let spread_obj = lower_expr_free(
                            b, locals, fields, next_field, expr, lowering_ctx 
                        )?;
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

        Expr::DeleteProp { obj, key } => {
            let o = lower_expr_free(b, locals, fields, next_field, obj, lowering_ctx)?;

            match key {
                // delete o.a  — delete both field and string
                PropKey::Ident(name) => {
                    let field = intern_field_local(fields, next_field, name);
                    let fid_smi = b.const_i32(field.0 as i32);

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
                    let (_nid_sc, ks) = b.push_node(
                        Inst::Const(Constant::Str(name.clone())),
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

                    Ok(rs[0]) // return last result (truthy if deleted)
                }

                // delete o["a"] — delete both string and field
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

        Expr::In { key, obj } => {
            let o = lower_expr_free(b, locals, fields, next_field, obj, lowering_ctx)?;

            match &**key {
                // identifier key:  a in o
                Expr::Ident(name) => {
                    let field = intern_field_local(fields, next_field, name);
                    let fid_smi = b.const_i32(field.0 as i32);

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
                    let (_nid_sc, ks) = b.push_node(
                        Inst::Const(Constant::Str(name.clone())),
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

                // string-literal key:  "a" in o
                Expr::Str(s) => {
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

        _ => Err(LowerError::NotLowerable("expression type not supported")),
    }
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

        for (name, &bid) in &links.export_bindings {
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
                let alloc = self.lowering_ctx.funcs.get(&format!("__class_new_{}", name)).copied();
                let mut statics = Vec::new();
                for (mname, _, _, _) in &ci.static_methods {
                    if let Some(&sfid) = self.lowering_ctx.funcs.get(&format!("__static_{}_{}", name, mname)) {
                        statics.push((mname.clone(), sfid));
                    }
                }
                class_exports.push((bid, alloc, statics));
                continue;
            }
            #[cfg(debug_assertions)]
            eprintln!(
                "[modinit] export {:?}: no es func/clase local (vars se materializan via Stmt::Var en __toplevel__)",
                name
            );
        }

        // ---- Cuerpo de la función (sólo muta self.module) ----
        let func = {
            let mut b = Builder::new(self.module, "__modinit__", vec![], vec![Type::Int32]);

            // 0) Inicializa SOLO las celdas de export de este módulo a `undefined` (TDZ-safe).
            //    NO tocar import_bindings: son celdas del proveedor.
            let undef = b.const_undef();
            for &bid in links.export_bindings.values() {
                b.store_binding(bid, undef);
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

            // 2) Materializa clases exportadas: objeto con 'new' + estáticos; luego publícalo
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
            //    Esto sólo escribe en nuestras celdas de namespace (locales), no en el proveedor.
            for (ns, exports) in &links.namespace_imports {
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
        let ci = self.lowering_ctx.classes.get(cname).expect("class collected").clone();

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

        // 4) Ctor (optional) — must share the same field-id map
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

        // 6) Allocator — also installs method closures onto the instance
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

            if is_async {
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
                    true
                )?;

                if !b.current_block_terminated() {
                    let zero = b.const_i32(0);
                    let (_nid, _) = b.push_node(
                        Inst::CallNative {
                            name: "wir_deferred_resolve".into(),
                            args: vec![d, zero],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    b.ret(&[d]);
                }
            } else {
                lower_block_free(
                    &mut b,
                    &mut locals,
                    &mut fields,
                    &mut next_field,
                    body,
                    &self.lowering_ctx
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
        // Resolve base class name once (if any). We’ll still rewrite even if there is none;
        // in that case unknown-func errors will be raised later if user wrote `super`.
        let base_opt = self.lowering_ctx.classes.get(class_name).and_then(|ci| ci.base.clone());

        fn rw_block<F: Fn(&Expr) -> Expr + Copy>(b: &Block, f: F) -> Block {
            Block {
                stmts: b.stmts.iter().map(|s| rw_stmt(s, f)).collect(),
            }
        }
        fn rw_stmt<F: Fn(&Expr) -> Expr + Copy>(s: &Stmt, f: F) -> Stmt {
            match s {
                Stmt::Var { name, init } => Stmt::Var {
                    name: name.clone(),
                    init: init.as_ref().map(|e| rw_expr(e, f)),
                },
                Stmt::VarDestruct { pattern, init } => Stmt::VarDestruct {
                    pattern: pattern.clone(),
                    init: rw_expr(init, f),
                },
                Stmt::If {
                    cond,
                    then_b,
                    else_b,
                } => Stmt::If {
                    cond: rw_expr(cond, f),
                    then_b: rw_block(then_b, f),
                    else_b: else_b.as_ref().map(|b| rw_block(b, f)),
                },
                Stmt::While { cond, body } => Stmt::While {
                    cond: rw_expr(cond, f),
                    body: rw_block(body, f),
                },
                Stmt::For {
                    init,
                    cond,
                    step,
                    body,
                } => Stmt::For {
                    init: init.as_deref().map(|i| SmallBox::new(rw_stmt(i, f))),
                    cond: cond.as_ref().map(|e| rw_expr(e, f)),
                    step: step.as_ref().map(|e| rw_expr(e, f)),
                    body: rw_block(body, f),
                },
                Stmt::Return(e) => Stmt::Return(e.as_ref().map(|x| rw_expr(x, f))),
                Stmt::Expr(e) => Stmt::Expr(rw_expr(e, f)),
                Stmt::Listen(ld) => {
                    let routes = ld
                        .routes
                        .iter()
                        .map(|r| RouteDecl {
                            method: r.method.clone(),
                            pattern: rw_expr(&r.pattern, f),
                            handler: rw_expr(&r.handler, f),
                        })
                        .collect();
                    Stmt::Listen(ListenDecl {
                        addr: ld.addr.clone(),
                        routes,
                    })
                }
            }
        }
        fn rw_expr<F: Fn(&Expr) -> Expr + Copy>(e: &Expr, f: F) -> Expr {
            use Expr::*;
            let m = f(e);
            if !std::mem::discriminant(&m).eq(&std::mem::discriminant(e)) {
                // f() replaced the node entirely (e.g. super-rewrite) – don’t recurse
                return m;
            }
            match m {
                Assign(ref lv, ref rhs) => Expr::Assign(lv.clone(), SmallBox::new(rw_expr(rhs, f))),
                Binary { op, ref a, ref b } => Expr::Binary {
                    op,
                    a: SmallBox::new(rw_expr(a, f)),
                    b: SmallBox::new(rw_expr(b, f)),
                },
                Unary { op, ref e } => Expr::Unary {
                    op,
                    e: SmallBox::new(rw_expr(e, f)),
                },
                Call {
                    ref callee,
                    ref args,
                } => Expr::Call {
                    callee: SmallBox::new(rw_expr(callee, f)),
                    args: args.iter().map(|x| rw_expr(x, f)).collect(),
                },
                GetProp { ref recv, ref name } => Expr::GetProp {
                    recv: SmallBox::new(rw_expr(recv, f)),
                    name: name.clone(),
                },
                Index {
                    ref recv,
                    ref index,
                } => Expr::Index {
                    recv: SmallBox::new(rw_expr(recv, f)),
                    index: SmallBox::new(rw_expr(index, f)),
                },
                Group(ref g) => Expr::Group(SmallBox::new(rw_expr(g, f))),
                ArrayLit(ref es) => Expr::ArrayLit(es.iter().map(|x| rw_expr(x, f)).collect()),
                ObjLit(ref items) => Expr::ObjLit(
                    items
                        .iter()
                        .map(|item| match item {
                            ObjItem::Prop(k, v) => ObjItem::Prop(k.clone(), rw_expr(v, f)),
                            ObjItem::Spread(expr) => ObjItem::Spread(rw_expr(expr, f)),
                        })
                        .collect(),
                ),
                GetPropObj { ref obj, ref key } => Expr::GetPropObj {
                    obj: SmallBox::new(rw_expr(obj, f)),
                    key: key.clone(),
                },
                SetPropObj {
                    ref obj,
                    ref key,
                    ref value,
                } => Expr::SetPropObj {
                    obj: SmallBox::new(rw_expr(obj, f)),
                    key: key.clone(),
                    value: SmallBox::new(rw_expr(value, f)),
                },
                In { ref key, ref obj } => Expr::In {
                    key: SmallBox::new(rw_expr(key, f)),
                    obj: SmallBox::new(rw_expr(obj, f)),
                },
                DeleteProp { ref obj, ref key } => Expr::DeleteProp {
                    obj: SmallBox::new(rw_expr(obj, f)),
                    key: key.clone(),
                },
                Await(ref inner) => Expr::Await(SmallBox::new(rw_expr(inner, f))),
                // terminals and simple refs
                _ => m,
            }
        }

        // Rewriter: (super(...)) and (super.m)(...) → direct calls with implicit `this`
        let class_name = class_name.to_string();

        let f = |e: &Expr| -> Expr {
            match e {
                // super(args...)  →  __ctor_Base(this, args...)  (only if there *is* a base)
                Expr::SuperCall(args) => {
                    if let Some(ref base) = base_opt {
                        let mut new_args = Vec::with_capacity(args.len() + 1);
                        new_args.push(Expr::This);
                        new_args.extend(args.iter().cloned());
                        Expr::Call {
                            callee: SmallBox::new(Expr::Ident(format!("__ctor_{}", base))),
                            args: new_args,
                        }
                    } else {
                        e.clone() // leave for lowerer to complain
                    }
                }

                // (super.m)(args...)  →  __method_Base_m(this, args...)  (only if base exists)
                Expr::Call { callee, args } => {
                    if let Expr::SuperProp(m) = &**callee {
                        if let Some(ref base) = base_opt {
                            let mut new_args = Vec::with_capacity(args.len() + 1);
                            new_args.push(Expr::This);
                            new_args.extend(args.iter().cloned());
                            Expr::Call {
                                callee: SmallBox::new(Expr::Ident(format!(
                                    "__method_{}_{}",
                                    base, m
                                ))),
                                args: new_args,
                            }
                        } else {
                            e.clone()
                        }
                    } else {
                        e.clone()
                    }
                }

                // Value-position super.m stays as-is so the lowerer raises your existing error.
                Expr::SuperProp(_) => e.clone(),

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

            if is_async {
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
                )?;

                // Fallthrough: if the body didn’t explicitly return, resolve with 0 and return d.
                if !b.current_block_terminated() {
                    let zero = b.const_i32(0);
                    let (_nid, _) = b.push_node(
                        Inst::CallNative {
                            name: "wir_deferred_resolve".into(),
                            args: vec![d, zero],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    b.ret(&[d]);
                }
            } else {
                // --- Sync path (what you already had), but sharing the CLASS field-id map
                lower_block_free(
                    &mut b,
                    &mut locals,
                    fields,
                    next_field,
                    &body_rw,
                    &self.lowering_ctx
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

        // Collect base chain names from root → ... → direct base (so overrides later will win)
        let mut base_chain: Vec<String> = Vec::new();
        let mut cur = ci.base.clone();
        while let Some(bn) = cur {
            base_chain.push(bn.clone());
            cur = self.lowering_ctx.classes.get(&bn).and_then(|x| x.base.clone());
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
                        if let Some(&mfid) = self.lowering_ctx.funcs.get(&format!("__method_{}_{}", bn, mname)) {
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
                            if let Some(&gid) = self.lowering_ctx.funcs.get(&format!("__get_{}_{}", bn, pname)) {
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
                            if let Some(&sid) = self.lowering_ctx.funcs.get(&format!("__set_{}_{}", bn, pname)) {
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
                if let Some(&mfid) = self.lowering_ctx.funcs.get(&format!("__method_{}_{}", ci.name, mname)) {
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
                    if let Some(&gid) = self.lowering_ctx.funcs.get(&format!("__get_{}_{}", ci.name, pname)) {
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
                    if let Some(&sid) = self.lowering_ctx.funcs.get(&format!("__set_{}_{}", ci.name, pname)) {
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
                        &self.lowering_ctx
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
