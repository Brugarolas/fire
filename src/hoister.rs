// src/lowerer.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::helpers::collections::{HashMap, HashSet};
use logos::Logos;
use smallbox::SmallBox;
use std::collections::hash_map::Entry;
use std::{collections::BTreeSet, ops::Deref};
use tinyvec::TinyVec;

// Bring in the WIR types from your other file/module.
use crate::wir::{
    AccessorInfo, BindingId, Builder, Constant, FieldId, FuncId, Inst, IntBinOp, MethodInfo,
    Module, Type, ValueId, next_id,
};

use crate::diag::Node;
use crate::front::{
    BinOp, Block, CatchClause, ClassDecl, ClassMember, DeferKind, ExportDecl, Expr, ExprKind,
    FuncDecl, ImportDecl, ImportItem, LValue, LValueKind, ListenDecl, ObjItem, ObjPattern,
    OptionalAccess, Program, PropKey, RouteDecl, Stmt, StmtKind, UnOp,
};

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

/// Hoist all function literals to top-level functions, replacing them with
pub fn hoist_fn_lits_program(prog: &Program) -> (Program, HashMap<String, Vec<String>>) {
    // name -> sorted capture list (stable order)
    let mut lam_captures: HashMap<String, Vec<String>> = HashMap::new();

    // Generate unique lam names avoiding collisions with existing functions.
    let mut used: BTreeSet<String> = prog.functions.iter().map(|f| f.name.clone()).collect();
    let mut counter: u32 = 0;
    fn fresh(used: &mut BTreeSet<String>, counter: &mut u32) -> String {
        loop {
            let name = format!("__lam_{}", *counter);
            *counter += 1;
            if used.insert(name.clone()) {
                return name;
            }
        }
    }

    fn insert_pattern_bindings(set: &mut BTreeSet<String>, pattern: &ObjPattern) {
        for field in &pattern.fields {
            set.insert(field.binding.clone());
        }
        if let Some(rest) = &pattern.rest {
            set.insert(rest.clone());
        }
    }

    // Collect {defs, uses} inside a block
    fn collect_defs_uses_block(
        b: &Block,
        defs: &mut BTreeSet<String>,
        uses: &mut BTreeSet<String>,
    ) {
        for s in &b.stmts {
            collect_defs_uses_stmt(s, defs, uses);
        }
    }
    fn collect_defs_uses_stmt(s: &Stmt, defs: &mut BTreeSet<String>, uses: &mut BTreeSet<String>) {
        match &s.kind {
            StmtKind::Enum { name, init, .. } => {
                defs.insert(name.clone());
                collect_uses_expr(init, uses);
            }
            StmtKind::Var { name, init } => {
                defs.insert(name.clone());
                if let Some(e) = init {
                    collect_uses_expr(e, uses);
                }
            }
            StmtKind::VarDestruct { pattern, init } => {
                insert_pattern_bindings(defs, pattern);
                collect_uses_expr(init, uses);
            }
            StmtKind::If {
                cond,
                then_b,
                else_b,
            } => {
                collect_uses_expr(cond, uses);
                collect_defs_uses_block(then_b, defs, uses);
                if let Some(b) = else_b {
                    collect_defs_uses_block(b, defs, uses);
                }
            }
            StmtKind::While { cond, body } => {
                collect_uses_expr(cond, uses);
                collect_defs_uses_block(body, defs, uses);
            }
            StmtKind::For {
                init,
                cond,
                step,
                body,
            } => {
                if let Some(i) = init.as_deref() {
                    collect_defs_uses_stmt(i, defs, uses);
                }
                if let Some(c) = cond {
                    collect_uses_expr(c, uses);
                }
                if let Some(st) = step {
                    collect_uses_expr(st, uses);
                }
                collect_defs_uses_block(body, defs, uses);
            }
            StmtKind::Return(e) => {
                if let Some(e) = e {
                    collect_uses_expr(e, uses);
                }
            }
            StmtKind::Try {
                try_block,
                catch,
                finally_block,
            } => {
                collect_defs_uses_block(try_block, defs, uses);
                if let Some(c) = catch {
                    if let Some(binding) = &c.binding {
                        defs.insert(binding.clone());
                    }
                    collect_defs_uses_block(&c.body, defs, uses);
                }
                if let Some(fin) = finally_block {
                    collect_defs_uses_block(fin, defs, uses);
                }
            }
            StmtKind::Throw(expr) => collect_uses_expr(expr, uses),
            StmtKind::Defer { binding, body, .. } => {
                let mut cleanup_defs = BTreeSet::new();
                let mut cleanup_uses = BTreeSet::new();
                collect_defs_uses_block(body, &mut cleanup_defs, &mut cleanup_uses);
                if let Some(binding) = binding {
                    cleanup_defs.insert(binding.clone());
                }
                uses.extend(cleanup_uses.difference(&cleanup_defs).cloned());
            }
            StmtKind::Expr(e) => collect_uses_expr(e, uses),
            StmtKind::Listen(ld) => {
                for r in &ld.routes {
                    collect_uses_expr(&r.pattern, uses);
                    collect_uses_expr(&r.handler, uses);
                }
            }
        }
    }

    fn collect_uses_expr(e: &Expr, uses: &mut BTreeSet<String>) {
        match &e.kind {
            ExprKind::Ident(s) => {
                uses.insert(s.clone());
            }
            ExprKind::Assign(lv, rhs) => {
                match &lv.kind {
                    LValueKind::Ident(s) => {
                        uses.insert(s.clone());
                    }
                    LValueKind::GetProp { recv, .. } => collect_uses_expr(recv, uses),
                    LValueKind::Index { recv, index } => {
                        collect_uses_expr(recv, uses);
                        collect_uses_expr(index, uses);
                    }
                }
                collect_uses_expr(rhs, uses);
            }
            ExprKind::Binary { a, b, .. } => {
                collect_uses_expr(a, uses);
                collect_uses_expr(b, uses);
            }
            ExprKind::Unary { e, .. } => {
                collect_uses_expr(e, uses);
            }
            ExprKind::Call { callee, args } => {
                collect_uses_expr(callee, uses);
                for a in args {
                    collect_uses_expr(a, uses);
                }
            }
            ExprKind::GetProp { recv, .. } => collect_uses_expr(recv, uses),
            ExprKind::Index { recv, index } => {
                collect_uses_expr(recv, uses);
                collect_uses_expr(index, uses);
            }
            ExprKind::Group(g) => collect_uses_expr(g, uses),
            ExprKind::FnLit { .. } | ExprKind::FnRef { .. } => { /* handled at outer level */ }
            ExprKind::LitInt(_)
            | ExprKind::LitF64(_)
            | ExprKind::LitBool(_)
            | ExprKind::LitNull
            | ExprKind::Str(_) => {}

            ExprKind::ArrayLit(elems) => {
                for el in elems {
                    collect_uses_expr(el, uses);
                }
            }

            ExprKind::ObjLit(items) => {
                for item in items {
                    match item {
                        ObjItem::Prop(_, value) => collect_uses_expr(value, uses),
                        ObjItem::Spread(expr) => collect_uses_expr(expr, uses),
                    }
                }
            }

            ExprKind::GetPropObj { obj, .. } => {
                collect_uses_expr(obj, uses);
            }

            ExprKind::SetPropObj { obj, value, .. } => {
                collect_uses_expr(obj, uses);
                collect_uses_expr(value, uses);
            }

            ExprKind::In { key, obj } => {
                collect_uses_expr(key, uses);
                collect_uses_expr(obj, uses);
            }

            ExprKind::DeleteProp { obj, .. } => {
                collect_uses_expr(obj, uses);
            }

            ExprKind::SuperProp(_) => { /* no local uses */ }
            ExprKind::SuperCall(args) => {
                for a in args {
                    collect_uses_expr(a, uses);
                }
            }

            ExprKind::CreateBuiltin { args, .. } => {
                for a in args {
                    collect_uses_expr(a, uses);
                }
            }
            ExprKind::CallBuiltinMapMethod { recv, args, .. } => {
                collect_uses_expr(recv, uses);
                for a in args {
                    collect_uses_expr(a, uses);
                }
            }
            ExprKind::CallBuiltinSetMethod { recv, args, .. } => {
                collect_uses_expr(recv, uses);
                for a in args {
                    collect_uses_expr(a, uses);
                }
            }

            _ => { /* other expr types have no uses */ }
        }
    }

    // Rewrite helpers
    fn rw_block(
        b: &Block,
        used: &mut BTreeSet<String>,
        counter: &mut u32,
        enclosing_locals: &BTreeSet<String>,
        out_funcs: &mut Vec<FuncDecl>,
        lam_caps_out: &mut HashMap<String, Vec<String>>,
    ) -> Block {
        // Start with the incoming scope, then extend as we see new `var`s.
        let mut scope = enclosing_locals.clone();
        let mut out_stmts = Vec::with_capacity(b.stmts.len());

        for s in &b.stmts {
            match &s.kind {
                StmtKind::Enum {
                    name,
                    binding,
                    init,
                } => {
                    let init = rw_expr(init, used, counter, &scope, out_funcs, lam_caps_out);
                    out_stmts.push(stmt_with_meta(
                        s,
                        StmtKind::Enum {
                            name: name.clone(),
                            binding: *binding,
                            init,
                        },
                    ));
                    scope.insert(name.clone());
                }
                // `var` introduces a name *after* its initializer; rewrite init with current scope,
                // then add the binding to the scope for following statements.
                StmtKind::Var { name, init } => {
                    let init_rw = init
                        .as_ref()
                        .map(|e| rw_expr(e, used, counter, &scope, out_funcs, lam_caps_out));
                    out_stmts.push(stmt_with_meta(
                        s,
                        StmtKind::Var {
                            name: name.clone(),
                            init: init_rw,
                        },
                    ));
                    scope.insert(name.clone());
                }
                StmtKind::VarDestruct { pattern, init } => {
                    let init_rw = rw_expr(init, used, counter, &scope, out_funcs, lam_caps_out);
                    out_stmts.push(stmt_with_meta(
                        s,
                        StmtKind::VarDestruct {
                            pattern: pattern.clone(),
                            init: init_rw,
                        },
                    ));
                    insert_pattern_bindings(&mut scope, pattern);
                }

                // `for` init can introduce a name that is visible to cond/step/body.
                StmtKind::For {
                    init,
                    cond,
                    step,
                    body,
                } => {
                    // The `for` sub-scope starts from the scope *before* the loop,
                    // then (if init is a `var`) it gains that binding.
                    let mut for_scope = scope.clone();

                    let init_rw = if let Some(i0) = init.as_deref() {
                        // Rewrite the init using the current for_scope.
                        let rewritten = SmallBox::new(rw_stmt(
                            i0,
                            used,
                            counter,
                            &for_scope,
                            out_funcs,
                            lam_caps_out,
                        ));
                        // If the init is `var id = ...;`, extend for_scope for the rest.
                        match &i0.kind {
                            StmtKind::Var { name, .. } => {
                                for_scope.insert(name.clone());
                            }
                            StmtKind::VarDestruct { pattern, .. } => {
                                insert_pattern_bindings(&mut for_scope, pattern);
                            }
                            _ => {}
                        }
                        Some(rewritten)
                    } else {
                        None
                    };

                    let cond_rw = cond
                        .as_ref()
                        .map(|e| rw_expr(e, used, counter, &for_scope, out_funcs, lam_caps_out));
                    let step_rw = step
                        .as_ref()
                        .map(|e| rw_expr(e, used, counter, &for_scope, out_funcs, lam_caps_out));
                    let body_rw =
                        rw_block(body, used, counter, &for_scope, out_funcs, lam_caps_out);

                    out_stmts.push(stmt_with_meta(
                        s,
                        StmtKind::For {
                            init: init_rw,
                            cond: cond_rw,
                            step: step_rw,
                            body: body_rw,
                        },
                    ));
                }

                // Everything else: rewrite with the current scope.
                _ => {
                    let srw = rw_stmt(s, used, counter, &scope, out_funcs, lam_caps_out);
                    out_stmts.push(srw);
                }
            }
        }

        Block { stmts: out_stmts }
    }

    fn rw_stmt(
        s: &Stmt,
        used: &mut BTreeSet<String>,
        counter: &mut u32,
        enclosing_locals: &BTreeSet<String>,
        out_funcs: &mut Vec<FuncDecl>,
        lam_caps_out: &mut HashMap<String, Vec<String>>,
    ) -> Stmt {
        match &s.kind {
            StmtKind::Enum {
                name,
                binding,
                init,
            } => stmt_with_meta(
                s,
                StmtKind::Enum {
                    name: name.clone(),
                    binding: *binding,
                    init: rw_expr(init, used, counter, enclosing_locals, out_funcs, lam_caps_out),
                },
            ),
            StmtKind::Var { name, init } => {
                let init_rw = init.as_ref().map(|expr| {
                    rw_expr(
                        expr,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )
                });
                stmt_with_meta(
                    s,
                    StmtKind::Var {
                        name: name.clone(),
                        init: init_rw,
                    },
                )
            }
            StmtKind::VarDestruct { pattern, init } => stmt_with_meta(
                s,
                StmtKind::VarDestruct {
                    pattern: pattern.clone(),
                    init: rw_expr(
                        init,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    ),
                },
            ),
            StmtKind::If {
                cond,
                then_b,
                else_b,
            } => stmt_with_meta(
                s,
                StmtKind::If {
                    cond: rw_expr(
                        cond,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    ),
                    then_b: rw_block(
                        then_b,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    ),
                    else_b: else_b.as_ref().map(|b| {
                        rw_block(b, used, counter, enclosing_locals, out_funcs, lam_caps_out)
                    }),
                },
            ),
            StmtKind::While { cond, body } => stmt_with_meta(
                s,
                StmtKind::While {
                    cond: rw_expr(
                        cond,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    ),
                    body: rw_block(
                        body,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    ),
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
                    init: init.as_ref().map(|boxed| {
                        SmallBox::new(rw_stmt(
                            &**boxed,
                            used,
                            counter,
                            enclosing_locals,
                            out_funcs,
                            lam_caps_out,
                        ))
                    }),
                    cond: cond.as_ref().map(|expr| {
                        rw_expr(
                            expr,
                            used,
                            counter,
                            enclosing_locals,
                            out_funcs,
                            lam_caps_out,
                        )
                    }),
                    step: step.as_ref().map(|expr| {
                        rw_expr(
                            expr,
                            used,
                            counter,
                            enclosing_locals,
                            out_funcs,
                            lam_caps_out,
                        )
                    }),
                    body: rw_block(
                        body,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    ),
                },
            ),
            StmtKind::Try {
                try_block,
                catch,
                finally_block,
            } => {
                let try_rw = rw_block(
                    try_block,
                    used,
                    counter,
                    enclosing_locals,
                    out_funcs,
                    lam_caps_out,
                );

                let catch_rw = catch.as_ref().map(|clause| {
                    let mut catch_scope = enclosing_locals.clone();
                    if let Some(binding) = &clause.binding {
                        catch_scope.insert(binding.clone());
                    }
                    CatchClause {
                        binding: clause.binding.clone(),
                        body: rw_block(
                            &clause.body,
                            used,
                            counter,
                            &catch_scope,
                            out_funcs,
                            lam_caps_out,
                        ),
                        meta: clause.meta.clone(),
                    }
                });

                let finally_rw = finally_block
                    .as_ref()
                    .map(|b| rw_block(b, used, counter, enclosing_locals, out_funcs, lam_caps_out));

                stmt_with_meta(
                    s,
                    StmtKind::Try {
                        try_block: try_rw,
                        catch: catch_rw,
                        finally_block: finally_rw,
                    },
                )
            }
            StmtKind::Throw(expr) => stmt_with_meta(
                s,
                StmtKind::Throw(rw_expr(
                    expr,
                    used,
                    counter,
                    enclosing_locals,
                    out_funcs,
                    lam_caps_out,
                )),
            ),
            StmtKind::Defer {
                kind,
                binding,
                body,
            } => {
                let mut scope = enclosing_locals.clone();
                if let Some(binding) = binding {
                    scope.insert(binding.clone());
                }
                stmt_with_meta(
                    s,
                    StmtKind::Defer {
                        kind: *kind,
                        binding: binding.clone(),
                        body: rw_block(body, used, counter, &scope, out_funcs, lam_caps_out),
                    },
                )
            }
            StmtKind::Return(expr_opt) => stmt_with_meta(
                s,
                StmtKind::Return(expr_opt.as_ref().map(|expr| {
                    rw_expr(
                        expr,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )
                })),
            ),
            StmtKind::Expr(expr) => stmt_with_meta(
                s,
                StmtKind::Expr(rw_expr(
                    expr,
                    used,
                    counter,
                    enclosing_locals,
                    out_funcs,
                    lam_caps_out,
                )),
            ),
            StmtKind::Listen(ld) => {
                let mut routes = Vec::with_capacity(ld.routes.len());
                for r in &ld.routes {
                    routes.push(RouteDecl {
                        method: r.method.clone(),
                        pattern: rw_expr(
                            &r.pattern,
                            used,
                            counter,
                            enclosing_locals,
                            out_funcs,
                            lam_caps_out,
                        ),
                        handler: rw_expr(
                            &r.handler,
                            used,
                            counter,
                            enclosing_locals,
                            out_funcs,
                            lam_caps_out,
                        ),
                    });
                }
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

    fn rw_lvalue(
        lv: &LValue,
        used: &mut BTreeSet<String>,
        counter: &mut u32,
        enclosing_locals: &BTreeSet<String>,
        out_funcs: &mut Vec<FuncDecl>,
        lam_caps_out: &mut HashMap<String, Vec<String>>,
    ) -> LValue {
        match &lv.kind {
            LValueKind::Ident(s) => lvalue_with_meta(lv, LValueKind::Ident(s.clone())),
            LValueKind::GetProp { recv, name } => lvalue_with_meta(
                lv,
                LValueKind::GetProp {
                    recv: rw_expr(
                        recv,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    ),
                    name: name.clone(),
                },
            ),
            LValueKind::Index { recv, index } => lvalue_with_meta(
                lv,
                LValueKind::Index {
                    recv: rw_expr(
                        recv,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    ),
                    index: rw_expr(
                        index,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    ),
                },
            ),
        }
    }

    fn rw_expr(
        e: &Expr,
        used: &mut BTreeSet<String>,
        counter: &mut u32,
        enclosing_locals: &BTreeSet<String>,
        out_funcs: &mut Vec<FuncDecl>,
        lam_caps_out: &mut HashMap<String, Vec<String>>,
    ) -> Expr {
        match &e.kind {
            ExprKind::Assign(lv, rhs) => expr_with_meta(
                e,
                ExprKind::Assign(
                    SmallBox::new(rw_lvalue(
                        &**lv,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    SmallBox::new(rw_expr(
                        rhs,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                ),
            ),
            ExprKind::Conditional {
                cond,
                then_branch,
                else_branch,
            } => expr_with_meta(
                e,
                ExprKind::Conditional {
                    cond: SmallBox::new(rw_expr(
                        cond,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    then_branch: SmallBox::new(rw_expr(
                        then_branch,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    else_branch: SmallBox::new(rw_expr(
                        else_branch,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                },
            ),
            ExprKind::Binary { op, a, b } => expr_with_meta(
                e,
                ExprKind::Binary {
                    op: *op,
                    a: SmallBox::new(rw_expr(
                        a,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    b: SmallBox::new(rw_expr(
                        b,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                },
            ),
            ExprKind::Unary { op, e: inner } => expr_with_meta(
                e,
                ExprKind::Unary {
                    op: *op,
                    e: SmallBox::new(rw_expr(
                        inner,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                },
            ),
            ExprKind::Call { callee, args } => expr_with_meta(
                e,
                ExprKind::Call {
                    callee: SmallBox::new(rw_expr(
                        callee,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    args: args
                        .iter()
                        .map(|a| {
                            rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out)
                        })
                        .collect(),
                },
            ),
            ExprKind::GetProp { recv, name } => expr_with_meta(
                e,
                ExprKind::GetProp {
                    recv: SmallBox::new(rw_expr(
                        recv,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    name: name.clone(),
                },
            ),
            ExprKind::Index { recv, index } => expr_with_meta(
                e,
                ExprKind::Index {
                    recv: SmallBox::new(rw_expr(
                        recv,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    index: SmallBox::new(rw_expr(
                        index,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                },
            ),
            ExprKind::Group(inner) => expr_with_meta(
                e,
                ExprKind::Group(SmallBox::new(rw_expr(
                    inner,
                    used,
                    counter,
                    enclosing_locals,
                    out_funcs,
                    lam_caps_out,
                ))),
            ),
            ExprKind::FnLit { params, body } => {
                let mut inner_defs: BTreeSet<String> = params.iter().cloned().collect();
                let mut uses: BTreeSet<String> = BTreeSet::new();
                collect_defs_uses_block(body, &mut inner_defs, &mut uses);

                let mut caps = Vec::<String>::new();
                for u in uses {
                    if enclosing_locals.contains(&u) && !params.contains(&u) {
                        caps.push(u);
                    }
                }
                caps.sort();

                let lam_name = fresh(used, counter);
                lam_caps_out.insert(lam_name.clone(), caps.clone());

                let mut lam_params = Vec::<String>::with_capacity(params.len() + 1);
                lam_params.push("__env".to_string());
                lam_params.extend(params.iter().cloned());

                let mut lam_enclosing: BTreeSet<String> = params.iter().cloned().collect();
                for c in &caps {
                    lam_enclosing.insert(c.clone());
                }
                let body_rewritten =
                    rw_block(body, used, counter, &lam_enclosing, out_funcs, lam_caps_out);

                out_funcs.push(FuncDecl {
                    fid: FuncId(next_id()),
                    name: lam_name.clone(),
                    params: lam_params,
                    body: body_rewritten,
                    is_async: false,
                    meta: e.meta.clone(),
                });

                expr_with_meta(e, ExprKind::FnRef { name: lam_name })
            }
            ExprKind::FnRef { name } => expr_with_meta(e, ExprKind::FnRef { name: name.clone() }),

            ExprKind::LitInt(_)
            | ExprKind::LitF64(_)
            | ExprKind::LitBool(_)
            | ExprKind::LitNull
            | ExprKind::Str(_)
            | ExprKind::Ident(_)
            | ExprKind::This => e.clone(),

            ExprKind::ArrayLit(elems) => expr_with_meta(
                e,
                ExprKind::ArrayLit(
                    elems
                        .iter()
                        .map(|el| {
                            rw_expr(el, used, counter, enclosing_locals, out_funcs, lam_caps_out)
                        })
                        .collect(),
                ),
            ),
            ExprKind::ObjLit(items) => expr_with_meta(
                e,
                ExprKind::ObjLit(
                    items
                        .iter()
                        .map(|item| match item {
                            ObjItem::Prop(k, v) => ObjItem::Prop(
                                k.clone(),
                                rw_expr(
                                    v,
                                    used,
                                    counter,
                                    enclosing_locals,
                                    out_funcs,
                                    lam_caps_out,
                                ),
                            ),
                            ObjItem::Spread(expr) => ObjItem::Spread(rw_expr(
                                expr,
                                used,
                                counter,
                                enclosing_locals,
                                out_funcs,
                                lam_caps_out,
                            )),
                        })
                        .collect(),
                ),
            ),
            ExprKind::GetPropObj { obj, key } => expr_with_meta(
                e,
                ExprKind::GetPropObj {
                    obj: SmallBox::new(rw_expr(
                        obj,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    key: key.clone(),
                },
            ),
            ExprKind::SetPropObj { obj, key, value } => expr_with_meta(
                e,
                ExprKind::SetPropObj {
                    obj: SmallBox::new(rw_expr(
                        obj,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    key: key.clone(),
                    value: SmallBox::new(rw_expr(
                        value,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                },
            ),
            ExprKind::In { key, obj } => expr_with_meta(
                e,
                ExprKind::In {
                    key: SmallBox::new(rw_expr(
                        key,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    obj: SmallBox::new(rw_expr(
                        obj,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                },
            ),
            ExprKind::DeleteProp { obj, key } => expr_with_meta(
                e,
                ExprKind::DeleteProp {
                    obj: SmallBox::new(rw_expr(
                        obj,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    key: key.clone(),
                },
            ),
            ExprKind::DeleteIndex { obj, index } => expr_with_meta(
                e,
                ExprKind::DeleteIndex {
                    obj: SmallBox::new(rw_expr(
                        obj,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    index: SmallBox::new(rw_expr(
                        index,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                },
            ),
            ExprKind::SuperProp(name) => expr_with_meta(e, ExprKind::SuperProp(name.clone())),
            ExprKind::SuperCall(args) => expr_with_meta(
                e,
                ExprKind::SuperCall(
                    args.iter()
                        .map(|a| {
                            rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out)
                        })
                        .collect(),
                ),
            ),
            ExprKind::New { class, args } => expr_with_meta(
                e,
                ExprKind::New {
                    class: class.clone(),
                    args: args
                        .iter()
                        .map(|a| {
                            rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out)
                        })
                        .collect(),
                },
            ),
            ExprKind::CreateBuiltin { kind, args } => expr_with_meta(
                e,
                ExprKind::CreateBuiltin {
                    kind: *kind,
                    args: args
                        .iter()
                        .map(|a| {
                            rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out)
                        })
                        .collect(),
                },
            ),
            ExprKind::CallBuiltinMapMethod { recv, method, args } => expr_with_meta(
                e,
                ExprKind::CallBuiltinMapMethod {
                    recv: SmallBox::new(rw_expr(
                        recv,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    method: *method,
                    args: args
                        .iter()
                        .map(|a| {
                            rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out)
                        })
                        .collect(),
                },
            ),
            ExprKind::CallBuiltinSetMethod { recv, method, args } => expr_with_meta(
                e,
                ExprKind::CallBuiltinSetMethod {
                    recv: SmallBox::new(rw_expr(
                        recv,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    method: *method,
                    args: args
                        .iter()
                        .map(|a| {
                            rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out)
                        })
                        .collect(),
                },
            ),
            ExprKind::CallBuiltinCommonMethod { recv, method } => expr_with_meta(
                e,
                ExprKind::CallBuiltinCommonMethod {
                    recv: SmallBox::new(rw_expr(
                        recv,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    )),
                    method: *method,
                },
            ),
            ExprKind::GetBuiltinSize(recv) => expr_with_meta(
                e,
                ExprKind::GetBuiltinSize(SmallBox::new(rw_expr(
                    recv,
                    used,
                    counter,
                    enclosing_locals,
                    out_funcs,
                    lam_caps_out,
                ))),
            ),
            ExprKind::Await(inner) => expr_with_meta(
                e,
                ExprKind::Await(SmallBox::new(rw_expr(
                    inner,
                    used,
                    counter,
                    enclosing_locals,
                    out_funcs,
                    lam_caps_out,
                ))),
            ),
            ExprKind::OptionalChain { base, access } => {
                let rewritten_base = rw_expr(
                    base,
                    used,
                    counter,
                    enclosing_locals,
                    out_funcs,
                    lam_caps_out,
                );
                let rewritten_access = match access {
                    OptionalAccess::Prop(name) => OptionalAccess::Prop(name.clone()),
                    OptionalAccess::Index(expr) => OptionalAccess::Index(SmallBox::new(rw_expr(
                        expr,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    ))),
                    OptionalAccess::Call(args) => OptionalAccess::Call(
                        args.iter()
                            .map(|a| {
                                rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out)
                            })
                            .collect(),
                    ),
                };
                expr_with_meta(
                    e,
                    ExprKind::OptionalChain {
                        base: SmallBox::new(rewritten_base),
                        access: rewritten_access,
                    },
                )
            }
        }
    }

    // Walk functions, threading the set of enclosing locals (toplevel has none).
    let mut out_funcs: Vec<FuncDecl> = Vec::new();
    for f in &prog.functions {
        // at top-level of a function, enclosing locals = its params (can be captured by nested lambdas)
        let enclosing: BTreeSet<String> = f.params.iter().cloned().collect();
        let rew_body = rw_block(
            &f.body,
            &mut used,
            &mut counter,
            &enclosing,
            &mut out_funcs,
            &mut lam_captures,
        );
        out_funcs.push(FuncDecl {
            fid: FuncId(next_id()),
            name: f.name.clone(),
            params: f.params.clone(),
            body: rew_body,
            is_async: f.is_async,
            meta: f.meta.clone(),
        });
    }

    (
        Program {
            functions: out_funcs,
            classes: prog.classes.clone(),
            imports: prog.imports.clone(),
            exports: prog.exports.clone(),
            modules: prog.modules.clone(),
        },
        lam_captures,
    )
}
