// src/lowerer.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::collections::{HashMap, HashSet};
use logos::Logos;
use smallbox::SmallBox;
use std::collections::hash_map::Entry;
use std::{collections::BTreeSet, ops::Deref};

// Bring in the WIR types from your other file/module.
use crate::wir::{
    AccessorInfo, BindingId, Builder, Constant, FieldId, FuncId, Inst, IntBinOp, MethodInfo,
    Module, Type, ValueId, next_id,
};

use crate::front::{
    BinOp, Block, ClassDecl, ClassMember, ExportDecl, Expr, FuncDecl, ImportDecl, ImportItem,
    LValue, ListenDecl, ObjItem, ObjPattern, OptionalAccess, Program, PropKey, RouteDecl, Stmt,
    UnOp,
};

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
        match s {
            Stmt::Var { name, init } => {
                defs.insert(name.clone());
                if let Some(e) = init {
                    collect_uses_expr(e, uses);
                }
            }
            Stmt::VarDestruct { pattern, init } => {
                insert_pattern_bindings(defs, pattern);
                collect_uses_expr(init, uses);
            }
            Stmt::If {
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
            Stmt::While { cond, body } => {
                collect_uses_expr(cond, uses);
                collect_defs_uses_block(body, defs, uses);
            }
            Stmt::For {
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
            Stmt::Return(e) => {
                if let Some(e) = e {
                    collect_uses_expr(e, uses);
                }
            }
            Stmt::Expr(e) => collect_uses_expr(e, uses),
            Stmt::Listen(ld) => {
                for r in &ld.routes {
                    collect_uses_expr(&r.pattern, uses);
                    collect_uses_expr(&r.handler, uses);
                }
            }
        }
    }

    fn collect_uses_expr(e: &Expr, uses: &mut BTreeSet<String>) {
        match e {
            Expr::Ident(s) => {
                uses.insert(s.clone());
            }
            Expr::Assign(lv, rhs) => {
                match &**lv {
                    LValue::Ident(s) => {
                        uses.insert(s.clone());
                    }
                    LValue::GetProp { recv, .. } => collect_uses_expr(recv, uses),
                    LValue::Index { recv, index } => {
                        collect_uses_expr(recv, uses);
                        collect_uses_expr(index, uses);
                    }
                }
                collect_uses_expr(rhs, uses);
            }
            Expr::Binary { a, b, .. } => {
                collect_uses_expr(a, uses);
                collect_uses_expr(b, uses);
            }
            Expr::Unary { e, .. } => {
                collect_uses_expr(e, uses);
            }
            Expr::Call { callee, args } => {
                collect_uses_expr(callee, uses);
                for a in args {
                    collect_uses_expr(a, uses);
                }
            }
            Expr::GetProp { recv, .. } => collect_uses_expr(recv, uses),
            Expr::Index { recv, index } => {
                collect_uses_expr(recv, uses);
                collect_uses_expr(index, uses);
            }
            Expr::Group(g) => collect_uses_expr(g, uses),
            Expr::FnLit { .. } | Expr::FnRef { .. } => { /* handled at outer level */ }
            Expr::LitInt(_) | Expr::LitF64(_) | Expr::LitBool(_) | Expr::LitNull | Expr::Str(_) => {
            }

            Expr::ArrayLit(elems) => {
                for el in elems {
                    collect_uses_expr(el, uses);
                }
            }

            Expr::ObjLit(items) => {
                for item in items {
                    match item {
                        ObjItem::Prop(_, value) => collect_uses_expr(value, uses),
                        ObjItem::Spread(expr) => collect_uses_expr(expr, uses),
                    }
                }
            }

            Expr::GetPropObj { obj, .. } => {
                collect_uses_expr(obj, uses);
            }

            Expr::SetPropObj { obj, value, .. } => {
                collect_uses_expr(obj, uses);
                collect_uses_expr(value, uses);
            }

            Expr::In { key, obj } => {
                collect_uses_expr(key, uses);
                collect_uses_expr(obj, uses);
            }

            Expr::DeleteProp { obj, .. } => {
                collect_uses_expr(obj, uses);
            }

            Expr::SuperProp(_) => { /* no local uses */ }
            Expr::SuperCall(args) => {
                for a in args {
                    collect_uses_expr(a, uses);
                }
            }

            Expr::CreateBuiltin { args, .. } => {
                for a in args {
                    collect_uses_expr(a, uses);
                }
            }
            Expr::CallBuiltinMapMethod { recv, args, .. } => {
                collect_uses_expr(recv, uses);
                for a in args {
                    collect_uses_expr(a, uses);
                }
            }
            Expr::CallBuiltinSetMethod { recv, args, .. } => {
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
            match s {
                // `var` introduces a name *after* its initializer; rewrite init with current scope,
                // then add the binding to the scope for following statements.
                Stmt::Var { name, init } => {
                    let init_rw = init
                        .as_ref()
                        .map(|e| rw_expr(e, used, counter, &scope, out_funcs, lam_caps_out));
                    out_stmts.push(Stmt::Var {
                        name: name.clone(),
                        init: init_rw,
                    });
                    scope.insert(name.clone());
                }
                Stmt::VarDestruct { pattern, init } => {
                    let init_rw = rw_expr(init, used, counter, &scope, out_funcs, lam_caps_out);
                    out_stmts.push(Stmt::VarDestruct {
                        pattern: pattern.clone(),
                        init: init_rw,
                    });
                    insert_pattern_bindings(&mut scope, pattern);
                }

                // `for` init can introduce a name that is visible to cond/step/body.
                Stmt::For {
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
                        match i0 {
                            Stmt::Var { name, .. } => {
                                for_scope.insert(name.clone());
                            }
                            Stmt::VarDestruct { pattern, .. } => {
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

                    out_stmts.push(Stmt::For {
                        init: init_rw,
                        cond: cond_rw,
                        step: step_rw,
                        body: body_rw,
                    });
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
        match s {
            Stmt::Var { name, init } => Stmt::Var {
                name: name.clone(),
                init: init
                    .as_ref()
                    .map(|e| rw_expr(e, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
            },
            Stmt::VarDestruct { pattern, init } => Stmt::VarDestruct {
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
            Stmt::If {
                cond,
                then_b,
                else_b,
            } => Stmt::If {
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
                else_b: else_b
                    .as_ref()
                    .map(|b| rw_block(b, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
            },
            Stmt::While { cond, body } => Stmt::While {
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
            Stmt::For {
                init,
                cond,
                step,
                body,
            } => Stmt::For {
                init: init.as_deref().map(|i| {
                    SmallBox::new(rw_stmt(
                        i,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    ))
                }),
                cond: cond
                    .as_ref()
                    .map(|e| rw_expr(e, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                step: step
                    .as_ref()
                    .map(|e| rw_expr(e, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                body: rw_block(
                    body,
                    used,
                    counter,
                    enclosing_locals,
                    out_funcs,
                    lam_caps_out,
                ),
            },
            Stmt::Return(e) => Stmt::Return(
                e.as_ref()
                    .map(|x| rw_expr(x, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
            ),
            Stmt::Expr(e) => Stmt::Expr(rw_expr(
                e,
                used,
                counter,
                enclosing_locals,
                out_funcs,
                lam_caps_out,
            )),

            Stmt::Listen(ld) => {
                let mut routes = Vec::with_capacity(ld.routes.len());
                for r in &ld.routes {
                    let pattern_rw = rw_expr(
                        &r.pattern,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    );
                    let handler_rw = rw_expr(
                        &r.handler,
                        used,
                        counter,
                        enclosing_locals,
                        out_funcs,
                        lam_caps_out,
                    );
                    routes.push(RouteDecl {
                        method: r.method.clone(),
                        pattern: pattern_rw,
                        handler: handler_rw,
                    });
                }
                Stmt::Listen(ListenDecl {
                    addr: ld.addr.clone(),
                    routes,
                })
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
        match lv {
            LValue::Ident(s) => LValue::Ident(s.clone()),
            LValue::GetProp { recv, name } => LValue::GetProp {
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
            LValue::Index { recv, index } => LValue::Index {
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
        match e {
            Expr::Assign(lv, rhs) => Expr::Assign(
                SmallBox::new(rw_lvalue(
                    lv,
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
            Expr::Conditional {
                cond,
                then_branch,
                else_branch,
            } => Expr::Conditional {
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
            Expr::Binary { op, a, b } => Expr::Binary {
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
            Expr::Unary { op, e } => Expr::Unary {
                op: *op,
                e: SmallBox::new(rw_expr(
                    e,
                    used,
                    counter,
                    enclosing_locals,
                    out_funcs,
                    lam_caps_out,
                )),
            },
            Expr::Call { callee, args } => Expr::Call {
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
                    .map(|a| rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out))
                    .collect(),
            },
            Expr::GetProp { recv, name } => Expr::GetProp {
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
            Expr::Index { recv, index } => Expr::Index {
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
            Expr::Group(g) => Expr::Group(SmallBox::new(rw_expr(
                g,
                used,
                counter,
                enclosing_locals,
                out_funcs,
                lam_caps_out,
            ))),

            // Core: hoist to a top-level function with extra hidden `__env` param; replace with FnRef
            Expr::FnLit { params, body } => {
                // names defined inside the lambda
                let mut inner_defs: BTreeSet<String> = params.iter().cloned().collect();
                let mut uses: BTreeSet<String> = BTreeSet::new();
                collect_defs_uses_block(body, &mut inner_defs, &mut uses);

                // captures = (uses ∩ enclosing_locals) \ params
                let mut caps = Vec::<String>::new();
                for u in uses {
                    if enclosing_locals.contains(&u) && !params.contains(&u) {
                        caps.push(u);
                    }
                }
                caps.sort();

                // Fresh name
                let lam_name = fresh(used, counter);

                // Record capture list
                lam_caps_out.insert(lam_name.clone(), caps.clone());

                // Create the hoisted function: first param is "__env", then user's params
                let mut lam_params = Vec::<String>::with_capacity(params.len() + 1);
                lam_params.push("__env".to_string());
                lam_params.extend(params.iter().cloned());

                // IMPORTANT: recursively hoist inside the lambda body.
                // Enclosing scope for nested lambdas = lambda params ∪ captured names.
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
                });

                // Replace literal with a named lam reference
                Expr::FnRef { name: lam_name }
            }

            // Already a reference (created earlier)
            Expr::FnRef { name } => Expr::FnRef { name: name.clone() },

            // terminals
            Expr::LitInt(_)
            | Expr::LitF64(_)
            | Expr::LitBool(_)
            | Expr::LitNull
            | Expr::Str(_)
            | Expr::Ident(_) => e.clone(),

            Expr::ArrayLit(elems) => Expr::ArrayLit(
                elems
                    .iter()
                    .map(|el| rw_expr(el, used, counter, enclosing_locals, out_funcs, lam_caps_out))
                    .collect(),
            ),

            Expr::ObjLit(items) => Expr::ObjLit(
                items
                    .iter()
                    .map(|item| match item {
                        ObjItem::Prop(k, v) => ObjItem::Prop(
                            k.clone(),
                            rw_expr(v, used, counter, enclosing_locals, out_funcs, lam_caps_out),
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

            Expr::GetPropObj { obj, key } => Expr::GetPropObj {
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

            Expr::SetPropObj { obj, key, value } => Expr::SetPropObj {
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

            Expr::In { key, obj } => Expr::In {
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

            Expr::DeleteProp { obj, key } => Expr::DeleteProp {
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

            Expr::DeleteIndex { obj, index } => Expr::DeleteIndex {
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

            Expr::This => Expr::This,

            Expr::SuperProp(name) => Expr::SuperProp(name.clone()),
            Expr::SuperCall(args) => Expr::SuperCall(
                args.iter()
                    .map(|a| rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out))
                    .collect(),
            ),

            Expr::New { class, args } => Expr::New {
                class: class.clone(),
                args: args
                    .iter()
                    .map(|a| rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out))
                    .collect(),
            },

            Expr::CreateBuiltin { kind, args } => Expr::CreateBuiltin {
                kind: *kind,
                args: args
                    .iter()
                    .map(|a| rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out))
                    .collect(),
            },
            Expr::CallBuiltinMapMethod { recv, method, args } => Expr::CallBuiltinMapMethod {
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
                    .map(|a| rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out))
                    .collect(),
            },
            Expr::CallBuiltinSetMethod { recv, method, args } => Expr::CallBuiltinSetMethod {
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
                    .map(|a| rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out))
                    .collect(),
            },

            Expr::Await(inner) => Expr::Await(SmallBox::new(rw_expr(
                inner,
                used,
                counter,
                enclosing_locals,
                out_funcs,
                lam_caps_out,
            ))),
            Expr::OptionalChain { base, access } => Expr::OptionalChain {
                base: SmallBox::new(rw_expr(
                    base,
                    used,
                    counter,
                    enclosing_locals,
                    out_funcs,
                    lam_caps_out,
                )),
                access: match access {
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
                },
            },
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
