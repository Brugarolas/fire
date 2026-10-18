//! Gradual static checker for the optional type annotations.
//!
//! Unannotated code is typed `any` and is never rejected.  Annotated code is
//! checked structurally (TypeScript-style); values flowing from `any` into an
//! annotated slot get a cheap compiled runtime guard (`TypedOp::Assert`), and
//! operations whose operand types are known are rewritten to faster typed
//! operations that skip dynamic dispatch during lowering.

use super::types::{TypeLiteral, TypeMember, TypeParam};
mod advanced;
pub(crate) mod imports;
use advanced::{literal_base, widen_scalar};
use super::*;
use std::collections::{HashMap as StdMap, HashSet as StdSet};
use std::fmt;
use std::rc::Rc;

#[cfg(test)]
mod tests;

#[derive(Clone, Debug, PartialEq)]
enum Ty {
    Any,
    Unknown,
    Literal(TypeLiteral),
    Tuple(Vec<Ty>),
    Deferred(Box<TypeExpr>, StdMap<String, Ty>),
    Never,
    Void,
    Number,
    Str,
    Bool,
    Null,
    Array(Box<Ty>),
    Map(Box<Ty>, Box<Ty>),
    Set(Box<Ty>),
    Promise(Box<Ty>),
    Func(Rc<Sig>),
    Object(Rc<Vec<Member>>),
    /// Interface or class instance.
    Named(String, Vec<Ty>),
    Param(String),
    Union(Vec<Ty>),
}

#[derive(Clone, Debug, PartialEq)]
struct Member {
    name: String,
    optional: bool,
    ty: Ty,
    /// Whether `"name" in value` can observe the member at runtime.
    probe: bool,
}

#[derive(Clone, Debug, PartialEq)]
struct Sig {
    type_params: Vec<(String, Option<Ty>)>,
    params: Vec<Ty>,
    min_args: usize,
    ret: Ty,
    /// `Function`: callable with anything.
    variadic: bool,
    /// Declared with annotations: arity is enforced.
    checked: bool,
}

impl Sig {
    fn dynamic(params: usize) -> Sig {
        Sig {
            type_params: Vec::new(),
            params: vec![Ty::Any; params],
            min_args: params,
            ret: Ty::Any,
            variadic: false,
            checked: false,
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ty::Any => write!(f, "any"),
            Ty::Unknown => write!(f, "unknown"),
            Ty::Literal(TypeLiteral::Number(n)) => write!(f, "{n}"),
            Ty::Literal(TypeLiteral::String(s)) => write!(f, "{s:?}"),
            Ty::Literal(TypeLiteral::Bool(b)) => write!(f, "{b}"),
            Ty::Tuple(items) => write!(f, "[{}]", items.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ")),
            Ty::Deferred(..) => write!(f, "deferred type"),
            Ty::Never => write!(f, "never"),
            Ty::Void => write!(f, "void"),
            Ty::Number => write!(f, "number"),
            Ty::Str => write!(f, "string"),
            Ty::Bool => write!(f, "boolean"),
            Ty::Null => write!(f, "null"),
            Ty::Array(t) if matches!(**t, Ty::Union(_) | Ty::Func(_)) => write!(f, "({t})[]"),
            Ty::Array(t) => write!(f, "{t}[]"),
            Ty::Map(k, v) => write!(f, "Map<{k}, {v}>"),
            Ty::Set(t) => write!(f, "Set<{t}>"),
            Ty::Promise(t) => write!(f, "Promise<{t}>"),
            Ty::Func(sig) if sig.variadic => write!(f, "Function"),
            Ty::Func(sig) => {
                write!(f, "(")?;
                for (i, param) in sig.params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    let optional = if i >= sig.min_args { "?" } else { "" };
                    write!(f, "p{i}{optional}: {param}")?;
                }
                write!(f, ") => {}", sig.ret)
            }
            Ty::Object(members) => {
                write!(f, "{{ ")?;
                for member in members.iter() {
                    let optional = if member.optional { "?" } else { "" };
                    write!(f, "{}{optional}: {}; ", member.name, member.ty)?;
                }
                write!(f, "}}")
            }
            Ty::Named(name, args) => {
                write!(f, "{name}")?;
                if !args.is_empty() {
                    write!(f, "<")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{arg}")?;
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
            Ty::Param(name) => write!(f, "{name}"),
            Ty::Union(members) => {
                for (i, member) in members.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{member}")?;
                }
                Ok(())
            }
        }
    }
}

fn union(types: impl IntoIterator<Item = Ty>) -> Ty {
    let mut out: Vec<Ty> = Vec::new();
    for ty in types {
        match ty {
            Ty::Any => return Ty::Any,
            Ty::Never => {}
            Ty::Union(inner) => {
                for ty in inner {
                    if !out.contains(&ty) {
                        out.push(ty);
                    }
                }
            }
            ty => {
                if !out.contains(&ty) {
                    out.push(ty);
                }
            }
        }
    }
    match out.len() {
        0 => Ty::Never,
        1 => out.pop().unwrap(),
        _ => Ty::Union(out),
    }
}

fn accepts_null(ty: &Ty) -> bool {
    match ty {
        Ty::Any | Ty::Unknown | Ty::Null | Ty::Void => true,
        Ty::Union(members) => members.iter().any(accepts_null),
        _ => false,
    }
}

fn strip_null(ty: &Ty) -> Ty {
    match ty {
        Ty::Null | Ty::Void => Ty::Never,
        Ty::Union(members) => union(
            members
                .iter()
                .filter(|t| !matches!(t, Ty::Null | Ty::Void))
                .cloned(),
        ),
        other => other.clone(),
    }
}

/// Primitive values compared by identity (no string payload).
fn is_identity_primitive(ty: &Ty) -> bool {
    match ty {
        Ty::Number | Ty::Bool | Ty::Null | Ty::Void => true,
        Ty::Union(members) => members.iter().all(is_identity_primitive),
        _ => false,
    }
}

fn subst(ty: &Ty, map: &StdMap<String, Ty>) -> Ty {
    if map.is_empty() {
        return ty.clone();
    }
    match ty {
        Ty::Param(name) => map.get(name).cloned().unwrap_or_else(|| ty.clone()),
        Ty::Tuple(items) => Ty::Tuple(items.iter().map(|t| subst(t, map)).collect()),
        Ty::Deferred(expr, bound) => Ty::Deferred(expr.clone(), bound.iter()
            .map(|(n, ty)| (n.clone(), subst(ty, map))).collect()),
        Ty::Array(t) => Ty::Array(Box::new(subst(t, map))),
        Ty::Set(t) => Ty::Set(Box::new(subst(t, map))),
        Ty::Promise(t) => Ty::Promise(Box::new(subst(t, map))),
        Ty::Map(k, v) => Ty::Map(Box::new(subst(k, map)), Box::new(subst(v, map))),
        Ty::Func(sig) => {
            let mut inner = map.clone();
            for (name, _) in &sig.type_params {
                inner.remove(name);
            }
            Ty::Func(Rc::new(Sig {
                type_params: sig
                    .type_params
                    .iter()
                    .map(|(n, c)| (n.clone(), c.as_ref().map(|c| subst(c, &inner))))
                    .collect(),
                params: sig.params.iter().map(|p| subst(p, &inner)).collect(),
                ret: subst(&sig.ret, &inner),
                ..(**sig).clone()
            }))
        }
        Ty::Object(members) => Ty::Object(Rc::new(
            members
                .iter()
                .map(|m| Member {
                    ty: subst(&m.ty, map),
                    ..m.clone()
                })
                .collect(),
        )),
        Ty::Named(name, args) => Ty::Named(name.clone(), args.iter().map(|a| subst(a, map)).collect()),
        Ty::Union(members) => union(members.iter().map(|m| subst(m, map))),
        other => other.clone(),
    }
}

fn take(e: &mut Expr) -> Expr {
    std::mem::replace(e, Node::unknown(ExprKind::LitNull))
}

fn wrap(e: &mut Expr, op: TypedOp) {
    let inner = take(e);
    let meta = inner.meta.clone();
    *e = Node::new(meta, ExprKind::Typed {
        op,
        args: vec![inner],
    });
}

fn block_returns(block: &Block) -> bool {
    block.stmts.iter().any(stmt_returns)
}

fn stmt_returns(stmt: &Stmt) -> bool {
    match stmt.kind() {
        StmtKind::Return(_) | StmtKind::Throw(_) => true,
        StmtKind::If {
            then_b,
            else_b: Some(else_b),
            ..
        } => block_returns(then_b) && block_returns(else_b),
        StmtKind::Try {
            try_block,
            catch,
            finally_block,
        } => {
            finally_block.as_ref().is_some_and(block_returns)
                || (block_returns(try_block)
                    && catch.as_ref().is_none_or(|c| block_returns(&c.body)))
        }
        StmtKind::While { cond, .. } => matches!(cond.kind(), ExprKind::LitBool(true)),
        StmtKind::For { cond: None, .. } => true,
        _ => false,
    }
}

#[derive(Clone)]
enum ClassMemberSrc {
    Field(Option<TypeExpr>, bool),
    Method {
        params: usize,
        types: Option<Box<FnTypes>>,
        is_async: bool,
    },
}

struct ClassInfo {
    type_params: Vec<TypeParam>,
    base: Option<(String, Vec<TypeExpr>)>,
    members: Vec<(String, ClassMemberSrc)>,
    ctor: Option<(usize, Option<Box<FnTypes>>)>,
    typed: bool,
}

struct InterfaceInfo {
    type_params: Vec<TypeParam>,
    extends: Vec<TypeExpr>,
    members: Vec<TypeMember>,
}

struct FnCtx {
    name: String,
    ret: Option<Ty>,
    this_ty: Ty,
    /// Narrowings recorded in scopes below this index belong to an enclosing
    /// function and are not trusted (the closure may run after a reassignment).
    narrow_floor: usize,
    /// Variables assigned inside nested closures or defer blocks never narrow.
    no_narrow: StdSet<String>,
    /// Annotated functions opt into inferring `var` types from initializers.
    infer_locals: bool,
}

struct Checker {
    aliases: StdMap<String, (Vec<TypeParam>, TypeExpr)>,
    interfaces: StdMap<String, Rc<InterfaceInfo>>,
    classes: StdMap<String, Rc<ClassInfo>>,
    enums: StdMap<String, (Ty, StdMap<String, Ty>)>,
    funcs: StdMap<String, Rc<Sig>>,
    globals: StdMap<String, Ty>,
    imported: StdSet<String>,
    type_names: StdMap<String, String>,
    scopes: Vec<StdMap<String, Ty>>,
    type_scope: Vec<(String, Option<Ty>)>,
    ctx: Vec<FnCtx>,
    expanding: Vec<String>,
    assuming: StdSet<String>,
    depth: usize,
    errors: Vec<String>,
    /// Location of the declaration/statement being checked, for diagnostics.
    span: Option<Meta>,
    first_error: Option<Meta>,
    unknown_types: StdSet<String>,
}

pub(super) fn check_program(
    funcs: &mut [FuncDecl],
    classes: &mut [ClassDecl],
    decls: &[TypeDecl],
    imported: &[String],
    file_id: FileId,
) -> PResult<()> {
    check_with_imports(funcs, classes, decls, imported, file_id, &imports::TypeImports::default())
}

pub(crate) fn check_with_imports(
    funcs: &mut [FuncDecl],
    classes: &mut [ClassDecl],
    decls: &[TypeDecl],
    imported: &[String],
    file_id: FileId,
    imports: &imports::TypeImports,
) -> PResult<()> {
    let mut checker = Checker {
        aliases: StdMap::new(),
        interfaces: StdMap::new(),
        classes: StdMap::new(),
        enums: StdMap::new(),
        funcs: StdMap::new(),
        globals: StdMap::new(),
        imported: imported.iter().cloned().collect(),
        type_names: imports.names.clone(),
        scopes: Vec::new(),
        type_scope: Vec::new(),
        ctx: Vec::new(),
        expanding: Vec::new(),
        assuming: StdSet::new(),
        depth: 0,
        errors: Vec::new(),
        span: None,
        first_error: None,
        unknown_types: StdSet::new(),
    };
    checker.collect(&imports.functions, &imports.classes, &imports.declarations);
    for (alias, canonical) in &imports.names {
        if let Some(class) = checker.classes.get(canonical).cloned() {
            checker.classes.insert(alias.clone(), class);
        }
        if let Some(sig) = checker.funcs.get(canonical).cloned() {
            checker.globals.insert(alias.clone(), Ty::Func(sig));
        }
        if let Some(ty) = imports.variables.get(canonical) {
            let ty = checker.resolve(ty);
            checker.globals.insert(alias.clone(), ty);
        }
    }
    for (name, ty) in &imports.namespaces {
        let ty = checker.resolve(ty);
        checker.globals.insert(name.clone(), ty);
    }
    checker.collect(funcs, classes, decls);
    checker.check_declarations(decls);
    for class in classes.iter_mut() {
        checker.span = Some(class.meta.clone());
        checker.class(class);
    }
    for func in funcs.iter_mut() {
        checker.span = Some(func.meta.clone());
        let this_ty = Ty::Any;
        checker.function(
            &func.name,
            &func.params,
            func.types.as_deref(),
            &mut func.body,
            func.is_async,
            this_ty,
        );
    }
    if checker.errors.is_empty() {
        Ok(())
    } else {
        Err(ParseError::new(
            checker.errors.join("\n"),
            checker
                .first_error
                .unwrap_or_else(|| Meta::new(file_id, Span::new(0, 0))),
        ))
    }
}

impl Checker {
    fn error(&mut self, message: String) {
        let message = match self.ctx.last() {
            Some(ctx) if ctx.name == "__toplevel__" => format!("type error at top level: {message}"),
            Some(ctx) => format!("type error in `{}`: {message}", ctx.name),
            None => format!("type error: {message}"),
        };
        if !self.errors.contains(&message) {
            self.errors.push(message);
            if self.first_error.is_none() {
                self.first_error = self.span.clone();
            }
        }
    }

    // ---------------------------------------------------------------------
    // Declarations
    // ---------------------------------------------------------------------

    fn collect(&mut self, funcs: &[FuncDecl], classes: &[ClassDecl], decls: &[TypeDecl]) {
        for decl in decls {
            let name = decl.name().to_string();
            if self.aliases.contains_key(&name) || self.interfaces.contains_key(&name) {
                self.error(format!("duplicate type declaration `{name}`"));
                continue;
            }
            match decl {
                TypeDecl::Alias {
                    type_params, ty, ..
                } => {
                    self.aliases.insert(name, (type_params.clone(), ty.clone()));
                }
                TypeDecl::Interface {
                    type_params,
                    extends,
                    members,
                    ..
                } => {
                    self.interfaces.insert(
                        name,
                        Rc::new(InterfaceInfo {
                            type_params: type_params.clone(),
                            extends: extends.clone(),
                            members: members.clone(),
                        }),
                    );
                }
            }
        }
        for class in classes {
            if self.aliases.contains_key(&class.name) || self.interfaces.contains_key(&class.name)
            {
                self.error(format!("class `{}` conflicts with a type declaration", class.name));
            }
            self.classes
                .insert(class.name.clone(), Rc::new(class_info(class)));
        }
        for func in funcs {
            for stmt in &func.body.stmts {
                if let StmtKind::Enum { name, init, .. } = stmt.kind() {
                    self.enums.insert(name.clone(), enum_type(init));
                }
            }
        }
        for func in funcs {
            if func.name == "__toplevel__" {
                continue;
            }
            self.span = Some(func.meta.clone());
            self.push_decl_ctx(func.name.clone());
            let sig = self.declared_sig(&func.params, func.types.as_deref(), func.is_async);
            self.ctx.pop();
            self.funcs.insert(func.name.clone(), Rc::new(sig));
        }
        if let Some(toplevel) = funcs.iter().find(|f| f.name == "__toplevel__") {
            for stmt in &toplevel.body.stmts {
                if let StmtKind::Var {
                    name, ty: Some(ty), ..
                } = stmt.kind()
                {
                    let ty = self.resolve(ty);
                    self.globals.insert(name.clone(), ty);
                }
            }
        }
    }

    /// Resolves every declaration once so unknown names are reported even when unused.
    fn check_declarations(&mut self, decls: &[TypeDecl]) {
        for decl in decls {
            match decl {
                TypeDecl::Alias {
                    type_params, ty, ..
                } => {
                    let mark = self.push_type_params(type_params);
                    self.resolve(ty);
                    self.type_scope.truncate(mark);
                }
                TypeDecl::Interface {
                    name,
                    type_params,
                    extends,
                    members,
                } => {
                    let mark = self.push_type_params(type_params);
                    for member in members {
                        self.resolve(&member.ty);
                    }
                    for parent in extends {
                        let ty = self.resolve(parent);
                        if !matches!(ty, Ty::Named(..) | Ty::Object(_) | Ty::Any) {
                            self.error(format!(
                                "interface `{name}` can only extend object types, not `{ty}`"
                            ));
                        }
                    }
                    self.type_scope.truncate(mark);
                }
            }
        }
    }

    fn push_type_params(&mut self, params: &[TypeParam]) -> usize {
        let mark = self.type_scope.len();
        for param in params {
            self.type_scope.push((param.name.clone(), None));
        }
        for (i, param) in params.iter().enumerate() {
            if let Some(constraint) = &param.constraint {
                let ty = self.resolve(constraint);
                self.type_scope[mark + i].1 = Some(ty);
            }
        }
        mark
    }

    fn constraint_of(&self, name: &str) -> Option<Ty> {
        self.type_scope
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .and_then(|(_, c)| c.clone())
    }

    /// Signature of a declaration, resolving its own type parameters.
    fn declared_sig(&mut self, params: &[String], types: Option<&FnTypes>, is_async: bool) -> Sig {
        self.sig_in(params.len(), types, is_async, &StdMap::new())
    }

    fn sig_in(
        &mut self,
        count: usize,
        types: Option<&FnTypes>,
        is_async: bool,
        outer: &StdMap<String, Ty>,
    ) -> Sig {
        let Some(types) = types else {
            return Sig::dynamic(count);
        };
        let mut map = outer.clone();
        for param in &types.type_params {
            map.remove(&param.name);
        }
        let mark = self.type_scope.len();
        for param in &types.type_params {
            self.type_scope.push((param.name.clone(), None));
        }
        let mut type_params = Vec::new();
        for (i, param) in types.type_params.iter().enumerate() {
            let constraint = param.constraint.as_ref().map(|c| self.resolve_in(c, &map));
            self.type_scope[mark + i].1 = constraint.clone();
            type_params.push((param.name.clone(), constraint));
        }
        let mut params = Vec::with_capacity(count);
        for i in 0..count {
            let ty = match types.params.get(i).and_then(Option::as_ref) {
                Some(ty) => self.resolve_in(ty, &map),
                None => Ty::Any,
            };
            if types.optional.get(i).copied().unwrap_or(false) {
                params.push(union([ty, Ty::Null]));
            } else {
                params.push(ty);
            }
        }
        let min_args = types
            .optional
            .iter()
            .position(|o| *o)
            .unwrap_or(count);
        let mut ret = match &types.ret {
            Some(ty) => self.resolve_in(ty, &map),
            None => Ty::Any,
        };
        if is_async && !matches!(ret, Ty::Promise(_) | Ty::Any) {
            ret = Ty::Promise(Box::new(ret));
        }
        self.type_scope.truncate(mark);
        Sig {
            type_params,
            params,
            min_args,
            ret,
            variadic: false,
            checked: true,
        }
    }

    // ---------------------------------------------------------------------
    // Type resolution
    // ---------------------------------------------------------------------

    fn resolve(&mut self, ty: &TypeExpr) -> Ty {
        self.resolve_in(ty, &StdMap::new())
    }

    fn resolve_in(&mut self, ty: &TypeExpr, map: &StdMap<String, Ty>) -> Ty {
        match ty {
            TypeExpr::Array(inner) => Ty::Array(Box::new(self.resolve_in(inner, map))),
            TypeExpr::Union(members) => {
                let members: Vec<Ty> = members.iter().map(|m| self.resolve_in(m, map)).collect();
                union(members)
            }
            TypeExpr::Object(members) => Ty::Object(Rc::new(
                members
                    .iter()
                    .map(|m| Member {
                        name: m.name.clone(),
                        optional: m.optional,
                        ty: self.resolve_in(&m.ty, map),
                        probe: true,
                    })
                    .collect(),
            )),
            TypeExpr::Function {
                type_params,
                params,
                min_args,
                ret,
            } => {
                let types = FnTypes {
                    type_params: type_params.clone(),
                    params: params.iter().cloned().map(Some).collect(),
                    optional: (0..params.len()).map(|i| i >= *min_args).collect(),
                    ret: Some((**ret).clone()),
                };
                Ty::Func(Rc::new(self.sig_in(params.len(), Some(&types), false, map)))
            }
            TypeExpr::Name { name, args } => self.resolve_name(name, args, map),
            other => self.resolve_advanced(other, map),
        }
    }

    fn resolve_name(&mut self, name: &str, args: &[TypeExpr], map: &StdMap<String, Ty>) -> Ty {
        if args.is_empty() {
            if let Some(ty) = map.get(name) {
                return ty.clone();
            }
            if self.type_scope.iter().any(|(n, _)| n == name) {
                return Ty::Param(name.to_string());
            }
        }
        if let Some(canonical) = self.type_names.get(name).cloned() {
            return self.resolve_name(&canonical, args, map);
        }
        let resolved: Vec<Ty> = args.iter().map(|a| self.resolve_in(a, map)).collect();
        let builtin_arity = |this: &mut Self, expected: usize| {
            if !resolved.is_empty() && resolved.len() != expected {
                this.error(format!(
                    "type `{name}` expects {expected} type argument(s), got {}",
                    resolved.len()
                ));
            }
        };
        let arg = |i: usize| resolved.get(i).cloned().unwrap_or(Ty::Any);
        let simple = match name {
            "number" => Some(Ty::Number),
            "string" => Some(Ty::Str),
            "boolean" => Some(Ty::Bool),
            "any" => Some(Ty::Any),
            "unknown" => Some(Ty::Unknown),
            "void" => Some(Ty::Void),
            "never" => Some(Ty::Never),
            "null" | "undefined" => Some(Ty::Null),
            "object" => Some(Ty::Object(Rc::new(Vec::new()))),
            "Function" => Some(Ty::Func(Rc::new(Sig {
                variadic: true,
                ..Sig::dynamic(0)
            }))),
            _ => None,
        };
        if let Some(ty) = simple {
            builtin_arity(self, 0);
            return ty;
        }
        match name {
            "Array" => {
                builtin_arity(self, 1);
                return Ty::Array(Box::new(arg(0)));
            }
            "Set" => {
                builtin_arity(self, 1);
                return Ty::Set(Box::new(arg(0)));
            }
            "Promise" => {
                builtin_arity(self, 1);
                return Ty::Promise(Box::new(arg(0)));
            }
            "Map" => {
                builtin_arity(self, 2);
                return Ty::Map(Box::new(arg(0)), Box::new(arg(1)));
            }
            "Proxy" | "Deferred" => return Ty::Any,
            _ => {}
        }
        if let Some((params, body)) = self.aliases.get(name).cloned() {
            if self.expanding.iter().any(|n| n == name) {
                self.error(format!("type alias `{name}` circularly references itself"));
                return Ty::Any;
            }
            let bound = self.bind_args(name, &params, resolved);
            self.expanding.push(name.to_string());
            let saved = std::mem::take(&mut self.type_scope);
            let ty = self.resolve_in(&body, &bound);
            self.type_scope = saved;
            self.expanding.pop();
            return ty;
        }
        if let Some(info) = self.interfaces.get(name).cloned() {
            let bound = self.bind_args(name, &info.type_params, resolved);
            return Ty::Named(name.to_string(), order_args(&info.type_params, bound));
        }
        if let Some(info) = self.classes.get(name).cloned() {
            let bound = self.bind_args(name, &info.type_params, resolved);
            return Ty::Named(name.to_string(), order_args(&info.type_params, bound));
        }
        if let Some((ty, _)) = self.enums.get(name) {
            return ty.clone();
        }
        // Types are resolved lazily from many places; report each name once.
        if self.unknown_types.insert(name.to_string()) {
            self.error(format!("unknown type `{name}`"));
        }
        Ty::Any
    }

    fn bind_args(
        &mut self,
        name: &str,
        params: &[TypeParam],
        args: Vec<Ty>,
    ) -> StdMap<String, Ty> {
        if !args.is_empty() && args.len() != params.len() {
            self.error(format!(
                "type `{name}` expects {} type argument(s), got {}",
                params.len(),
                args.len()
            ));
        }
        let mut map = StdMap::new();
        for (i, param) in params.iter().enumerate() {
            map.insert(param.name.clone(), args.get(i).cloned().unwrap_or(Ty::Any));
        }
        for param in params {
            if let Some(constraint) = &param.constraint {
                let constraint = {
                    let saved = std::mem::take(&mut self.type_scope);
                    let ty = self.resolve_in(constraint, &map);
                    self.type_scope = saved;
                    ty
                };
                let actual = map[&param.name].clone();
                if let Err(reason) = self.compat(&actual, &constraint) {
                    self.error(format!(
                        "type `{actual}` does not satisfy the constraint `{constraint}` of `{}` in `{name}`{}",
                        param.name,
                        detail(&reason)
                    ));
                }
            }
        }
        map
    }

    // ---------------------------------------------------------------------
    // Members, assignability and runtime checks
    // ---------------------------------------------------------------------

    /// Members of an object-like type and whether unknown members are allowed.
    fn members(&mut self, ty: &Ty) -> Option<(Vec<Member>, bool)> {
        if self.depth > 64 {
            return Some((Vec::new(), true));
        }
        self.depth += 1;
        let result = match ty {
            Ty::Object(members) => Some((members.to_vec(), false)),
            Ty::Named(name, args) => {
                if let Some(info) = self.interfaces.get(name).cloned() {
                    Some(self.interface_members(&info, args))
                } else if let Some(info) = self.classes.get(name).cloned() {
                    Some(self.class_members(&info, args))
                } else {
                    None
                }
            }
            Ty::Param(name) => match self.constraint_of(name) {
                Some(constraint) => self.members(&constraint),
                None => None,
            },
            _ => None,
        };
        self.depth -= 1;
        result
    }

    fn interface_members(&mut self, info: &InterfaceInfo, args: &[Ty]) -> (Vec<Member>, bool) {
        let map = zip_args(&info.type_params, args);
        let saved = std::mem::take(&mut self.type_scope);
        let mut out: Vec<Member> = Vec::new();
        for member in &info.members {
            out.push(Member {
                name: member.name.clone(),
                optional: member.optional,
                ty: self.resolve_in(&member.ty, &map),
                probe: true,
            });
        }
        let mut open = false;
        for parent in &info.extends {
            let parent = self.resolve_in(parent, &map);
            match self.members(&parent) {
                Some((members, parent_open)) => {
                    open |= parent_open;
                    for member in members {
                        if !out.iter().any(|m| m.name == member.name) {
                            out.push(member);
                        }
                    }
                }
                None => open = true,
            }
        }
        self.type_scope = saved;
        (out, open)
    }

    fn class_members(&mut self, info: &ClassInfo, args: &[Ty]) -> (Vec<Member>, bool) {
        let map = zip_args(&info.type_params, args);
        let saved = std::mem::take(&mut self.type_scope);
        let mut out: Vec<Member> = Vec::new();
        for (name, source) in &info.members {
            if out.iter().any(|m| &m.name == name) {
                continue;
            }
            let (ty, probe) = match source {
                ClassMemberSrc::Field(ty, probe) => (
                    ty.as_ref()
                        .map(|t| self.resolve_in(t, &map))
                        .unwrap_or(Ty::Any),
                    *probe,
                ),
                ClassMemberSrc::Method {
                    params,
                    types,
                    is_async,
                } => {
                    let sig = self.sig_in(*params, types.as_deref(), *is_async, &map);
                    (Ty::Func(Rc::new(sig)), true)
                }
            };
            out.push(Member {
                name: name.clone(),
                optional: false,
                ty,
                probe,
            });
        }
        let mut open = !info.typed;
        if let Some((base, base_args)) = &info.base {
            if self.classes.contains_key(base) {
                let base_ty = self.resolve_name(base, base_args, &map);
                match self.members(&base_ty) {
                    Some((members, base_open)) => {
                        open |= base_open;
                        for member in members {
                            if !out.iter().any(|m| m.name == member.name) {
                                out.push(member);
                            }
                        }
                    }
                    None => open = true,
                }
            } else {
                open = true;
            }
        }
        self.type_scope = saved;
        (out, open)
    }

    fn compat(&mut self, src: &Ty, dst: &Ty) -> Result<(), String> {
        if matches!(src, Ty::Deferred(..)) || matches!(dst, Ty::Deferred(..)) {
            let (a, b) = (self.normalize(src.clone()), self.normalize(dst.clone()));
            if &a != src || &b != dst { return self.compat(&a, &b); }
        }
        if src == dst {
            return Ok(());
        }
        match (src, dst) {
            (_, Ty::Any | Ty::Unknown) | (Ty::Any, _) | (Ty::Never, _) => return Ok(()),
            _ => {}
        }
        if let Ty::Union(members) = src {
            for member in members {
                self.compat(member, dst)?;
            }
            return Ok(());
        }
        if let Ty::Union(members) = dst {
            let mut last = String::new();
            for member in members {
                match self.compat(src, member) {
                    Ok(()) => return Ok(()),
                    Err(reason) => last = reason,
                }
            }
            return Err(if members.len() == 2 && accepts_null(dst) { last } else { String::new() });
        }
        match (src, dst) {
            (Ty::Literal(lit), _) => self.compat(&literal_base(lit), dst),
            (Ty::Tuple(a), Ty::Tuple(b)) => {
                if a.len() != b.len() { return Err("tuple lengths differ".into()); }
                for (a, b) in a.iter().zip(b) { self.compat(a, b)?; }
                Ok(())
            }
            (Ty::Tuple(items), Ty::Array(element)) => {
                for item in items { self.compat(item, element)?; }
                Ok(())
            }
            (Ty::Null | Ty::Void, Ty::Null | Ty::Void) => Ok(()),
            (Ty::Param(a), Ty::Param(b)) if a == b => Ok(()),
            (Ty::Param(name), _) => match self.constraint_of(name) {
                Some(constraint) => self.compat(&constraint, dst),
                None => Err(String::new()),
            },
            (Ty::Array(a), Ty::Array(b))
            | (Ty::Set(a), Ty::Set(b))
            | (Ty::Promise(a), Ty::Promise(b)) => self.compat(a, b),
            (Ty::Map(k1, v1), Ty::Map(k2, v2)) => {
                self.compat(k1, k2)?;
                self.compat(v1, v2)
            }
            (Ty::Func(s), Ty::Func(d)) => self.compat_sig(s, d),
            (Ty::Object(_) | Ty::Named(..), Ty::Object(_) | Ty::Named(..)) => {
                self.compat_struct(src, dst)
            }
            (Ty::Str | Ty::Array(_) | Ty::Tuple(_), Ty::Object(_) | Ty::Named(..)) => self.compat_length(dst),
            _ => Err(String::new()),
        }
    }

    /// Strings and arrays structurally provide only `length: number`.
    fn compat_length(&mut self, dst: &Ty) -> Result<(), String> {
        let Some((required, _)) = self.members(dst) else {
            return Err(String::new());
        };
        for want in required {
            if want.name == "length" {
                self.compat(&Ty::Number, &want.ty).map_err(|reason| {
                    format!("property `length` has type `number`, expected `{}`{}", want.ty, detail(&reason))
                })?;
            } else if !want.optional {
                return Err(format!("property `{}` is missing", want.name));
            }
        }
        Ok(())
    }

    fn compat_sig(&mut self, src: &Sig, dst: &Sig) -> Result<(), String> {
        if src.variadic || dst.variadic {
            return Ok(());
        }
        let erase = |sig: &Sig| -> StdMap<String, Ty> {
            sig.type_params
                .iter()
                .map(|(n, _)| (n.clone(), Ty::Any))
                .collect()
        };
        let (src_map, dst_map) = (erase(src), erase(dst));
        if src.checked && src.min_args > dst.params.len() {
            return Err(format!(
                "it requires {} argument(s) but only {} are provided",
                src.min_args,
                dst.params.len()
            ));
        }
        for (i, (s, d)) in src.params.iter().zip(&dst.params).enumerate() {
            let (s, d) = (subst(s, &src_map), subst(d, &dst_map));
            self.compat(&d, &s)
                .map_err(|r| format!("parameter {} is incompatible{}", i + 1, detail(&r)))?;
        }
        if matches!(dst.ret, Ty::Void) {
            return Ok(());
        }
        let (s, d) = (subst(&src.ret, &src_map), subst(&dst.ret, &dst_map));
        self.compat(&s, &d)
            .map_err(|r| format!("return types are incompatible{}", detail(&r)))
    }

    fn compat_struct(&mut self, src: &Ty, dst: &Ty) -> Result<(), String> {
        let key = format!("{src} <: {dst}");
        if !self.assuming.insert(key.clone()) {
            return Ok(());
        }
        let result = self.compat_struct_inner(src, dst);
        self.assuming.remove(&key);
        result
    }

    fn compat_struct_inner(&mut self, src: &Ty, dst: &Ty) -> Result<(), String> {
        let Some((required, _)) = self.members(dst) else {
            return Ok(());
        };
        let Some((available, open)) = self.members(src) else {
            return Err(String::new());
        };
        for want in required {
            match available.iter().find(|m| m.name == want.name) {
                Some(have) => {
                    let have = have.ty.clone();
                    if let Err(reason) = self.compat(&have, &want.ty) {
                        return Err(format!(
                            "property `{}` has type `{have}`, expected `{}`{}",
                            want.name,
                            want.ty,
                            detail(&reason)
                        ));
                    }
                }
                None if want.optional || open => {}
                None => return Err(format!("property `{}` is missing", want.name)),
            }
        }
        Ok(())
    }

    fn rt_check(&mut self, ty: &Ty) -> Option<RtCheck> {
        self.runtime_check(ty, &mut StdSet::new())
    }

    /// Checks a value flowing into a typed slot; dynamic values get a runtime guard.
    fn coerce(&mut self, e: &mut Expr, src: &Ty, dst: &Ty, what: &str) {
        if matches!(dst, Ty::Any | Ty::Unknown) {
            return;
        }
        if matches!(src, Ty::Any) {
            if let Some(check) = self.rt_check(dst) {
                wrap(e, TypedOp::Assert {
                    check,
                    message: format!("TypeError: {what} expects {dst}"),
                });
            }
            return;
        }
        self.check_assignable(src, dst, what);
    }

    fn check_assignable(&mut self, src: &Ty, dst: &Ty, what: &str) {
        if let Err(reason) = self.compat(src, dst) {
            self.error(format!(
                "{what}: type `{src}` is not assignable to type `{dst}`{}",
                detail(&reason)
            ));
        }
    }

    fn infer(&mut self, pattern: &Ty, actual: &Ty, names: &[String], out: &mut StdMap<String, Ty>) {
        if matches!(actual, Ty::Any | Ty::Never) {
            return;
        }
        match (pattern, actual) {
            (Ty::Param(name), _) if names.contains(name) => match out.get(name).cloned() {
                None => {
                    out.insert(name.clone(), widen_scalar(actual.clone()));
                }
                Some(previous) => {
                    if self.compat(actual, &previous).is_err() {
                        let widened = if self.compat(&previous, actual).is_ok() {
                            actual.clone()
                        } else {
                            union([previous, actual.clone()])
                        };
                        out.insert(name.clone(), widened);
                    }
                }
            },
            (Ty::Array(p), Ty::Tuple(items)) => {
                for item in items { self.infer(p, &widen_scalar(item.clone()), names, out); }
            }
            (Ty::Tuple(p), Ty::Tuple(a)) => {
                for (p, a) in p.iter().zip(a) { self.infer(p, a, names, out); }
            }
            (Ty::Array(p), Ty::Array(a))
            | (Ty::Set(p), Ty::Set(a))
            | (Ty::Promise(p), Ty::Promise(a)) => self.infer(p, a, names, out),
            (Ty::Map(pk, pv), Ty::Map(ak, av)) => {
                self.infer(pk, ak, names, out);
                self.infer(pv, av, names, out);
            }
            (Ty::Func(p), Ty::Func(a)) => {
                for (p, a) in p.params.iter().zip(&a.params) {
                    self.infer(p, a, names, out);
                }
                self.infer(&p.ret, &a.ret, names, out);
            }
            (Ty::Union(patterns), _) => {
                let actual = if patterns.iter().any(accepts_null) {
                    strip_null(actual)
                } else {
                    actual.clone()
                };
                for pattern in patterns {
                    if !matches!(pattern, Ty::Null | Ty::Void) {
                        self.infer(pattern, &actual, names, out);
                    }
                }
            }
            (Ty::Named(pn, pa), Ty::Named(an, aa)) if pn == an => {
                for (p, a) in pa.iter().zip(aa) {
                    self.infer(p, a, names, out);
                }
            }
            (Ty::Object(_) | Ty::Named(..), Ty::Object(_) | Ty::Named(..)) => {
                let (Some((want, _)), Some((have, _))) = (self.members(pattern), self.members(actual))
                else {
                    return;
                };
                for w in want {
                    if let Some(h) = have.iter().find(|h| h.name == w.name) {
                        self.infer(&w.ty, &h.ty, names, out);
                    }
                }
            }
            _ => {}
        }
    }

    // ---------------------------------------------------------------------
    // Functions, classes and statements
    // ---------------------------------------------------------------------

    fn lookup(&self, name: &str) -> Option<Ty> {
        for scope in self.scopes.iter().rev() {
            if let Some(ty) = scope.get(name) {
                return Some(ty.clone());
            }
        }
        self.globals.get(name).cloned()
    }

    fn is_local(&self, name: &str) -> bool {
        self.scopes.iter().any(|s| s.contains_key(name)) || self.globals.contains_key(name)
    }

    fn declare(&mut self, name: &str, ty: Ty) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.remove(&narrow_key(name));
            scope.insert(name.to_string(), ty);
        }
    }

    /// Type of a variable read, honoring flow narrowing (`x != null`).
    fn lookup_read(&self, name: &str) -> Option<Ty> {
        let floor = self.ctx.last().map_or(0, |c| c.narrow_floor);
        let key = narrow_key(name);
        for (depth, scope) in self.scopes.iter().enumerate().rev() {
            if depth >= floor {
                if let Some(ty) = scope.get(&key) {
                    return Some(ty.clone());
                }
            }
            if let Some(ty) = scope.get(name) {
                return Some(ty.clone());
            }
        }
        self.globals.get(name).cloned()
    }

    /// The non-null type of a nullable variable that may be narrowed.
    fn narrowable(&self, name: &str) -> Option<Ty> {
        if self.ctx.last().is_some_and(|c| c.no_narrow.contains(name)) {
            return None;
        }
        let declared = self.lookup(name)?;
        match &declared {
            Ty::Union(members) if members.iter().any(|m| matches!(m, Ty::Null | Ty::Void)) => {
                Some(strip_null(&declared))
            }
            _ => None,
        }
    }

    fn narrow(&mut self, name: &str, ty: Ty) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(narrow_key(name), ty);
        }
    }

    fn forget_narrowing(&mut self, name: &str) {
        let key = narrow_key(name);
        for scope in &mut self.scopes {
            scope.remove(&key);
        }
    }

    /// `x != null`, `x == null` or a truthiness test of a nullable variable:
    /// returns the variable, its non-null type and whether the test holds when
    /// the value is non-null.
    fn null_test(&self, cond: &Expr) -> Option<(String, Ty, bool)> {
        let (name, non_null_when_true) = match cond.kind() {
            ExprKind::Group(inner) => return self.null_test(inner),
            ExprKind::Ident(name) => (name.clone(), true),
            ExprKind::Binary {
                op: op @ (BinOp::Eq | BinOp::Ne),
                a,
                b,
            } => match (a.kind(), b.kind()) {
                (ExprKind::Ident(name), ExprKind::LitNull)
                | (ExprKind::LitNull, ExprKind::Ident(name)) => (name.clone(), *op == BinOp::Ne),
                _ => return None,
            },
            _ => return None,
        };
        let ty = self.narrowable(&name)?;
        Some((name, ty, non_null_when_true))
    }

    fn block_narrowed(&mut self, block: &mut Block, narrowing: Option<(&str, &Ty)>) {
        self.scopes.push(StdMap::new());
        if let Some((name, ty)) = narrowing {
            self.narrow(name, ty.clone());
        }
        for stmt in &mut block.stmts {
            self.stmt(stmt);
        }
        self.scopes.pop();
    }

    /// Loop bodies run repeatedly: drop narrowings of anything they reassign.
    fn forget_assigned_in_loop(&mut self, parts: &[&Expr], body: &Block) {
        let mut assigned = StdSet::new();
        for part in parts {
            assigned_in_expr(part, false, &mut assigned, &mut StdSet::new());
        }
        for stmt in &body.stmts {
            assigned_in_stmt(stmt, false, &mut assigned, &mut StdSet::new());
        }
        for name in assigned {
            self.forget_narrowing(&name);
        }
    }

    fn function(
        &mut self,
        name: &str,
        params: &[String],
        types: Option<&FnTypes>,
        body: &mut Block,
        is_async: bool,
        this_ty: Ty,
    ) -> Sig {
        let mark = match types {
            Some(types) => self.push_type_params(&types.type_params),
            None => self.type_scope.len(),
        };
        let sig = self.sig_in(params.len(), types, is_async, &StdMap::new());
        let ret = types.and_then(|t| t.ret.as_ref()).map(|_| match &sig.ret {
            Ty::Promise(inner) if is_async => (**inner).clone(),
            ret => ret.clone(),
        });
        let mut scope = StdMap::new();
        for (param, ty) in params.iter().zip(&sig.params) {
            scope.insert(param.clone(), ty.clone());
        }
        let narrow_floor = self.scopes.len();
        self.scopes.push(scope);
        let mut no_narrow = StdSet::new();
        for stmt in &body.stmts {
            assigned_in_stmt(stmt, false, &mut StdSet::new(), &mut no_narrow);
        }
        self.ctx.push(FnCtx {
            name: name.to_string(),
            ret: ret.clone(),
            this_ty,
            narrow_floor,
            no_narrow,
            infer_locals: types.is_some(),
        });
        for stmt in &mut body.stmts {
            self.stmt(stmt);
        }
        if let Some(ret) = &ret {
            if !accepts_null(ret) && !block_returns(body) {
                self.error(format!(
                    "function lacks an ending return statement and its return type `{ret}` does not include null"
                ));
            }
        }
        self.ctx.pop();
        self.scopes.pop();

        if let Some(types) = types {
            let mut guards = Vec::new();
            for (i, param) in params.iter().enumerate() {
                if types.params.get(i).is_none_or(Option::is_none) {
                    continue;
                }
                if let Some(check) = self.rt_check(&sig.params[i]) {
                    guards.push(stmt_unknown(StmtKind::Expr(expr_unknown(ExprKind::Typed {
                        op: TypedOp::Assert {
                            check,
                            message: format!(
                                "TypeError: parameter `{param}` of `{name}` expects {}",
                                sig.params[i]
                            ),
                        },
                        args: vec![expr_unknown(ExprKind::Ident(param.clone()))],
                    }))));
                }
            }
            body.stmts.splice(0..0, guards);
        }
        self.type_scope.truncate(mark);
        sig
    }

    fn push_decl_ctx(&mut self, name: String) {
        self.ctx.push(FnCtx {
            name,
            ret: None,
            this_ty: Ty::Any,
            narrow_floor: self.scopes.len(),
            no_narrow: StdSet::new(),
            infer_locals: false,
        });
    }

    fn class(&mut self, class: &mut ClassDecl) {
        let name = class.name.clone();
        let mark = self.push_type_params(&class.type_params);
        // Resolve member annotations in their own context first so that
        // diagnostics name the member that contains the bad annotation.
        for member in &class.members {
            match member {
                ClassMember::Method { name: method, params, types, is_async, .. } => {
                    self.push_decl_ctx(format!("{name}.{method}"));
                    self.declared_sig(params, types.as_deref(), *is_async);
                    self.ctx.pop();
                }
                ClassMember::Constructor { params, types, is_async, .. } => {
                    self.push_decl_ctx(format!("{name}.constructor"));
                    self.declared_sig(params, types.as_deref(), *is_async);
                    self.ctx.pop();
                }
                ClassMember::Stored { name: field, type_ann: Some(ty), .. }
                | ClassMember::Accessor { name: field, type_ann: Some(ty), .. } => {
                    self.push_decl_ctx(format!("{name}.{field}"));
                    self.resolve(ty);
                    self.ctx.pop();
                }
                _ => {}
            }
        }
        let this_ty = Ty::Named(
            name.clone(),
            class
                .type_params
                .iter()
                .map(|p| Ty::Param(p.name.clone()))
                .collect(),
        );
        self.ctx.push(FnCtx {
            name: name.clone(),
            ret: None,
            this_ty: this_ty.clone(),
            narrow_floor: self.scopes.len(),
            no_narrow: StdSet::new(),
            infer_locals: false,
        });
        if let Some(base) = &class.base {
            if !class.base_args.is_empty() || self.classes.contains_key(base) {
                let base_ty = self.resolve_name(base, &class.base_args, &StdMap::new());
                if !matches!(base_ty, Ty::Named(..) | Ty::Any) {
                    self.error(format!("class `{name}` cannot extend `{base_ty}`"));
                }
            }
        }
        let implements = class.implements.clone();
        for parent in &implements {
            let parent = self.resolve(parent);
            self.check_implements(&name, &this_ty, &parent);
        }
        self.ctx.pop();

        for member in &mut class.members {
            match member {
                ClassMember::Stored {
                    is_static,
                    name: field,
                    type_ann,
                    init,
                } => {
                    let declared = type_ann.as_ref().map(|t| self.resolve(t));
                    let this_ty = if *is_static { Ty::Any } else { this_ty.clone() };
                    self.ctx.push(FnCtx {
                        name: format!("{name}.{field}"),
                        ret: None,
                        this_ty,
                        narrow_floor: self.scopes.len(),
                        no_narrow: StdSet::new(),
                        infer_locals: false,
                    });
                    self.scopes.push(StdMap::new());
                    if let Some(init) = init {
                        let ty = self.expr(init);
                        if let Some(declared) = &declared {
                            self.coerce(init, &ty, declared, &format!("field `{field}`"));
                        }
                    }
                    self.scopes.pop();
                    self.ctx.pop();
                }
                ClassMember::Accessor {
                    is_static,
                    name: field,
                    getter,
                    setter_param,
                    setter_body,
                    type_ann,
                } => {
                    let this_ty = if *is_static { Ty::Any } else { this_ty.clone() };
                    if let Some(getter) = getter {
                        let types = type_ann.as_ref().map(|t| FnTypes {
                            ret: Some(t.clone()),
                            ..FnTypes::default()
                        });
                        self.function(
                            &format!("{name}.get {field}"),
                            &[],
                            types.as_ref(),
                            getter,
                            false,
                            this_ty.clone(),
                        );
                    }
                    if let (Some(param), Some(body)) = (setter_param, setter_body) {
                        let types = type_ann.as_ref().map(|t| FnTypes {
                            params: vec![Some(t.clone())],
                            optional: vec![false],
                            ..FnTypes::default()
                        });
                        self.function(
                            &format!("{name}.set {field}"),
                            std::slice::from_ref(param),
                            types.as_ref(),
                            body,
                            false,
                            this_ty,
                        );
                    }
                }
                ClassMember::Method {
                    is_static,
                    name: method,
                    params,
                    body,
                    is_async,
                    types,
                } => {
                    let this_ty = if *is_static { Ty::Any } else { this_ty.clone() };
                    self.function(
                        &format!("{name}.{method}"),
                        params,
                        types.as_deref(),
                        body,
                        *is_async,
                        this_ty,
                    );
                }
                ClassMember::Constructor {
                    params,
                    body,
                    is_async,
                    types,
                } => {
                    self.function(
                        &format!("{name}.constructor"),
                        params,
                        types.as_deref(),
                        body,
                        *is_async,
                        this_ty.clone(),
                    );
                }
                ClassMember::Destructor { body } => {
                    self.function(
                        &format!("{name}.destructor"),
                        &[],
                        None,
                        body,
                        false,
                        this_ty.clone(),
                    );
                }
            }
        }
        self.type_scope.truncate(mark);
    }

    fn check_implements(&mut self, class: &str, this_ty: &Ty, parent: &Ty) {
        let Some((required, _)) = (match parent {
            Ty::Named(..) | Ty::Object(_) => self.members(parent),
            Ty::Any => return,
            _ => None,
        }) else {
            self.error(format!("class `{class}` can only implement object types, not `{parent}`"));
            return;
        };
        let (available, _) = self.members(this_ty).unwrap_or_default();
        for want in required {
            match available.iter().find(|m| m.name == want.name) {
                Some(have) => {
                    let have = have.ty.clone();
                    if let Err(reason) = self.compat(&have, &want.ty) {
                        self.error(format!(
                            "class `{class}` incorrectly implements `{parent}`: property `{}` has type `{have}`, expected `{}`{}",
                            want.name,
                            want.ty,
                            detail(&reason)
                        ));
                    }
                }
                None if want.optional => {}
                None => self.error(format!(
                    "class `{class}` incorrectly implements `{parent}`: property `{}` is missing",
                    want.name
                )),
            }
        }
    }

    fn block(&mut self, block: &mut Block) {
        self.scopes.push(StdMap::new());
        for stmt in &mut block.stmts {
            self.stmt(stmt);
        }
        self.scopes.pop();
    }

    fn stmt(&mut self, stmt: &mut Stmt) {
        let previous = self.span.replace(stmt.meta.clone());
        self.stmt_kind(stmt);
        self.span = previous;
    }

    fn stmt_kind(&mut self, stmt: &mut Stmt) {
        match &mut stmt.kind {
            StmtKind::Var { name, init, ty } => {
                let declared = ty.as_ref().map(|t| self.resolve(t));
                let actual = init.as_mut().map(|init| self.expr(init));
                match declared {
                    Some(declared) => {
                        match (init.as_mut(), actual) {
                            (Some(init), Some(actual)) => {
                                self.coerce(init, &actual, &declared, &format!("variable `{name}`"));
                            }
                            _ if !accepts_null(&declared) => self.error(format!(
                                "variable `{name}` of type `{declared}` must be initialized"
                            )),
                            _ => {}
                        }
                        let name = name.clone();
                        self.declare(&name, declared);
                    }
                    None => {
                        let infer = self.ctx.last().is_some_and(|c| c.infer_locals);
                        let ty = match actual {
                            Some(actual) if infer => widen_inferred(actual),
                            _ => Ty::Any,
                        };
                        let name = name.clone();
                        self.declare(&name, ty);
                    }
                }
            }
            StmtKind::VarDestruct { pattern, init } => {
                self.expr(init);
                let mut names: Vec<String> =
                    pattern.fields.iter().map(|f| f.binding.clone()).collect();
                names.extend(pattern.rest.clone());
                for name in names {
                    self.declare(&name, Ty::Any);
                }
            }
            StmtKind::Enum { name, init, .. } => {
                self.expr(init);
                let name = name.clone();
                self.declare(&name, Ty::Any);
            }
            StmtKind::If {
                cond,
                then_b,
                else_b,
            } => {
                let test = self.null_test(cond);
                self.expr(cond);
                let then_narrowing = test
                    .as_ref()
                    .filter(|(_, _, when_true)| *when_true)
                    .map(|(name, ty, _)| (name.as_str(), ty));
                self.block_narrowed(then_b, then_narrowing);
                if let Some(else_b) = else_b {
                    let else_narrowing = test
                        .as_ref()
                        .filter(|(_, _, when_true)| !*when_true)
                        .map(|(name, ty, _)| (name.as_str(), ty));
                    self.block_narrowed(else_b, else_narrowing);
                }
                // `if (x == null) return;` narrows `x` for the rest of the block.
                if let Some((name, ty, when_true)) = test {
                    let exits = if when_true {
                        else_b.as_ref().is_some_and(block_returns)
                    } else {
                        block_returns(then_b)
                    };
                    if exits && self.narrowable(&name).is_some() {
                        self.narrow(&name, ty);
                    }
                }
            }
            StmtKind::While { cond, body } => {
                self.forget_assigned_in_loop(&[&*cond], body);
                self.expr(cond);
                self.block(body);
            }
            StmtKind::For {
                init,
                cond,
                step,
                body,
            } => {
                self.scopes.push(StdMap::new());
                if let Some(init) = init {
                    self.stmt(init);
                }
                let parts: Vec<&Expr> = cond.iter().chain(step.iter()).collect();
                self.forget_assigned_in_loop(&parts, body);
                if let Some(cond) = cond {
                    self.expr(cond);
                }
                if let Some(step) = step {
                    self.expr(step);
                }
                self.block(body);
                self.scopes.pop();
            }
            StmtKind::Try {
                try_block,
                catch,
                finally_block,
            } => {
                self.block(try_block);
                if let Some(catch) = catch {
                    self.scopes.push(StdMap::new());
                    if let Some(binding) = &catch.binding {
                        let binding = binding.clone();
                        self.declare(&binding, Ty::Any);
                    }
                    self.block(&mut catch.body);
                    self.scopes.pop();
                }
                if let Some(finally_block) = finally_block {
                    self.block(finally_block);
                }
            }
            StmtKind::Throw(e) | StmtKind::Expr(e) => {
                self.expr(e);
            }
            StmtKind::Defer { binding, body, .. } => {
                self.scopes.push(StdMap::new());
                if let Some(binding) = binding {
                    let binding = binding.clone();
                    self.declare(&binding, Ty::Any);
                }
                self.block(body);
                self.scopes.pop();
            }
            StmtKind::Return(value) => {
                let ret = self.ctx.last().and_then(|c| c.ret.clone());
                match (value, ret) {
                    (Some(value), Some(ret)) => {
                        let actual = self.expr(value);
                        self.coerce(value, &actual, &ret, "return value");
                    }
                    (Some(value), None) => {
                        self.expr(value);
                    }
                    (None, Some(ret)) if !accepts_null(&ret) => {
                        self.error(format!("missing return value of type `{ret}`"));
                    }
                    (None, _) => {}
                }
            }
            StmtKind::Listen(_) => {}
        }
    }

    // ---------------------------------------------------------------------
    // Expressions
    // ---------------------------------------------------------------------

    fn expr(&mut self, e: &mut Expr) -> Ty {
        let mut rewrite: Option<ExprKind> = None;
        let ty = match &mut e.kind {
            ExprKind::LitInt(n) => Ty::Literal(TypeLiteral::Number(*n as f64)),
            ExprKind::LitF64(n) => Ty::Literal(TypeLiteral::Number(*n)),
            ExprKind::LitBool(v) => Ty::Literal(TypeLiteral::Bool(*v)),
            ExprKind::LitNull => Ty::Null,
            ExprKind::Str(s) => Ty::Literal(TypeLiteral::String(s.clone())),
            ExprKind::FnRef { .. } => Ty::Any,
            ExprKind::Ident(name) => self.ident(name),
            ExprKind::Group(inner) => self.expr(inner),
            ExprKind::Binary {
                op: op @ (BinOp::And | BinOp::Or),
                a,
                b,
            } => {
                // `x != null && x.length` / `x == null || x.length`
                let test = self.null_test(a);
                let ta = self.expr(a);
                let narrowing = test.filter(|(_, _, when_true)| *when_true == (*op == BinOp::And));
                self.scopes.push(StdMap::new());
                if let Some((name, ty, _)) = narrowing {
                    self.narrow(&name, ty);
                }
                let tb = self.expr(b);
                self.scopes.pop();
                self.binary(op, a, b, ta, tb, &mut rewrite)
            }
            ExprKind::This => self.ctx.last().map(|c| c.this_ty.clone()).unwrap_or(Ty::Any),
            ExprKind::Assign(target, value) => self.assign(target, value, &mut rewrite),
            ExprKind::Conditional {
                cond,
                then_branch,
                else_branch,
            } => {
                self.expr(cond);
                let a = self.expr(then_branch);
                let b = self.expr(else_branch);
                union([a, b])
            }
            ExprKind::Binary { op, a, b } => {
                let ta = self.expr(a);
                let tb = self.expr(b);
                self.binary(op, a, b, ta, tb, &mut rewrite)
            }
            ExprKind::Unary { op, e: inner } => {
                let ty = self.expr(inner);
                match op {
                    UnOp::Not => Ty::Bool,
                    _ => {
                        self.expect_number(&ty, "unary operator");
                        Ty::Number
                    }
                }
            }
            ExprKind::Call { callee, args } => self.call(callee, args, None),
            ExprKind::GetProp { recv, name } => {
                if let ExprKind::Ident(enum_name) = recv.kind() {
                    if let Some((_, members)) = self.enums.get(enum_name) {
                        return members.get(name.as_str()).cloned().unwrap_or(Ty::Any);
                    }
                }
                let recv_ty = self.expr(recv);
                let recv_ty = self.normalize(recv_ty);
                match (&recv_ty, name.as_str()) {
                    (Ty::Array(_) | Ty::Tuple(_), "length") => {
                        rewrite = Some(ExprKind::Typed {
                            op: TypedOp::ArrayLen,
                            args: vec![take(recv)],
                        });
                        Ty::Number
                    }
                    (Ty::Str | Ty::Literal(TypeLiteral::String(_)), "length") => {
                        rewrite = Some(ExprKind::Typed {
                            op: TypedOp::StrLen,
                            args: vec![take(recv)],
                        });
                        Ty::Number
                    }
                    _ => self.prop_type(&recv_ty, name),
                }
            }
            ExprKind::GetPropObj { obj, key } => {
                let recv_ty = self.expr(obj);
                let name = prop_key_name(key).to_string();
                self.prop_type(&recv_ty, &name)
            }
            ExprKind::SetPropObj { obj, key, value } => {
                let recv_ty = self.expr(obj);
                let value_ty = self.expr(value);
                let name = prop_key_name(key).to_string();
                let field_ty = self.prop_type(&recv_ty, &name);
                self.coerce(value, &value_ty, &field_ty, &format!("property `{name}`"));
                value_ty
            }
            ExprKind::Index { recv, index } => {
                let recv_ty = self.expr(recv);
                let recv_ty = self.normalize(recv_ty);
                let index_ty = self.expr(index);
                let index_ty = widen_scalar(index_ty);
                match (&recv_ty, &index_ty) {
                    (Ty::Tuple(items), Ty::Number) => {
                        if let ExprKind::LitInt(i) = index.kind() {
                            if *i < 0 || *i as usize >= items.len() {
                                self.error(format!("tuple index {i} is out of bounds"));
                                Ty::Never
                            } else { items[*i as usize].clone() }
                        } else { union(items.clone()) }
                    }
                    (Ty::Unknown, _) => {
                        self.error("cannot index a value of type `unknown`".into()); Ty::Any
                    }
                    (Ty::Array(element), Ty::Number) => {
                        let element = (**element).clone();
                        rewrite = Some(ExprKind::Typed {
                            op: TypedOp::ArrayGet,
                            args: vec![take(recv), take(index)],
                        });
                        element
                    }
                    (Ty::Str, Ty::Number) => Ty::Str,
                    _ => match index.kind() {
                        ExprKind::Str(name) => {
                            let name = name.clone();
                            self.prop_type(&recv_ty, &name)
                        }
                        _ => Ty::Any,
                    },
                }
            }
            ExprKind::FnLit {
                params,
                body,
                types,
            } => {
                let outer = self.ctx.last().map(|c| c.name.clone()).unwrap_or_default();
                let sig = self.function(
                    &format!("{outer} (closure)"),
                    params,
                    types.as_deref(),
                    body,
                    false,
                    Ty::Any,
                );
                if types.is_some() {
                    Ty::Func(Rc::new(sig))
                } else {
                    Ty::Any
                }
            }
            ExprKind::ArrayLit(elements) => {
                let types: Vec<Ty> = elements.iter_mut().map(|e| self.expr(e)).collect();
                Ty::Tuple(types)
            }
            ExprKind::SuperProp(_) => Ty::Any,
            ExprKind::SuperCall(args) => {
                for arg in args {
                    self.expr(arg);
                }
                Ty::Any
            }
            ExprKind::New { class, args } => {
                let class = class.clone();
                self.new_instance(&class, args, None)
            }
            ExprKind::ObjLit(items) => {
                let mut members = Vec::new();
                let mut spread = false;
                for item in items {
                    match item {
                        ObjItem::Prop(key, value) => {
                            let ty = self.expr(value);
                            let name = prop_key_name(key).to_string();
                            members.retain(|m: &Member| m.name != name);
                            members.push(Member {
                                name,
                                optional: false,
                                ty,
                                probe: true,
                            });
                        }
                        ObjItem::Spread(value) => {
                            self.expr(value);
                            spread = true;
                        }
                    }
                }
                if spread {
                    Ty::Any
                } else {
                    Ty::Object(Rc::new(members))
                }
            }
            ExprKind::In { key, obj } => {
                self.expr(key);
                self.expr(obj);
                Ty::Bool
            }
            ExprKind::DeleteProp { obj, .. } => {
                self.expr(obj);
                Ty::Any
            }
            ExprKind::DeleteIndex { obj, index } => {
                self.expr(obj);
                self.expr(index);
                Ty::Any
            }
            ExprKind::Await(inner) => match self.expr(inner) {
                Ty::Promise(inner) => *inner,
                _ => Ty::Any,
            },
            ExprKind::OptionalChain { base, access } => {
                self.expr(base);
                match access {
                    OptionalAccess::Prop(_) => {}
                    OptionalAccess::Index(index) => {
                        self.expr(index);
                    }
                    OptionalAccess::Call(args) => {
                        for arg in args {
                            self.expr(arg);
                        }
                    }
                }
                Ty::Any
            }
            ExprKind::CreateBuiltin { kind, args } => {
                let kind = *kind;
                self.create_builtin(kind, args, None)
            }
            ExprKind::CallBuiltinMapMethod { recv, method, args } => {
                let recv_ty = self.expr(recv);
                let recv_ty = self.normalize(recv_ty);
                let arg_types: Vec<Ty> = args.iter_mut().map(|a| self.expr(a)).collect();
                self.map_method(&recv_ty, *method, &arg_types)
            }
            ExprKind::CallBuiltinSetMethod { recv, method, args } => {
                let recv_ty = self.expr(recv);
                let recv_ty = self.normalize(recv_ty);
                let arg_types: Vec<Ty> = args.iter_mut().map(|a| self.expr(a)).collect();
                let method = *method;
                match (strip_null(&recv_ty), method) {
                    (Ty::Set(element), BuiltinSetMethod::Add | BuiltinSetMethod::Has) => {
                        if let Some(arg) = arg_types.first() {
                            self.check_assignable(arg, &element, "set element");
                        }
                        if method == BuiltinSetMethod::Has { Ty::Bool } else { recv_ty }
                    }
                    (Ty::Set(_), BuiltinSetMethod::Delete) => Ty::Bool,
                    _ => Ty::Any,
                }
            }
            ExprKind::CallBuiltinCommonMethod { recv, .. } => {
                self.expr(recv);
                Ty::Any
            }
            ExprKind::GetBuiltinSize(inner) => match self.expr(inner) {
                Ty::Map(..) | Ty::Set(_) => Ty::Number,
                _ => Ty::Any,
            },
            ExprKind::Typed { op, args } => match op {
                TypedOp::TypeArgs(type_args) => {
                    let type_args: Vec<Ty> = type_args.iter().map(|t| self.resolve(t)).collect();
                    let mut inner = args.pop().expect("type arguments wrap an expression");
                    let ty = self.with_type_args(&mut inner, type_args);
                    *e = inner;
                    return ty;
                }
                TypedOp::Cast(target) => {
                    let target = target.clone();
                    let mut inner = args.pop().expect("cast wraps an expression");
                    let ty = self.cast(&mut inner, &target);
                    *e = inner;
                    return ty;
                }
                _ => {
                    for arg in args {
                        self.expr(arg);
                    }
                    Ty::Any
                }
            },
        };
        if let Some(kind) = rewrite {
            e.kind = kind;
        }
        ty
    }

    fn ident(&mut self, name: &str) -> Ty {
        if let Some(ty) = self.lookup_read(name) {
            return ty;
        }
        if !self.imported.contains(name) {
            if let Some(sig) = self.funcs.get(name) {
                return if sig.checked {
                    Ty::Func(sig.clone())
                } else {
                    Ty::Any
                };
            }
        }
        Ty::Any
    }

    fn expect_number(&mut self, ty: &Ty, what: &str) {
        if !matches!(ty, Ty::Any | Ty::Number | Ty::Literal(TypeLiteral::Number(_)) | Ty::Param(_)) {
            self.error(format!("{what} expects a number, found `{ty}`"));
        }
    }

    fn binary(
        &mut self,
        op: &mut BinOp,
        a: &mut Expr,
        b: &mut Expr,
        ta: Ty,
        tb: Ty,
        rewrite: &mut Option<ExprKind>,
    ) -> Ty {
        let (ta, tb) = (widen_scalar(ta), widen_scalar(tb));
        if (ta == Ty::Unknown || tb == Ty::Unknown)
            && !matches!(op, BinOp::Eq | BinOp::Ne | BinOp::And | BinOp::Or | BinOp::Nullish)
        {
            self.error("operator cannot be applied to `unknown`; narrow or cast the value first".into());
            return Ty::Any;
        }
        let literal = |e: &Expr| matches!(e.kind(), ExprKind::Str(_));
        let constant = |e: &Expr| {
            matches!(
                e.kind(),
                ExprKind::Str(_) | ExprKind::LitInt(_) | ExprKind::LitF64(_) | ExprKind::LitBool(_) | ExprKind::LitNull
            )
        };
        match *op {
            BinOp::Add => match (&ta, &tb) {
                (Ty::Number, Ty::Number) => Ty::Number,
                (Ty::Str, Ty::Str) => {
                    *rewrite = Some(ExprKind::Typed {
                        op: TypedOp::StrConcat,
                        args: vec![take(a), take(b)],
                    });
                    Ty::Str
                }
                (Ty::Str, Ty::Any) | (Ty::Any, Ty::Str) => {
                    // Literal-only operands keep the untyped semantics; a statically
                    // known string makes `+` a concatenation, as in TypeScript.
                    if literal(a) || literal(b) {
                        Ty::Any
                    } else {
                        *op = BinOp::StrConcat;
                        Ty::Str
                    }
                }
                (Ty::Str, _) | (_, Ty::Str) => {
                    // Typed non-literal operands would otherwise reach integer
                    // addition; coerce them like `__`. Constant-only operands keep
                    // the untyped semantics.
                    if !constant(a) || !constant(b) {
                        *op = BinOp::StrConcat;
                    }
                    Ty::Str
                }
                (Ty::Any, _) | (_, Ty::Any) | (Ty::Param(_), _) | (_, Ty::Param(_)) => Ty::Any,
                _ => {
                    self.error(format!("operator `+` cannot be applied to `{ta}` and `{tb}`"));
                    Ty::Any
                }
            },
            BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Rem
            | BinOp::BitOr
            | BinOp::Shl
            | BinOp::Shr
            | BinOp::ShrU => {
                self.expect_number(&ta, "arithmetic operator");
                self.expect_number(&tb, "arithmetic operator");
                Ty::Number
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => Ty::Bool,
            BinOp::Eq | BinOp::Ne => {
                let negate = *op == BinOp::Ne;
                if ta == Ty::Str && tb == Ty::Str {
                    *rewrite = Some(ExprKind::Typed {
                        op: TypedOp::StrEq { negate },
                        args: vec![take(a), take(b)],
                    });
                } else if (is_identity_primitive(&ta) && is_identity_primitive(&tb))
                    || (ta == Ty::Null && !matches!(tb, Ty::Any))
                    || (tb == Ty::Null && !matches!(ta, Ty::Any))
                {
                    *rewrite = Some(ExprKind::Typed {
                        op: TypedOp::PrimEq { negate },
                        args: vec![take(a), take(b)],
                    });
                }
                Ty::Bool
            }
            BinOp::And | BinOp::Or => {
                if ta == Ty::Bool && tb == Ty::Bool {
                    Ty::Bool
                } else {
                    Ty::Any
                }
            }
            BinOp::StrConcat => Ty::Str,
            BinOp::Nullish => union([strip_null(&ta), tb]),
        }
    }

    fn assign(
        &mut self,
        target: &mut LValue,
        value: &mut Expr,
        rewrite: &mut Option<ExprKind>,
    ) -> Ty {
        match &mut target.kind {
            LValueKind::Ident(name) => {
                let actual = self.expr(value);
                let declared = self.lookup(name).unwrap_or(Ty::Any);
                let name = name.clone();
                self.forget_narrowing(&name);
                self.coerce(value, &actual, &declared, &format!("assignment to `{name}`"));
                if matches!(declared, Ty::Any) { actual } else { declared }
            }
            LValueKind::GetProp { recv, name } => {
                let recv_ty = self.expr(recv);
                let recv_ty = self.normalize(recv_ty);
                let actual = self.expr(value);
                let name = name.clone();
                let field = self.prop_type(&recv_ty, &name);
                self.coerce(value, &actual, &field, &format!("property `{name}`"));
                actual
            }
            LValueKind::Index { recv, index } => {
                let recv_ty = self.expr(recv);
                let recv_ty = self.normalize(recv_ty);
                let index_ty = self.expr(index);
                let index_ty = widen_scalar(index_ty);
                let actual = self.expr(value);
                if let (Ty::Array(element), Ty::Number) = (&recv_ty, &index_ty) {
                    let element = (**element).clone();
                    self.check_assignable(&actual, &element, "array element");
                    *rewrite = Some(ExprKind::Typed {
                        op: TypedOp::ArraySet,
                        args: vec![take(recv), take(index), take(value)],
                    });
                }
                actual
            }
        }
    }

    fn prop_type(&mut self, ty: &Ty, name: &str) -> Ty {
        match ty {
            Ty::Unknown => { self.error(format!("cannot access property `{name}` on `unknown`")); return Ty::Any; }
            Ty::Literal(lit) => return self.prop_type(&literal_base(lit), name),
            Ty::Tuple(items) => return self.prop_type(&Ty::Array(Box::new(union(items.clone()))), name),
            Ty::Deferred(..) => {
                let normalized = self.normalize(ty.clone());
                if &normalized != ty { return self.prop_type(&normalized, name); }
                return Ty::Unknown;
            }
            _ => {}
        }
        match ty {
            Ty::Any | Ty::Never | Ty::Number | Ty::Bool | Ty::Func(_) | Ty::Promise(_) => Ty::Any,
            Ty::Map(..) | Ty::Set(_) => Ty::Any,
            Ty::Array(_) | Ty::Str => {
                if name == "length" {
                    Ty::Number
                } else {
                    Ty::Any
                }
            }
            Ty::Null | Ty::Void => {
                self.error(format!("cannot access property `{name}` of null"));
                Ty::Any
            }
            Ty::Union(_) => {
                let non_null = strip_null(ty);
                if matches!(non_null, Ty::Union(_)) {
                    let Ty::Union(members) = non_null else { unreachable!() };
                    let types: Vec<Ty> = members.iter().map(|m| self.prop_type(m, name)).collect();
                    union(types)
                } else {
                    self.prop_type(&non_null, name)
                }
            }
            Ty::Param(param) => match self.constraint_of(param) {
                Some(constraint) => self.prop_type(&constraint, name),
                None => Ty::Any,
            },
            Ty::Object(_) | Ty::Named(..) => match self.members(ty) {
                Some((members, open)) => match members.into_iter().find(|m| m.name == name) {
                    Some(member) if member.optional => union([member.ty, Ty::Null]),
                    Some(member) => member.ty,
                    None if open => Ty::Any,
                    None => {
                        self.error(format!("property `{name}` does not exist on type `{ty}`"));
                        Ty::Any
                    }
                },
                None => Ty::Any,
            },
            Ty::Unknown | Ty::Literal(_) | Ty::Tuple(_) | Ty::Deferred(..) => unreachable!(),
        }
    }

    fn call(&mut self, callee: &mut Expr, args: &mut Vec<Expr>, type_args: Option<Vec<Ty>>) -> Ty {
        if let ExprKind::Ident(name) = callee.kind() {
            if !self.is_local(name) && !self.imported.contains(name) {
                if let Some(sig) = self.funcs.get(name).cloned() {
                    let name = name.clone();
                    return self.check_call(&sig, args, type_args, &format!("`{name}`"), true);
                }
            }
        }
        if let ExprKind::GetProp { recv, name } = &mut callee.kind {
            let is_enum = matches!(recv.kind(), ExprKind::Ident(n) if self.enums.contains_key(n));
            if !is_enum {
                let recv_ty = self.expr(recv);
                let recv_ty = self.normalize(recv_ty);
                let name = name.clone();
                return match strip_null(&recv_ty) {
                    Ty::Array(element) => self.array_method(&element, &name, args),
                    Ty::Tuple(items) => self.array_method(&union(items.into_iter().map(widen_scalar)), &name, args),
                    Ty::Str | Ty::Literal(TypeLiteral::String(_)) => self.string_method(&name, args),
                    _ => match self.prop_type(&recv_ty, &name) {
                        Ty::Func(sig) => {
                            self.check_call(&sig, args, type_args, &format!("`{name}`"), false)
                        }
                        _ => self.dynamic_args(args),
                    },
                };
            }
        }
        match self.expr(callee) {
            Ty::Unknown => {
                self.error("cannot call a value of type `unknown`".into());
                self.dynamic_args(args)
            }
            Ty::Func(sig) => self.check_call(&sig, args, type_args, "function value", false),
            _ => self.dynamic_args(args),
        }
    }

    fn dynamic_args(&mut self, args: &mut [Expr]) -> Ty {
        for arg in args {
            self.expr(arg);
        }
        Ty::Any
    }

    /// `direct`: callee is a declared function whose entry guards check its parameters.
    fn check_call(
        &mut self,
        sig: &Sig,
        args: &mut Vec<Expr>,
        type_args: Option<Vec<Ty>>,
        what: &str,
        direct: bool,
    ) -> Ty {
        let arg_types: Vec<Ty> = args.iter_mut().map(|a| self.expr(a)).collect();
        let mut map = StdMap::new();
        let names: Vec<String> = sig.type_params.iter().map(|(n, _)| n.clone()).collect();
        match type_args {
            Some(explicit) if explicit.len() != names.len() => {
                self.error(format!(
                    "{what} expects {} type argument(s), got {}",
                    names.len(),
                    explicit.len()
                ));
            }
            Some(explicit) => map.extend(names.iter().cloned().zip(explicit)),
            None if !sig.variadic => {
                for (param, actual) in sig.params.iter().zip(&arg_types) {
                    self.infer(param, actual, &names, &mut map);
                }
            }
            None => {}
        }
        for (name, constraint) in &sig.type_params {
            let actual = map.entry(name.clone()).or_insert(Ty::Any).clone();
            if let Some(constraint) = constraint {
                let constraint = subst(constraint, &map);
                if let Err(reason) = self.compat(&actual, &constraint) {
                    self.error(format!(
                        "type `{actual}` does not satisfy the constraint `{constraint}` of `{name}` in {what}{}",
                        detail(&reason)
                    ));
                }
            }
        }
        if sig.variadic {
            return subst(&sig.ret, &map);
        }
        if sig.checked {
            if args.len() > sig.params.len() {
                self.error(format!(
                    "{what} expects at most {} argument(s), got {}",
                    sig.params.len(),
                    args.len()
                ));
            } else if args.len() < sig.min_args {
                self.error(format!(
                    "{what} expects at least {} argument(s), got {}",
                    sig.min_args,
                    args.len()
                ));
            }
        }
        for (i, (arg, actual)) in args.iter_mut().zip(&arg_types).enumerate() {
            let Some(param) = sig.params.get(i) else { break };
            let param = self.normalize(subst(param, &map));
            let label = format!("argument {} of {what}", i + 1);
            if direct && sig.type_params.is_empty() {
                self.check_assignable(actual, &param, &label);
            } else {
                self.coerce(arg, actual, &param, &label);
            }
        }
        if sig.checked {
            while args.len() < sig.params.len() {
                args.push(expr_unknown(ExprKind::LitNull));
            }
        }
        self.normalize(subst(&sig.ret, &map))
    }

    fn array_method(&mut self, element: &Ty, name: &str, args: &mut [Expr]) -> Ty {
        let arg_types: Vec<Ty> = args.iter_mut().map(|a| self.expr(a)).collect();
        let element = element.clone();
        match name {
            "push" | "unshift" => {
                for ty in &arg_types {
                    self.check_assignable(ty, &element, &format!("argument of `{name}`"));
                }
                Ty::Number
            }
            "pop" | "shift" | "find" => element,
            "indexOf" | "lastIndexOf" | "findIndex" => Ty::Number,
            "includes" | "some" | "every" => Ty::Bool,
            "join" => Ty::Str,
            "slice" | "concat" | "reverse" | "sort" | "filter" | "fill" | "splice" => {
                Ty::Array(Box::new(element))
            }
            "map" => match arg_types.first() {
                Some(Ty::Func(sig)) => Ty::Array(Box::new(sig.ret.clone())),
                _ => Ty::Array(Box::new(Ty::Any)),
            },
            "forEach" => Ty::Null,
            _ => Ty::Any,
        }
    }

    fn string_method(&mut self, name: &str, args: &mut [Expr]) -> Ty {
        for arg in args.iter_mut() {
            self.expr(arg);
        }
        match name {
            "toUpperCase" | "toLowerCase" | "trim" | "trimStart" | "trimEnd" | "slice"
            | "substring" | "charAt" | "repeat" | "replace" | "replaceAll" | "padStart"
            | "padEnd" | "concat" => Ty::Str,
            "indexOf" | "lastIndexOf" | "charCodeAt" => Ty::Number,
            "startsWith" | "endsWith" | "includes" => Ty::Bool,
            "split" => Ty::Array(Box::new(Ty::Str)),
            _ => Ty::Any,
        }
    }

    fn map_method(&mut self, recv: &Ty, method: BuiltinMapMethod, args: &[Ty]) -> Ty {
        match strip_null(recv) {
            Ty::Map(key, value) => {
                if let Some(arg) = args.first() {
                    if !matches!(method, BuiltinMapMethod::Clear) {
                        self.check_assignable(arg, &key, "map key");
                    }
                }
                match method {
                    BuiltinMapMethod::Get => *value,
                    BuiltinMapMethod::Set => {
                        if let Some(arg) = args.get(1) {
                            self.check_assignable(arg, &value, "map value");
                        }
                        recv.clone()
                    }
                    BuiltinMapMethod::Has | BuiltinMapMethod::Delete => Ty::Bool,
                    _ => Ty::Any,
                }
            }
            Ty::Set(element) => match method {
                BuiltinMapMethod::Has | BuiltinMapMethod::Delete => {
                    if let Some(arg) = args.first() {
                        self.check_assignable(arg, &element, "set element");
                    }
                    Ty::Bool
                }
                _ => Ty::Any,
            },
            _ => Ty::Any,
        }
    }

    fn new_instance(&mut self, class: &str, args: &mut Vec<Expr>, type_args: Option<Vec<Ty>>) -> Ty {
        let Some(info) = self.classes.get(class).cloned() else {
            if type_args.is_some() && !self.imported.contains(class) {
                self.error(format!("unknown class `{class}`"));
            }
            return self.dynamic_args(args);
        };
        let saved = std::mem::take(&mut self.type_scope);
        let mark = self.push_type_params(&info.type_params);
        let type_params: Vec<(String, Option<Ty>)> = self.type_scope[mark..].to_vec();
        let ctor = match &info.ctor {
            Some((count, types)) => self.sig_in(*count, types.as_deref(), false, &StdMap::new()),
            None => Sig {
                variadic: true,
                ..Sig::dynamic(0)
            },
        };
        self.type_scope = saved;
        let sig = Sig {
            ret: Ty::Named(
                class.to_string(),
                info.type_params
                    .iter()
                    .map(|p| Ty::Param(p.name.clone()))
                    .collect(),
            ),
            type_params,
            ..ctor
        };
        self.check_call(&sig, args, type_args, &format!("`new {class}`"), true)
    }

    fn create_builtin(&mut self, kind: BuiltinType, args: &mut [Expr], type_args: Option<Vec<Ty>>) -> Ty {
        for arg in args.iter_mut() {
            self.expr(arg);
        }
        let type_args = type_args.unwrap_or_default();
        let arg = |i: usize| Box::new(type_args.get(i).cloned().unwrap_or(Ty::Any));
        let (ty, expected) = match kind {
            BuiltinType::Map => (Ty::Map(arg(0), arg(1)), 2),
            BuiltinType::Set => (Ty::Set(arg(0)), 1),
            BuiltinType::Proxy => (Ty::Any, 0),
        };
        if !type_args.is_empty() && type_args.len() != expected {
            self.error(format!(
                "built-in constructor expects {expected} type argument(s), got {}",
                type_args.len()
            ));
        }
        ty
    }

    fn with_type_args(&mut self, inner: &mut Expr, type_args: Vec<Ty>) -> Ty {
        match &mut inner.kind {
            ExprKind::Call { callee, args } => self.call(callee, args, Some(type_args)),
            ExprKind::New { class, args } => {
                let class = class.clone();
                self.new_instance(&class, args, Some(type_args))
            }
            ExprKind::CreateBuiltin { kind, args } => {
                let kind = *kind;
                self.create_builtin(kind, args, Some(type_args))
            }
            _ => self.expr(inner),
        }
    }

    fn cast(&mut self, inner: &mut Expr, target: &TypeExpr) -> Ty {
        let source = self.expr(inner);
        let target = self.resolve(target);
        if matches!(target, Ty::Any) || self.compat(&source, &target).is_ok() && !matches!(source, Ty::Any) {
            return target;
        }
        if matches!(source, Ty::Any) || self.compat(&target, &source).is_ok() {
            if let Some(check) = self.rt_check(&target) {
                wrap(inner, TypedOp::Assert {
                    check,
                    message: format!("TypeError: cannot cast value to {target}"),
                });
            }
            return target;
        }
        self.error(format!("cannot cast type `{source}` to unrelated type `{target}`"));
        target
    }
}

fn zip_args(params: &[TypeParam], args: &[Ty]) -> StdMap<String, Ty> {
    params
        .iter()
        .enumerate()
        .map(|(i, p)| (p.name.clone(), args.get(i).cloned().unwrap_or(Ty::Any)))
        .collect()
}

fn order_args(params: &[TypeParam], map: StdMap<String, Ty>) -> Vec<Ty> {
    params
        .iter()
        .map(|p| map.get(&p.name).cloned().unwrap_or(Ty::Any))
        .collect()
}

fn detail(reason: &str) -> String {
    if reason.is_empty() {
        String::new()
    } else {
        format!(" ({reason})")
    }
}

fn prop_key_name(key: &PropKey) -> &str {
    match key {
        PropKey::Ident(name) | PropKey::Str(name) => name,
    }
}

fn class_info(class: &ClassDecl) -> ClassInfo {
    let mut members = Vec::new();
    let mut ctor = None;
    let mut typed = !class.type_params.is_empty()
        || !class.base_args.is_empty()
        || !class.implements.is_empty();
    for member in &class.members {
        match member {
            ClassMember::Stored {
                is_static: false,
                name,
                type_ann,
                ..
            } => {
                typed |= type_ann.is_some();
                members.push((name.clone(), ClassMemberSrc::Field(type_ann.clone(), true)));
            }
            ClassMember::Accessor {
                is_static: false,
                name,
                type_ann,
                ..
            } => {
                typed |= type_ann.is_some();
                members.push((name.clone(), ClassMemberSrc::Field(type_ann.clone(), false)));
            }
            ClassMember::Method {
                is_static: false,
                name,
                params,
                is_async,
                types,
                ..
            } => {
                typed |= types.is_some();
                members.push((
                    name.clone(),
                    ClassMemberSrc::Method {
                        params: params.len(),
                        types: types.clone(),
                        is_async: *is_async,
                    },
                ));
            }
            ClassMember::Constructor {
                params, body, types, ..
            } => {
                typed |= types.is_some();
                ctor = Some((params.len(), types.clone()));
                let mut assigned = Vec::new();
                collect_this_fields(&body.stmts, &mut assigned);
                for name in assigned {
                    members.push((name, ClassMemberSrc::Field(None, true)));
                }
            }
            _ => {}
        }
    }
    ClassInfo {
        type_params: class.type_params.clone(),
        base: class
            .base
            .as_ref()
            .map(|b| (b.clone(), class.base_args.clone())),
        members,
        ctor,
        typed,
    }
}

/// Initializers that say nothing useful about later assignments stay dynamic.
fn widen_inferred(ty: Ty) -> Ty {
    match ty {
        Ty::Literal(lit) => literal_base(&lit),
        Ty::Tuple(items) => Ty::Array(Box::new(union(items.into_iter().map(widen_inferred)))),
        Ty::Null | Ty::Void | Ty::Never => Ty::Any,
        Ty::Object(members) if members.is_empty() => Ty::Any,
        ty => ty,
    }
}

fn narrow_key(name: &str) -> String {
    format!("?{name}")
}

/// Collects variables assigned in a statement. Assignments inside closures and
/// defer blocks (which run later) are also recorded in `deferred`.
fn assigned_in_stmt(stmt: &Stmt, late: bool, out: &mut StdSet<String>, deferred: &mut StdSet<String>) {
    let block = |b: &Block, late: bool, out: &mut StdSet<String>, deferred: &mut StdSet<String>| {
        for stmt in &b.stmts {
            assigned_in_stmt(stmt, late, out, deferred);
        }
    };
    match stmt.kind() {
        StmtKind::Enum { init, .. } | StmtKind::VarDestruct { init, .. } => {
            assigned_in_expr(init, late, out, deferred)
        }
        StmtKind::Var { init, .. } => {
            if let Some(init) = init {
                assigned_in_expr(init, late, out, deferred);
            }
        }
        StmtKind::If { cond, then_b, else_b } => {
            assigned_in_expr(cond, late, out, deferred);
            block(then_b, late, out, deferred);
            if let Some(else_b) = else_b {
                block(else_b, late, out, deferred);
            }
        }
        StmtKind::While { cond, body } => {
            assigned_in_expr(cond, late, out, deferred);
            block(body, late, out, deferred);
        }
        StmtKind::For { init, cond, step, body } => {
            if let Some(init) = init {
                assigned_in_stmt(init, late, out, deferred);
            }
            for e in cond.iter().chain(step.iter()) {
                assigned_in_expr(e, late, out, deferred);
            }
            block(body, late, out, deferred);
        }
        StmtKind::Try { try_block, catch, finally_block } => {
            block(try_block, late, out, deferred);
            if let Some(catch) = catch {
                block(&catch.body, late, out, deferred);
            }
            if let Some(finally_block) = finally_block {
                block(finally_block, late, out, deferred);
            }
        }
        StmtKind::Defer { body, .. } => block(body, true, out, deferred),
        StmtKind::Throw(e) | StmtKind::Expr(e) => assigned_in_expr(e, late, out, deferred),
        StmtKind::Return(e) => {
            if let Some(e) = e {
                assigned_in_expr(e, late, out, deferred);
            }
        }
        StmtKind::Listen(_) => {}
    }
}

fn assigned_in_expr(e: &Expr, late: bool, out: &mut StdSet<String>, deferred: &mut StdSet<String>) {
    let each = |exprs: &[&Expr], out: &mut StdSet<String>, deferred: &mut StdSet<String>| {
        for e in exprs {
            assigned_in_expr(e, late, out, deferred);
        }
    };
    match e.kind() {
        ExprKind::LitInt(_)
        | ExprKind::LitF64(_)
        | ExprKind::LitBool(_)
        | ExprKind::LitNull
        | ExprKind::Str(_)
        | ExprKind::Ident(_)
        | ExprKind::FnRef { .. }
        | ExprKind::This
        | ExprKind::SuperProp(_) => {}
        ExprKind::Assign(target, value) => {
            match target.kind() {
                LValueKind::Ident(name) => {
                    out.insert(name.clone());
                    if late {
                        deferred.insert(name.clone());
                    }
                }
                LValueKind::GetProp { recv, .. } => each(&[recv], out, deferred),
                LValueKind::Index { recv, index } => each(&[recv, index], out, deferred),
            }
            each(&[value], out, deferred);
        }
        ExprKind::Conditional { cond, then_branch, else_branch } => {
            each(&[cond, then_branch, else_branch], out, deferred)
        }
        ExprKind::Binary { a, b, .. } => each(&[a, b], out, deferred),
        ExprKind::Unary { e, .. }
        | ExprKind::Group(e)
        | ExprKind::GetProp { recv: e, .. }
        | ExprKind::GetPropObj { obj: e, .. }
        | ExprKind::DeleteProp { obj: e, .. }
        | ExprKind::Await(e)
        | ExprKind::GetBuiltinSize(e)
        | ExprKind::CallBuiltinCommonMethod { recv: e, .. } => each(&[e], out, deferred),
        ExprKind::Index { recv: a, index: b }
        | ExprKind::In { key: a, obj: b }
        | ExprKind::DeleteIndex { obj: a, index: b }
        | ExprKind::SetPropObj { obj: a, value: b, .. } => each(&[a, b], out, deferred),
        ExprKind::Call { callee, args } => {
            each(&[callee], out, deferred);
            for arg in args {
                assigned_in_expr(arg, late, out, deferred);
            }
        }
        ExprKind::CallBuiltinMapMethod { recv, args, .. }
        | ExprKind::CallBuiltinSetMethod { recv, args, .. } => {
            each(&[recv], out, deferred);
            for arg in args {
                assigned_in_expr(arg, late, out, deferred);
            }
        }
        ExprKind::FnLit { body, .. } => {
            for stmt in &body.stmts {
                assigned_in_stmt(stmt, true, out, deferred);
            }
        }
        ExprKind::ArrayLit(args)
        | ExprKind::SuperCall(args)
        | ExprKind::New { args, .. }
        | ExprKind::CreateBuiltin { args, .. }
        | ExprKind::Typed { args, .. } => {
            for arg in args {
                assigned_in_expr(arg, late, out, deferred);
            }
        }
        ExprKind::ObjLit(items) => {
            for item in items {
                match item {
                    ObjItem::Prop(_, value) | ObjItem::Spread(value) => {
                        assigned_in_expr(value, late, out, deferred)
                    }
                }
            }
        }
        ExprKind::OptionalChain { base, access } => {
            each(&[base], out, deferred);
            match access {
                OptionalAccess::Prop(_) => {}
                OptionalAccess::Index(index) => each(&[index], out, deferred),
                OptionalAccess::Call(args) => {
                    for arg in args {
                        assigned_in_expr(arg, late, out, deferred);
                    }
                }
            }
        }
    }
}

/// Fields created by `this.name = ...` statements in a constructor.
fn collect_this_fields(stmts: &[Stmt], out: &mut Vec<String>) {
    for stmt in stmts {
        match stmt.kind() {
            StmtKind::Expr(e) => {
                if let ExprKind::Assign(target, _) = e.kind() {
                    if let LValueKind::GetProp { recv, name } = target.kind() {
                        if matches!(recv.kind(), ExprKind::This) && !out.contains(name) {
                            out.push(name.clone());
                        }
                    }
                }
            }
            StmtKind::If { then_b, else_b, .. } => {
                collect_this_fields(&then_b.stmts, out);
                if let Some(else_b) = else_b {
                    collect_this_fields(&else_b.stmts, out);
                }
            }
            StmtKind::Try {
                try_block,
                catch,
                finally_block,
            } => {
                collect_this_fields(&try_block.stmts, out);
                if let Some(catch) = catch {
                    collect_this_fields(&catch.body.stmts, out);
                }
                if let Some(finally_block) = finally_block {
                    collect_this_fields(&finally_block.stmts, out);
                }
            }
            StmtKind::While { body, .. } | StmtKind::For { body, .. } => {
                collect_this_fields(&body.stmts, out);
            }
            _ => {}
        }
    }
}

/// The value type of an enum and of each member (`Color.Red`).
fn enum_type(init: &Expr) -> (Ty, StdMap<String, Ty>) {
    let mut members = StdMap::new();
    if let ExprKind::ObjLit(items) = init.kind() {
        for item in items {
            let ObjItem::Prop(key, value) = item else { continue };
            let name = prop_key_name(key);
            if name.parse::<f64>().is_ok() {
                continue;
            }
            let ty = match value.kind() {
                ExprKind::LitInt(_) | ExprKind::LitF64(_) => Ty::Number,
                ExprKind::Str(_) => Ty::Str,
                _ => Ty::Any,
            };
            members.insert(name.to_string(), ty);
        }
    }
    let ty = union(members.values().cloned());
    let ty = if matches!(ty, Ty::Never) { Ty::Any } else { ty };
    (ty, members)
}
