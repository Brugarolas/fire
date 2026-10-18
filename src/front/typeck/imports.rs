//! Type information imported from other modules.
//!
//! Declarations of every module reachable from the importer are copied into
//! the importer's checker under collision-free canonical names. A name keeps
//! its spelling only when the importer imports it under that same name; every
//! other foreign declaration is renamed `Name@module`, so private exporter
//! types never leak into the importer's scope. Type references inside the
//! copied declarations are rewritten to the canonical names (honoring type
//! parameter shadowing), including names the exporter itself imported.

use super::*;
use std::path::{Path, PathBuf};

#[derive(Default)]
pub(crate) struct TypeImports {
    /// Importer-local name → canonical name of the imported declaration.
    pub(crate) names: StdMap<String, String>,
    pub(crate) functions: Vec<FuncDecl>,
    pub(crate) classes: Vec<ClassDecl>,
    pub(crate) declarations: Vec<TypeDecl>,
    /// Canonical name → declared type of an annotated module variable.
    pub(crate) variables: StdMap<String, TypeExpr>,
    /// Namespace import alias → object type of the module's exported values.
    pub(crate) namespaces: Vec<(String, TypeExpr)>,
}

/// A parsed module plus its resolved import/re-export specifiers.
pub(crate) struct TypeModule<'a> {
    pub(crate) program: &'a Program,
    pub(crate) specifiers: StdMap<String, PathBuf>,
}

type Graph<'a> = StdMap<PathBuf, TypeModule<'a>>;

const MAX_EXPORT_DEPTH: usize = 64;

/// Names declared at module level, in every namespace the checker knows.
fn declared_names(program: &Program) -> Vec<String> {
    let mut names: Vec<String> = program.type_decls.iter().map(|d| d.name().to_string()).collect();
    names.extend(program.classes.iter().map(|c| c.name.clone()));
    for func in &program.functions {
        if func.name != "__toplevel__" {
            names.push(func.name.clone());
            continue;
        }
        for stmt in &func.body.stmts {
            match stmt.kind() {
                StmtKind::Enum { name, .. } | StmtKind::Var { name, .. } => names.push(name.clone()),
                _ => {}
            }
        }
    }
    names
}

fn declares(program: &Program, name: &str) -> bool {
    declared_names(program).iter().any(|n| n == name)
}

/// The module and module-local name a `local` binding of `path` refers to.
fn resolve_local(graph: &Graph, path: &Path, local: &str, depth: usize) -> Option<(PathBuf, String)> {
    let module = graph.get(path)?;
    if declares(module.program, local) {
        return Some((path.to_path_buf(), local.to_string()));
    }
    for import in &module.program.imports {
        for item in &import.items {
            if let ImportItem::Named { name, alias } = item {
                if alias.as_deref().unwrap_or(name) == local {
                    let target = module.specifiers.get(&import.specifier)?;
                    return resolve_export(graph, target, name, depth + 1);
                }
            }
        }
    }
    None
}

/// The declaration behind `exported` as seen by importers of `path`.
fn resolve_export(graph: &Graph, path: &Path, exported: &str, depth: usize) -> Option<(PathBuf, String)> {
    if depth > MAX_EXPORT_DEPTH {
        return None;
    }
    let module = graph.get(path)?;
    for export in &module.program.exports {
        match export {
            ExportDecl::Func(n) | ExportDecl::Class(n) | ExportDecl::Var(n) | ExportDecl::Type(n)
                if n == exported =>
            {
                return Some((path.to_path_buf(), n.clone()));
            }
            ExportDecl::Named { items } => {
                for (local, alias) in items {
                    if alias.as_deref().unwrap_or(local) == exported {
                        return resolve_local(graph, path, local, depth);
                    }
                }
            }
            ExportDecl::From { specifier, items } => {
                for (source, alias) in items {
                    if alias.as_deref().unwrap_or(source) == exported {
                        let target = module.specifiers.get(specifier)?;
                        return resolve_export(graph, target, source, depth + 1);
                    }
                }
            }
            _ => {}
        }
    }
    for export in &module.program.exports {
        if let ExportDecl::AllFrom { specifier } = export {
            if let Some(target) = module.specifiers.get(specifier) {
                if let Some(found) = resolve_export(graph, target, exported, depth + 1) {
                    return Some(found);
                }
            }
        }
    }
    None
}

/// Every exported value name of `path` (types are not namespace members).
fn exported_values(graph: &Graph, path: &Path, depth: usize, out: &mut Vec<String>) {
    let Some(module) = graph.get(path) else { return };
    if depth > MAX_EXPORT_DEPTH {
        return;
    }
    for export in &module.program.exports {
        match export {
            ExportDecl::Func(n) | ExportDecl::Class(n) | ExportDecl::Var(n) => out.push(n.clone()),
            ExportDecl::Named { items } | ExportDecl::From { items, .. } => {
                out.extend(items.iter().map(|(n, a)| a.clone().unwrap_or_else(|| n.clone())));
            }
            ExportDecl::AllFrom { specifier } => {
                if let Some(target) = module.specifiers.get(specifier) {
                    exported_values(graph, target, depth + 1, out);
                }
            }
            ExportDecl::Type(_) => {}
        }
    }
}

/// Names of `export interface`/`export type` declarations of `path`, including
/// those forwarded by `export *`. Listed exports (`export { T }`) are values-side.
fn exported_types(graph: &Graph, path: &Path, depth: usize, out: &mut Vec<String>) {
    let Some(module) = graph.get(path) else { return };
    if depth > MAX_EXPORT_DEPTH {
        return;
    }
    for export in &module.program.exports {
        match export {
            ExportDecl::Type(n) => out.push(n.clone()),
            ExportDecl::AllFrom { specifier } => {
                if let Some(target) = module.specifiers.get(specifier) {
                    exported_types(graph, target, depth + 1, out);
                }
            }
            _ => {}
        }
    }
}

/// Named imports and re-exports of `path` that the target module does not export
/// (as a value or a type), with the import's location when it has one.
pub(crate) fn unresolved_imports(graph: &Graph, path: &Path) -> Vec<(String, Option<Meta>)> {
    let mut out = Vec::new();
    let Some(module) = graph.get(path) else { return out };
    for import in &module.program.imports {
        let Some(target) = module.specifiers.get(&import.specifier) else { continue };
        for item in &import.items {
            if let ImportItem::Named { name, .. } = item {
                if resolve_export(graph, target, name, 0).is_none() {
                    out.push((
                        format!("module \"{}\" has no exported member `{name}`", import.specifier),
                        Some(import.meta.clone()),
                    ));
                }
            }
        }
    }
    for export in &module.program.exports {
        if let ExportDecl::From { specifier, items } = export {
            let Some(target) = module.specifiers.get(specifier) else { continue };
            for (name, _) in items {
                if resolve_export(graph, target, name, 0).is_none() {
                    out.push((
                        format!("cannot re-export `{name}`: module \"{specifier}\" has no exported member `{name}`"),
                        None,
                    ));
                }
            }
        }
    }
    out
}

fn reachable(graph: &Graph, importer: &Path) -> Vec<PathBuf> {
    let mut seen: StdSet<PathBuf> = StdSet::new();
    let mut stack = vec![importer.to_path_buf()];
    while let Some(path) = stack.pop() {
        if !seen.insert(path.clone()) {
            continue;
        }
        if let Some(module) = graph.get(&path) {
            stack.extend(module.specifiers.values().cloned());
        }
    }
    seen.remove(importer);
    let mut out: Vec<PathBuf> = seen.into_iter().filter(|p| graph.contains_key(p)).collect();
    out.sort();
    out
}

fn module_stem(path: &Path) -> String {
    path.file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "module".to_string())
}

pub(crate) fn type_imports(graph: &Graph, importer: &Path) -> TypeImports {
    let mut out = TypeImports::default();
    let Some(module) = graph.get(importer) else { return out };
    let modules = reachable(graph, importer);
    if modules.is_empty() {
        return out;
    }

    // Importer-visible spellings: `import { Point }` keeps `Point` as canonical.
    let mut preferred: StdMap<(PathBuf, String), String> = StdMap::new();
    for import in &module.program.imports {
        let Some(target) = module.specifiers.get(&import.specifier) else { continue };
        for item in &import.items {
            if let ImportItem::Named { name, alias } = item {
                if alias.as_ref().is_none_or(|a| a == name) {
                    if let Some(found) = resolve_export(graph, target, name, 0) {
                        preferred.entry(found).or_insert_with(|| name.clone());
                    }
                }
            }
        }
    }

    let mut used: StdSet<String> = declared_names(module.program).into_iter().collect();
    let mut canonical: StdMap<(PathBuf, String), String> = StdMap::new();
    for path in &modules {
        let stem = module_stem(path);
        for name in declared_names(graph[path].program) {
            let key = (path.clone(), name.clone());
            if canonical.contains_key(&key) {
                continue;
            }
            let plain = preferred.get(&key).filter(|n| !used.contains(*n)).cloned();
            let chosen = plain.unwrap_or_else(|| {
                let mut candidate = format!("{name}@{stem}");
                let mut n = 2;
                while used.contains(&candidate) {
                    candidate = format!("{name}@{stem}{n}");
                    n += 1;
                }
                candidate
            });
            used.insert(chosen.clone());
            canonical.insert(key, chosen);
        }
    }
    let canonical_of = |found: &(PathBuf, String)| -> Option<String> {
        if found.0 == importer {
            Some(found.1.clone())
        } else {
            canonical.get(found).cloned()
        }
    };

    // Names visible inside each module: own declarations plus its named imports.
    let scope_of = |path: &Path| -> StdMap<String, String> {
        let module = &graph[path];
        let mut scope = StdMap::new();
        for import in &module.program.imports {
            let Some(target) = module.specifiers.get(&import.specifier) else { continue };
            for item in &import.items {
                if let ImportItem::Named { name, alias } = item {
                    if let Some(c) = resolve_export(graph, target, name, 0).and_then(|f| canonical_of(&f)) {
                        scope.insert(alias.clone().unwrap_or_else(|| name.clone()), c);
                    }
                }
            }
        }
        for name in declared_names(module.program) {
            if let Some(c) = canonical_of(&(path.to_path_buf(), name.clone())) {
                scope.insert(name, c);
            }
        }
        scope
    };

    let mut enum_stmts = Vec::new();
    for path in &modules {
        let program = graph[path].program;
        let scope = scope_of(path);
        let rename = |name: &str| scope.get(name).cloned().unwrap_or_else(|| name.to_string());
        for decl in &program.type_decls {
            let mut decl = decl.clone();
            rename_decl(&mut decl, &scope);
            out.declarations.push(decl);
        }
        for class in &program.classes {
            let mut class = class.clone();
            class.name = rename(&class.name);
            class.base = class.base.as_deref().map(rename);
            rename_class(&mut class, &scope);
            out.classes.push(class);
        }
        for func in &program.functions {
            if func.name == "__toplevel__" {
                for stmt in &func.body.stmts {
                    match &stmt.kind {
                        StmtKind::Enum { name, .. } => {
                            let mut stmt = stmt.clone();
                            if let StmtKind::Enum { name: n, .. } = &mut stmt.kind {
                                *n = rename(name);
                            }
                            enum_stmts.push(stmt);
                        }
                        StmtKind::Var { name, ty: Some(ty), .. } => {
                            let mut ty = ty.clone();
                            rename_ty(&mut ty, &scope, &mut Vec::new());
                            out.variables.insert(rename(name), ty);
                        }
                        _ => {}
                    }
                }
                continue;
            }
            let mut types = func.types.clone();
            if let Some(types) = types.as_deref_mut() {
                rename_fn_types(types, &scope, &mut Vec::new());
            }
            out.functions.push(FuncDecl {
                fid: func.fid,
                name: rename(&func.name),
                params: func.params.clone(),
                body: Block { stmts: Vec::new() },
                is_async: func.is_async,
                types,
                meta: func.meta.clone(),
            });
        }
    }
    if !enum_stmts.is_empty() {
        let meta = module.program.functions.first().map(|f| f.meta.clone()).unwrap_or_default();
        out.functions.push(FuncDecl {
            fid: FuncId(u32::MAX),
            name: "__toplevel__".to_string(),
            params: Vec::new(),
            body: Block { stmts: enum_stmts },
            is_async: false,
            types: None,
            meta,
        });
    }

    for import in &module.program.imports {
        let Some(target) = module.specifiers.get(&import.specifier) else { continue };
        for item in &import.items {
            match item {
                ImportItem::Named { name, alias } => {
                    let Some(found) = resolve_export(graph, target, name, 0) else { continue };
                    if found.0 == importer {
                        continue;
                    }
                    if let Some(c) = canonical_of(&found) {
                        out.names.insert(alias.clone().unwrap_or_else(|| name.clone()), c);
                    }
                }
                ImportItem::Namespace { alias } => {
                    let ty = namespace_type(graph, target, &out, &canonical_of);
                    out.namespaces.push((alias.clone(), ty));
                    // Qualified type references: `ns.Point`, `ns.Box<T>`, `ns.Color`.
                    let mut exported = Vec::new();
                    exported_values(graph, target, 0, &mut exported);
                    exported_types(graph, target, 0, &mut exported);
                    for name in exported {
                        let Some(found) = resolve_export(graph, target, &name, 0) else { continue };
                        if found.0 == importer {
                            continue;
                        }
                        if let Some(c) = canonical_of(&found) {
                            out.names.entry(format!("{alias}.{name}")).or_insert(c);
                        }
                    }
                }
            }
        }
    }
    out
}

/// Object type of a namespace import; untyped exports are `any`.
fn namespace_type(
    graph: &Graph,
    target: &Path,
    imports: &TypeImports,
    canonical_of: &dyn Fn(&(PathBuf, String)) -> Option<String>,
) -> TypeExpr {
    let mut names = Vec::new();
    exported_values(graph, target, 0, &mut names);
    let mut members: Vec<TypeMember> = Vec::new();
    for name in names {
        if members.iter().any(|m| m.name == name) {
            continue;
        }
        let canonical = resolve_export(graph, target, &name, 0).and_then(|f| canonical_of(&f));
        let ty = canonical
            .and_then(|c| {
                if let Some(ty) = imports.variables.get(&c) {
                    return Some(ty.clone());
                }
                let func = imports.functions.iter().find(|f| f.name == c)?;
                Some(function_type(func))
            })
            .unwrap_or_else(|| TypeExpr::named("any"));
        members.push(TypeMember { name, optional: false, ty });
    }
    TypeExpr::Object(members)
}

fn function_type(func: &FuncDecl) -> TypeExpr {
    let Some(types) = func.types.as_deref() else {
        return TypeExpr::named("any");
    };
    let any = || TypeExpr::named("any");
    let params = (0..func.params.len())
        .map(|i| types.params.get(i).cloned().flatten().unwrap_or_else(any))
        .collect();
    let mut ret = types.ret.clone().unwrap_or_else(any);
    let is_promise = matches!(&ret, TypeExpr::Name { name, .. } if name == "Promise" || name == "any");
    if func.is_async && !is_promise {
        ret = TypeExpr::Name { name: "Promise".to_string(), args: vec![ret] };
    }
    TypeExpr::Function {
        type_params: types.type_params.clone(),
        params,
        min_args: types.optional.iter().position(|o| *o).unwrap_or(func.params.len()),
        ret: Box::new(ret),
    }
}

// -------------------------------------------------------------------------
// Renaming
// -------------------------------------------------------------------------

fn rename_decl(decl: &mut TypeDecl, scope: &StdMap<String, String>) {
    let mut bound = Vec::new();
    match decl {
        TypeDecl::Interface { name, type_params, extends, members } => {
            *name = scope.get(name.as_str()).cloned().unwrap_or_else(|| name.clone());
            let mark = bind_params(type_params, scope, &mut bound);
            for ty in extends {
                rename_ty(ty, scope, &mut bound);
            }
            for member in members {
                rename_ty(&mut member.ty, scope, &mut bound);
            }
            bound.truncate(mark);
        }
        TypeDecl::Alias { name, type_params, ty } => {
            *name = scope.get(name.as_str()).cloned().unwrap_or_else(|| name.clone());
            let mark = bind_params(type_params, scope, &mut bound);
            rename_ty(ty, scope, &mut bound);
            bound.truncate(mark);
        }
    }
}

fn rename_class(class: &mut ClassDecl, scope: &StdMap<String, String>) {
    let mut bound = Vec::new();
    bind_params(&mut class.type_params, scope, &mut bound);
    for ty in class.base_args.iter_mut().chain(class.implements.iter_mut()) {
        rename_ty(ty, scope, &mut bound);
    }
    for member in &mut class.members {
        match member {
            ClassMember::Stored { type_ann, .. } | ClassMember::Accessor { type_ann, .. } => {
                if let Some(ty) = type_ann {
                    rename_ty(ty, scope, &mut bound);
                }
            }
            ClassMember::Method { types, .. } | ClassMember::Constructor { types, .. } => {
                if let Some(types) = types.as_deref_mut() {
                    rename_fn_types(types, scope, &mut bound);
                }
            }
            ClassMember::Destructor { .. } => {}
        }
    }
}

/// Binds type parameters (constraints may reference each other) and returns the mark.
fn bind_params(params: &mut [TypeParam], scope: &StdMap<String, String>, bound: &mut Vec<String>) -> usize {
    let mark = bound.len();
    bound.extend(params.iter().map(|p| p.name.clone()));
    for param in params {
        if let Some(constraint) = &mut param.constraint {
            rename_ty(constraint, scope, bound);
        }
    }
    mark
}

fn rename_fn_types(types: &mut FnTypes, scope: &StdMap<String, String>, bound: &mut Vec<String>) {
    let mark = bind_params(&mut types.type_params, scope, bound);
    for ty in types.params.iter_mut().flatten().chain(types.ret.iter_mut()) {
        rename_ty(ty, scope, bound);
    }
    bound.truncate(mark);
}

fn collect_infers(ty: &TypeExpr, out: &mut Vec<String>) {
    match ty {
        TypeExpr::Infer(name) => out.push(name.clone()),
        TypeExpr::Name { args, .. } => args.iter().for_each(|a| collect_infers(a, out)),
        TypeExpr::Array(inner) | TypeExpr::KeyOf(inner) => collect_infers(inner, out),
        TypeExpr::Union(items) | TypeExpr::Tuple(items) => items.iter().for_each(|a| collect_infers(a, out)),
        TypeExpr::Indexed(a, b) => {
            collect_infers(a, out);
            collect_infers(b, out);
        }
        TypeExpr::Object(members) => members.iter().for_each(|m| collect_infers(&m.ty, out)),
        TypeExpr::Function { params, ret, .. } => {
            params.iter().for_each(|a| collect_infers(a, out));
            collect_infers(ret, out);
        }
        TypeExpr::Mapped { keys, value, .. } => {
            collect_infers(keys, out);
            collect_infers(value, out);
        }
        TypeExpr::Conditional { check, extends, yes, no } => {
            for ty in [check, extends, yes, no] {
                collect_infers(ty, out);
            }
        }
        TypeExpr::Literal(_) => {}
    }
}

pub(crate) fn rename_ty(ty: &mut TypeExpr, scope: &StdMap<String, String>, bound: &mut Vec<String>) {
    match ty {
        TypeExpr::Name { name, args } => {
            for arg in args.iter_mut() {
                rename_ty(arg, scope, bound);
            }
            if !bound.iter().any(|b| b == name) {
                if let Some(canonical) = scope.get(name.as_str()) {
                    *name = canonical.clone();
                }
            }
        }
        TypeExpr::Array(inner) | TypeExpr::KeyOf(inner) => rename_ty(inner, scope, bound),
        TypeExpr::Union(items) | TypeExpr::Tuple(items) => {
            items.iter_mut().for_each(|t| rename_ty(t, scope, bound));
        }
        TypeExpr::Indexed(a, b) => {
            rename_ty(a, scope, bound);
            rename_ty(b, scope, bound);
        }
        TypeExpr::Literal(_) | TypeExpr::Infer(_) => {}
        TypeExpr::Object(members) => {
            members.iter_mut().for_each(|m| rename_ty(&mut m.ty, scope, bound));
        }
        TypeExpr::Function { type_params, params, ret, .. } => {
            let mark = bind_params(type_params, scope, bound);
            params.iter_mut().for_each(|t| rename_ty(t, scope, bound));
            rename_ty(ret, scope, bound);
            bound.truncate(mark);
        }
        TypeExpr::Mapped { param, keys, value, .. } => {
            rename_ty(keys, scope, bound);
            bound.push(param.clone());
            rename_ty(value, scope, bound);
            bound.pop();
        }
        TypeExpr::Conditional { check, extends, yes, no } => {
            rename_ty(check, scope, bound);
            let mut infers = Vec::new();
            collect_infers(extends, &mut infers);
            let mark = bound.len();
            bound.extend(infers);
            rename_ty(extends, scope, bound);
            rename_ty(yes, scope, bound);
            bound.truncate(mark);
            rename_ty(no, scope, bound);
        }
    }
}
