// src/modules.rs
#![allow(dead_code)]

use ahash::{AHashMap as HashMap, AHashSet as HashSet};
use parking_lot::RwLock;
use hybrid_rc::Arc;

use std::path::{Path, PathBuf};
use std::collections::{VecDeque};
use std::sync::atomic::{AtomicU8, Ordering};
use std::{fs, io};

use may::coroutine;

use crate::value::ValueRepr; // pub type ValueRepr = i64;
use crate::opt::Optimize;
use crate::opt::OptimizationPass;
use crate::opt::optimization::optimization_passes;

// -----------------------------------------------------------------------------
// Loader / fuentes
// -----------------------------------------------------------------------------

pub type Url = PathBuf;

#[derive(Debug)]
pub enum LoadError {
    NotFound(Url),
    Io(io::Error),
    Parse(String),
}

pub enum ModuleKind {
    Text,
}

pub struct LoadedSource {
    pub url: Url,
    pub code: Arc<str>,
    pub kind: ModuleKind,
}

pub trait ModuleLoader: Send + Sync {
    fn resolve(&self, referrer: &Url, spec: &str) -> Result<Url, LoadError>;
    fn load(&self, url: &Url) -> Result<LoadedSource, LoadError>;
}

// Loader de FS simple (ESM-like: extensionless + index.nap)
pub struct FSLoader;

impl ModuleLoader for FSLoader {
    fn resolve(&self, referrer: &Url, spec: &str) -> Result<Url, LoadError> {
        let base = if spec.starts_with("./") || spec.starts_with("../") {
            let mut p = referrer.clone();
            p.pop(); // dir del referrer
            p.push(spec);
            normalize_path(&p)
        } else {
            // por ahora sólo relativos
            let mut p = referrer.clone();
            p.pop();
            p.push(spec);
            normalize_path(&p)
        };

        let base = base.ok_or_else(|| LoadError::NotFound(referrer.clone()))?;

        let candidates = [
            base.clone(),
            with_ext(&base, EXT),
            base.join(INDEX),
        ];
        for c in candidates {
            if c.is_file() { return Ok(c); }
        }
        Err(LoadError::NotFound(base))
    }

    fn load(&self, url: &Url) -> Result<LoadedSource, LoadError> {
        let code = fs::read_to_string(url).map_err(LoadError::Io)?;
        Ok(LoadedSource {
            url: url.clone(),
            code: Arc::<str>::from(code.as_str()),
            kind: ModuleKind::Text,
        })
    }
}

fn with_ext(p: &Path, ext: &str) -> PathBuf {
    if p.extension().is_some() { return p.to_path_buf(); }
    let mut s = p.to_path_buf().into_os_string();
    s.push(ext);
    PathBuf::from(s)
}

fn normalize_path(p: &Path) -> Option<PathBuf> {
    use std::path::Component::*;
    let mut out = PathBuf::new();
    for comp in p.components() {
        match comp {
            CurDir => {}
            ParentDir => { out.pop(); }
            c => out.push(c.as_os_str()),
        }
    }
    Some(out)
}

// -----------------------------------------------------------------------------
// Superficie ESM (entradas de import/export)
// -----------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum ImportName {
    Name(String),  // import { a as b } -> Name("a")
    Namespace,     // import * as ns
    Default,       // import foo from "..."
    None,          // import "./side_effects"
}

#[derive(Debug, Clone)]
pub struct ImportEntry {
    pub local: String,        // nombre local en el importador (vacío si None)
    pub import_name: ImportName,
    pub from: String,         // specifier tal cual
}

#[derive(Debug, Clone)]
pub struct ExportEntry {
    pub local: Option<String>,  // export const x ...  => Some("x")
    pub export_name: String,    // "default" o nombre
    pub from: Option<String>,   // re-export desde otro módulo
    pub is_export_all: bool,    // export * from "..."
}

// -----------------------------------------------------------------------------
// Env & Binding cells (live bindings estilo ESM)
// -----------------------------------------------------------------------------

pub struct BindingCell {
    state: AtomicU8,          // 0 = Uninit (TDZ), 1 = Init
    value: RwLock<ValueRepr>, // Napalm value
}
impl BindingCell {
    pub fn new_uninit() -> Self {
        Self { state: AtomicU8::new(0), value: RwLock::new(0) }
    }
    pub fn read(&self) -> Result<ValueRepr, ()> {
        if self.state.load(Ordering::Acquire) == 0 { return Err(()); }
        Ok(*self.value.read())
    }
    pub fn write_init(&self, v: ValueRepr) {
        *self.value.write() = v;
        self.state.store(1, Ordering::Release);
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ModuleId(pub u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ModuleStatus { Unlinked, Linked, Instantiated, Evaluated }

pub struct ModuleEnv {
    pub locals: HashMap<String, usize>,
    pub cells: Vec<BindingCell>,
}
impl ModuleEnv {
    pub fn new() -> Self { Self { locals: HashMap::new(), cells: vec![] } }
    pub fn define_export(&mut self, name: &str) -> usize {
        let idx = self.cells.len();
        self.cells.push(BindingCell::new_uninit());
        self.locals.insert(name.to_string(), idx);
        idx
    }
    pub fn lookup(&self, name: &str) -> Option<usize> {
        self.locals.get(name).copied()
    }
}

pub struct ModuleRecord {
    pub id: ModuleId,
    pub url: Url,
    pub status: ModuleStatus,
    pub import_entries: Vec<ImportEntry>,
    pub local_export_entries: Vec<(String /*export name*/, usize /*cell idx*/ )>,
    pub indirect_export_entries: Vec<(String /*export name*/, String /*import name*/, Url /*from*/ )>,
    pub star_export_entries: Vec<Url>,
    pub env: ModuleEnv,
}
impl ModuleRecord {
    pub fn lookup_local_export(&self, name: &str) -> Option<usize> {
        self.local_export_entries.iter()
            .find(|(n, _)| n == name)
            .map(|(_, idx)| *idx)
    }
}

// -----------------------------------------------------------------------------
// Resolver de exports (export *, re-exports) con caché
// -----------------------------------------------------------------------------

#[derive(Clone)]
pub enum ExportResolution {
    Resolved { module: ModuleId, cell_index: usize },
    NotFound,
    Ambiguous,
}

pub struct ModuleResolver<L: ModuleLoader> {
    pub loader: Arc<L>,
    pub modules: HashMap<Url, ModuleId>,
    pub records: Vec<ModuleRecord>,
    pub export_cache: HashMap<(ModuleId, String), ExportResolution>,
}

impl<L: ModuleLoader> ModuleResolver<L> {
    pub fn new(loader: Arc<L>) -> Self {
        Self {
            loader,
            modules: HashMap::new(),
            records: vec![],
            export_cache: HashMap::new(),
        }
    }

    pub fn resolve_export(
        &mut self,
        mid: ModuleId,
        name: &str,
        seen: &mut HashMap<(ModuleId, String), ()>
    ) -> ExportResolution {
        let key = (mid, name.to_string());
        if let Some(r) = self.export_cache.get(&key) {
            return r.clone();
        }
        if seen.contains_key(&key) {
            return ExportResolution::NotFound;
        }
        seen.insert(key.clone(), ());

        // 1) locales (cerramos el borrow antes de recursar)
        {
            let m = &self.records[mid.0 as usize];
            if let Some(cell) = m.lookup_local_export(name) {
                let res = ExportResolution::Resolved { module: mid, cell_index: cell };
                self.export_cache.insert(key, res.clone());
                return res;
            }
        }

        // 2) copias para evitar préstamos solapados
        let (indirects, stars) = {
            let m = &self.records[mid.0 as usize];
            (m.indirect_export_entries.clone(), m.star_export_entries.clone())
        };

        // 2) indirectos: export { x as y } from "..."
        for (exp, imp, from_url) in indirects {
            if exp == name {
                let from_id = *self.modules.get(&from_url).expect("linked url");
                let r = self.resolve_export(from_id, &imp, seen);
                self.export_cache.insert((mid, name.to_string()), r.clone());
                return r;
            }
        }

        // 3) export * from ...
        let mut found: Option<ExportResolution> = None;
        if name != "default" {
            for from_url in stars {
                let from_id = *self.modules.get(&from_url).expect("linked url");
                match self.resolve_export(from_id, name, seen) {
                    r @ ExportResolution::Resolved { .. } => {
                        if found.is_none() { found = Some(r); } else { return ExportResolution::Ambiguous; }
                    }
                    _ => {}
                }
            }
        }

        let res = found.unwrap_or(ExportResolution::NotFound);
        self.export_cache.insert((mid, name.to_string()), res.clone());
        res
    }
}

// -----------------------------------------------------------------------------
// Construcción del grafo + carga/parse/lower paralelos con May
// -----------------------------------------------------------------------------

pub const EXT: &str = ".napalm";
pub const INDEX: &str = "index.napalm";
const WORKER_STACK_BYTES: usize = 4 * 1024 * 1024; // 4 MiB para parser/lower

pub struct ModuleUnit {
    pub url: Url,
    pub code: Arc<str>,
    pub imports: Vec<String>,   // specifiers tal cual
    pub deps: Vec<Url>,         // URLs resueltas de imports estáticos
    pub links: crate::front::LinkInfo,          // link info snapshot (filled after lowering)
    pub wir: crate::wir::Module,        // WIR after lowering+opt
}

pub struct ModuleGraph {
    pub entry: Url,
    pub units: HashMap<Url, ModuleUnit>,
    pub edges: HashMap<Url, Vec<Url>>, // url -> hijos
    pub topo: Vec<Url>,                // orden topológico
    pub sccs: Vec<Vec<Url>>,           // SCCs
}

#[derive(Debug)]
pub enum BuildError {
    Io(io::Error),
    Load(LoadError),
    Parse { url: Url, msg: String, span: Option<(usize, usize)> },
    Lower(String),
    Panic(String),
}

impl From<io::Error> for BuildError { fn from(e: io::Error) -> Self { BuildError::Io(e) } }
impl From<LoadError> for BuildError { fn from(e: LoadError) -> Self { BuildError::Load(e) } }

// extracción simple de imports estáticos ESM en el fuente
fn extract_static_imports(src: &str) -> Vec<String> {
    let mut out = Vec::new();

    // quitar comentarios
    let mut s = String::with_capacity(src.len());
    let mut it = src.chars().peekable();
    while let Some(ch) = it.next() {
        if ch == '/' && matches!(it.peek(), Some('/')) {
            it.next();
            while let Some(c) = it.next() { if c == '\n' { break; } }
            s.push('\n');
            continue;
        }
        if ch == '/' && matches!(it.peek(), Some('*')) {
            it.next();
            let mut prev = '\0';
            while let Some(c) = it.next() {
                if prev == '*' && c == '/' { break; }
                prev = c;
            }
            s.push(' ');
            continue;
        }
        s.push(ch);
    }

    let bytes = s.as_bytes();
    let mut i = 0;
    while i + 6 <= bytes.len() {
        if &bytes[i..i+6] == b"import" {
            i += 6;
            while i < bytes.len() && bytes[i].is_ascii_whitespace() { i += 1; }
            if i < bytes.len() && (bytes[i] == b'\'' || bytes[i] == b'\"') {
                let q = bytes[i]; i += 1;
                let start = i;
                while i < bytes.len() && bytes[i] != q { i += 1; }
                if i <= bytes.len() {
                    out.push(s[start..i].to_string());
                }
            } else {
                while i + 4 <= bytes.len() && &bytes[i..i+4] != b"from" { i += 1; }
                if i + 4 <= bytes.len() && &bytes[i..i+4] == b"from" {
                    i += 4;
                    while i < bytes.len() && bytes[i].is_ascii_whitespace() { i += 1; }
                    if i < bytes.len() && (bytes[i] == b'\'' || bytes[i] == b'\"') {
                        let q = bytes[i]; i += 1;
                        let start = i;
                        while i < bytes.len() && bytes[i] != q { i += 1; }
                        if i <= bytes.len() {
                            out.push(s[start..i].to_string());
                        }
                    }
                }
            }
        }
        i += 1;
    }
    out
}

fn panic_to_string(e: Box<dyn std::any::Any + Send + 'static>) -> String {
    if let Some(s) = e.downcast_ref::<&'static str>() { (*s).to_string() }
    else if let Some(s) = e.downcast_ref::<String>()   { s.clone() }
    else { format!("{:?}", e) }
}

/// Build incoming LinkInfo for `unit` using:
///  - namespace aliases from its AST,
///  - named imports resolved against already-lowered provider modules.
fn build_incoming_links_for_unit<L: ModuleLoader>(
    loader: &Arc<L>,
    units: &HashMap<Url, ModuleUnit>,
    unit_url: &Url,
) -> Result<crate::front::LinkInfo, BuildError> {
    use crate::front::{Parser, ImportItem, LinkInfo};

    let unit = units.get(unit_url).expect("unit present");

    // Parse AST just to read the structured import declarations.
    let mut p = Parser::new(&unit.code);
    let prog = p.program().map_err(|e| BuildError::Parse {
        url: unit_url.clone(),
        msg: e.msg,
        span: Some((e.span.start, e.span.end)),
    })?;

    let mut links = LinkInfo::default();

    // Seed namespace aliases (even if we don't materialize members yet).
    for imp in &prog.imports {
        for it in &imp.items {
            if let ImportItem::Namespace { alias } = it {
                links.namespace_imports.entry(alias.clone()).or_default();
            }
        }
    }

    // Wire named imports from providers' export_bindings.
    for imp in &prog.imports {
        let prov_url = loader.resolve(&unit.url, &imp.specifier)?;
        let prov = units.get(&prov_url).ok_or_else(|| {
            BuildError::Load(LoadError::NotFound(prov_url.clone()))
        })?;

        for it in &imp.items {
            match it {
                ImportItem::Named { name, alias } => {
                    let local = alias.clone().unwrap_or_else(|| name.clone());
                    if let Some(&bid) = prov.links.export_bindings.get(name.as_str()) {
                        links.import_bindings.insert(local, bid);
                    } else {
                        return Err(BuildError::Lower(format!(
                            "Import resolution failed: '{}' not exported by {} (needed by {})",
                            name,
                            prov_url.display(),
                            unit_url.display(),
                        )));
                    }
                }
                ImportItem::Namespace { alias } => {
                    // Optional: materialize members list for make_namespace.
                    let mut members = Vec::new();
                    for (exp_name, &bid) in &prov.links.export_bindings {
                        members.push((exp_name.clone(), bid));
                    }
                    links.namespace_imports.insert(alias.clone(), members);
                }
            }
        }
    }

    Ok(links)
}

/// Lower and optimize all modules in topological order so that providers
/// are lowered before importers. This lets us feed importers with the
/// providers' BindingIds via LinkInfo.
fn lower_and_optimize_in_topo<L: ModuleLoader + 'static>(
    loader: Arc<L>,
    topo: &[Url],
    units: &mut HashMap<Url, ModuleUnit>,
) -> Result<(), BuildError> {
    use crate::front::Parser;

    for url in topo {
        // Re-parse the module to obtain its full AST for lowering.
        let code = { units.get(url).expect("unit").code.clone() };
        let mut p = Parser::new(&code);
        let prog = p.program().map_err(|e| BuildError::Parse {
            url: url.clone(),
            msg: e.msg,
            span: Some((e.span.start, e.span.end)),
        })?;

        // Build incoming links using already-lowered providers.
        let incoming_links = build_incoming_links_for_unit(&loader, units, url)?;

        // Lower to WIR.
        let mut m = crate::wir::Module::new();
        let mut lowerer = crate::front::Lowerer::new(&mut m);
        lowerer.set_links(incoming_links);
        lowerer.lower_program(&prog)
            .map_err(|e| BuildError::Lower(format!("{:?}", e)))?;

        // Snapshot final links (must include export_bindings).
        let links_out = lowerer.links_snapshot();

        // Optimize single module.
        let optimize = optimization_passes();
        optimize.optimize_module(&mut m);

        // Store back.
        let u = units.get_mut(url).expect("unit exists");
        u.links = links_out;
        u.wir = m;
    }
    Ok(())
}

pub fn build_graph_parallel<L: ModuleLoader + 'static>(
    loader: Arc<L>,
    entry: Url
) -> Result<ModuleGraph, BuildError> {
    let mut units: HashMap<Url, ModuleUnit> = HashMap::new();
    let mut edges: HashMap<Url, Vec<Url>> = HashMap::new();
    let mut queue = VecDeque::new();
    queue.push_back(entry.clone());
    let mut seen = HashSet::new();

    // Phase A: load + discover deps (no lowering)
    while let Some(url) = queue.pop_front() {
        if !seen.insert(url.clone()) { continue; }

        // Load file
        let loaded = loader.load(&url)?;

        // Ensure edge bucket exists
        edges.entry(url.clone()).or_default();

        // Discover static imports with the quick scanner
        let imports = extract_static_imports(&loaded.code);
        let mut deps = Vec::new();
        for spec in &imports {
            let dep = loader.resolve(&url, spec)?;
            deps.push(dep.clone());
            edges.entry(url.clone()).or_default().push(dep.clone());
            queue.push_back(dep);
        }

        // Initialize unit with placeholders (links, wir will be filled in Phase B)
        units.insert(url.clone(), ModuleUnit {
            url: url.clone(),
            code: loaded.code.clone(),
            imports,
            deps: deps.clone(),
            links: crate::front::LinkInfo::default(),
            wir: crate::wir::Module::new(),
        });
    }

    let topo = topo_sort(&edges, &entry);
    let sccs = scc_kosaraju(&edges);

    // Phase B: lower + optimize in topo order so providers are ready for importers.
    lower_and_optimize_in_topo(loader, &topo, &mut units)?;

    Ok(ModuleGraph { entry, units, edges, topo, sccs })
}

fn topo_sort(edges: &HashMap<Url, Vec<Url>>, entry: &Url) -> Vec<Url> {
    let mut out = Vec::new();
    let mut visited = HashSet::new();
    fn dfs(u: &Url, edges: &HashMap<Url, Vec<Url>>, vis: &mut HashSet<Url>, out: &mut Vec<Url>) {
        if !vis.insert(u.clone()) { return; }
        if let Some(ns) = edges.get(u) {
            for v in ns { dfs(v, edges, vis, out); }
        }
        out.push(u.clone());
    }
    dfs(entry, edges, &mut visited, &mut out);
    out
}

fn scc_kosaraju(edges: &HashMap<Url, Vec<Url>>) -> Vec<Vec<Url>> {
    let mut order = Vec::new();
    let mut vis = HashSet::new();

    fn dfs1(u: &Url, g: &HashMap<Url, Vec<Url>>, vis: &mut HashSet<Url>, order: &mut Vec<Url>) {
        if !vis.insert(u.clone()) { return; }
        if let Some(ns) = g.get(u) { for v in ns { dfs1(v, g, vis, order); } }
        order.push(u.clone());
    }

    // grafo inverso
    let mut rev: HashMap<Url, Vec<Url>> = HashMap::new();
    for (u, ns) in edges {
        for v in ns {
            rev.entry(v.clone()).or_default().push(u.clone());
        }
    }

    for u in edges.keys() { if !vis.contains(u) { dfs1(u, edges, &mut vis, &mut order); } }
    vis.clear();

    let mut out = Vec::new();
    for u in order.into_iter().rev() {
        if !vis.insert(u.clone()) { continue; }
        let mut comp = Vec::new();
        let mut stack = vec![u.clone()];
        while let Some(x) = stack.pop() {
            comp.push(x.clone());
            if let Some(ns) = rev.get(&x) {
                for v in ns {
                    if vis.insert(v.clone()) { stack.push(v.clone()); }
                }
            }
        }
        out.push(comp);
    }
    out
}

// -----------------------------------------------------------------------------
// Unión a un único WIR con rebase de IDs
// -----------------------------------------------------------------------------

#[derive(Default)]
struct Rebase {
    func: u32,
    shape: u32,
    field: u32,
    envshape: u32,
    site: u32,
    deopt: u32,
    class: u32,
}

fn rebase_function_ids(f: &mut crate::wir::Function, rb: &Rebase) {
    use crate::wir::Inst as I;

    for n in &mut f.nodes {
        match &mut n.kind {
            I::CallDirect { callee, .. } => { callee.0 += rb.func; }
            I::CallDirectMemoized { callee, .. } => { callee.0 += rb.func; }
            I::ArrayMap { func, .. } => { func.0 += rb.func; }
            I::ArrayReduce { func, .. } => { func.0 += rb.func; }
            I::ArrayForEach { func, .. } => { func.0 += rb.func; }
            I::ArrayFind { func, .. } => { func.0 += rb.func; }
            I::ArrayFindIndex { func, .. } => { func.0 += rb.func; }
            I::ArrayFilter { func, .. } => { func.0 += rb.func; }
            I::AllocClosure { func, .. } => { func.0 += rb.func; }

            I::RegisterClass { meta, fields, statics, methods, accessors, ctor } => {
                meta.id.0 += rb.class;
                meta.instance_shape.0 += rb.shape;
                meta.static_shape.0 += rb.shape;
                for fid in fields { fid.0 += rb.field; }
                for fid in statics { fid.0 += rb.field; }
                for (fid, func, _st) in methods {
                    fid.0 += rb.field;
                    func.0 += rb.func;
                }
                for (fid, get, set, _st) in accessors {
                    fid.0 += rb.field;
                    if let Some(g) = get { g.0 += rb.func; }
                    if let Some(s) = set { s.0 += rb.func; }
                }
                if let Some(c) = ctor { c.0 += rb.func; }
            }
            I::AllocInstance { class } => { class.0 += rb.class; }
            I::LoadMethod { expected, .. } => {
                if let Some(sh) = expected { sh.0 += rb.shape; }
            }
            I::CallMethodIC { site, .. } => { site.0 += rb.site; }
            I::CallSuper { home_class, .. } => { home_class.0 += rb.class; }
            I::LoadSuperMethod { home_class, .. } => { home_class.0 += rb.class; }

            I::GuardType { deopt, .. }
            | I::GuardShape { deopt, .. }
            | I::GuardBounds { deopt, .. }
            | I::GuardNotNull { deopt, .. }
            | I::GuardIsInt { deopt, .. }
            | I::GuardIsF64 { deopt, .. }
            | I::Bailout { deopt, .. } => {
                deopt.0 += rb.deopt;
            }

            _ => {}
        }
    }

    for d in &mut f.deopts {
        d.id.0 += rb.deopt;
    }
}

pub fn merge_graph_into_single_wir(
    g: &ModuleGraph,
) -> crate::wir::Module {
    let mut out = crate::wir::Module::new();
    let mut rb = Rebase::default();

    // Guardaremos aquí los inits por-módulo en el orden topo
    let mut prog_inits: Vec<crate::wir::FuncId> = Vec::new();

    for url in &g.topo {
        let Some(u) = g.units.get(url) else { continue; };
        let uwir = &u.wir;

        rb.func     = out.funcs.len() as u32;
        rb.shape    = out.next_shape;
        rb.field    = out.next_field;
        rb.envshape = out.next_envshape;
        rb.site     = out.next_site;
        rb.deopt    = out.next_deopt;
        rb.class    = out.next_class;

        for mut f in uwir.funcs.clone() {
            let is_mod_toplevel = f.sig.name == "__toplevel__";
            if is_mod_toplevel {
                f.sig.name = format!("__mod_init__#{}", prog_inits.len());
            }

            rebase_function_ids(&mut f, &rb);

            let new_id = crate::wir::FuncId(out.funcs.len() as u32);
            f.id = new_id;
            out.funcs.push(f);

            if is_mod_toplevel {
                prog_inits.push(new_id);
            }
        }

        out.next_shape    += uwir.next_shape;
        out.next_field    += uwir.next_field;
        out.next_envshape += uwir.next_envshape;
        out.next_site     += uwir.next_site;
        out.next_deopt    += uwir.next_deopt;
        out.next_class    += uwir.next_class;

        for (k, v) in &uwir.strings { out.strings.entry(k.clone()).or_insert(*v); }
        for (k, v) in &uwir.shapes  { out.shapes.entry(k.clone()).or_insert(crate::wir::ShapeId(v.0 + rb.shape)); }
        for (k, v) in &uwir.fields  { out.fields.entry(k.clone()).or_insert(crate::wir::FieldId(v.0 + rb.field)); }
    }

    // Inserta el __toplevel__ global que llama a todos los inits en orden topo
    add_program_toplevel(&mut out, &prog_inits);

    out
}


fn add_program_toplevel(module: &mut crate::wir::Module, inits: &[crate::wir::FuncId]) {
    use crate::wir::{Builder, Type, Inst, CallConv};

    let mut b = Builder::new(module, "__toplevel__", vec![], vec![Type::Int32]);

    for &fid in inits {
        let _ = b.push_node(
            Inst::CallDirect { conv: CallConv::Fast, callee: fid, args: vec![] },
            Some(Type::Int32),
            1,
            true,
        );
    }

    let zero = b.const_i32(0);
    b.ret(&[zero]);

    let mut f = b.finish();

    module.push_function(f);
}

/// Very small lexer to extract `import * as <Ident> from "..."` namespace identifiers.
/// This is intentionally simple and runs before the real parser to seed LinkInfo.
fn extract_namespace_import_idents(src: &str) -> Vec<String> {
    let bytes = src.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();

    // tiny helpers
    fn is_ident_start(c: u8) -> bool { c == b'_' || c == b'$' || (c as char).is_ascii_alphabetic() }
    fn is_ident_continue(c: u8) -> bool { is_ident_start(c) || (c as char).is_ascii_digit() }
    fn skip_ws(bytes: &[u8], mut j: usize) -> usize {
        while j < bytes.len() && bytes[j].is_ascii_whitespace() { j += 1; }
        j
    }

    while i + 6 <= bytes.len() {
        // match "import"
        if &bytes[i..i+6] != b"import" { i += 1; continue; }
        i += 6;
        i = skip_ws(bytes, i);

        // expect '*'
        if i >= bytes.len() || bytes[i] != b'*' { continue; }
        i += 1;
        i = skip_ws(bytes, i);

        // expect "as"
        if i + 2 > bytes.len() || &bytes[i..i+2] != b"as" { continue; }
        i += 2;
        i = skip_ws(bytes, i);

        // read identifier
        if i >= bytes.len() || !is_ident_start(bytes[i]) { continue; }
        let start = i;
        i += 1;
        while i < bytes.len() && is_ident_continue(bytes[i]) { i += 1; }
        let name = std::str::from_utf8(&bytes[start..i]).unwrap_or("").to_string();
        if !name.is_empty() {
            out.push(name);
        }

        // best-effort; skip to end of this import stmt (look for ';' or newline)
        while i < bytes.len() && bytes[i] != b';' && bytes[i] != b'\n' { i += 1; }
    }

    out
}

// -----------------------------------------------------------------------------
// Pipeline global (placeholder). Aquí engancharás el inliner cross-módulo.
// -----------------------------------------------------------------------------

pub fn run_global_pipeline(m: &mut crate::wir::Module) {
    let optimize = crate::opt::optimization::optimization_passes();
    optimize.optimize_module(m);

    // TODO (cuando el lowerer emita ops de módulos):
    //  - plegado de LoadBinding a constantes tras init (si write-once)
    //  - eliminación / fusión de namespaces triviales
    //  - conversión de imports resueltos a CallDirect
}

// -----------------------------------------------------------------------------
// API de alto nivel: construir programa completo desde entry
// -----------------------------------------------------------------------------

pub struct PipelinesConfig;

pub fn build_whole_program_from_entry(entry_path: &str) -> Result<crate::wir::Module, BuildError> {
    let entry = PathBuf::from(entry_path);
    if !entry.exists() {
        return Err(BuildError::Load(LoadError::NotFound(entry)));
    }

    let loader = Arc::new(FSLoader);

    let g = build_graph_parallel(loader, entry.clone())?;
    let mut m = merge_graph_into_single_wir(&g);
    //run_global_pipeline(&mut m);
    Ok(m)
}
