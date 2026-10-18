// src/modules.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

use bumpalo::Bump;
use may::coroutine;
use std::num::NonZeroUsize;
use std::sync::Arc;
use std::thread;
use std::{
    cell::RefCell,
    path::{Path, PathBuf},
};

use crate::front::{ExportDecl, ImportItem, ModuleAST, Parser, Program};
use crate::helpers::collections::{HashMap, HashSet};
use crate::helpers::layered::LayeredMap;
use crate::lowerer::{LinkInfo, LowerError, Lowerer};
use crate::opt::optimization::optimization_passes;
use crate::resolver::Resolver;
use crate::wir::{BindingId, Builder as WirBuilder, CallConv, FuncId, IdRemap, Inst, Type};
use compact_str::CompactString;

/// -----------------------------------------
/// Minimal infra
/// -----------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(pub u32);

const WORKER_STACK_BYTES: usize = 4 * 1024 * 1024;

#[derive(Default)]
pub struct ModulesCTX {
    /// Bump arena used by the parser to intern &'static str for import/export names.
    pub arena: Bump,
    /// Registry of parsed modules (by absolute path) â†’ Box<ModuleAST>.
    pub registry: HashMap<Arc<PathBuf>, Box<ModuleAST<'static>>>,
}


pub trait ModuleLoader {
    fn read_to_string(&self, path: &Path) -> std::io::Result<String>;
    fn resolve(&self, referrer: &Path, spec: &str) -> std::io::Result<PathBuf>;
}

pub struct FSLoader;

/// Embedded standard-library modules, importable as `napalm:<name>`.
const STD_MODULES: &[(&str, &str)] = &[("napalm:date", include_str!("stdlib/date.napalm"))];

/// Global names provided by std modules and imported implicitly when a module uses them.
const STD_GLOBALS: &[(&str, &str)] = &[("Date", "napalm:date")];

fn std_module_source(path: &Path) -> Option<&'static str> {
    let path = path.to_str()?;
    STD_MODULES.iter().find(|(name, _)| *name == path).map(|(_, src)| *src)
}

/// Appends `import { X } from "napalm:..."` for every std global `src` uses
/// without declaring or importing it. Appending keeps existing spans valid.
pub fn with_implicit_std_imports(path: &Path, src: &str) -> Option<String> {
    use crate::front::Tok;
    use logos::Logos;

    if std_module_source(path).is_some() {
        return None;
    }
    let toks: Vec<Tok> = Tok::lexer(src).filter_map(Result::ok).collect();
    let mut imports = String::new();
    for (global, spec) in STD_GLOBALS {
        let mut used = false;
        let mut declared = false;
        let mut in_import = false;
        for (i, tok) in toks.iter().enumerate() {
            match tok {
                Tok::Import => in_import = true,
                Tok::From => in_import = false,
                Tok::Ident(name) if name == global => {
                    let prev = i.checked_sub(1).map(|j| &toks[j]);
                    if in_import
                        || matches!(
                            prev,
                            Some(
                                Tok::Class
                                    | Tok::Fn
                                    | Tok::Function
                                    | Tok::Var
                                    | Tok::Let
                                    | Tok::Const
                                    | Tok::Enum
                                    | Tok::As
                            )
                        )
                    {
                        declared = true;
                    } else if !matches!(prev, Some(Tok::Dot)) {
                        used = true;
                    }
                }
                _ => {}
            }
        }
        if used && !declared {
            imports.push_str(&format!("\nimport {{ {global} }} from \"{spec}\";\n"));
        }
    }
    (!imports.is_empty()).then(|| format!("{src}{imports}"))
}

impl ModuleLoader for FSLoader {
    fn read_to_string(&self, path: &Path) -> std::io::Result<String> {
        if let Some(src) = std_module_source(path) {
            return Ok(src.to_string());
        }
        std::fs::read_to_string(path)
    }

    fn resolve(&self, referrer: &Path, spec: &str) -> std::io::Result<PathBuf> {
        if STD_MODULES.iter().any(|(name, _)| *name == spec) {
            return Ok(PathBuf::from(spec));
        }
        // Simple resolution relative to the referrer's directory.
        let base = if referrer.is_dir() {
            referrer.to_path_buf()
        } else {
            referrer.parent().unwrap_or(Path::new(".")).to_path_buf()
        };

        let mut p = base.join(spec);
        if p.extension().is_none() {
            p = p.with_extension("napalm");
        }
        p = p.canonicalize()?;
        Ok(p)
    }
}

/// -----------------------------------------
/// ProgramBuilder (single source of truth)
/// -----------------------------------------
/// Owns:
///  - the global ModulesCTX (arena + registry),
///  - a queue of pending modules discovered via `import`,
///  - the single public entry `build_from_entry`,
///  - the `Program` AST per file (to run lowerer later).
pub struct ProgramBuilder {
    pub ctx: ModulesCTX,
    loader: FSLoader,

    /// LIFO queue of absolute paths to parse (pop/push).
    pending: RefCell<Vec<Arc<PathBuf>>>,
    /// Set of absolute paths already enqueued/visited to avoid duplicates.
    visited: RefCell<HashSet<Arc<PathBuf>>>,
    /// Per-module full AST (what `Lowerer` needs).
    programs: HashMap<Arc<PathBuf>, Program>,
    sources: HashMap<Arc<PathBuf>, String>,
}

pub struct BuiltBundle {
    pub shards: HashMap<Arc<PathBuf>, crate::wir::Module>,
    pub init_order: Vec<Arc<PathBuf>>,
}

impl ProgramBuilder {
    pub fn new(loader: FSLoader) -> Self {
        Self {
            ctx: ModulesCTX::default(),
            loader,
            pending: RefCell::new(Vec::new()),
            visited: RefCell::new(HashSet::new()),
            programs: HashMap::default(),
            sources: HashMap::default(),
        }
    }

    pub fn build_whole_program(&mut self, entry: &str) -> Result<crate::wir::Module, String> {
        // 1) parse + bind
        let entry_abs =
            std::fs::canonicalize(entry).map_err(|e| format!("canonicalize({entry}): {e}"))?;
        let entry_arc = Arc::new(entry_abs);

        self.build_from_entry(entry)?;

        self.resolve_all_modules()?;
        self.check_module_types()?;

        // 2) lower + optimize en paralelo
        let shards = self.lower_all_modules_parallel_sharded()?;

        // 3) orden de inicializaciÃ³n (proveedores â†’ consumidores)
        let order = self.topo_order()?;

        // 4) merge a un Ãºnico WIR
        self.merge_wir_shards(shards, &order, &entry_arc)
    }

    fn resolve_all_modules(&self) -> Result<(), String> {
        let mut paths: Vec<&Arc<PathBuf>> = self.programs.keys().collect();
        paths.sort();

        for path in paths {
            let prog = self.programs.get(path).expect("Program must exist");
            let file_name = path.to_string_lossy();

            let mut resolver = Resolver::new(CompactString::from(file_name.as_ref()));
            if let Err(err) = resolver.resolve_program(prog) {
                let source = self
                    .sources
                    .get(path)
                    .expect("Source code must exist for resolved program");

                // CORRECTED LOGIC:
                // 1. Let Ariadne print its beautiful, detailed report.
                let _ = err.emit((file_name.as_ref(), source));

                // 2. Return a simple message to stop compilation. The user will see the report above.
                return Err(format!("Semantic error in {:?}", path));
            }
        }
        Ok(())
    }

    /// Type-checks every module with the declarations it imports. The parser
    /// skips checking module programs because imports are unknown until here.
    fn check_module_types(&mut self) -> Result<(), String> {
        use crate::front::typeck::check_with_imports;
        use crate::front::typeck::imports::{type_imports, unresolved_imports, TypeModule};

        let mut paths: Vec<Arc<PathBuf>> = self.programs.keys().cloned().collect();
        paths.sort();

        let all_imports = {
            let mut graph = std::collections::HashMap::new();
            for path in &paths {
                let program = &self.programs[path];
                let mut specifiers = std::collections::HashMap::new();
                let specs = program.imports.iter().map(|i| &i.specifier).chain(
                    program.exports.iter().filter_map(|e| match e {
                        ExportDecl::From { specifier, .. } | ExportDecl::AllFrom { specifier } => {
                            Some(specifier)
                        }
                        _ => None,
                    }),
                );
                for spec in specs {
                    if let Ok(target) = self.loader.resolve(path, spec) {
                        specifiers.insert(spec.clone(), target);
                    }
                }
                graph.insert((**path).clone(), TypeModule { program, specifiers });
            }
            // Broken re-exports (no location) are the root cause of their importers' errors.
            let unresolved = paths
                .iter()
                .flat_map(|path| {
                    unresolved_imports(&graph, path)
                        .into_iter()
                        .map(move |(message, meta)| (path, message, meta))
                })
                .min_by_key(|(_, _, meta)| meta.is_some());
            if let Some((path, message, meta)) = unresolved {
                let file_name = path.to_string_lossy();
                if let Some(meta) = meta {
                    let source = self.sources.get(path).map(String::as_str).unwrap_or("");
                    crate::front::ParseError::new(message.clone(), meta)
                        .emit(file_name.as_ref(), source);
                }
                return Err(format!("Import error in {:?}: {}", path, message));
            }
            paths
                .iter()
                .map(|path| type_imports(&graph, path))
                .collect::<Vec<_>>()
        };

        for (path, imports) in paths.iter().zip(all_imports) {
            let program = self.programs.get_mut(path).expect("Program must exist");
            let imported: Vec<String> = program
                .imports
                .iter()
                .flat_map(|import| import.local_names())
                .collect();
            let file_id = program
                .functions
                .iter()
                .find_map(|f| f.meta.file)
                .or_else(|| program.classes.iter().find_map(|c| c.meta.file))
                .unwrap_or(crate::diag::FileId(0));
            let result = check_with_imports(
                &mut program.functions,
                &mut program.classes,
                &program.type_decls,
                &imported,
                file_id,
                &imports,
            );
            if let Err(err) = result {
                let file_name = path.to_string_lossy();
                let source = self.sources.get(path).map(String::as_str).unwrap_or("");
                err.emit(file_name.as_ref(), source);
                return Err(format!("Type error in {:?}: {}", path, err.msg));
            }
        }
        Ok(())
    }

    fn merge_wir_shards(
        &self,
        mut shards: HashMap<Arc<PathBuf>, crate::wir::Module>,
        order: &[Arc<PathBuf>],
        entry: &Arc<PathBuf>,
    ) -> Result<crate::wir::Module, String> {
        use crate::wir::Module as WirModule;

        let mut dst = WirModule::new();
        let mut modinit_funcs: HashMap<Arc<PathBuf>, FuncId> = HashMap::default();
        let mut toplevel_funcs: HashMap<Arc<PathBuf>, FuncId> = HashMap::default();

        for path in order {
            let mut src = match shards.remove(path) {
                Some(m) => m,
                None => continue,
            };

            // Record function IDs we care about before moving them into the destination module.
            for f in &src.funcs {
                match f.sig.name.as_str() {
                    "__modinit__" => {
                        modinit_funcs.insert(path.clone(), f.id);
                    }
                    "__toplevel__" => {
                        toplevel_funcs.insert(path.clone(), f.id);
                    }
                    _ => {}
                }
            }

            // Merge global pools/metadata here; at least bump counters
            // so future fresh_*() keep monotonicity:
            dst.next_shape = dst.next_shape.max(src.next_shape);
            dst.next_field = dst.next_field.max(src.next_field);
            dst.next_envshape = dst.next_envshape.max(src.next_envshape);
            dst.next_site = dst.next_site.max(src.next_site);
            dst.next_deopt = dst.next_deopt.max(src.next_deopt);
            dst.next_class = dst.next_class.max(src.next_class);
            dst.next_binding = dst.next_binding.max(src.next_binding);
            dst.next_func = dst.next_func.max(src.next_func);

            // Move functions verbatim, preserving Function.id
            for f in src.funcs.drain(..) {
                let _ = dst.push_function_preserve_id(f);
            }
        }

        #[cfg(debug_assertions)]
        {
            eprintln!("[merge] module order:");
            for p in order {
                eprintln!(
                    "  {:?} modinit={:?} toplevel={:?}",
                    p,
                    modinit_funcs.get(p),
                    toplevel_funcs.get(p)
                );
            }
        }

        // Build a tiny bootstrap that runs every module's __modinit__ and __toplevel__
        // following the dependency order, returning the entry module's result.
        let mut builder = WirBuilder::new(&mut dst, "__program__", vec![], vec![Type::Int32]);
        let mut last_ret: Option<crate::wir::ValueId> = None;
        let mut entry_ret: Option<crate::wir::ValueId> = None;

        for path in order {
            if let Some(fid) = modinit_funcs.get(path) {
                let _ = builder.push_node(
                    Inst::CallDirect {
                        conv: CallConv::Fast,
                        callee: *fid,
                        args: Vec::new(),
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
            }

            if let Some(fid) = toplevel_funcs.get(path) {
                let (_nid, res) = builder.push_node(
                    Inst::CallDirect {
                        conv: CallConv::Fast,
                        callee: *fid,
                        args: Vec::new(),
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
                let (_nid, awaited) = builder.push_node(
                    Inst::CallNative {
                        name: "wir_await".into(),
                        args: vec![res[0]],
                        pure: false,
                        can_throw: true,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
                last_ret = Some(awaited[0]);
                if path.as_ref() == entry.as_ref() {
                    entry_ret = Some(awaited[0]);
                }
            }
        }

        let ret_val = if let Some(v) = entry_ret {
            v
        } else if let Some(v) = last_ret {
            v
        } else {
            builder.const_i32(0)
        };
        builder.ret(&[ret_val]);
        let bootstrap = builder.finish();
        let _ = dst.push_function(bootstrap);

        Ok(dst)
    }

    fn build_link_info_for_module(
        &self,
        path: &Arc<PathBuf>,
        prog: &Program,
        // Bindings of exported classes across all modules (re-exports share them).
        class_bindings: &HashSet<BindingId>,
    ) -> Result<LinkInfo, String> {
        // 1. Start with a fresh LinkInfo for the current module.
        let mut links = LinkInfo::default();

        // 2. Get the ModuleAST for the current module, which contains the results of the parse-time binding.
        let module_ast = self.ctx.registry.get(path).ok_or_else(|| {
            format!(
                "[Linker] FATAL: Missing ModuleAST for own module {:?}",
                path
            )
        })?;

        // 3. Populate this module's OWN exports, keyed by local name. Re-exported names are
        //    left out: their cells are owned and initialized by the providing module.
        for (local, binding) in Self::own_export_bindings(module_ast, prog) {
            links.export_bindings.insert(local, binding);
        }

        // 4. Iterate through all `import` statements in this module to resolve them.
        for imp in &prog.imports {
            // Resolve the "./math" style specifier to a full, canonical path.
            let resolved_provider_path = self
                .loader
                .resolve(path.as_ref(), &imp.specifier)
                .map_err(|e| {
                    format!(
                        "Linker cannot resolve '{}' from {:?}: {}",
                        imp.specifier, path, e
                    )
                })?;
            let resolved_provider_arc = Arc::new(resolved_provider_path);

            // Get the ModuleAST of the module we are importing FROM.
            let provider_ast = self
                .ctx
                .registry
                .get(&resolved_provider_arc)
                .ok_or_else(|| {
                    format!(
                        "[Linker] FATAL: Missing provider ModuleAST for {:?}",
                        resolved_provider_arc
                    )
                })?;

            // 5. Now, process each item in the `import` statement (`{a, b}`, `* as ns`).
            for item in &imp.items {
                match item {
                    // Case: `import { name as alias } from ...`
                    ImportItem::Named { name, alias } => {
                        let local_name = alias.as_ref().unwrap_or(name);

                        // Find the export in the provider module to get the globally unique BindingId.
                        if let Some(provider_export_item) = provider_ast.exports.get(name.as_str())
                        {
                            let global_binding_id = provider_export_item.binding;

                            // Map our local name to that global ID.
                            links
                                .import_bindings
                                .insert(local_name.clone(), global_binding_id);

                            // Check if this binding is for a class and record it.
                            if class_bindings.contains(&global_binding_id) {
                                links.imported_class_bindings.insert(global_binding_id);
                            }
                        } else {
                            // This would be a linker error in a real compiler.
                            #[cfg(debug_assertions)]
                            eprintln!(
                                "[Linker] WARNING: Module {:?} imports '{}' from {:?}, but it is not exported.",
                                path, name, resolved_provider_arc
                            );
                        }
                    }
                    // Case: `import * as ns from ...`
                    ImportItem::Namespace { alias } => {
                        // Collect ALL exports from the provider module.
                        let all_provider_exports: Vec<(String, BindingId)> = provider_ast
                            .exports
                            .iter()
                            .map(|(name, item)| ((*name).to_string(), item.binding))
                            .collect();

                        // Map our local namespace alias to this full list.
                        links
                            .namespace_imports
                            .insert(alias.clone(), all_provider_exports);
                    }
                }
            }
        }

        // 6. Return the fully populated LinkInfo for this module.
        Ok(links)
    }

    /// Single public entry point to build the whole program graph from an entry file.
    /// Resolves the entry to an absolute path, parses it, drains the queue of modules
    /// discovered through `import`, and binds named imports to exporters.
    pub fn build_from_entry(&mut self, entry: &str) -> Result<crate::wir::Module, String> {
        let abs =
            std::fs::canonicalize(entry).map_err(|e| format!("canonicalize({entry}): {e}"))?;
        let abs = Arc::new(abs);

        self.enqueue_if_new(abs.clone());

        // Drain the queue (no re-entrancy; parser only runs here).
        loop {
            let next_opt = { self.pending.borrow_mut().pop() };
            if let Some(next) = next_opt {
                self.parse_one(next)?;
            } else {
                break;
            }
        }

        // Point re-exports at the bindings of the declarations they forward.
        self.link_reexports()?;

        // After parsing every module, bind named imports to export BindingIds.
        self.bind_imports()?;

        // For compatibility: return an empty WIR here. Real code should call
        // `lower_all_modules_parallel_sharded()` (parallel) or provide a merge.
        Ok(crate::wir::Module::new())
    }

    /// Parallel lower: one May fiber per module. Each fiber produces its own
    /// `wir::Module` shard. We return a map pathâ†’module for the caller to link/merge.
    ///
    /// Safety/ownership:
    ///  - We **precompute** (path, Program, LinkInfo) on the main thread to avoid
    ///    shared mutable borrows inside fibers.
    ///  - Each fiber owns its `Program` clone and `LinkInfo` (by value).
    ///  - The `Lowerer` inside the fiber only mutates its own fresh `wir::Module`.
    pub fn lower_all_modules_parallel_sharded(
        &self,
    ) -> Result<HashMap<Arc<PathBuf>, crate::wir::Module>, String> {
        use may::coroutine::Builder as CoBuilder;
        let num_cpus: usize = thread::available_parallelism()
            .unwrap_or(NonZeroUsize::new(1).unwrap())
            .get();
        may::config().set_workers(num_cpus).set_worker_pin(true);
        may::config().set_stack_size(WORKER_STACK_BYTES);

        // 1) Materialize the worklist with all immutable data a fiber needs.
        //    (path, program, links)
        #[derive(Clone)]
        struct Job {
            path: Arc<PathBuf>,
            prog: Program,
            links: LinkInfo,
            source: String,
        }

        let build_start = std::time::Instant::now();

        let mut jobs: Vec<Job> = Vec::new();
        let mut class_bindings: HashSet<BindingId> = HashSet::default();
        for (path, prog) in self.programs.get_internals() {
            if let Some(module_ast) = self.ctx.registry.get(path) {
                for (local, binding) in Self::own_export_bindings(module_ast, prog) {
                    if prog.classes.iter().any(|c| c.name == local) {
                        class_bindings.insert(binding);
                    }
                }
            }
        }

        // Stable order for determinism
        let mut paths: Vec<Arc<PathBuf>> = self.ctx.registry.keys().cloned().collect();
        paths.sort_by(|a, b| a.as_path().cmp(b.as_path()));

        for path in paths {
            // Get Program clone
            let prog = self
                .programs
                .get(&path)
                .ok_or_else(|| format!("lower(parallel): missing Program for {:?}", path))?
                .clone();

            // Build LinkInfo (imports resolved, exports, namespaces, class metadata)
            let links = self.build_link_info_for_module(&path, &prog, &class_bindings)?;

            let source = self.sources.get(&path).cloned().unwrap_or_default();
            jobs.push(Job {
                path,
                prog,
                links,
                source,
            });
        }

        // 2) Spawn one fiber per job. Each returns (path, Module) or error String.
        let mut handles = Vec::with_capacity(jobs.len());
        for (i, job) in jobs.into_iter().enumerate() {
            let name = format!("lower#{}", i);
            let h = unsafe {
                CoBuilder::new().name(name).spawn(
                    move || -> Result<(Arc<PathBuf>, crate::wir::Module), String> {
                        // Lower into a fresh module
                        let mut m = crate::wir::Module::new();

                        let mut lowerer = Lowerer::new(&mut m);
                        lowerer
                            .set_links(job.links)
                            .lower_program(&job.prog)
                            .map_err(|e| {
                                report_lower_error(&job.path, &job.prog, &job.source, e)
                            })?;

                        let optimize = optimization_passes();
                        optimize.optimize_module(&mut m);

                        Ok((job.path, m))
                    },
                )
            }
            .map_err(|e| format!("may spawn failed: {e}"))?;
            handles.push(h);
        }

        // 3) Join all and gather results.
        let mut out: HashMap<Arc<PathBuf>, crate::wir::Module> = HashMap::default();
        let mut coroutine_counter = 1;
        for h in handles {
            let (p, m) = h
                .join()
                .map_err(|e| format!("fiber join failed: {}", coroutine_counter))??;
            out.insert(p, m);
            coroutine_counter += 1;
        }

        let build_elapsed = build_start.elapsed();
        #[cfg(debug_assertions)]
        eprintln!(
            "(Debug build) Lowering the program took {:.6} seconds with {} workers",
            build_elapsed.as_secs_f64(),
            num_cpus
        );

        Ok(out)
    }

    fn topo_order(&self) -> Result<Vec<Arc<PathBuf>>, String> {
        // 1) provider -> {importers}
        let mut incoming: HashMap<Arc<PathBuf>, usize> = HashMap::default(); // indegree
        let mut outgoing: HashMap<Arc<PathBuf>, Vec<Arc<PathBuf>>> = HashMap::default();

        for k in self.ctx.registry.keys() {
            incoming.entry(k.clone()).or_insert(0);
            outgoing.entry(k.clone()).or_insert_with(Vec::new);
        }

        // tgt imports from src  =>  src -> tgt
        for (tgt_path, tgt_box) in self.ctx.registry.get_internals() {
            let tgt = &**tgt_box;
            for (_k, req) in tgt.imports.get_internals() {
                let src = req.from_path.clone();
                outgoing
                    .entry(src.clone())
                    .or_default()
                    .push(tgt_path.clone());
                *incoming.entry(tgt_path.clone()).or_insert(0) += 1;
                // aseguros de tener src en incoming
                incoming.entry(src).or_insert(0);
            }
        }

        // 2) Kahn
        use std::collections::VecDeque;
        let q: VecDeque<Arc<PathBuf>> = incoming
            .iter()
            .filter_map(|(k, &deg)| if deg == 0 { Some(k.clone()) } else { None })
            .collect();

        // deterministic order
        let mut qv: Vec<_> = q.into_iter().collect();
        qv.sort_by(|a, b| a.as_path().cmp(b.as_path()));
        let mut q: VecDeque<_> = qv.into_iter().collect();

        let mut out = Vec::new();
        while let Some(n) = q.pop_front() {
            out.push(n.clone());
            if let Some(children) = outgoing.get(&n) {
                for ch in children {
                    if let Some(d) = incoming.get_mut(ch) {
                        *d -= 1;
                        if *d == 0 {
                            q.push_back(ch.clone());
                        }
                    }
                }
            }
        }

        // If we didn't output every node, there's a cycle
        if out.len() != self.ctx.registry.len() {
            return Err("cycle detected in module imports".into());
        }
        Ok(out)
    }

    // ------------------------
    // API called by the Parser
    // ------------------------

    /// The parser calls this when it encounters an `import` (absolute path already resolved).
    pub fn note_pending(&self, abs: Arc<PathBuf>) {
        self.enqueue_if_new(abs);
    }

    /// The parser may call this at the end of `program()`. We keep it a no-op to
    /// avoid re-entrancy and borrow complexity. The actual draining happens in
    /// `build_from_entry`.
    pub fn parse_next(&self, _ctx: &ModulesCTX) -> Result<(), String> {
        Ok(())
    }

    // ------------------------
    // Internals
    // ------------------------

    fn enqueue_if_new(&self, abs: Arc<PathBuf>) {
        let mut v = self.visited.borrow_mut();
        if v.insert(abs.clone()) {
            self.pending.borrow_mut().push(abs);
        }
    }

    /// Parse a single module at absolute path `abs`, producing and registering a fresh ModuleAST,
    /// and keeping the full `Program` AST aside (for lowerer).
    fn parse_one(&mut self, abs: Arc<PathBuf>) -> Result<(), String> {
        // 1) Read source
        let src = self
            .loader
            .read_to_string(&abs)
            .map_err(|e| format!("read_to_string({:?}): {e}", abs))?;
        let src = with_implicit_std_imports(&abs, &src).unwrap_or(src);

        self.sources.insert(abs.clone(), src.clone());

        // 2) Create ModuleAST box (non-'static â†’ 'static)
        let ast_box_nonstatic: Box<ModuleAST<'_>> = Box::new(ModuleAST {
            id: ModuleId(self.ctx.registry.len() as u32),
            path: abs.clone(),
            exports: HashMap::default(),
            imports: HashMap::default(),
        });
        let ast_box_static: Box<ModuleAST<'static>> = unsafe {
            std::mem::transmute::<Box<ModuleAST<'_>>, Box<ModuleAST<'static>>>(ast_box_nonstatic)
        };

        // Insert the Box into the registry and take a temporary raw pointer
        let ast_ptr: *mut ModuleAST<'_> = {
            let entry: &mut Box<ModuleAST<'static>> = self
                .ctx
                .registry
                .entry(abs.clone())
                .or_insert(ast_box_static);
            &mut **entry as *mut ModuleAST<'static> as *mut ModuleAST<'_>
        };

        // 3) Parse AND do debug logging **inside** this scope so `Parser` is dropped
        let prog: Program = {
            let mut p = Parser::with_module(
                &src,
                &self.ctx,
                self,        // &ProgramBuilder (resolver)
                ast_ptr,     // *mut ModuleAST
                abs.clone(), // referrer
            );

            let prog = match p.program() {
                Ok(pr) => pr,
                Err(e) => {
                    e.emit(p.file_name(), p.source());
                    return Err(format!("Parse error in {:?}: {}", abs, e.msg));
                }
            };

            // Debug while `p` (and its borrows) are still in-scope
            #[cfg(debug_assertions)]
            unsafe {
                let m = &*ast_ptr;
                eprintln!(
                    "[builder:end-parse] path={:?} | imports={} | exports={}",
                    m.path,
                    m.imports.len(),
                    m.exports.len()
                );
                if m.imports.is_empty() {
                    eprintln!("  [imports] (none)");
                } else {
                    eprintln!("  [imports]");
                    for (key_path, req) in m.imports.get_internals() {
                        let names = if req.names.is_empty() {
                            "(side-effect only)".to_string()
                        } else {
                            req.names.iter().copied().collect::<Vec<_>>().join(", ")
                        };
                        eprintln!(
                            "    - key={:?}\n      from_path={:?}\n      names=[{}]\n      resolved_items={}",
                            key_path,
                            req.from_path,
                            names,
                            req.resolved.len()
                        );
                    }
                }
                if m.exports.is_empty() {
                    eprintln!("  [exports] (none)");
                } else {
                    eprintln!("  [exports]");
                    for (name, item) in m.exports.get_internals() {
                        eprintln!("    - {} -> binding {:?}", name, item.binding);
                    }
                }
            }

            // <- `p` se destruye aquÃ­, junto con cualquier prÃ©stamo a `&self`
            prog
        };

        // 4) Ahora ya podemos mutar `self` con total seguridad
        self.programs.insert(abs.clone(), prog);
        Ok(())
    }

    /// Makes every exported name share the binding of the declaration it refers to:
    /// `export { a as b } from`, `export * from`, and a local exported under several
    /// names (`export { a, a as b }`). Providers are linked before their re-exporters.
    fn link_reexports(&mut self) -> Result<(), String> {
        let mut paths: Vec<Arc<PathBuf>> = self.programs.keys().cloned().collect();
        paths.sort();
        let mut done: HashSet<Arc<PathBuf>> = HashSet::default();
        for path in &paths {
            self.link_module_reexports(path, &mut done, &mut Vec::new())?;
        }
        Ok(())
    }

    fn link_module_reexports(
        &mut self,
        path: &Arc<PathBuf>,
        done: &mut HashSet<Arc<PathBuf>>,
        stack: &mut Vec<Arc<PathBuf>>,
    ) -> Result<(), String> {
        if done.contains(path) {
            return Ok(());
        }
        if stack.contains(path) {
            return Err(format!("cyclic re-export involving {:?}", path));
        }
        let Some(program) = self.programs.get(path) else {
            return Ok(());
        };
        let exports = program.exports.clone();
        stack.push(path.clone());

        let mut providers = Vec::new();
        for export in &exports {
            if let ExportDecl::From { specifier, .. } | ExportDecl::AllFrom { specifier } = export {
                let target = self
                    .loader
                    .resolve(path.as_ref(), specifier)
                    .map_err(|e| format!("cannot resolve re-export '{}' from {:?}: {}", specifier, path, e))?;
                let target = Arc::new(target);
                self.link_module_reexports(&target, done, stack)?;
                providers.push((export, target));
            }
        }

        let module = self
            .ctx
            .registry
            .get(path)
            .ok_or_else(|| format!("[Linker] FATAL: Missing ModuleAST for {:?}", path))?;
        let mut updates: Vec<(&'static str, Option<BindingId>, Option<crate::diag::Meta>)> =
            Vec::new();

        // Several public names for the same local share one binding.
        let mut local_binding: HashMap<String, BindingId> = HashMap::default();
        for export in &exports {
            if let ExportDecl::Func(n) | ExportDecl::Class(n) | ExportDecl::Var(n) = export {
                if let Some(item) = module.exports.get(n.as_str()) {
                    local_binding.entry(n.clone()).or_insert(item.binding);
                }
            }
        }
        for export in &exports {
            if let ExportDecl::Named { items } = export {
                for (local, alias) in items {
                    let public = alias.as_ref().unwrap_or(local);
                    let Some((&key, item)) = module.exports.get_key_value(public.as_str()) else {
                        continue;
                    };
                    match local_binding.get(local) {
                        Some(&binding) => updates.push((key, Some(binding), None)),
                        None => {
                            local_binding.insert(local.clone(), item.binding);
                        }
                    }
                }
            }
        }

        for (export, target) in providers {
            let provider = self
                .ctx
                .registry
                .get(&target)
                .ok_or_else(|| format!("[Linker] FATAL: Missing ModuleAST for {:?}", target))?;
            match export {
                ExportDecl::From { items, .. } => {
                    for (source, alias) in items {
                        let public = alias.as_ref().unwrap_or(source);
                        let Some((&key, _)) = module.exports.get_key_value(public.as_str()) else {
                            continue;
                        };
                        // Names without a runtime binding are type-only re-exports; the
                        // type checker reports the ones that are not exported at all.
                        match provider.exports.get(source.as_str()) {
                            Some(item) => updates.push((key, Some(item.binding), None)),
                            None => updates.push((key, None, None)),
                        }
                    }
                }
                ExportDecl::AllFrom { .. } => {
                    for (&name, item) in provider.exports.iter() {
                        // Explicit exports win over `export *`, as do earlier `export *`s.
                        if module.exports.contains_key(name)
                            || updates.iter().any(|(n, _, _)| *n == name)
                        {
                            continue;
                        }
                        updates.push((name, Some(item.binding), Some(item.meta.clone())));
                    }
                }
                _ => {}
            }
        }

        let module = self
            .ctx
            .registry
            .get_mut(path)
            .ok_or_else(|| format!("[Linker] FATAL: Missing ModuleAST for {:?}", path))?;
        for (name, binding, meta) in updates {
            let Some(binding) = binding else {
                module.exports.remove(name);
                continue;
            };
            match module.exports.get_mut(name) {
                Some(item) => item.binding = binding,
                None => {
                    module.exports.insert(
                        name,
                        crate::front::ExportItem {
                            name,
                            binding,
                            meta: meta.unwrap_or_default(),
                        },
                    );
                }
            }
        }

        stack.pop();
        done.insert(path.clone());
        Ok(())
    }

    /// Exports declared by `prog` itself, keyed by local name. Re-exported names
    /// are excluded: their cells belong to (and are initialized by) the provider.
    fn own_export_bindings(module_ast: &ModuleAST<'static>, prog: &Program) -> Vec<(String, BindingId)> {
        let mut out: Vec<(String, BindingId)> = Vec::new();
        let mut push = |local: &str, public: &str| {
            if out.iter().any(|(n, _)| n == local) {
                return;
            }
            if let Some(item) = module_ast.exports.get(public) {
                out.push((local.to_string(), item.binding));
            }
        };
        for export in &prog.exports {
            match export {
                ExportDecl::Func(n) | ExportDecl::Class(n) | ExportDecl::Var(n) => push(n, n),
                ExportDecl::Named { items } => {
                    for (local, alias) in items {
                        push(local, alias.as_ref().unwrap_or(local));
                    }
                }
                _ => {}
            }
        }
        out
    }

    /// Bind named imports to the exporter modules' BindingIds, writing into each
    /// `ImportRequest.resolved`. Namespace imports and re-exports are left for later.
    fn bind_imports(&mut self) -> Result<(), String> {
        // Snapshot all jobs to avoid borrow conflicts.
        let mut jobs: Vec<(Arc<PathBuf>, Arc<PathBuf>, Vec<&'static str>)> = Vec::new();

        for (tgt_path, tgt_box) in self.ctx.registry.get_internals() {
            let tgt: &ModuleAST<'static> = &**tgt_box;
            for (_k, req) in tgt.imports.get_internals() {
                jobs.push((
                    tgt_path.clone(),
                    req.from_path.clone(),
                    req.names.clone(), // Vec<&'static str>
                ));
            }
        }

        for (tgt_path, from_path, names) in jobs {
            for name in names {
                let binding_opt = {
                    let src_box =
                        self.ctx.registry.get(&from_path).ok_or_else(|| {
                            format!("bind: source module not found: {:?}", from_path)
                        })?;
                    let src = &**src_box;
                    src.exports.get(name).map(|ei| ei.binding)
                };

                if let Some(binding) = binding_opt {
                    let tgt_box_mut =
                        self.ctx.registry.get_mut(&tgt_path).ok_or_else(|| {
                            format!("bind: target module not found: {:?}", tgt_path)
                        })?;
                    let tgt: &mut ModuleAST<'static> = &mut **tgt_box_mut;
                    if let Some(req_mut) = tgt.imports.get_mut(&from_path) {
                        req_mut.resolved.push((name, binding));
                    }
                } else {
                    #[cfg(debug_assertions)]
                    eprintln!(
                        "[bind] WARNING: {:?} imports '{}' from {:?}, but it's not exported there.",
                        tgt_path, name, from_path
                    );
                }
            }
        }

        Ok(())
    }
}

/// -----------------------------------------
/// Public facade
/// -----------------------------------------
pub fn build_whole_program_from_entry(entry: &str) -> Result<crate::wir::Module, String> {
    let mut builder = ProgramBuilder::new(FSLoader);
    builder.build_whole_program(entry)
}

/// Finds a `var`/`enum` declaration of `name` anywhere in the program's statements.
fn find_block_decl(prog: &Program, name: &str) -> Option<crate::diag::Meta> {
    use crate::front::{Block, Stmt, StmtKind};
    fn in_block(block: &Block, name: &str) -> Option<crate::diag::Meta> {
        block.stmts.iter().find_map(|s| in_stmt(s, name))
    }
    fn in_stmt(stmt: &Stmt, name: &str) -> Option<crate::diag::Meta> {
        match stmt.kind() {
            StmtKind::Var { name: n, .. } | StmtKind::Enum { name: n, .. } if n == name => {
                Some(stmt.meta.clone())
            }
            StmtKind::If { then_b, else_b, .. } => {
                in_block(then_b, name).or_else(|| else_b.as_ref().and_then(|b| in_block(b, name)))
            }
            StmtKind::While { body, .. } | StmtKind::Defer { body, .. } => in_block(body, name),
            StmtKind::For { init, body, .. } => init
                .as_deref()
                .and_then(|s| in_stmt(s, name))
                .or_else(|| in_block(body, name)),
            StmtKind::Try {
                try_block,
                catch,
                finally_block,
            } => in_block(try_block, name)
                .or_else(|| catch.as_ref().and_then(|c| in_block(&c.body, name)))
                .or_else(|| finally_block.as_ref().and_then(|b| in_block(b, name))),
            _ => None,
        }
    }
    prog.functions.iter().find_map(|f| in_block(&f.body, name))
}

/// Turns a lowering error into a message, printing a source diagnostic when possible.
fn report_lower_error(path: &Path, prog: &Program, source: &str, err: LowerError) -> String {
    let LowerError::Undefined { name, meta } = err else {
        return format!("lower error in {:?}: {:?}", path, err);
    };
    let mut message = format!("`{}` is not defined in this scope", name);
    if let Some(decl) = find_block_decl(prog, &name) {
        let line = source
            .get(..decl.span.range.start)
            .map_or(0, |s| s.matches('\n').count())
            + 1;
        message.push_str(&format!(
            " (it is declared at line {} inside a block; `var` is block-scoped, \
             so declare it in an enclosing scope)",
            line
        ));
    }
    let file_name = path.to_string_lossy();
    crate::front::ParseError::new(message.clone(), meta).emit(file_name.as_ref(), source);
    format!("Scope error in {:?}: {}", path, message)
}

pub fn build_simple_program_from_entry(entry: &str) -> Result<crate::wir::Module, String> {
    let abs = std::fs::canonicalize(entry).map_err(|e| format!("canonicalize({entry}): {e}"))?;

    let src =
        std::fs::read_to_string(&abs).map_err(|e| format!("read_to_string({}): {e}", entry))?;

    let path_str = abs.to_string_lossy();
    let mut parser: Parser = Parser::with_name(&src, path_str.as_ref());

    let prog = match parser.program() {
        Ok(p) => p,
        Err(e) => {
            e.emit(parser.file_name(), parser.source());
            return Err(format!("Parse error in {:?}: {}", abs, e.msg));
        }
    };

    let mut m = crate::wir::Module::new();

    let mut lowerer = Lowerer::new(&mut m);
    lowerer
        .lower_program(&prog)
        .map_err(|e| report_lower_error(&abs, &prog, &src, e))?;

    let optimize = optimization_passes();
    optimize.optimize_module(&mut m);
    Ok(m)
}
