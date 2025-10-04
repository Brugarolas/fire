// src/modules.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

use bumpalo::Bump;
use hybrid_rc::Arc;
use may::coroutine;
use std::num::NonZeroUsize;
use std::thread;
use std::{
    cell::RefCell,
    path::{Path, PathBuf},
};

use crate::collections::{HashMap, HashSet};
use crate::front::{ExportDecl, ImportItem, ModuleAST, Parser, Program};
use crate::lowerer::{LinkInfo, Lowerer};
use crate::opt::optimization::optimization_passes;
use crate::wir::{Builder as WirBuilder, CallConv, FuncId, IdRemap, Inst, Type, BindingId};

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
    /// Registry of parsed modules (by absolute path) → Box<ModuleAST>.
    pub registry: HashMap<Arc<PathBuf>, Box<ModuleAST<'static>>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ExportSymbolKind {
    Function,
    Class,
    Other,
}

pub trait ModuleLoader {
    fn read_to_string(&self, path: &Path) -> std::io::Result<String>;
    fn resolve(&self, referrer: &Path, spec: &str) -> std::io::Result<PathBuf>;
}

pub struct FSLoader;

impl ModuleLoader for FSLoader {
    fn read_to_string(&self, path: &Path) -> std::io::Result<String> {
        std::fs::read_to_string(path)
    }

    fn resolve(&self, referrer: &Path, spec: &str) -> std::io::Result<PathBuf> {
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
        }
    }

    pub fn build_whole_program(&mut self, entry: &str) -> Result<crate::wir::Module, String> {
        // 1) parse + bind
        let entry_abs =
            std::fs::canonicalize(entry).map_err(|e| format!("canonicalize({entry}): {e}"))?;
        let entry_arc = Arc::new(entry_abs);

        self.build_from_entry(entry)?;

        // 2) lower + optimize en paralelo
        let shards = self.lower_all_modules_parallel_sharded()?;

        // 3) orden de inicialización (proveedores → consumidores)
        let order = self.topo_order()?;

        // 4) merge a un único WIR
        self.merge_wir_shards(shards, &order, &entry_arc)
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
                last_ret = Some(res[0]);
                if path.as_ref() == entry.as_ref() {
                    entry_ret = Some(res[0]);
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
        // This cache is important to avoid re-analyzing the AST of modules that are imported multiple times.
        export_kind_cache: &mut HashMap<Arc<PathBuf>, HashMap<String, ExportSymbolKind>>,
    ) -> Result<LinkInfo, String> {
        // 1. Start with a fresh LinkInfo for the current module.
        let mut links = LinkInfo::default();

        // 2. Get the ModuleAST for the current module, which contains the results of the parse-time binding.
        let module_ast = self
            .ctx
            .registry
            .get(path)
            .ok_or_else(|| format!("[Linker] FATAL: Missing ModuleAST for own module {:?}", path))?;

        // 3. Populate this module's OWN exports. The BindingIds were already created correctly by the parser
        //    and stored in this module's ModuleAST. We just copy them over.
        for (name, item) in module_ast.exports.get_internals() {
            links
                .export_bindings
                .insert((*name).to_string(), item.binding);
        }

        // 4. Iterate through all `import` statements in this module to resolve them.
        for imp in &prog.imports {
            // Resolve the "./math" style specifier to a full, canonical path.
            let resolved_provider_path = self
                .loader
                .resolve(path.as_ref(), &imp.specifier)
                .map_err(|e| format!("Linker cannot resolve '{}' from {:?}: {}", imp.specifier, path, e))?;
            let resolved_provider_arc = Arc::new(resolved_provider_path);

            // Get the ModuleAST of the module we are importing FROM.
            let provider_ast = self
                .ctx
                .registry
                .get(&resolved_provider_arc)
                .ok_or_else(|| format!("[Linker] FATAL: Missing provider ModuleAST for {:?}", resolved_provider_arc))?;

            // 5. To know if an import is a class, we need to inspect the provider's full AST.
            //    We do this once per provider and cache the results.
            if !export_kind_cache.contains_key(&resolved_provider_arc) {
                let provider_prog = self
                    .programs
                    .get(&resolved_provider_arc)
                    .ok_or_else(|| format!("[Linker] FATAL: Missing provider Program AST for {:?}", resolved_provider_arc))?;

                let mut kind_map = HashMap::default();
                for ed in &provider_prog.exports {
                    match ed {
                        ExportDecl::Func(name) => {
                            kind_map.insert(name.clone(), ExportSymbolKind::Function);
                        }
                        ExportDecl::Class(name) => {
                            kind_map.insert(name.clone(), ExportSymbolKind::Class);
                        }
                        ExportDecl::Var(name) => {
                            kind_map.insert(name.clone(), ExportSymbolKind::Other);
                        }
                        ExportDecl::Named { items } | ExportDecl::From { items, .. } => {
                            for (local, alias) in items {
                                let public_name = alias.clone().unwrap_or_else(|| local.clone());
                                // We can't know the original type of a re-export without deep analysis,
                                // so we conservatively mark it as 'Other'.
                                kind_map.entry(public_name).or_insert(ExportSymbolKind::Other);
                            }
                        }
                        ExportDecl::AllFrom { .. } => {
                            // Re-exporting all is too complex to analyze here, skip for now.
                        }
                    }
                }
                export_kind_cache.insert(resolved_provider_arc.clone(), kind_map);
            }
            let export_kinds = export_kind_cache.get(&resolved_provider_arc).unwrap();

            // 6. Now, process each item in the `import` statement (`{a, b}`, `* as ns`).
            for item in &imp.items {
                match item {
                    // Case: `import { name as alias } from ...`
                    ImportItem::Named { name, alias } => {
                        let local_name = alias.as_ref().unwrap_or(name);

                        // Find the export in the provider module to get the globally unique BindingId.
                        if let Some(provider_export_item) = provider_ast.exports.get(name.as_str()) {
                            let global_binding_id = provider_export_item.binding;

                            // Map our local name to that global ID.
                            links.import_bindings.insert(local_name.clone(), global_binding_id);

                            // Check if this binding is for a class and record it.
                            if matches!(export_kinds.get(name), Some(&ExportSymbolKind::Class)) {
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
                        links.namespace_imports.insert(alias.clone(), all_provider_exports);
                    }
                }
            }
        }

        // 7. Return the fully populated LinkInfo for this module.
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

        // After parsing every module, bind named imports to export BindingIds.
        self.bind_imports()?;

        // For compatibility: return an empty WIR here. Real code should call
        // `lower_all_modules_parallel_sharded()` (parallel) or provide a merge.
        Ok(crate::wir::Module::new())
    }

    /// Parallel lower: one May fiber per module. Each fiber produces its own
    /// `wir::Module` shard. We return a map path→module for the caller to link/merge.
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
        }

        let mut jobs: Vec<Job> = Vec::new();
        let mut export_kind_cache: HashMap<Arc<PathBuf>, HashMap<String, ExportSymbolKind>> =
            HashMap::default();

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
            let links = self.build_link_info_for_module(&path, &prog, &mut export_kind_cache)?;

            jobs.push(Job { path, prog, links });
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
                        lowerer.set_links(job.links)
                            .lower_program(&job.prog)
                            .map_err(|e| format!("lower error in {:?}: {:?}", &job.path, e))?;

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
        let mut q: VecDeque<Arc<PathBuf>> = incoming
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

    pub fn build_bundle(&mut self, entry: &str) -> Result<BuiltBundle, String> {
        // 1) parser + bind imports
        self.build_from_entry(entry)?; // ya parsea cola y hace `bind_imports()`

        // 2) lowering and optimization (parallel)
        let shards = self.lower_all_modules_parallel_sharded()?;

        // 3) init order (topological sort)
        let init_order = self.topo_order()?;

        Ok(BuiltBundle { shards, init_order })
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

        // 2) Create ModuleAST box (non-'static → 'static)
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

            let prog = p
                .program()
                .map_err(|e| format!("Parse error in {:?}: {} at {:?}", abs, e.msg, e.span))?;

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

            // <- `p` se destruye aquí, junto con cualquier préstamo a `&self`
            prog
        };

        // 4) Ahora ya podemos mutar `self` con total seguridad
        self.programs.insert(abs.clone(), prog);
        Ok(())
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

pub fn build_simple_program_from_entry(entry: &str) -> Result<crate::wir::Module, String> {
    let abs = std::fs::canonicalize(entry).map_err(|e| format!("canonicalize({entry}): {e}"))?;

    let src =
        std::fs::read_to_string(&abs).map_err(|e| format!("read_to_string({}): {e}", entry))?;

    let mut parser: Parser = Parser::new(&src);

    let prog = parser
        .program()
        .map_err(|e| format!("Parse error in {:?}: {} at {:?}", abs, e.msg, e.span))?;

    let mut m = crate::wir::Module::new();

    let mut lowerer = Lowerer::new(&mut m);
    lowerer
        .lower_program(&prog)
        .map_err(|e| format!("lower error in {:?}: {:?}", &abs, e))?;

    let optimize = optimization_passes();
    optimize.optimize_module(&mut m);
    Ok(m)
}
