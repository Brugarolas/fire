// src/modules.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

use ahash::{AHashMap as HashMap, AHashSet as HashSet};
use bumpalo::Bump;
use hybrid_rc::Arc;
use std::{
    cell::RefCell,
    path::{Path, PathBuf},
};

use crate::front::{ModuleAST, Parser};

/// -----------------------------------------
/// Minimal infra
/// -----------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(pub u32);

#[derive(Default)]
pub struct ModulesCTX {
    /// Bump arena used by the parser to intern &'static str for import/export names.
    pub arena: Bump,
    /// Registry of parsed modules (by absolute path) → Box<ModuleAST>.
    pub registry: HashMap<Arc<PathBuf>, Box<ModuleAST<'static>>>,
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
///  - the single public entry `build_from_entry`.
pub struct ProgramBuilder {
    pub ctx: ModulesCTX,
    loader: FSLoader,

    /// LIFO queue of absolute paths to parse (pop/push).
    pending: RefCell<Vec<Arc<PathBuf>>>,
    /// Set of absolute paths already enqueued/visited to avoid duplicates.
    visited: RefCell<HashSet<Arc<PathBuf>>>,
}

impl ProgramBuilder {
    pub fn new(loader: FSLoader) -> Self {
        Self {
            ctx: ModulesCTX::default(),
            loader,
            pending: RefCell::new(Vec::new()),
            visited: RefCell::new(HashSet::new()),
        }
    }

    /// Single public entry point to build the whole program graph from an entry file.
    /// Resolves the entry to an absolute path, parses it, drains the queue of modules
    /// discovered through `import`, and then binds named imports to export bindings.
    pub fn build_from_entry(&mut self, entry: &str) -> Result<crate::wir::Module, String> {
        let abs = std::fs::canonicalize(entry)
            .map_err(|e| format!("canonicalize({entry}): {e}"))?;
        let abs = Arc::new(abs);

        self.enqueue_if_new(abs.clone());

        // Drain the queue. IMPORTANT: limit the lifetime of RefMut so we can
        // borrow `self` mutably again inside the loop (for parse_one).
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

        // For now just return an empty WIR to keep compatibility with your pipeline.
        let wir = crate::wir::Module::new();
        Ok(wir)
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

    /// Parse a single module at absolute path `abs`, producing and registering a fresh ModuleAST.
    fn parse_one(&mut self, abs: Arc<PathBuf>) -> Result<(), String> {
        // 1) Read source
        let src = self
            .loader
            .read_to_string(&abs)
            .map_err(|e| format!("read_to_string({:?}): {e}", abs))?;

        // 2) Create a fresh ModuleAST in a Box with a non-'static lifetime first
        let ast_box_nonstatic: Box<ModuleAST<'_>> = Box::new(ModuleAST {
            id: ModuleId(self.ctx.registry.len() as u32),
            path: abs.clone(),
            exports: HashMap::default(),
            imports: HashMap::default(),
        });

        // SAFETY: ModuleAST contains no borrowed data at construction time.
        // The parser will only store &'static str coming from self.ctx.arena.
        let ast_box_static: Box<ModuleAST<'static>> = unsafe {
            std::mem::transmute::<Box<ModuleAST<'_>>, Box<ModuleAST<'static>>>(ast_box_nonstatic)
        };

        // Insert the Box into the registry (we keep ownership there).
        // Then take a temporary raw pointer to pass into the parser.
        let ast_ptr: *mut ModuleAST<'_> = {
            let entry: &mut Box<ModuleAST<'static>> = self.ctx.registry.entry(abs.clone()).or_insert(ast_box_static);
            &mut **entry as *mut ModuleAST<'static> as *mut ModuleAST<'_>
        };

        // 3) Parse
        let mut p = Parser::with_module(
            &src,
            &self.ctx,
            self,        // resolver (ProgramBuilder)
            ast_ptr,     // borrowed raw pointer, valid while Box lives in registry
            abs.clone(), // absolute referrer path
        );

        let _prog = p.program().map_err(|e| {
            format!("Parse error in {:?}: {} at {:?}", abs, e.msg, e.span)
        })?;

        // 4) Debug logs: what the parser stored in the module’s boxes
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
                for (key_path, req) in &m.imports {
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
                for (name, item) in &m.exports {
                    eprintln!("    - {} -> binding {:?}", name, item.binding);
                }
            }
        }

        Ok(())
    }

    /// Bind named imports to the exporter modules' BindingIds, writing into each
    /// `ImportRequest.resolved`. Namespace imports and re-exports are left for later.
    fn bind_imports(&mut self) -> Result<(), String> {
        // 1) Snapshot all “jobs” so we don’t fight the borrow checker:
        //    (target_path, from_path, names[])
        let mut jobs: Vec<(Arc<PathBuf>, Arc<PathBuf>, Vec<&'static str>)> = Vec::new();

        for (tgt_path, tgt_box) in &self.ctx.registry {
            // SAFETY: read-only
            let tgt: &ModuleAST<'static> = &**tgt_box;
            for (_k, req) in &tgt.imports {
                jobs.push((
                    tgt_path.clone(),
                    req.from_path.clone(),
                    req.names.clone(), // Vec<&'static str>
                ));
            }
        }

        // 2) Resolve each name and push into target's `resolved`.
        for (tgt_path, from_path, names) in jobs {
            for name in names {
                // get export binding from source (immutable access)
                let binding_opt = {
                    let src_box = self
                        .ctx
                        .registry
                        .get(&from_path)
                        .ok_or_else(|| format!("bind: source module not found: {:?}", from_path))?;
                    let src = &**src_box;
                    src.exports.get(name).map(|ei| ei.binding)
                };

                match binding_opt {
                    Some(binding) => {
                        // push into target's resolved (mutable access)
                        let tgt_box_mut = self
                            .ctx
                            .registry
                            .get_mut(&tgt_path)
                            .ok_or_else(|| format!("bind: target module not found: {:?}", tgt_path))?;
                        let tgt: &mut ModuleAST<'static> = &mut **tgt_box_mut;
                        if let Some(req_mut) = tgt.imports.get_mut(&from_path) {
                            req_mut.resolved.push((name, binding));
                        }
                    }
                    None => {
                        #[cfg(debug_assertions)]
                        eprintln!(
                            "[bind] WARNING: {:?} imports '{}' from {:?}, but it's not exported there.",
                            tgt_path, name, from_path
                        );
                    }
                }
            }
        }

        // 3) Debug summary
        #[cfg(debug_assertions)]
        {
            for (p, mbox) in &self.ctx.registry {
                let m: &ModuleAST<'static> = &**mbox;
                eprintln!("[bind:summary] module={:?}", p);
                for (fp, req) in &m.imports {
                    let summary = req
                        .resolved
                        .iter()
                        .map(|(n, b)| format!("{}->{:?}", n, b))
                        .collect::<Vec<_>>()
                        .join(", ");
                    eprintln!("  from {:?}: [{}]", fp, summary);
                }
            }
        }

        Ok(())
    }
}

/// -----------------------------------------
/// Public facade (single exported entry point)
/// -----------------------------------------
pub fn build_whole_program_from_entry(entry: &str) -> Result<crate::wir::Module, String> {
    let mut builder = ProgramBuilder::new(FSLoader);
    builder.build_from_entry(entry)
}
