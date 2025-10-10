// src/main.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

mod event_loop;
mod front;
mod gc;
mod helpers;
mod hoister;
mod http;
mod jit;
mod lowerer;
mod modules;
mod native_promises;
mod native_timers;
mod opt;
mod runtime;
mod value;
mod wir;
mod diag;

use crate::helpers::collections::HashMap;
use crate::native_timers::invoke_and_pump;
use crate::opt::Optimize;
use crate::opt::optimization::optimization_passes;
use front::Parser;
use mimalloc::MiMalloc;
use std::path::Path;
use std::time::Instant;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn default_script() -> &'static str {
    r#"
        fn fibonacci(n) {
            if (n <= 1) { return n; }
            return fibonacci(n - 1) + fibonacci(n - 2);
        }
        print(fibonacci(50));
    "#
}

fn build_module_from_source(name: &str, src: &str) -> Result<wir::Module, String> {
    let mut parser = Parser::new(src);
    let prog = parser
        .program()
        .map_err(|e| format!("Parse error in {name}: {} at {:?}", e.msg, e.span))?;

    let mut module = wir::Module::new();
    let mut lowerer = lowerer::Lowerer::new(&mut module);
    lowerer
        .lower_program(&prog)
        .map_err(|e| format!("Lower error in {name}: {:?}", e))?;

    let optimize = optimization_passes();
    optimize.optimize_module(&mut module);
    Ok(module)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // 4.1) Init GC y bind
    #[cfg(feature = "gc")]
    {
        let _gc = gc::NapalmGc::new();
        _gc.bind_current_thread();
    }

    let build_start = Instant::now();

    let (module, build_label) = if args.len() > 1 {
        let input_path = &args[1];
        #[cfg(debug_assertions)]
        eprintln!(
            "(Debug build) Building whole-program (modules graph) from {} ...",
            input_path
        );
        match modules::build_whole_program_from_entry(input_path) {
            Ok(m) => (m, input_path.clone()),
            Err(e) => {
                eprintln!("Error building whole program: {}", e);
                return;
            }
        }
    } else {
        #[cfg(debug_assertions)]
        eprintln!("(Debug build) Building embedded default script ...");
        match build_module_from_source("<default>", default_script()) {
            Ok(m) => (m, "<default>".to_string()),
            Err(e) => {
                eprintln!("Error building default script: {}", e);
                return;
            }
        }
    };

    let build_elapsed = build_start.elapsed();
    #[cfg(debug_assertions)]
    eprintln!(
        "(Debug build) Build WIR for {} took {:.6} seconds",
        build_label,
        build_elapsed.as_secs_f64()
    );

    let jit_start = Instant::now();

    // 4.2) JIT compile ALL functions
    let mut jit = jit::JIT::default();

    let jit_elapsed = jit_start.elapsed();
    #[cfg(debug_assertions)]
    eprintln!(
        "(Debug build) JIT compilation for {} took {:.6} seconds",
        build_label,
        jit_elapsed.as_secs_f64()
    );

    #[cfg(debug_assertions)]
    {
        for f in &module.funcs {
            eprintln!("[func] id={:?} name={}", f.id, f.sig.name);
            if f.sig.name == "__toplevel__" {
                eprintln!("[func-body {:?}] {:#?}", f.id, f);
            }
            if f.sig.name == "__modinit__" {
                eprintln!("[modinit-body {:?}] {:#?}", f.id, f);
            }
        }
    }

    if let Err(e) = jit.predeclare(&module.funcs) {
        eprintln!("JIT predeclare error: {}", e);
        return;
    }

    let mut compile_order: Vec<&wir::Function> = module.funcs.iter().collect();

    for f in compile_order {
        if let Err(e) = jit.compile(f) {
            eprintln!("JIT compile error in {}: {}", f.sig.name, e);
            return;
        }
    }

    // After all functions are defined, finalize the module and get all pointers.
    let all_fptrs_by_id = match jit.finalize_and_get_pointers() {
        Ok(ptrs) => ptrs,
        Err(e) => {
            eprintln!("JIT finalization error: {}", e);
            return;
        }
    };

    let mut fptrs = HashMap::new();
    for f in &module.funcs {
        if let Some(fptr) = all_fptrs_by_id.get(&f.id.0) {
            fptrs.insert(f.sig.name.clone(), *fptr);
        }
    }

    let entry_name = pick_entrypoint(&module).unwrap_or_else(|| {
        eprintln!("No functions to run.");
        std::process::exit(1);
    });

    let entry_fun = module
        .funcs
        .iter()
        .find(|f| f.sig.name == entry_name)
        .unwrap();

    #[cfg(debug_assertions)]
    eprintln!(
        "(Debug build) Selected function: {} (id={:?}) with {} params",
        entry_fun.sig.name,
        entry_fun.id,
        entry_fun.sig.params.len()
    );

    // 6) Build argv and run (ABI: (argv_ptr, argc) -> i64)
    let argv: Vec<i64> = vec![0; entry_fun.sig.params.len()];
    let fptr = *fptrs.get(&entry_name).unwrap();

    // let ret: i64 = unsafe { fptr(argv.as_ptr(), argv.len()) };
    let t0 = Instant::now();
    let ret: i64 = invoke_and_pump(fptr, &argv);
    let t1 = Instant::now();

    eprintln!(
        "(Debug build) Program returned: {} (0x{:x}) and took {:.6} seconds",
        ret,
        ret as u64,
        (t1 - t0).as_secs_f64()
    );
}

fn pick_entrypoint(module: &wir::Module) -> Option<String> {
    if module.funcs.iter().any(|f| f.sig.name == "__program__") {
        return Some("__program__".to_string());
    }
    if module.funcs.iter().any(|f| f.sig.name == "__toplevel__") {
        return Some("__toplevel__".to_string());
    }
    if module.funcs.iter().any(|f| f.sig.name == "main") {
        return Some("main".to_string());
    }
    module.funcs.get(0).map(|f| f.sig.name.clone())
}

fn compile_priority(name: &str) -> u8 {
    if name.starts_with("__get_")
        || name.starts_with("__set_")
        || name.starts_with("__method_")
        || name.starts_with("__static_")
        || name.starts_with("__ctor_")
        || name.starts_with("__dtor_")
        || name.starts_with("__class_new_")
    {
        0
    } else {
        1
    }
}
