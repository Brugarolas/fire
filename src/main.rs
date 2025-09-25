// src/main.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

mod value;
mod wir;
mod front;
mod lowerer;
mod hoister;
mod opt;
mod gc;
mod runtime;
mod jit;
mod event_loop;
mod native_timers;
mod native_promises;
mod http;
mod modules;
mod helpers;

use crate::opt::Optimize;
use crate::opt::optimization::optimization_passes;
use mimalloc::MiMalloc;
use ahash::AHashMap as HashMap;
use std::time::Instant;
use std::path::Path;
use crate::native_timers::invoke_and_pump;

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

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // ¿Tenemos una ruta de entrada real? ⇒ modo multi-módulo
    let try_multi = args.len() > 1 && Path::new(&args[1]).exists();

    // 4.1) Init GC y bind
    #[cfg(feature = "gc")] {
        let _gc = gc::NapalmGc::new();
        _gc.bind_current_thread();
    }

    #[cfg(debug_assertions)]
    eprintln!("(Debug build) Building whole-program (modules graph) from {} ...", &args[1]);
    let b0 = Instant::now();

    let m = modules::build_simple_program_from_entry(&args[1]);
    let module = match m {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Error building whole program: {}", e);
            return;
        }
    };

    let b1 = Instant::now();
    #[cfg(debug_assertions)]
    eprintln!("(Debug build) Whole-program build took {:.6} seconds", (b1 - b0).as_secs_f64());

    // 4.2) JIT compile ALL functions
    let mut jit = jit::JIT::default();
    let mut fptrs = HashMap::new();
    for f in &module.funcs {
        match jit.compile(f) {
            Ok(fp) => { fptrs.insert(f.sig.name.clone(), fp); }
            Err(e) => {
                eprintln!("JIT compile error in {}: {}", f.sig.name, e);
                return;
            }
        }
    }

    // 5) Pick entrypoint: __toplevel__ > main > first function
    let entry_name = pick_entrypoint(&module).unwrap_or_else(|| {
        eprintln!("No functions to run.");
        std::process::exit(1);
    });

    let entry_fun = module.funcs.iter().find(|f| f.sig.name == entry_name).unwrap();
    #[cfg(debug_assertions)]
    eprintln!(
        "(Debug build) Selected function: {} (id={:?}) with {} params",
        entry_fun.sig.name, entry_fun.id, entry_fun.sig.params.len()
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
        ret, ret as u64, (t1 - t0).as_secs_f64()
    );
}

fn pick_entrypoint(module: &wir::Module) -> Option<String> {
    if module.funcs.iter().any(|f| f.sig.name == "__toplevel__") {
        return Some("__toplevel__".to_string());
    }
    if module.funcs.iter().any(|f| f.sig.name == "main") {
        return Some("main".to_string());
    }
    module.funcs.get(0).map(|f| f.sig.name.clone())
}
