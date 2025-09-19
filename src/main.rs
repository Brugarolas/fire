// src/main.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

mod value;
mod wir;
mod front;
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

    // ------------------------------
    // A) MODO MULTI-MÓDULO (grafo)
    // ------------------------------
    let mut module = if try_multi {
        #[cfg(debug_assertions)]
        eprintln!("(Debug build) Building whole-program (modules graph) from {} ...", &args[1]);
        let b0 = Instant::now();

        let mut m = match modules::build_whole_program_from_entry(&args[1]) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("Whole-program build failed: {e:?}");
                eprintln!("Falling back to single-file mode with the file contents...");

                #[cfg(debug_assertions)]
                {
                    eprintln!("[fallback] single-file build: LinkInfo de imports probablemente vacío");
                }

                // Fallback: leemos el archivo y seguimos flujo single-file
                let src = std::fs::read_to_string(&args[1]).unwrap_or_else(|_| default_script().to_string());
                build_single_file_module(&src)
            }
        };

        let b1 = Instant::now();
        #[cfg(debug_assertions)]
        eprintln!("(Debug build) Whole-program build took {:.6} seconds", (b1 - b0).as_secs_f64());
        m
    } else {
        // ------------------------------
        // B) MODO SINGLE-FILE (tu flujo)
        // ------------------------------
        let src = if args.len() > 1 {
            match std::fs::read_to_string(&args[1]) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Failed to read {}: {e}. Falling back to built-in demo.", args[1]);
                    default_script().to_string()
                }
            }
        } else {
            eprintln!("(No file provided) Using built-in demo script:\n\n{}", default_script());
            default_script().to_string()
        };
        build_single_file_module(&src)
    };

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

fn build_single_file_module(src: &str) -> wir::Module {
    #[cfg(debug_assertions)]
    eprintln!("(Debug build) Parsing and lowering the code...");
    let p0 = Instant::now();

    // Parse
    let mut p = front::Parser::new(src);
    let prog = match p.program() {
        Ok(pr) => pr,
        Err(e) => {
            eprintln!("Parse error: {} at byte range {:?}", e.msg, e.span);
            std::process::exit(1);
        }
    };

    // Lower to WIR
    let mut module = wir::Module::new();
    let mut lowerer = front::Lowerer::new(&mut module);
    if let Err(e) = lowerer.lower_program(&prog) {
        eprintln!("Lowering error: {:?}", e);
        std::process::exit(1);
    }

    #[cfg(debug_assertions)]
    {
        let p1 = Instant::now();
        eprintln!("(Debug build) Parsing and lowering the code took {:.6} seconds", (p1 - p0).as_secs_f64());
        eprintln!("(Debug build) Optimizing the code...");
    }
    let o0 = Instant::now();

    // Optimize WIR (pipeline single-file)
    let optimize = optimization_passes();
    optimize.optimize_module(&mut module);

    #[cfg(debug_assertions)]
    {
        let o1 = Instant::now();
        eprintln!("(Debug build) Optimizing the code took {:.6} seconds", (o1 - o0).as_secs_f64());
    }

    module
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
