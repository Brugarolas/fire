// src/main.rs
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

use crate::opt::Optimize;
use crate::opt::optimization::optimization_passes;
use mimalloc::MiMalloc;
use ahash::AHashMap as HashMap;
use std::time::Instant;
use crate::native_timers::invoke_and_pump;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

//pub use crate::opt::optimization::early_pipeline;

fn default_script() -> &'static str {
    r#"
        fn fibonacci(n) {
            if (n <= 1) {
                return n;
            }
            return fibonacci(n - 1) + fibonacci(n - 2);
        }
        print(fibonacci(45));
    "#
}

fn main() {
    // 1) Load source
    let args: Vec<String> = std::env::args().collect();
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

    // 2) Parse
    let mut p = front::Parser::new(&src);
    let prog = match p.program() {
        Ok(pr) => pr,
        Err(e) => { eprintln!("Parse error: {} at byte range {:?}", e.msg, e.span); return; }
    };

    // 3) Lower to WIR
    let mut module = wir::Module::new();
    let mut lowerer = front::Lowerer::new(&mut module);
    if let Err(e) = lowerer.lower_program(&prog) {
        eprintln!("Lowering error: {:?}", e);
        return;
    }

    // 3.5) Optimize WIR
    let optimize = optimization_passes();
    optimize.optimize_module(&mut module); // TODO Too Slow?

    // 4.1) Init GC and bind to this thread
    #[cfg(feature = "gc")] {
        let _gc = gc::NapalmGc::new();
        _gc.bind_current_thread();
    }

    // 4.2) JIT compile ALL functions
    let mut jit = jit::JIT::default();
    let mut fptrs = HashMap::new();
    for f in &module.funcs {
        match jit.compile(f) {
            Ok(fp) => {
                fptrs.insert(f.sig.name.clone(), fp);
            }
            Err(e) => {
                eprintln!("JIT compile error in {}: {}", f.sig.name, e);
                return;
            }
        }
    }

    // 5) Pick entrypoint: prefer __toplevel__, else main, else first parsed fn
    let entry_name = if module.funcs.iter().any(|f| f.sig.name == "__toplevel__") {
        "__toplevel__".to_string()
    } else if module.funcs.iter().any(|f| f.sig.name == "main") {
        "main".to_string()
    } else if !prog.functions.is_empty() {
        prog.functions[0].name.clone()
    } else {
        eprintln!("No functions to run.");
        return;
    };

    let entry_fun = module.funcs.iter().find(|f| f.sig.name == entry_name).unwrap();
    #[cfg(debug_assertions)] {
        eprintln!("(Debug build) Selected function: {} (id={:?}) with {} params", entry_fun.sig.name, entry_fun.id, entry_fun.sig.params.len());
    }
    let t0 = Instant::now(); // Start timing just before running the entry function

    // 6) Build argv and run (ABI: (argv_ptr, argc) -> i64)
    let argv: Vec<i64> = vec![0; entry_fun.sig.params.len()];
    let fptr = *fptrs.get(&entry_name).unwrap();

    // let ret: i64 = unsafe { fptr(argv.as_ptr(), argv.len()) };
    let ret: i64 = invoke_and_pump(fptr, &argv);

    let t1 = Instant::now(); // End timing just after the function returns
    let duration = t1.duration_since(t0);
    let secs = duration.as_secs_f64();
    eprintln!("(Debug build) Program returned: {} (0x{:x}) and took {:.6} seconds", ret, ret as u64, secs);
}
