// src/main.rs
mod wir;
mod front;
mod runtime;
// mod optimizer; // not used yet, but keep for future pipeline
mod jit;

use std::env;
use std::fs;

fn default_script() -> &'static str {
    // Keep it straight-line (no calls/branches) to match current JIT support.
    r#"
        // A tiny program with one function; JIT will run this by name.
        fn add2(a, b) {
            return a + b;
        }
    "#
}

fn main() {
    // -------- 1) Load source --------
    let args: Vec<String> = env::args().collect();
    let (src, from_file) = if args.len() > 1 {
        let path = &args[1];
        let content = fs::read_to_string(path).expect("failed to read source file");
        (content, true)
    } else {
        (default_script().to_string(), false)
    };

    if !from_file {
        println!("(no file provided) Using built-in demo script:\n{}\n", src);
    }

    // -------- 2) Parse to AST --------
    let mut parser = front::Parser::new(&src);
    let prog = match parser.program() {
        Ok(p) => p,
        Err(e) => {
            eprintln!(
                "Parse error: {} at byte range {:?}",
                e.msg, e.span
            );
            std::process::exit(1);
        }
    };

    // -------- 3) Lower to WIR --------
    let mut module = wir::Module::new();
    let mut lowerer = front::Lowerer::new(&mut module);
    let fids = match lowerer.lower_program(&prog) {
        Ok(ids) => ids,
        Err(e) => {
            eprintln!("Lowering error: {:?}", e);
            std::process::exit(1);
        }
    };

    // Pick a function to run:
    //   Preference order:
    //     - a function named "main" (if present, 0-arg straight-line!)
    //     - else a function named "add2"
    //     - else the first function
    let mut pick_idx: usize = 0;
    if let Some((i, _)) = prog
        .functions
        .iter()
        .enumerate()
        .find(|(_, f)| f.name == "main")
    {
        pick_idx = i;
    } else if let Some((i, _)) = prog
        .functions
        .iter()
        .enumerate()
        .find(|(_, f)| f.name == "add2")
    {
        pick_idx = i;
    }

    let fid = fids[pick_idx];
    let fun = &module.funcs[fid.0 as usize];

    println!(
        "Selected function: {} (id={:?}) with {} params",
        prog.functions[pick_idx].name,
        fid,
        fun.sig.params.len()
    );

    // -------- 4) JIT compile --------
    let mut jit = jit::JIT::default();
    let fptr = match jit.compile(fun) {
        Ok(fp) => fp,
        Err(e) => {
            eprintln!("JIT compile error: {}", e);
            std::process::exit(1);
        }
    };

    // -------- 5) Build argv and run --------
    // Our demo ABI: argv = *const i64, argc = usize, returns i64.
    // Provide a couple of demo args; unused ones are ignored.
    let argv: Vec<i64> = match prog.functions[pick_idx].name.as_str() {
        "add2" => vec![21, 21],     // expect 42
        "main" => vec![],           // only if your main is straight-line and has 0 params
        _ => {
            // Fill with zeros based on parsed parameter count
            let n = prog.functions[pick_idx].params.len();
            if n == 0 {
                vec![]
            } else if n == 1 {
                vec![10]
            } else if n == 2 {
                vec![3, 39]
            } else {
                vec![0; n]
            }
        }
    };

    let ret: i64 = unsafe { fptr(argv.as_ptr(), argv.len()) };

    println!(
        "Program returned: {} (0x{:x})",
        ret,
        ret as u64
    );
}
