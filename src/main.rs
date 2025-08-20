// src/main.rs
mod wir;
mod front;
// mod optimizer; // not used yet, but keep for future pipeline
mod jit;

fn default_script() -> &'static str {
    r#"
        fn add2(a, b) {
            return a + b;
        }

        // top-level runs without mandatory main
        print(add2(2, 3)); // expect 5
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
        println!("(no file provided) Using built-in demo script:\n\n{}", default_script());
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

    // 4) JIT compile ALL functions
    let mut jit = jit::JIT::default();
    let mut fptrs = std::collections::HashMap::new();
    for f in &module.funcs {
        match jit.compile(f) {
            Ok(fp) => { fptrs.insert(f.sig.name.clone(), fp); }
            Err(e) => { eprintln!("JIT compile error in {}: {}", f.sig.name, e); return; }
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
    println!(
        "Selected function: {} (id={:?}) with {} params",
        entry_fun.sig.name, entry_fun.id, entry_fun.sig.params.len()
    );

    // 6) Build argv and run (ABI: (argv_ptr, argc) -> i64)
    let argv: Vec<i64> = vec![0; entry_fun.sig.params.len()];
    let fptr = *fptrs.get(&entry_name).unwrap();
    let ret: i64 = unsafe { fptr(argv.as_ptr(), argv.len()) };
    println!("Program returned: {} (0x{:x})", ret, ret as u64);
}
