// src/runtime.rs
#![allow(non_snake_case)]

#[unsafe(no_mangle)]
pub extern "C" fn wir_print_i64(x: i64) -> i64 {
    println!("{}", x);
    x // return the printed value; handy if used in expressions
}
