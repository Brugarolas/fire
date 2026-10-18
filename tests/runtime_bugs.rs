use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_SCRIPT: AtomicUsize = AtomicUsize::new(0);
static RUN_LOCK: Mutex<()> = Mutex::new(());

fn run(source: &str) -> std::process::Output {
    run_with_module(source, None)
}

fn run_with_module(source: &str, provider: Option<&str>) -> std::process::Output {
    match provider {
        Some(provider) => run_with_modules(source, &[("provider.napalm", provider)]),
        None => run_with_modules(source, &[]),
    }
}

fn run_with_modules(source: &str, modules: &[(&str, &str)]) -> std::process::Output {
    let _guard = RUN_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let directory = std::env::temp_dir().join(format!(
        "napalm-runtime-bugs-{}-{}",
        std::process::id(),
        NEXT_SCRIPT.fetch_add(1, Ordering::Relaxed),
    ));
    std::fs::create_dir(&directory).expect("create test directory");
    let entry = directory.join("main.napalm");
    std::fs::write(&entry, source).expect("write test script");
    for (name, text) in modules {
        std::fs::write(directory.join(name), text).expect("write provider module");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_Napalm"))
        .arg(&entry)
        .output();
    std::fs::remove_file(&entry).expect("remove test script");
    for (name, _) in modules {
        std::fs::remove_file(directory.join(name)).expect("remove provider module");
    }
    std::fs::remove_dir(&directory).expect("remove test directory");
    output.expect("execute Napalm")
}

fn assert_output(source: &str, expected: &str) {
    let output = run(source);
    assert_process_output(output, expected);
}

fn assert_process_output(output: std::process::Output, expected: &str) {
    assert!(
        output.status.success(),
        "exit {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).replace("\r\n", "\n"),
        expected
    );
}

#[test]
fn float_arithmetic_and_js_division() {
    assert_output(
        r#"
        print(1 + 2.5);
        print(2.5 * 2);
        var a = 1.5; var b = 2;
        print(a + b);
        print(a * b - 0.25);
        print(7 / 2);
        print(6 / 2);
        print(-7 / 2);
        print(0.1 + 0.2 > 0.3);
        var t = 0;
        for (var i = 0; i < 10; i = i + 1) { t = t + i * 0.5; }
        print(t);
        print(3 - 1.5 * 2);
        "#,
        "3.5\n5\n3.5\n2.75\n3.5\n3\n-3.5\ntrue\n22.5\n0\n",
    );
}

#[test]
fn integer_overflow_division_by_zero_and_remainder() {
    assert_output(
        r#"
        print(2147483647 * 2147483647);
        print(1 / 0);
        print(-1 / 0);
        print(0 / 0);
        print(7 % 3);
        print(-7 % 3);
        print(7.5 % 2);
        print(5 % 0);
        print(5.9 >> 1);
        print(~2.5);
        "#,
        "4611686014132420609\ninf\n-inf\nNaN\n1\n-1\n1.5\nNaN\n2\n-3\n",
    );
}

#[test]
fn nan_and_mixed_comparisons() {
    assert_output(
        r#"
        var n = 0 / 0;
        print(n == n);
        print(n != n);
        fn eq(a, b) { return a == b; }
        print(eq(n, n));
        var x = 2.5;
        print(x == 2.5);
        print(x != 2.5);
        print(2.5 > 2);
        print(2 < 2.5);
        print(2.0 == 2);
        "#,
        "false\ntrue\nfalse\ntrue\nfalse\ntrue\ntrue\ntrue\n",
    );
}

#[test]
fn untyped_string_concatenation_and_inequality() {
    assert_output(
        r#"
        fn greet(name) { return "hi " + name; }
        var a = "foo"; var b = "bar";
        print(a + b);
        print(greet("bob"));
        print(a + 1);
        print(1 + 2);
        print(a != b);
        print(a != a);
        print(a == a);
        fn label(i) { return "item " + i; }
        print(label(4));
        print(label(2.5));
        print(label(true));
        var n = 7; print(n + a);
        "#,
        "\"foobar\"\n\"hi bob\"\n\"foo1\"\n3\ntrue\nfalse\ntrue\n\"item 4\"\n\"item 2.5\"\n\"item true\"\n\"7foo\"\n",
    );
}

#[test]
fn operands_with_side_effects_are_evaluated_once() {
    assert_output(
        r#"
        var c = [];
        fn bump(box) { box.push(1); return 8; }
        print(bump(c) >>> 1);
        print(c.length);
        print(bump(c) __ "x");
        print(c.length);
        class C { constructor() { this.v = 1; } fn inc() { this.v = this.v + 1; return this.v; } }
        fn mk() { print("mk"); return new C(); }
        print(mk().inc());
        fn arrs() { print("arrs"); return [3, 4]; }
        print(arrs().push(9));
        "#,
        "4\n1\n\"8x\"\n2\nmk\n2\narrs\n3\n",
    );
}

#[test]
fn size_is_an_assignable_property() {
    assert_output(
        r#"
        class Box { constructor() { this.size = 3; } fn grow() { this.size = this.size + 1; return this.size; } }
        var x = new Box();
        print(x.size);
        print(x.grow());
        var o = { size: 9 }; print(o.size);
        x.size += 10; print(x.size);
        class T { size: string; constructor() { this.size = "big"; } }
        print(new T().size);
        var m = new Map(); m.set("a", 1); print(m.size);
        var s = new Set(); s.add(1).add(2).add(1); print(s.size);
        "#,
        "3\n4\n9\n14\n\"big\"\n1\n2\n",
    );
}

#[test]
fn user_methods_named_like_string_and_array_builtins() {
    assert_output(
        r#"
        class Stack {
            constructor() { this.n = 0; }
            fn push(v) { this.n = this.n + 1; return this.n; }
            fn map(f) { return f(this.n); }
            fn replace(a, b) { return a + b; }
            fn slice(a, b, c) { return a + b + c; }
        }
        var s = new Stack();
        print(s.push(5));
        print(s.push(6));
        print(s.map(fn(x) { return x * 10; }));
        print(s.replace(1, 2));
        print(s.slice(1, 2, 3));
        print([1, 2].map(fn(x) { return x + 1; }));
        var arr = [1]; arr.push(2); print(arr);
        print("abc".replace("b", "x"));
        "#,
        "1\n2\n20\n3\n6\n[2, 3]\n[1, 2]\n\"axc\"\n",
    );
}

#[test]
fn user_methods_named_like_map_and_set_builtins() {
    assert_output(
        r#"
        class Bag {
            constructor() { this.items = []; }
            fn add(v) { this.items.push(v); return this.items.length; }
            fn get(i) { return this.items[i]; }
            fn set(i, v) { this.items[i] = v; return "set"; }
            fn delete(i) { return "deleted " + i; }
            fn keys(p) { return p + "!"; }
            fn clear() { this.items = []; return "cleared"; }
        }
        var b = new Bag();
        for (var i = 0; i < 20; i = i + 1) { b.add(i); }
        print(b.items);
        print(b.get(3));
        print(b.set(0, 99));
        print(b.items[0]);
        print(b.delete(4));
        print(b.keys("k"));
        print(b.clear());
        print(b.items.length);
        var m = new Map(); m.set("a", 1).set("b", 2); print(m.get("b")); print(m.has("a"));
        var s = new Set(); s.add(1); print(s.has(1));
        var o = { a: 1, b: 2 }; print(o.keys()); print(o.values());
        enum Empty {}
        print(Empty.keys());
        "#,
        "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]\n3\n\"set\"\n99\n\"deleted 4\"\n\"k!\"\n\"cleared\"\n0\n2\ntrue\ntrue\n[\"a\", \"b\"]\n[1, 2]\n[]\n",
    );
}

#[test]
fn generic_method_returning_new_instance() {
    assert_output(
        r#"
        class Box<T> {
            value: T;
            constructor(v: T) { this.value = v; }
            fn map<U>(f: (x: T) => U): Box<U> { return new Box<U>(f(this.value)); }
        }
        var b = new Box<number>(20);
        print(b.map(fn(x) { return x + 1; }).value);
        print(b.map(fn(x: number): string { return "v" + x; }).value);
        class Plain { constructor(v) { this.value = v; } fn map(f) { return new Plain(f(this.value)); } }
        print(new Plain(5).map(fn(x) { return x * 3; }).value);
        "#,
        "21\n\"v20\"\n15\n",
    );
}

#[test]
fn length_on_untyped_values() {
    assert_output(
        r#"
        fn longest(a, b) {
            if (a.length >= b.length) { return a; }
            return b;
        }
        print(longest([1, 2], [3, 4, 5]));
        fn len(a) { return a.length; }
        print(len([1, 2, 3]));
        print(len("abcd"));
        var x = [1, 2, 3]; print(x.length);
        class L { constructor() { this.length = 7; this.w = 3; } }
        var l = new L(); print(l.length); print(l.w);
        l.length = 9; print(l.length);
        var o = { length: 5 }; print(o.length);
        var a = [1, 2, 3]; a.length = 1; print(a); print(a.length);
        "#,
        "[3, 4, 5]\n3\n4\n3\n7\n3\n9\n5\n[1]\n1\n",
    );
}

#[test]
fn in_operator_evaluates_variable_keys() {
    assert_output(
        r#"
        var t = { foo: 10 };
        var k = "foo"; var z = "zzz";
        print(k in t);
        print(z in t);
        print("foo" in t);
        class C { constructor() { this.a = 1; } }
        var c = new C(); var ka = "a";
        print(ka in c);
        print(5 in t);
        var log = [];
        var p = new Proxy(t, { "has": fn (tt, key) { log.push("has:" + key); return key in tt; } });
        print("foo" in p);
        print(log);
        "#,
        "true\nfalse\ntrue\ntrue\nfalse\ntrue\n[\"has:foo\"]\n",
    );
}

#[test]
fn large_integer_literals_and_bitwise_or() {
    assert_output(
        r#"
        print(2147483648);
        print(-2147483649);
        print(4294967295);
        print(9007199254740991);
        print(9223372036854775808 > 9007199254740991);
        print(1 | 2 | 4);
        fn bits(a, b) { return a | b; }
        print(bits(5.9, 2));
        print(bits(-4, 1));
        print(1 + 2 | 4 << 1);
        print((1 | 2) == 3);
        print(true && (1 | 2) == 3);
        var f = |x| { return x | 2; };
        print(f(4));
        var empty = | | { return 8 | 1; };
        print(empty());
        "#,
        "2147483648\n-2147483649\n4294967295\n9007199254740991\ntrue\n7\n7\n-3\n11\ntrue\ntrue\n6\n9\n",
    );
    // Even literals beyond f64's finite range must not panic in the lexer.
    assert_output(&format!("print({});", "9".repeat(400)), "inf\n");
}

#[test]
fn module_variables_are_live_in_functions_and_closures() {
    assert_output(
        r#"
        var count = 1;
        fn read() { return count; }
        fn bump() { count += 1; return count; }
        var closure = fn() { count += 10; return count; };
        print(read()); print(bump()); print(count);
        count = 5; print(read()); print(closure()); print(read());
        fn shadow(count) { count += 100; return count; }
        fn local() { var count = 50; count += 1; return count; }
        print(shadow(2)); print(local()); print(count);
        fn early() { return later; }
        var later = 42; print(early());
        var { x, ...rest } = { x: 7, y: 9 };
        fn destructured() { return x + rest.y; }
        print(destructured());
        class Counter { fn tick() { count += 1; return count; } }
        print(new Counter().tick()); print(count);
        fn nested() { return fn() { return count; }; }
        var reader = nested(); count = 30; print(reader());
        var count = 40; print(count); print(reader());
        "#,
        "1\n2\n2\n5\n15\n15\n102\n51\n15\n42\n16\n16\n16\n30\n40\n40\n",
    );
}

#[test]
fn module_variables_preserve_exports_privacy_and_shadowing() {
    let output = run_with_module(
        r#"
        import { value, read, bump, shadow, reader } from "./provider.napalm";
        var hidden = 100;
        print(read()); print(bump()); print(value); print(read()); print(hidden);
        print(shadow()); print(value); print(reader());
        "#,
        Some(r#"
        var hidden = 2;
        export var value = 10;
        export fn read() { return hidden + value; }
        export fn bump() { hidden += 1; value += 5; return read(); }
        export fn shadow() { var value = 99; value += 1; return value; }
        export var reader = fn() { return value; };
        "#),
    );
    assert_process_output(output, "12\n18\n15\n18\n100\n100\n15\n15\n");
}

#[test]
fn module_variables_work_with_async_loops_and_local_captures() {
    assert_output(
        r#"
        var count = 0;
        async fn increment() { count += 1; return count; }
        for (var i = 0; i < 3; i += 1) { print(await increment()); }
        print(count);
        fn make() { var count = 10; return fn() { count += 1; return count; }; }
        var local = make(); print(local()); print(local()); print(count);
        var callbacks = [fn() { return count; }];
        count = 20; print(callbacks[0]());
        "#,
        "1\n2\n3\n3\n11\n12\n3\n20\n",
    );
}

#[test]
fn array_searches_dispatch_by_receiver_and_compare_values() {
    assert_output(
        r#"
        fn has(a, v) { return a.includes(v); }
        fn index(a, v) { return a.indexOf(v); }
        var a = [1, 2.5, 1, "hello", true, null];
        print(has(a, 2.5)); print(index(a, 1.0));
        print(a.includes(8)); print(a.indexOf(8));
        print(a.indexOf(1, 1)); print(a.indexOf(1, -4));
        print(a.includes(1, -3)); print(a.includes(1, -100));
        print(a.indexOf(1, 100)); print(a.indexOf(1, 1.9));
        print(a.includes("he" + "llo"));
        print([true].includes(1)); print([null].indexOf(0));
        var n = 0 / 0; print([n].includes(n)); print([n].indexOf(n));
        print([0].includes(-0.0)); print([0.0].indexOf(0));
        var obj = {}; print([obj].includes(obj)); print([obj].indexOf({}));
        print([].includes(1)); print([].indexOf(1));
        print(a.indexOf(1, 1 / 0)); print(a.indexOf(1, -1 / 0));
        print(a.indexOf(1, n));
        print("hello".includes("ell")); print("hello".indexOf("l", 3));
        print("hello".includes("h", 1));
        class Custom {
            fn includes(x) { return x + 10; }
            fn indexOf(x) { return x + 20; }
        }
        print(new Custom().includes(2)); print(new Custom().indexOf(3));
        "#,
        "true\n0\nfalse\n-1\n2\n2\nfalse\ntrue\n-1\n2\ntrue\nfalse\n-1\ntrue\n-1\ntrue\n0\ntrue\n-1\nfalse\n-1\n-1\n0\n0\ntrue\n3\nfalse\n12\n23\n",
    );
}

#[test]
fn missing_array_methods_raise_catchable_errors() {
    assert_output(
        r#"
        fn missing(a) { a.doesNotExist(); }
        try { missing([1, 2]); } catch (e) { print(e); }
        try { [].push(1, 2); } catch (e) { print(e); }
        var key = "missing";
        try { [1][key](); } catch (e) { print(e); }
        try { [1]["missing"](); } catch (e) { print(e); }
        print("still running");
        "#,
        "\"TypeError: method 'doesNotExist' is not callable\"\n\"TypeError: method 'push' is not callable\"\n\"TypeError: indexed value is not callable\"\n\"TypeError: method 'missing' is not callable\"\nstill running\n",
    );
    let output = run("[1, 2].doesNotExist();");
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("Uncaught exception:"), "{stderr}");
    assert!(!stderr.contains("panicked"), "{stderr}");
}

#[test]
fn closures_capturing_loop_variables_keep_looping() {
    assert_output(
        r#"
        fn inner() {
            var hs = [];
            for (var q = 0; q < 3; q = q + 1) { hs.push(fn() { return q; }); }
            var n = 0;
            var w = 0;
            while (w < 3) { var c = fn() { return w; }; n = n + c(); w = w + 1; }
            return hs.length * 100 + hs[0]() * 10 + n;
        }
        print(inner());
        fn branch(flag) {
            var x = 1;
            if (flag) { var read = fn() { return x; }; }
            x = x + 1;
            return x;
        }
        print(branch(true));
        print(branch(false));
        var gs = [];
        for (var m = 0; m < 3; m = m + 1) { gs.push(fn() { return m; }); }
        print(gs.length);
        print(m);
        print(gs[0]());
        "#,
        "333\n2\n2\n3\n3\n3\n",
    );
}

#[test]
fn bitwise_operators_use_int32_semantics() {
    assert_output(
        r#"
        print(4294967295 | 0);
        print(2147483648 | 0);
        print(1 << 31);
        print(-1 >>> 0);
        print(8 >> 33);
        print(8 >>> 33);
        print(5.5 << 1);
        fn or0(a) { return a | 0; }
        fn shr(a, b) { return a >> b; }
        fn shru(a, b) { return a >>> b; }
        print(or0(4294967296));
        print(or0(-2147483649));
        print(or0(100000000000000000000.0));
        print(or0(0 / 0));
        print(shr(8, 33));
        print(shru(-8.5, 1));
        "#,
        "-1\n-2147483648\n-2147483648\n4294967295\n4\n4\n10\n0\n2147483647\n1661992960\n0\n4\n2147483644\n",
    );
}

#[test]
fn top_level_redeclaration_after_for_var_is_visible() {
    assert_output(
        r#"
        class C { var z = 7; fn getZ() { return this.z; } }
        for (var i = 0; i < 2; i += 1) { }
        var i = new C();
        print(i.z);
        print(i.getZ());
        "#,
        "7\n7\n",
    );
}

#[test]
fn namespace_member_calls_do_not_receive_this() {
    let output = run_with_module(
        r#"
        import * as lib from "./provider.napalm";
        print(lib.norm({ x: 1, y: 2 }));
        print(lib.two(10, 3));
        print(lib.value);
        try { lib.value(); } catch (e) { print(e); }
        "#,
        Some(
            r#"
            export fn norm(p) { return p.x * p.x + p.y * p.y; }
            export fn two(a, b) { return a - b; }
            export var value = 7;
            "#,
        ),
    );
    assert_process_output(output, "5\n7\n7\n\"TypeError: lib.value is not a function\"\n");
}

const REEXPORT_BASE: &str = r#"
export var counter = 1;
export fn inc() { counter = counter + 1; }
export fn add(a, b) { return a + b; }
export class Sq { constructor(s) { this.s = s; } fn area() { return this.s * this.s; } }
export enum Color { Red = 1, Green = 2 }
"#;

#[test]
fn reexports_share_live_bindings() {
    let output = run_with_modules(
        r#"
        import { plus, count, local } from "./mid.napalm";
        import { inc, Sq } from "./hub.napalm";
        import * as h from "./hub.napalm";
        print(plus(1, 2));
        print(count);
        inc();
        print(count);
        print(h.counter);
        h.inc();
        print(h.counter);
        print(h.add(2, 3));
        print(new Sq(3).area());
        print(new h.Sq(4).area());
        print(h.Color.Green);
        print(local());
        "#,
        &[
            ("base.napalm", REEXPORT_BASE),
            ("hub.napalm", "export * from \"./base.napalm\";\n"),
            (
                "mid.napalm",
                "export { add as plus, counter as count } from \"./hub.napalm\";\nexport fn local() { return 9; }\n",
            ),
        ],
    );
    assert_process_output(output, "3\n1\n2\n2\n3\n5\n9\n16\n2\n9\n");
}

fn assert_build_error(output: std::process::Output, expected: &[&str]) {
    assert!(
        !output.status.success(),
        "expected failure\nstdout:\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    for message in expected {
        assert!(all.contains(message), "missing `{message}` in:\n{all}");
    }
}

#[test]
fn reexporting_a_missing_member_is_an_import_error() {
    let output = run_with_modules(
        "import { nope } from \"./mid.napalm\";\nprint(nope);\n",
        &[
            ("base.napalm", REEXPORT_BASE),
            ("mid.napalm", "export { nope } from \"./base.napalm\";\n"),
        ],
    );
    assert_build_error(output, &["cannot re-export `nope`"]);
}

#[test]
fn out_of_scope_variables_report_a_located_error() {
    assert_build_error(
        run("fn f(c) {\n  if (c) { var z = 1; }\n  return z;\n}\nprint(f(true));\n"),
        &[
            "`z` is not defined in this scope",
            "declared at line 2 inside a block",
            "main.napalm:3:10",
        ],
    );
    assert_build_error(run("print(nothere);\n"), &["`nothere` is not defined in this scope"]);
}
#[test]
fn missing_arguments_are_null() {
    assert_output(
        r#"
fn f(a, b, c) { return [a, b == null, c == null]; }
print(f(1));
class P { constructor(x, y) { this.x = x; this.y = y; } }
let p = new P(3);
print([p.x, p.y == null]);
"#,
        "[1, true, true]\n[3, true]\n",
    );
}

#[test]
fn else_if_chains_of_any_length() {
    assert_output(
        r#"
fn grade(n) {
    if (n > 90) { return "A"; }
    else if (n > 80) { return "B"; }
    else if (n > 70) { return "C"; }
    else if (n > 60) { return "D"; }
    else { return "F"; }
}
print([grade(95), grade(85), grade(75), grade(65), grade(5)]);
"#,
        "[\"A\", \"B\", \"C\", \"D\", \"F\"]\n",
    );
}

#[test]
fn null_equality_and_logical_operator_values() {
    assert_output(
        r#"
print([0 == null, null == 0, null == null, 0 != null, "" == null]);
print([0 || 5, 3 || 5, null || "x", 0 && 5, 3 && 5, "" || "fallback"]);
"#,
        "[false, false, true, true, false]\n[5, 3, \"x\", 0, 5, \"fallback\"]\n",
    );
}

#[test]
fn conditions_use_js_truthiness() {
    assert_output(
        r#"
fn t(v) { if (v) { return 1; } return 0; }
print([t(0), t(1), t(2), t(-1), t(""), t("a"), t(null), t(false), t(true), t(0.0), t(0.5), t([])]);
print([!0, !2, !"", !"a", !null]);
let n = 3;
let c = 0;
while (n) { n = n - 1; c = c + 1; }
print(c);
"#,
        "[0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1]\n[true, false, true, false, true]\n3\n",
    );
}

#[test]
fn values_defined_in_later_numbered_blocks_reach_their_uses() {
    // The nested `if` with an early return makes the lowerer number the block
    // defining `i = 4` after the join block that consumes it.
    assert_output(
        r#"
fn a(f, g) { let i = 0; if (f) { i = 7; } else { if (g) { return 5; } i = 4; } return i; }
fn b(f, g) { let i = 0; if (f) { i = 7; } else { if (g) { return 5; } i = 4; } return i; }
print([a(false, false), b(false, false), b(true, false), b(false, true)]);
"#,
        "[4, 4, 7, 5]\n",
    );
}