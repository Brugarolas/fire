use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_SCRIPT: AtomicUsize = AtomicUsize::new(0);
static RUN_LOCK: Mutex<()> = Mutex::new(());

fn run(source: &str, provider: Option<&str>) -> std::process::Output {
    let _guard = RUN_LOCK.lock().expect("serialize JIT processes");
    let directory = std::env::temp_dir().join(format!(
        "napalm-types-{}-{}",
        std::process::id(),
        NEXT_SCRIPT.fetch_add(1, Ordering::Relaxed),
    ));
    std::fs::create_dir(&directory).expect("create type test directory");
    let entry = directory.join("main.napalm");
    let module = directory.join("geo.napalm");
    std::fs::write(&entry, source).expect("write type test");
    if let Some(provider) = provider {
        std::fs::write(&module, provider).expect("write type provider");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_Napalm"))
        .arg(&entry)
        .output();
    std::fs::remove_file(&entry).expect("remove type test");
    if provider.is_some() {
        std::fs::remove_file(&module).expect("remove type provider");
    }
    std::fs::remove_dir(&directory).expect("remove empty type test directory");
    output.expect("execute Napalm")
}

fn assert_output(source: &str, provider: Option<&str>, expected: &str) {
    let output = run(source, provider);
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

fn assert_failure(source: &str, expected: &[&str]) {
    let output = run(source, None);
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
fn type_example() {
    assert_output(
        include_str!("../scripts/types.napalm"),
        None,
        "15\n\"a\"\n\"b\"\n[4, \"napalm!\", \"plain\"]\n\
         \"TypeError: variable `count` expects number\"\n\
         \"TypeError: parameter `shape` of `describe` expects Shape\"\n12\n",
    );
}

#[test]
fn generic_functions_classes_and_constraints() {
    assert_output(
        r##"
        fn identity<T>(value: T): T { return value; }
        fn firstOr<T>(items: T[], fallback: T): T {
            if (items.length == 0) { return fallback; }
            return items[0];
        }
        fn longest<T extends { length: number }>(a: T, b: T): T {
            if (a.length >= b.length) { return a; }
            return b;
        }
        class Box<T> {
            value: T;
            constructor(value: T) { this.value = value; }
            fn transform<U>(f: (value: T) => U): Box<U> {
                var mapped: U = f(this.value);
                return new Box<U>(mapped);
            }
        }
        print(identity<number>(4));
        print(identity("text"));
        print(firstOr([], 9));
        print(firstOr(["x", "y"], "z"));
        print(longest("napalm", "jit"));
        print(longest("a", "bcd"));
        var boxed = new Box<number>(20).transform(fn(v: number): string { return "#" + v; });
        print(boxed.value);
    "##,
        None,
        "4\n\"text\"\n9\n\"x\"\n\"napalm\"\n\"bcd\"\n\"#20\"\n",
    );
}

#[test]
fn structural_interfaces_and_implements() {
    assert_output(
        r#"
        interface Named { name: string; }
        interface Animal extends Named {
            legs: number;
            speak(): string;
        }
        class Dog implements Animal {
            name: string;
            legs: number = 4;
            constructor(name: string) { this.name = name; }
            fn speak(): string { return this.name + " says woof"; }
        }
        fn intro(a: Animal): string { return a.speak() + " on " + a.legs + " legs"; }
        fn greet(n: Named): string { return "hi " + n.name; }
        var bird = { name: "tweety", legs: 2, speak: fn() { return "tweet"; } };
        print(intro(new Dog("rex")));
        print(intro(bird));
        print(greet(new Dog("fido")));
        fn untyped() { return { name: "ghost" }; }
        print(greet(untyped()));
        try { print(intro(untyped())); } catch (e) { print(e); }
    "#,
        None,
        "\"rex says woof on 4 legs\"\n\"tweet on 2 legs\"\n\"hi fido\"\n\"hi ghost\"\n\
         \"TypeError: parameter `a` of `intro` expects Animal\"\n",
    );
}

#[test]
fn aliases_unions_optional_parameters_and_narrowing() {
    assert_output(
        r#"
        type Id = number | string;
        type Maybe<T> = T | null;
        type Point = { x: number; y: number; label?: string };
        fn show(id: Id): string { return "id:" + id; }
        fn orZero(v: Maybe<number>): number {
            if (v == null) { return 0; }
            return v;
        }
        fn norm(p: Point): number { return p.x * p.x + p.y * p.y; }
        fn tag(name: string, suffix?: string, count?: number): string {
            var out = name;
            if (suffix != null) { out = out + suffix; }
            if (count == null) { return out; }
            return out + count;
        }
        fn size(s: string | null): number { return s != null && s.length > 0 ? s.length : -1; }
        print(show(7));
        print(show("seven"));
        print([orZero(null), orZero(5), norm({ x: 3, y: 4 })]);
        print([tag("a"), tag("a", "b"), tag("a", "b", 3)]);
        print([size("abc"), size(null)]);
    "#,
        None,
        "\"id:7\"\n\"id:seven\"\n[0, 5, 25]\n[\"a\", \"ab\", \"ab3\"]\n[3, -1]\n",
    );
}

#[test]
fn typed_string_array_and_map_operations() {
    assert_output(
        r#"
        fn join(words: string[], sep: string): string {
            var out = "";
            for (var i = 0; i < words.length; i = i + 1) {
                if (i > 0) { out = out + sep; }
                out = out + words[i];
            }
            return out;
        }
        fn sum(xs: number[]): number {
            var total = 0;
            for (var i = 0; i < xs.length; i = i + 1) { total = total + xs[i]; }
            return total;
        }
        fn same(a: string, b: string): boolean { return a == b; }
        var scores: Map<string, number> = new Map();
        scores.set("a", 1);
        print(join(["typed", "napalm", "code"], "-"));
        print(sum([1, 2, 39]));
        print([same("x", "x"), same("x", "y")]);
        print("napalm".length + join(["a"], ""));
        print(scores.get("a"));
        var flags: boolean[] = [true, false];
        flags[1] = true;
        print(flags);
    "#,
        None,
        "\"typed-napalm-code\"\n42\n[true, false]\n\"6a\"\n1\n[true, true]\n",
    );
}

#[test]
fn untyped_code_keeps_working() {
    assert_output(
        r#"
        fn add(a, b) { return a + b; }
        var items = [1, "two", null];
        items.push(add(1, 2));
        print(items);
        print(add(2, 3));
        print("a" + "b");
        var m = new Map();
        m.set(1, "one");
        print(m.get(1));
        var x = 1;
        x = "now a string";
        print(x);
    "#,
        None,
        "[1, \"two\", null, 3]\n5\n\"ab\"\n\"one\"\n\"now a string\"\n",
    );
}

#[test]
fn boundary_guards_are_catchable_exceptions() {
    assert_output(
        r#"
        fn loose(v) { return v; }
        fn double(n: number): number { return n * 2; }
        async fn later(s: string): Promise<string> { return s + "!"; }
        fn run() {
            try {
                double(loose("x"));
            } finally {
                print("finally ran");
            }
        }
        try { run(); } catch (e) { print(e); }
        try { var s: string = loose(3); print(s); } catch (e) { print(e); }
        try { print(loose(4) as boolean); } catch (e) { print(e); }
        print(double(loose(21)));
        print(await later(loose("ok")));
        try { await later(loose(1)); } catch (e) { print(e); }
    "#,
        None,
        "finally ran\n\"TypeError: parameter `n` of `double` expects number\"\n\
         \"TypeError: variable `s` expects string\"\n\"TypeError: cannot cast value to boolean\"\n\
         42\n\"ok!\"\n\"TypeError: parameter `s` of `later` expects string\"\n",
    );
}

#[test]
fn exported_types_cross_modules() {
    assert_output(
        r#"
        import { Point, Label, norm, name } from "./geo.napalm";
        var p: Point = { x: 3, y: 4 };
        print(norm(p));
        var l: Label = name("origin");
        print(l);
        fn loose(v) { return v; }
        try { norm(loose({ x: 1 })); } catch (e) { print(e); }
        try { name(loose(5)); } catch (e) { print(e); }
    "#,
        Some(
            r#"
            export interface Point { x: number; y: number; }
            export type Label = string;
            export fn norm(p: Point): number { return p.x * p.x + p.y * p.y; }
            export fn name(l: Label): Label { return "<" + l + ">"; }
        "#,
        ),
        "25\n\"<origin>\"\n\"TypeError: parameter `p` of `norm` expects Point\"\n\
         \"TypeError: parameter `l` of `name` expects string\"\n",
    );
}

#[test]
fn static_errors_are_reported_before_execution() {
    assert_failure(
        r#"
        print("must not run");
        interface Shape { area(): number; }
        fn f(a: number): string { return a; }
        var x: number = "s";
        f(1, 2);
        fn g(s: Shape) {}
        g({ name: "no area" });
    "#,
        &[
            "return value: type `number` is not assignable to type `string`",
            "variable `x`: type `string` is not assignable to type `number`",
            "`f` expects at most 1 argument(s), got 2",
            "property `area` is missing",
        ],
    );
    assert_failure("var y: Missing = 1;", &["unknown type `Missing`"]);
    let output = run("print(\"must not run\");\nvar n: number = \"s\";", None);
    assert!(!String::from_utf8_lossy(&output.stdout).contains("must not run"));
}

#[test]
fn uncaught_guard_failures_terminate_the_program() {
    assert_failure(
        r#"
        fn loose(v) { return v; }
        var s = loose(1) as string;
        print("unreachable");
    "#,
        &["TypeError: cannot cast value to string"],
    );
}
