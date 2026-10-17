use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_SCRIPT: AtomicUsize = AtomicUsize::new(0);
static RUN_LOCK: Mutex<()> = Mutex::new(());

fn run(source: &str, provider: Option<&str>) -> std::process::Output {
    let _guard = RUN_LOCK.lock().expect("serialize JIT processes");
    let directory = std::env::temp_dir().join(format!(
        "napalm-enums-{}-{}",
        std::process::id(),
        NEXT_SCRIPT.fetch_add(1, Ordering::Relaxed),
    ));
    std::fs::create_dir(&directory).expect("create enum test directory");
    let entry = directory.join("main.napalm");
    let module = directory.join("colors.napalm");
    std::fs::write(&entry, source).expect("write enum test");
    if let Some(provider) = provider {
        std::fs::write(&module, provider).expect("write enum provider");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_Napalm"))
        .arg(&entry)
        .output();
    std::fs::remove_file(&entry).expect("remove enum test");
    if provider.is_some() {
        std::fs::remove_file(&module).expect("remove enum provider");
    }
    std::fs::remove_dir(&directory).expect("remove empty enum test directory");
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

#[test]
fn enum_example() {
    assert_output(
        include_str!("../scripts/enums.napalm"),
        None,
        "[0, 1, 2]\n[10, 11, -1, 20]\n[\"up\", \"down\"]\n[\"Red\", \"Blue\", \"Failed\"]\n\"green\"\n\"Blue\"\n[3, 4, 9]\n",
    );
}

#[test]
fn constant_initializers_aliases_and_reverse_mapping() {
    assert_output(
        r#"
        enum Values {
            Zero, Negative = -3, Next,
            Fraction = 1.5, Following,
            Alias = Values.Next, Arithmetic = (Alias + 5) * 2 / 3,
            Text = "na" + "palm", Same = Text, Restart = 7, End,
        };
        print([Values.Zero, Values.Negative, Values.Next, Values.Fraction, Values.Following]);
        print([Values.Alias, Values.Arithmetic, Values.Text, Values.Same, Values.End]);
        print([Values[-2], Values[1.5], Values[2.5], Values[Values.End]]);
        print(Values["Negative"]);
        print("napalm" in Values);
        enum Empty {}
        print(Empty.keys());
    "#,
        None,
        "[0, -3, -2, 1.5, 2.5]\n[-2, 2, \"napalm\", \"napalm\", 8]\n[\"Alias\", \"Fraction\", \"Following\", \"End\"]\n-3\nfalse\n[]\n",
    );
}

#[test]
fn module_enums_are_visible_to_functions_and_methods() {
    assert_output(
        r#"
        enum Mode { Off, On }
        fn read() { return Mode.On; }
        class Device {
            fn mode() { return Mode.On; }
            static fn initial() { return Mode.Off; }
        }
        print(read());
        var device = new Device();
        print([device.mode(), Device.initial()]);
        var alias = Mode;
        print(alias == Mode);
        print(alias[alias.On]);
        fn shadow() { enum Mode { On = 9 } return Mode.On; }
        print(shadow());
        print(read());
    "#,
        None,
        "1\n[1, 0]\ntrue\n\"On\"\n9\n1\n",
    );
}

#[test]
fn enum_declarations_work_in_async_and_exception_scopes() {
    assert_output(
        r#"
        async fn task() {
            enum Step { Begin = 2, End }
            return Step.End;
        }
        print(await task());
        fn guarded() {
            enum Result { Good = "ok", Bad = "bad" }
            try { throw Result.Bad; }
            catch (error) { print(error == Result.Bad); }
            finally { print(Result.Good); }
        }
        guarded();
        fn loop() {
            var sum = 0;
            for (var i = 0; i < 3; i = i + 1) {
                enum Local { Value = 4 }
                sum = sum + Local.Value;
            }
            return sum;
        }
        print(loop());
    "#,
        None,
        "3\ntrue\n\"ok\"\n12\n",
    );
}

#[test]
fn exported_and_private_enums_keep_module_identity() {
    assert_output(
        r#"
        import { Color as Shade, read, getColor, privateValue } from "./colors.napalm";
        import * as colors from "./colors.napalm";
        print([Shade.Red, Shade.Blue, read(), privateValue()]);
        print([Shade[Shade.Red], colors.Color[colors.Color.Blue]]);
        print(Shade == getColor());
        print(colors.keys());
    "#,
        Some(
            r#"
        enum Hidden { Value = 42 }
        export enum Color { Red = 4, Blue }
        export fn read() { return Color.Blue; }
        export fn getColor() { return Color; }
        export fn privateValue() { return Hidden.Value; }
    "#,
        ),
        "[4, 5, 5, 42]\n[\"Red\", \"Blue\"]\ntrue\n[\"Color\", \"getColor\", \"privateValue\", \"read\"]\n",
    );
}

#[test]
fn dynamic_indexing_keeps_array_and_string_behavior() {
    assert_output(
        r#"
        enum Kind { A, B }
        fn index(value, key) { return value[key]; }
        print([index(Kind, 0), index(Kind, "B"), index([4, 5], 1)]);
        print([index([4, 5], -1), index([4, 5], 2), index("abc", 1)]);
        print([index(null, 0), index(false, 0), index(3, 0)]);
    "#,
        None,
        "[\"A\", 1, 5]\n[null, null, \"b\"]\n[null, null, null]\n",
    );
}

#[test]
fn contextual_names_and_builtin_properties_resolve_to_members() {
    assert_output(
        r#"
        enum Names { size = 40, length = Names.size + 2, get = 7, set, "odd-name" = "value" }
        enum Other { Value = 10 }
        print([Names.size, Names.length, Names.get, Names.set, Names["odd-name"]]);
        print([Names[40], Names[42], Other.size]);
        print([new Map().size, new Set().size, [1, 2].size]);
    "#,
        None,
        "[40, 42, 7, 8, \"value\"]\n[\"size\", \"length\", 2]\n[0, 0, 2]\n",
    );
}

#[test]
fn local_enums_in_methods_and_modules_do_not_overwrite_outer_bindings() {
    assert_output(
        r#"
        enum Choice { A = 1 }
        fn global() { return Choice.A; }
        if (true) { enum Choice { A = 9 } print(Choice.A); }
        print(global());
        class Factory {
            fn create() {
                enum State { A = 3, B = State["A"] + 1 }
                return State.B;
            }
            static fn local() {
                enum Choice { A = 7 }
                return Choice.A;
            }
        }
        var factory = new Factory();
        print(factory.create());
        print([Factory.local(), global()]);
    "#,
        None,
        "9\n1\n4\n[7, 1]\n",
    );
}

#[test]
fn enums_can_be_exported_by_name_after_declaration() {
    assert_output(
        r#"
        import { Color } from "./colors.napalm";
        print([Color.Red, Color[Color.Red]]);
    "#,
        Some("enum Color { Red = 6 } export { Color };"),
        "[6, \"Red\"]\n",
    );
}

#[test]
fn invalid_enum_initializers_fail_before_execution() {
    for (source, message) in [
        (
            "print(\"unreachable\"); enum E { A = \"s\", B }",
            "requires an initializer",
        ),
        ("enum E { A, A }", "duplicate enum member"),
        ("enum E { A = not_constant() }", "enum initializer"),
        ("enum E { A = 1 / 0 }", "finite numeric/string constant"),
        ("enum E {} enum E {}", "duplicate enum declaration"),
        ("fn test() { enum E { A = unknown } }", "enum initializer"),
    ] {
        let output = run(source, None);
        assert!(!output.status.success(), "{source}");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            !stdout.lines().any(|line| line == "unreachable"),
            "{source}"
        );
        let diagnostics = format!("{}\n{}", stdout, String::from_utf8_lossy(&output.stderr));
        assert!(diagnostics.contains(message), "{source}\n{diagnostics}");
    }
}
