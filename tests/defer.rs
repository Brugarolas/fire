use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_SCRIPT: AtomicUsize = AtomicUsize::new(0);
static RUN_LOCK: Mutex<()> = Mutex::new(());

fn run(source: &str) -> std::process::Output {
    run_with_provider(source, None)
}

fn run_with_provider(source: &str, provider: Option<&str>) -> std::process::Output {
    let _guard = RUN_LOCK
        .lock()
        .expect("serialize memory-intensive JIT processes");
    let directory = std::env::temp_dir().join(format!(
        "napalm-defer-{}-{}",
        std::process::id(),
        NEXT_SCRIPT.fetch_add(1, Ordering::Relaxed),
    ));
    std::fs::create_dir(&directory).expect("create test directory");
    let path = directory.join("main.napalm");
    let provider_path = directory.join("provider.napalm");
    std::fs::write(&path, source).expect("write test script");
    if let Some(provider) = provider {
        std::fs::write(&provider_path, provider).expect("write provider script");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_Napalm"))
        .arg(&path)
        .output();
    std::fs::remove_file(&path).expect("remove test script");
    if provider.is_some() {
        std::fs::remove_file(&provider_path).expect("remove provider script");
    }
    std::fs::remove_dir(&directory).expect("remove empty test directory");
    output.expect("execute Napalm")
}

fn assert_output(source: &str, expected: &str) {
    let output = run(source);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).replace("\r\n", "\n"),
        expected,
        "{}",
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn delayed_expressions_blocks_and_return_value_snapshot() {
    assert_output(
        r#"
        fn test() {
            var x = 1;
            defer print(["first", x]);
            defer { print(["second", x]); x = 90; }
            x = 7;
            print("body");
            return x;
        }
        print(test());
        "#,
        "body\n[\"second\", 7]\n[\"first\", 90]\n7\n",
    );
}

#[test]
fn errdefer_only_runs_when_an_exception_escapes_its_scope() {
    assert_output(
        r#"
        fn test(fail) {
            defer print("always first");
            errdefer print("error only");
            defer print("always last");
            try { throw "handled"; } catch (e) { print(e); }
            if (fail) { throw "escaping"; }
            return 3;
        }
        print(test(false));
        try { test(true); } catch (e) { print(e); }
        "#,
        "\"handled\"\nalways last\nalways first\n3\n\"handled\"\nalways last\nerror only\nalways first\n\"escaping\"\n",
    );
}

#[test]
fn captures_errors_without_replacing_them_or_shadowed_locals() {
    assert_output(
        r#"
        fn test() {
            var error = 2;
            defer print(["outer", error]);
            errdefer |error| {
                print(error);
                error = "changed";
                defer print(error);
                errdefer print("unreachable nested errdefer");
            }
            error = 8;
            throw {message: "original"};
        }
        try { test(); } catch (e) { print(e.message); }
        "#,
        "{\"message\": \"original\"}\n\"changed\"\n[\"outer\", 8]\n\"original\"\n",
    );
}

#[test]
fn dynamic_registration_and_per_iteration_scope_exit() {
    assert_output(
        r#"
        fn test(flag) {
            defer print("function");
            if (flag) { defer print("branch"); print("inside"); }
            if (flag) { return 10; }
            defer print("reached");
            var i = 0;
            while (i < 2) {
                defer print(i);
                i = i + 1;
            }
            for (var j = 0; j < 2; j = j + 1) {
                defer print(["for", j]);
            }
            return 20;
            defer print("unreachable");
        }
        print(test(true));
        print(test(false));
        "#,
        "inside\nbranch\nfunction\n10\n1\n2\n[\"for\", 0]\n[\"for\", 1]\nreached\nfunction\n20\n",
    );
}

#[test]
fn cleanup_failures_replace_pending_completion_and_run_outer_cleanup() {
    assert_output(
        r#"
        fn fail(value) { throw value; }
        fn test(value) {
            defer print("outer defer");
            errdefer |e| print(["outer error", e]);
            defer { print("throwing defer"); fail("cleanup failure"); }
            if (value) { throw "body failure"; }
            return 4;
        }
        try { test(false); } catch (e) { print(e); }
        try { test(true); } catch (e) { print(e); }
        "#,
        "throwing defer\n[\"outer error\", \"cleanup failure\"]\nouter defer\n\"cleanup failure\"\n\
         throwing defer\n[\"outer error\", \"cleanup failure\"]\nouter defer\n\"cleanup failure\"\n",
    );
}

#[test]
fn try_catch_finally_and_nested_cleanup_interoperate() {
    assert_output(
        r#"
        fn test() {
            defer print("function defer");
            try {
                defer print("try defer");
                errdefer |e| print(e);
                throw 5;
            } catch (e) {
                defer print("catch defer");
                print(e + 1);
                return 9;
            } finally {
                defer print("finally defer");
                print("finally");
            }
        }
        print(test());
        "#,
        "5\ntry defer\n6\ncatch defer\nfinally\nfinally defer\nfunction defer\n9\n",
    );
}

#[test]
fn closure_capture_and_method_cleanup() {
    assert_output(
        r#"
        fn outer() {
            var x = 12;
            return fn () {
                defer {
                    var callback = fn () { return x + 1; };
                    print(callback());
                }
                return x;
            };
        }
        class Example {
            fn value() { defer print("method"); return 4; }
            static fn fail() { errdefer |e| print(e); throw 8; }
        }
        print(outer()());
        print(new Example().value());
        try { Example.fail(); } catch (e) { print(e + 1); }
        "#,
        "13\n12\nmethod\n4\n8\n9\n",
    );
}

#[test]
fn async_and_await_finish_cleanup_before_settlement() {
    assert_output(
        r#"
        async fn value() {
            var x = 1;
            defer { print(await 9); print(x); }
            errdefer print("unreachable");
            x = 4;
            return x;
        }
        async fn fail() { throw "rejected"; }
        async fn test() {
            defer print("async defer");
            errdefer |e| print(["async errdefer", e]);
            await fail();
        }
        class Example {
            async fn value() { defer print("async method"); return 6; }
            static async fn fail() { errdefer |e| print(e); await fail(); }
        }
        print(await value());
        try { await test(); } catch (e) { print(e); }
        print(await new Example().value());
        try { await Example.fail(); } catch (e) { print(e); }
        "#,
        "9\n4\n4\n[\"async errdefer\", \"rejected\"]\nasync defer\n\"rejected\"\nasync method\n6\n\"rejected\"\n\"rejected\"\n",
    );
}

#[test]
fn top_level_cleanup_and_enum_declarations() {
    assert_output(
        r#"
        defer print("module cleanup");
        errdefer print("unreachable");
        enum E { A = 5 }
        fn read() { return E.A; }
        print(read());
        defer print(E.A);
        "#,
        "5\n5\nmodule cleanup\n",
    );
}

#[test]
fn invalid_cleanup_control_flow_is_reported_as_failure() {
    for source in [
        "fn f() { defer { return 1; } }",
        "fn f() { errdefer { if (true) { return; } } }",
        "fn f() { defer { try { return; } finally { print(0); } } }",
    ] {
        let output = run(source);
        assert!(!output.status.success());
        let diagnostic = String::from_utf8_lossy(&output.stderr);
        assert!(
            diagnostic.contains("cannot return from a defer or errdefer body"),
            "{diagnostic}"
        );
    }
}

#[test]
fn throwing_before_registration_skips_unreached_cleanup() {
    assert_output(
        r#"
        fn fail() { throw null; }
        fn test() {
            defer print("registered");
            fail();
            defer print("unreachable defer");
            errdefer print("unreachable errdefer");
        }
        try { test(); } catch (e) { print(e); }
        "#,
        "registered\nnull\n",
    );
}

#[test]
fn implicit_returns_and_fallthrough_propagate_cleanup_mutations() {
    assert_output(
        r#"
        fn test() {
            var x = 0;
            if (true) {
                defer { x = x + 2; }
                defer { x = x + 1; }
            }
            print(x);
            while (x < 5) {
                defer { x = x + 1; }
            }
            print(x);
            defer print("implicit return");
        }
        test();
        "#,
        "3\n5\nimplicit return\n",
    );
}

#[test]
fn errdefer_throw_replaces_error_and_runs_remaining_handlers() {
    assert_output(
        r#"
        fn test() {
            errdefer |e| print(["outer", e]);
            errdefer |e| {
                defer print("inner cleanup");
                errdefer |inner| print(["inner", inner]);
                print(e);
                throw 9;
            }
            throw 3;
        }
        try { test(); } catch (e) { print(e); }
        "#,
        "3\n[\"inner\", 9]\ninner cleanup\n[\"outer\", 9]\n9\n",
    );
}

#[test]
fn async_loop_cleanup_and_early_returns() {
    assert_output(
        r#"
        async fn test() {
            var x = 0;
            while (x < 2) {
                defer { x = x + 1; print(await x); }
            }
            for (var j = 0; j < 3; j = j + 1) {
                defer print(["exit", j]);
                if (j == 1) { return x; }
            }
            return 99;
        }
        print(await test());
        "#,
        "1\n2\n[\"exit\", 0]\n[\"exit\", 1]\n2\n",
    );
}

#[test]
fn error_bindings_are_available_to_nested_closures_only_in_cleanup() {
    assert_output(
        r#"
        fn test() {
            var x = 1;
            defer {
                var f = fn () { return x; };
                print(f());
            }
            errdefer |error| {
                var f = fn () { return error; };
                print(f());
            }
            x = 4;
            throw false;
        }
        try { test(); } catch (e) { print(e); }
        "#,
        "false\n4\nfalse\n",
    );
}

#[test]
fn uncaught_throw_runs_cleanup_before_nonzero_exit() {
    let output = run("defer print(\"cleaned\"); errdefer |e| print(e); throw 4;");
    assert!(!output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).replace("\r\n", "\n"),
        "4\ncleaned\n"
    );
    assert!(String::from_utf8_lossy(&output.stderr).contains("Uncaught exception"));
}

#[test]
fn documented_example() {
    assert_output(
        include_str!("../scripts/defer.napalm"),
        "[\"first cleanup\", 7]\n[\"last cleanup\", 8]\n7\n\
         [\"first cleanup\", 7]\n[\"failure cleanup\", \"work failed\"]\n\
         [\"last cleanup\", 8]\n\"work failed\"\n\
         [\"iteration\", 0]\n[\"iteration cleanup\", 0]\n\
         [\"iteration\", 1]\n[\"iteration cleanup\", 1]\n",
    );
}

#[test]
fn imported_module_cleanup_runs_at_initializer_exit() {
    let output = run_with_provider(
        r#"
        import { work, State } from "./provider.napalm";
        defer print("entry cleanup");
        print(work());
        print(State.Ready);
        "#,
        Some(
            r#"
            export enum State { Ready = 5 }
            defer print("provider cleanup");
            export fn work() { defer print(State.Ready); return State.Ready; }
            "#,
        ),
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).replace("\r\n", "\n"),
        "provider cleanup\n5\n5\n5\nentry cleanup\n",
        "{}",
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn zero_iteration_loops_do_not_register_cleanup_or_leak_body_locals() {
    assert_output(
        r#"
        fn test() {
            var x = 3;
            defer print(x);
            while (false) { defer print("unreachable"); }
            for (var i = 0; i < 0; i = i + 1) {
                defer print("unreachable");
            }
            return x;
        }
        async fn async_test() {
            var x = 4;
            defer print(x);
            while (false) { defer print("unreachable"); }
            for (var i = 0; i < 0; i = i + 1) {
                defer print("unreachable");
            }
            return x;
        }
        print(test());
        print(await async_test());
        "#,
        "3\n3\n4\n4\n",
    );
}

#[test]
fn null_and_false_are_successful_return_values_not_errors() {
    assert_output(
        r#"
        fn test(value) {
            defer print("success");
            errdefer print("unreachable");
            return value;
        }
        fn implicit() {
            defer print("implicit");
            errdefer print("unreachable");
        }
        print(test(null));
        print(test(false));
        implicit();
        "#,
        "success\nnull\nsuccess\nfalse\nimplicit\n",
    );
}
