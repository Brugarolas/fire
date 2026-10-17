use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_SCRIPT: AtomicUsize = AtomicUsize::new(0);
static RUN_LOCK: Mutex<()> = Mutex::new(());

fn run(source: &str) -> std::process::Output {
    let _guard = RUN_LOCK
        .lock()
        .expect("serialize memory-intensive JIT processes");
    let path = std::env::temp_dir().join(format!(
        "napalm-exceptions-{}-{}.napalm",
        std::process::id(),
        NEXT_SCRIPT.fetch_add(1, Ordering::Relaxed),
    ));
    std::fs::write(&path, source).expect("write test script");
    let output = Command::new(env!("CARGO_BIN_EXE_Napalm"))
        .arg(&path)
        .output();
    std::fs::remove_file(&path).expect("remove test script");
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
        expected
    );
}

#[test]
fn supplied_trycatch_script() {
    assert_output(
        include_str!("../scripts/trycatch.napalm"),
        concat!(
            "===== try/finally (no throw) =====\n",
            "body: normal\nfinally: normal\nafter normal try\n",
            "===== try/catch/finally (throw handled) =====\n",
            "body: throwing\n[\"caught\", \"boom\"]\nfinally after handled throw\n",
            "after handled throw\nreturn_from_try: body\nreturn_from_try: finally\n",
            "[\"return_from_try result\", 42]\n",
            "return_from_finally: body\nreturn_from_finally: overriding return\n",
            "[\"return_from_finally result\", 77]\n",
            "throw_from_finally: body\nthrow_from_finally: throwing\n",
            "[\"caught from finally\", \"finally error\"]\nafter throw_from_finally\n",
            "===== nested try with rethrow =====\ninner body\n",
            "[\"inner caught\", \"inner fault\"]\ninner finally\n",
            "[\"outer caught\", \"inner fault\"]\nouter finally\nafter nested try\n",
        ),
    );
}

#[test]
fn propagates_calls_and_preserves_local_mutations() {
    assert_output(
        r#"
        fn fail() { throw "failure"; print("unreachable"); }
        fn middle() { fail(); print("unreachable"); }
        fn test() {
            var x = 1;
            try {
                x = 9;
                middle();
                print("unreachable");
            } catch (e) {
                print([e, x]);
                x = 12;
            } finally {
                print(x);
                x = 15;
            }
            print(x);
        }
        test();
        "#,
        "[\"failure\", 9]\n12\n15\n",
    );
}

#[test]
fn nested_returns_and_finally_overrides() {
    assert_output(
        r#"
        fn nested() {
            try {
                try { return 3; } finally { print("inner"); }
            } finally { print("outer"); }
        }
        fn override() {
            try {
                try { throw 5; } finally { return 8; }
            } finally { print("override outer"); }
        }
        print(nested());
        print(override());
        "#,
        "inner\nouter\n3\noverride outer\n8\n",
    );
}

#[test]
fn conditional_returns_loops_and_catch_returns() {
    assert_output(
        r#"
        fn conditional(flag) {
            var x = 0;
            try {
                if (flag) { return 10; }
                while (x < 3) { x = x + 1; }
                throw x;
            } catch (e) {
                return e + 20;
            } finally {
                print("cleanup");
            }
        }
        print(conditional(true));
        print(conditional(false));
        "#,
        "cleanup\n10\ncleanup\n23\n",
    );
}

#[test]
fn throws_in_catch_and_finally_skip_the_current_handler() {
    assert_output(
        r#"
        try {
            try { throw "first"; }
            catch (e) { print(e); throw "second"; }
            finally { print("inner cleanup"); throw "third"; }
        } catch (e) { print(e); }
        try { throw null; } catch (e) { print(e); }
        print("done");
        "#,
        "\"first\"\ninner cleanup\n\"third\"\nnull\ndone\n",
    );
}

#[test]
fn propagates_closures_and_methods() {
    assert_output(
        r#"
        fn invoke(f) { f(); print("unreachable"); }
        class Bomb { explode() { throw 17; } }
        try { invoke(| | { throw 13; }); }
        catch (e) { print(e); }
        var bomb = new Bomb();
        try { bomb.explode(); }
        catch (e) { print(e); }
        "#,
        "13\n17\n",
    );
}

#[test]
fn unhandled_exceptions_fail_explicitly_after_finally() {
    let output = run(r#"
        try { throw "unhandled"; }
        finally { print("cleanup"); }
        print("unreachable");
    "#);
    assert!(!output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).trim(),
        "cleanup",
        "{}",
        String::from_utf8_lossy(&output.stderr),
    );
    assert!(String::from_utf8_lossy(&output.stderr).contains("Uncaught exception:"));
}

#[test]
fn handles_bindingless_catches_and_preserves_thrown_values() {
    assert_output(
        r#"
        try { throw false; } catch (e) { print(e); }
        try { throw 0; } catch (e) { print(e); }
        var object = { answer: 42 };
        try { throw object; } catch (e) { print(e.answer); }
        try { throw 1; } catch { print("bindingless"); }
        "#,
        "false\n0\n42\nbindingless\n",
    );
}

#[test]
fn catches_calls_in_expressions_after_assignments() {
    assert_output(
        r#"
        fn fail(x) { throw x; }
        fn test() {
            var x = 1;
            try { print(fail(x = 7)); }
            catch (e) { print([e, x]); }
            print(x);
        }
        test();
        "#,
        "[7, 7]\n7\n",
    );
}

#[test]
fn finally_with_nested_handler_preserves_pending_completion() {
    assert_output(
        r#"
        fn returning() {
            try { return 9; }
            finally {
                try { throw 1; } catch (e) { print(e); }
                print("cleanup");
            }
        }
        fn failing() {
            try { throw 5; }
            finally {
                try { throw 2; } catch (e) { print(e); }
            }
        }
        print(returning());
        try { failing(); } catch (e) { print(e); }
        "#,
        "1\ncleanup\n9\n2\n5\n",
    );
}

#[test]
fn catch_bindings_shadow_without_mutating_outer_locals() {
    assert_output(
        r#"
        fn test() {
            var e = 10;
            try { throw 3; }
            catch (e) { print(e); e = 4; }
            finally { print(e); }
            print(e);
        }

        test();
        "#,
        "3\n10\n10\n",
    );
}

#[test]
fn async_completion_waits_for_finally_and_rejected_await_is_catchable() {
    assert_output(
        r#"
        async fn returning() {
            try { return 1; }
            finally { print("async cleanup"); return 7; }
        }
        async fn failing() {
            try { throw "async failure"; }
            finally { print("async failure cleanup"); }
        }
        async fn caller() {
            print(await returning());
            try { await failing(); }
            catch (e) { print(e); }
            return 11;
        }
        print(await caller());
        "#,
        "async cleanup\n7\nasync failure cleanup\n\"async failure\"\n11\n",
    );
}

#[test]
fn native_callback_loops_do_not_execute_user_code_after_a_throw() {
    assert_output(
        r#"
        try {
            [1, 2, 3].map(|x| { print(x); throw x; });
        } catch (e) { print(["caught", e]); }
        print("done");
        "#,
        "1\n[\"caught\", 1]\ndone\n",
    );
}

#[test]
fn async_instance_and_static_methods_run_finally_before_settlement() {
    assert_output(
        r#"
        class AsyncTest {
            async fn value() {
                try { return 1; } finally { return 2; }
            }
            static async fn fail() {
                try { return 3; } finally { throw 4; }
            }
        }
        var object = new AsyncTest();
        print(await object.value());
        try { await AsyncTest.fail(); } catch (e) { print(e); }
        "#,
        "2\n4\n",
    );
}

#[test]
fn existing_boolean_and_module_scripts_keep_their_output() {
    let _guard = RUN_LOCK
        .lock()
        .expect("serialize memory-intensive JIT processes");
    for (script, expected) in [
        (
            "bool.napalm",
            concat!(
                "===== Boolean basics =====\ntrue\nfalse\nfalse\ntrue\n",
                "===== Boolean control flow =====\ntrue branch\nfalse branch\n",
                "===== Boolean equality =====\nfalse\ntrue\n",
            ),
        ),
        ("import.napalm", "SMOKE\n42\n5\n2\n21\n"),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("scripts")
            .join(script);
        let output = Command::new(env!("CARGO_BIN_EXE_Napalm"))
            .arg(path)
            .output()
            .expect("execute existing script");
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout).replace("\r\n", "\n"),
            expected
        );
    }
}
