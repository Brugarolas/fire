use super::*;

#[test]
fn parses_expressions_blocks_and_exception_bindings() {
    let program = Parser::with_name(
        "defer print(1); defer { print(2); }; errdefer |error| print(error); \
         errdefer { print(3); }",
        "defer-parser",
    )
    .program()
    .unwrap();
    let statements = &program.functions[0].body.stmts;
    assert_eq!(statements.len(), 4);
    for (index, statement) in statements.iter().enumerate() {
        let StmtKind::Defer {
            kind,
            binding,
            body,
        } = statement.kind()
        else {
            panic!("expected deferred cleanup");
        };
        assert_eq!(
            *kind,
            if index < 2 {
                DeferKind::Defer
            } else {
                DeferKind::ErrDefer
            }
        );
        assert_eq!(binding.as_deref(), (index == 2).then_some("error"));
        assert_eq!(body.stmts.len(), 1);
    }
}

#[test]
fn rejects_returns_but_allows_returns_inside_nested_functions() {
    for source in [
        "defer { return; }",
        "errdefer { while (true) { return 1; } }",
        "defer { for (;;) { return; } }",
        "defer { try {} catch (e) { return; } }",
        "errdefer |e { print(e); }",
        "errdefer |3| print(3);",
        "defer print(1)",
    ] {
        assert!(
            Parser::with_name(source, "invalid-defer")
                .program()
                .is_err(),
            "{source}"
        );
    }
    Parser::with_name(
        "defer { var f = fn () { return 4; }; print(f()); }",
        "defer-lambda",
    )
    .program()
    .unwrap();
}

#[test]
fn cleanup_lowers_to_compiled_regions_without_runtime_scheduling() {
    use crate::wir::Inst;

    let module = crate::build_module_from_source(
        "defer-lowering",
        "fn f() { defer print(1); errdefer |e| print(e); throw 4; } f();",
    )
    .unwrap();
    let function = module.funcs.iter().find(|f| f.sig.name == "f").unwrap();
    assert!(!function.try_regions.is_empty());
    assert!(
        function
            .nodes
            .iter()
            .any(|node| matches!(node.kind, Inst::TryFinallyExit { .. }))
    );
    assert!(
        function
            .nodes
            .iter()
            .any(|node| matches!(node.kind, Inst::Throw(_)))
    );
    assert!(function.nodes.iter().all(|node| match &node.kind {
        Inst::ScheduleDefer { .. } => false,
        Inst::CallNative { name, .. } => name != "napalm_rt_schedule_defer",
        _ => true,
    }));
}
