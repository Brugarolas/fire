use super::*;

#[test]
fn constants_and_reverse_mappings_are_resolved_before_lowering() {
    let mut parser = Parser::with_name(
        "enum E { Zero, First = 4, Next, Negative = -3, Fraction = 1.5, \
         Alias = E.First, Computed = (Alias + 2) * 3, \
         Text = \"nap\" + \"alm\", Same = Text, \"quoted-name\" = \"q\", }",
        "enum-test",
    );
    let program = parser.program().unwrap();
    let StmtKind::Enum { name, init, .. } = program.functions[0].body.stmts[0].kind() else {
        panic!("expected enum declaration");
    };
    assert_eq!(name, "E");
    let ExprKind::ObjLit(properties) = init.kind() else {
        panic!("expected lowered enum object");
    };
    let find = |key: &str| {
        properties
            .iter()
            .rev()
            .find_map(|property| match property {
                ObjItem::Prop(PropKey::Str(name), expression) if name == key => {
                    Some(expression.kind())
                }
                _ => None,
            })
            .unwrap()
    };
    assert!(matches!(find("Zero"), ExprKind::LitInt(0)));
    assert!(matches!(find("Next"), ExprKind::LitInt(5)));
    assert!(matches!(find("Negative"), ExprKind::LitInt(-3)));
    assert!(matches!(find("Fraction"), ExprKind::LitF64(value) if *value == 1.5));
    assert!(matches!(find("Computed"), ExprKind::LitInt(18)));
    assert!(matches!(find("Same"), ExprKind::Str(value) if value == "napalm"));
    assert!(matches!(find("4"), ExprKind::Str(value) if value == "Alias"));
    assert!(matches!(find("quoted-name"), ExprKind::Str(value) if value == "q"));
    assert!(!properties.iter().any(
        |property| matches!(property, ObjItem::Prop(PropKey::Str(key), _) if key == "napalm")
    ));
}

#[test]
fn standalone_lowering_resolves_private_module_enums() {
    let module = crate::build_module_from_source(
        "enum-test",
        "enum E { A = 4 } fn read() { return E.A; } print(read());",
    )
    .expect("the standalone compiler also registers enum bindings");
    assert!(
        module
            .funcs
            .iter()
            .any(|function| function.sig.name == "read")
    );
}

#[test]
fn invalid_declarations_have_explicit_diagnostics() {
    for (source, diagnostic) in [
        ("enum { A }", "expected enum name"),
        ("enum E A", "expected '{'"),
        ("enum E { A A }", "expected ','"),
        ("enum E { A", "unexpected end"),
        ("enum E { A, A }", "duplicate enum member"),
        ("enum E { \"0\" = 3 }", "names cannot be numeric"),
        ("enum E { A = \"s\", B }", "requires an initializer"),
        ("enum E { A = Later, Later = 1 }", "enum initializer"),
        ("enum E { A = E.A }", "enum initializer"),
        ("enum E { A = other() }", "enum initializer"),
        ("enum E { A = true }", "enum initializer"),
        ("enum E { A = 1 / 0 }", "finite numeric/string constant"),
        ("enum E { A = 0 / 0 }", "finite numeric/string constant"),
        (
            "enum E { A = 100000000000000000000.0, B }",
            "numeric precision",
        ),
    ] {
        let error = Parser::with_name(source, "invalid-enum")
            .program()
            .unwrap_err();
        assert!(error.to_string().contains(diagnostic), "{source}: {error}");
    }
}
