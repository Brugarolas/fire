use super::*;

fn parse(source: &str) -> Result<Program, String> {
    Parser::with_name(source, "typeck-test")
        .program()
        .map_err(|error| error.msg)
}

fn errors(source: &str) -> String {
    match parse(source) {
        Ok(_) => panic!("expected type errors in:\n{source}"),
        Err(message) => message,
    }
}

fn function<'p>(program: &'p Program, name: &str) -> &'p FuncDecl {
    program
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("missing function `{name}`"))
}

fn typed_ops(block: &Block) -> Vec<String> {
    fn walk_expr(e: &Expr, out: &mut Vec<String>) {
        match e.kind() {
            ExprKind::Typed { op, args } => {
                out.push(match op {
                    TypedOp::Assert { message, .. } => format!("Assert({message})"),
                    other => format!("{other:?}"),
                });
                args.iter().for_each(|a| walk_expr(a, out));
            }
            ExprKind::Binary { a, b, .. } => {
                walk_expr(a, out);
                walk_expr(b, out);
            }
            ExprKind::Call { callee, args } => {
                walk_expr(callee, out);
                args.iter().for_each(|a| walk_expr(a, out));
            }
            ExprKind::Assign(_, value) => walk_expr(value, out),
            ExprKind::GetProp { recv, .. } => walk_expr(recv, out),
            _ => {}
        }
    }
    let mut out = Vec::new();
    for stmt in &block.stmts {
        match stmt.kind() {
            StmtKind::Expr(e) | StmtKind::Return(Some(e)) => walk_expr(e, &mut out),
            StmtKind::Var { init: Some(e), .. } => walk_expr(e, &mut out),
            _ => {}
        }
    }
    out
}

#[test]
fn untyped_code_is_left_untouched() {
    let program = parse(
        "fn f(a, b) { var xs = [a, b]; return xs.length + xs[0] + (a == b); }\n\
         print(f(1, \"x\") + true);",
    )
    .unwrap();
    assert!(typed_ops(&function(&program, "f").body).is_empty());
    assert!(typed_ops(&function(&program, "__toplevel__").body).is_empty());
}

#[test]
fn parameters_get_entry_guards_and_typed_operations() {
    let program = parse(
        "fn f(xs: number[], s: string, t: string): number {\n\
             var joined = s + t;\n\
             xs[0] = xs[1];\n\
             return xs.length + s.length;\n\
         }",
    )
    .unwrap();
    let ops = typed_ops(&function(&program, "f").body);
    for expected in [
        "Assert(TypeError: parameter `xs` of `f` expects number[])",
        "Assert(TypeError: parameter `s` of `f` expects string)",
        "StrConcat",
        "ArraySet",
        "ArrayGet",
        "ArrayLen",
        "StrLen",
    ] {
        assert!(ops.iter().any(|op| op == expected), "{expected} not in {ops:?}");
    }
}

#[test]
fn values_from_untyped_code_are_guarded_at_typed_boundaries() {
    let program = parse("fn source() { return 1; }\nvar n: number = source();").unwrap();
    let ops = typed_ops(&function(&program, "__toplevel__").body);
    assert_eq!(ops, ["Assert(TypeError: variable `n` expects number)"]);
}

#[test]
fn statically_known_types_need_no_guards() {
    let program = parse(
        "fn id<T>(v: T): T { return v; }\n\
         var n: number = id(4);\n\
         var s: string = id<string>(\"x\");",
    )
    .unwrap();
    let ops = typed_ops(&function(&program, "__toplevel__").body);
    assert!(ops.iter().all(|op| !op.starts_with("Assert")), "{ops:?}");
}

#[test]
fn mismatches_are_reported_together() {
    let message = errors(
        "fn f(a: number): string { return a; }\n\
         var x: number = \"s\";\n\
         f(1, 2);\n\
         var y: Missing = 1;",
    );
    for expected in [
        "type error in `f`: return value: type `number` is not assignable to type `string`",
        "variable `x`: type `string` is not assignable to type `number`",
        "`f` expects at most 1 argument(s), got 2",
        "unknown type `Missing`",
    ] {
        assert!(message.contains(expected), "{expected}\n---\n{message}");
    }
}

#[test]
fn interfaces_are_structural_and_checked_on_implements() {
    let message = errors(
        "interface Named { name: string; greet(other: string): string }\n\
         class Good implements Named {\n\
             name: string;\n\
             constructor(n: string) { this.name = n; }\n\
             greet(other: string): string { return this.name + other; }\n\
         }\n\
         class Bad implements Named { name: number; constructor() { this.name = 1; } }\n\
         var ok: Named = new Good(\"a\");\n\
         var literal: Named = { name: \"b\", greet: |x| x };\n\
         var missing: Named = { name: \"c\" };",
    );
    assert!(message.contains("class `Bad` incorrectly implements `Named`"), "{message}");
    assert!(message.contains("variable `missing`"), "{message}");
    assert!(!message.contains("`Good`"), "{message}");
    assert!(!message.contains("variable `ok`"), "{message}");
    assert!(!message.contains("variable `literal`"), "{message}");
}

#[test]
fn generics_infer_and_enforce_constraints() {
    let message = errors(
        "interface HasLength { length: number }\n\
         fn longest<T extends HasLength>(a: T, b: T): T { return a; }\n\
         class Box<T> { value: T; constructor(v: T) { this.value = v; } }\n\
         var s: string = longest(\"ab\", \"c\");\n\
         var n: number = new Box(1).value;\n\
         var wrong: string = new Box<number>(1).value;\n\
         longest(1, 2);",
    );
    assert!(message.contains("variable `wrong`"), "{message}");
    assert!(message.contains("does not satisfy the constraint `HasLength`"), "{message}");
    assert!(!message.contains("variable `s`"), "{message}");
    assert!(!message.contains("variable `n`"), "{message}");
}

#[test]
fn optional_parameters_are_padded_and_nullable() {
    let program = parse(
        "fn greet(name: string, greeting?: string): string {\n\
             if (greeting == null) { return name; }\n\
             return greeting + name;\n\
         }\n\
         greet(\"a\");",
    )
    .unwrap();
    let top = function(&program, "__toplevel__");
    let StmtKind::Expr(call) = top.body.stmts[0].kind() else { panic!() };
    let ExprKind::Call { args, .. } = call.kind() else { panic!() };
    assert_eq!(args.len(), 2);
    assert!(matches!(args[1].kind(), ExprKind::LitNull));
    assert!(errors("fn f(a: number, b?: number) {}\nf();").contains("at least 1 argument"));
}

#[test]
fn casts_downcast_with_guards_and_reject_unrelated_types() {
    let program = parse("fn any() { return 1; }\nvar n = any() as number;").unwrap();
    let ops = typed_ops(&function(&program, "__toplevel__").body);
    assert_eq!(ops, ["Assert(TypeError: cannot cast value to number)"]);
    assert!(errors("var s = 1 as string;").contains("cannot cast type `number`"));
}

#[test]
fn aliases_unions_and_nullability() {
    let message = errors(
        "type Id = number | string;\n\
         type Maybe<T> = T | null;\n\
         var a: Id = 1;\n\
         var b: Id = \"x\";\n\
         var c: Maybe<number> = null;\n\
         var d: number = null;\n\
         var e: Id = true;\n\
         type Loop = Loop[];",
    );
    assert!(message.contains("variable `d`"), "{message}");
    assert!(message.contains("variable `e`"), "{message}");
    assert!(!message.contains("variable `a`"), "{message}");
    assert!(!message.contains("variable `c`"), "{message}");
}

#[test]
fn null_checks_narrow_nullable_variables() {
    parse(
        "fn a(v: number | null): number { if (v == null) { return 0; } return v; }\n\
         fn b(s: string | null): number { if (s != null) { return s.length; } return 0; }\n\
         fn c(s: string | null): number { if (s == null) { return 0; } else { return s.length; } }\n\
         fn d(s: string | null): boolean { return s != null && s.length > 1; }\n\
         fn e(s: string | null): boolean { return s == null || s.length > 1; }",
    )
    .unwrap();
    for unsound in [
        "fn f(v: number | null): number { if (v == null) { v = 3; } return v; }",
        "fn f(v: number | null): number { if (v == null) { return 0; } v = null; return v; }",
        "fn f(v: number | null): number { var h = fn() { v = null; }; if (v == null) { return 0; } return v; }",
        "fn f(v: number | null): number { if (v == null) { return 0; } var g = fn(): number { return v; }; return 1; }",
        "fn f(v: number | null) { if (v == null) { return; } while (true) { var n: number = v; v = null; } }",
    ] {
        assert!(errors(unsound).contains("number | null"), "{unsound}");
    }
}

#[test]
fn annotated_functions_infer_local_types() {
    let program = parse(
        "fn typed(name: string, n: number): string { var out = name; return out + n; }\n\
         fn untyped(name, n) { var out = name; out = 1; return out + n; }",
    )
    .unwrap();
    let ops = typed_ops(&function(&program, "typed").body);
    assert!(!ops.iter().any(|op| op.contains("return value")), "{ops:?}");
    assert!(typed_ops(&function(&program, "untyped").body).is_empty());
    assert!(errors("fn f(s: string) { var out = s; out = 1; }").contains("assignment to `out`"));
    parse("fn f(s: string) { var later = null; later = 1; var o = {}; o.x = 1; }").unwrap();
}

#[test]
fn strings_and_arrays_satisfy_length_constraints() {
    let program = parse(
        "fn longest<T extends { length: number }>(a: T, b: T): T { return a; }\n\
         fn size(x: { length: number }): number { return x.length; }\n\
         longest(\"ab\", \"c\"); longest([1], [2, 3]); size(\"abc\"); size({ length: 2 });",
    )
    .unwrap();
    assert!(typed_ops(&function(&program, "__toplevel__").body).is_empty());
    assert!(errors("fn f(x: { length: number; first: number }) {} f(\"s\");")
        .contains("property `first` is missing"));
}

#[test]
fn string_concatenation_with_typed_operands() {
    let program = parse(
        "fn f(n: number, s: string, a) { var x = \"n=\" + n; var y = s + a; var z = \"k\" + a; return 1; }\n\
         var lit = \"a\" + 1;",
    )
    .unwrap();
    let ops = format!("{:?}", function(&program, "f").body.stmts);
    assert_eq!(ops.matches("StrConcat").count(), 2, "{ops}");
    let top = format!("{:?}", function(&program, "__toplevel__").body.stmts);
    assert!(!top.contains("StrConcat"), "{top}");
}
