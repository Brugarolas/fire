// parser.rs

use crate::ast::*;
use crate::tokenizer::Token;
use chumsky::prelude::*;

pub fn parser<'a>() -> impl Parser<Token<'a>, Script<'a>, Error = Simple<Token<'a>>> {
    let ident = select! { Token::Identifier(s) => s }.map_with_span(|i, s| (i, s));

    let expr = recursive(|expr| {
        let literal = select! {
            Token::Number(n) => ExprKind::Literal(LiteralValue::Number(n)),
            Token::String(s) => ExprKind::Literal(LiteralValue::String(s)),
            Token::True => ExprKind::Literal(LiteralValue::Bool(true)),
            Token::False => ExprKind::Literal(LiteralValue::Bool(false)),
            Token::Null => ExprKind::Literal(LiteralValue::Null),
            Token::This => ExprKind::This,
            Token::Super => ExprKind::Super,
            Token::Identifier(s) => ExprKind::Identifier(s),
        }
        .map_with_span(|kind, span| Expr { kind, span });

        let list = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map(ExprKind::List)
            .map_with_span(|kind, span| Expr { kind, span });

        let map_entry = expr.clone().then_ignore(just(Token::Colon)).then(expr.clone());
        let map = map_entry
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .map(ExprKind::Map)
            .map_with_span(|kind, span| Expr { kind, span });

        let atom = literal
            .or(list)
            .or(map)
            .or(expr
                .clone()
                .delimited_by(just(Token::LParen), just(Token::RParen)));

        let call = atom.then(
            choice((
                // Regular call
                expr.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .map_with_span(|args, span| (args, span)),
                // Property access
                just(Token::Dot).ignore_then(ident).map(|(name, span)| (name, span)),
                // Subscript
                expr.clone()
                    .delimited_by(just(Token::LBracket), just(Token::RBracket))
                    .map_with_span(|index, span| (index, span)),
            ))
            .repeated(),
        )
        .foldl(|callee, call| {
            let span = callee.span.start..call.1.end;
            let kind = match call {
                (args, _) if args.is_empty() => ExprKind::Call(Box::new(callee), vec![]),
                (args, _) if !args.is_empty() => ExprKind::Call(Box::new(callee), args),
                (name, _) => ExprKind::Get(Box::new(callee), (name, call.1)),
                (index, _) => ExprKind::SubscriptGet(Box::new(callee), Box::new(index)),
            };
            Expr { kind, span }
        });


        let unary = choice((
                just(Token::Minus).to(UnaryOp::Neg),
                just(Token::Bang).to(UnaryOp::Not),
                just(Token::Tilde).to(UnaryOp::BitNot),
            ))
            .repeated()
            .then(call)
            .foldr(|op, rhs| {
                let span = rhs.span.clone(); // A bit tricky, but ok for now
                Expr {
                    kind: ExprKind::Unary(op, Box::new(rhs)),
                    span,
                }
            });

        let op = |op| just(op).to(op);
        let infix = |op, op_type| just(op).to(op_type);

        let product = unary.clone().then(
            choice((
                op(Token::Star).to(InfixOp::Mul),
                op(Token::Slash).to(InfixOp::Div),
                op(Token::Percent).to(InfixOp::Mod),
            ))
            .then(unary)
            .repeated(),
        ).foldl(|lhs, (op, rhs)| {
                let span = lhs.span.start..rhs.span.end;
                Expr { kind: ExprKind::Binary(Box::new(lhs), op, Box::new(rhs)), span }
            });

        // ... and so on for other precedence levels ...

        let assignment = ident
            .then_ignore(just(Token::Eq))
            .then(expr.clone())
            .map(|((name, _), value)| ExprKind::Assignment(name, Box::new(value)))
            .map_with_span(|kind, span| Expr { kind, span });
            
        product.or(assignment) // Simplified for brevity
    });


    let stmt = recursive(|stmt| {
        let var_decl = just(Token::Var)
            .ignore_then(ident)
            .then(just(Token::Eq).ignore_then(expr.clone()).or_not())
            .map_with_span(|(name, init), span| Stmt::Var(VarDecl { name, initializer: init, span }))
            .then_ignore(just(Token::Semicolon)); // Wren doesn't use semicolons, but good for recovery

        let expr_stmt = expr.clone().map(Stmt::Expr);

        let block = stmt.clone()
            .repeated()
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .map_with_span(Stmt::Block);

        let if_stmt = just(Token::If)
            .ignore_then(expr.clone().delimited_by(just(Token::LParen), just(Token::RParen)))
            .then(stmt.clone())
            .then(just(Token::Else).ignore_then(stmt.clone()).or_not())
            .map_with_span(|((cond, then_b), else_b), span| {
                Stmt::If(IfStmt {
                    condition: cond,
                    then_branch: Box::new(then_b),
                    else_branch: else_b.map(Box::new),
                    span,
                })
            });

        let return_stmt = just(Token::Return)
            .then(expr.clone().or_not())
            .map_with_span(|(_, val), span| Stmt::Return(ReturnStmt { value: val, span }));

        choice((var_decl, if_stmt, return_stmt, block, expr_stmt))
    });

    let top_level = stmt
        .repeated()
        .map(|body| Script { body })
        .then_ignore(end());
        
    top_level
}```
*Note: This is a simplified version to illustrate the core structure. A complete implementation would require adding all precedence levels for binary operators (sum, comparison, bitwise, logical), handling all statement types (for, while, class, import), and correctly parsing method signatures and class bodies.*

### 5. The Main Driver (`main.rs`)

This file contains the entry point. It reads a source file, tokenizes it, parses it, and if there are any errors, it uses Ariadne to print them beautifully to the console.

```rust
// main.rs

mod ast;
mod parser;
mod tokenizer;

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::Parser;
use logos::Logos;
use tokenizer::Token;

fn main() {
    let src = r#"
class Point {
    construct.new(x, y) {
        this.x = x
        this.y = y
    }

    toString {
        return "Point(%(this.x), %(this.y))"
    }
}

var p = Point.new(1, 2)
IO.print(p.toString) // Should be IO.print(p.toString())
"#;

    let (tokens, mut errs) = tokenizer::Token::lexer(src)
        .spanned()
        .map(|(tok, span)| match tok {
            Ok(tok) => (tok, span),
            Err(_) => (Token::Error, span),
        })
        .filter(|(tok, _)| *tok != Token::Error) // Simple error handling
        .collect::<Vec<_>>()
        .into_iter()
        .unzip::<_, _, Vec<_>, Vec<_>>();

    let (ast, parse_errs) = parser::parser().parse_recovery(&tokens);

    errs.extend(parse_errs.into_iter().map(|e| e.map(|tok| (tok, e.span()))));

    if let Some(ast) = ast {
        println!("Successfully parsed AST:\n{:#?}", ast);
    }

    errs.into_iter().for_each(|(tok, span)| {
        let report = Report::build(ReportKind::Error, (), span.start)
            .with_message(format!(
                "Unexpected token {}",
                tok.fg(Color::Red)
            ))
            .with_label(
                Label::new(span)
                    .with_message(format!("Found {} here", tok.fg(Color::Yellow)))
                    .with_color(Color::Red),
            );

        report.finish().print(Source::from(&src)).unwrap();
    });
}
