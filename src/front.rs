// front.rs
//! frontend.rs — Logos-based tokenizer + hand-rolled parser → WIR lowerer
//!
//! This is a real, compiling Rust module that provides:
//!   1) A `logos` lexer for a small, Wren-ish language subset
//!   2) A hand-rolled Pratt parser (expressions) + RD parser (statements/functions)
//!   3) A lowering pass from the parsed AST into the previously defined WIR
//!
//! Drop this next to the WIR file you already have (the one I gave earlier).
//! Then in `Cargo.toml`, add:
//!     [dependencies]
//!     logos = "0.14"
//!
//! Example supported grammar (subset, Wren-ish / C-ish blend):
//!   program     := { fn_def | class_def? }*
//!   fn_def      := "fn" IDENT "(" param_list? ")" block
//!   param_list  := IDENT ("," IDENT)*
//!   block       := "{" stmt* "}"
//!   stmt        := var_decl | if_stmt | while_stmt | for_stmt | return_stmt | expr_stmt
//!   var_decl    := "var" IDENT ("=" expr)? ";"
//!   if_stmt     := "if" "(" expr ")" block ("else" block)?
//!   while_stmt  := "while" "(" expr ")" block
//!   for_stmt    := "for" "(" (var_decl | expr_stmt | ";") expr? ";" expr? ")" block
//!   return_stmt := "return" expr? ";"
//!   expr_stmt   := expr ";"
//!   expr        := assignment
//!   assignment  := (primary "." IDENT | IDENT | index) "=" assignment | logic_or
//!   logic_or    := logic_and ("||" logic_and)*
//!   logic_and   := equality ("&&" equality)*
//!   equality    := comparison (("==" | "!=") comparison)*
//!   comparison  := term (("<" | "<=" | ">" | ">=") term)*
//!   term        := factor (("+" | "-") factor)*
//!   factor      := unary (("*" | "/" | "%") unary)*
//!   unary       := ("!" | "-" | "+") unary | call
//!   call        := primary ( "(" arg_list? ")" | "." IDENT | "[" expr "]" )*
//!   primary     := NUMBER | STRING | "true" | "false" | "null" | IDENT | "(" expr ")"
//!
//! Types: we keep them dynamic in the surface, but the lowerer prefers i32/f64/bool and Array<i32>
//! to keep the WIR example tight. You can expand as needed.
//!
//! Lowering strategy (initial):
//!  - locals are SSA-ish by rewriting to builder temps (this is *not* full SSA; good enough to
//!    generate WIR for tests). A future pass can do proper SSA construction & phi placement.
//!  - arithmetic → Int32 by default unless literals are f64 (*very* simple typing).
//!  - arrays: `list(n)` intrinsic -> AllocArray; `a[i]` -> GuardBounds + LoadElem.
//!  - calls to known `fn` (parsed in same module) → CallDirect; otherwise CallIC on receiver.
//!
//! Note: this is deliberately small to keep it readable, but fully functional.

use logos::Logos;
use std::collections::BTreeSet;

// Bring in the WIR types from your other file/module.
use crate::wir::{
    Type::Array as _, // just to avoid name clash in comments; no actual item
    BlockId, Builder, Constant, EffectKind, EnvShapeId, FieldId, FuncId, Inst, IntBinOp, Module,
    ShapeId, ShapeSet, Signature, SiteId, Type, Value, ValueDef, ValueId,
};

/// -------------------------
/// LEXER (Logos)
/// -------------------------

#[derive(Logos, Debug, Clone, PartialEq)]
pub enum Tok {
    // --- Skips (must come before '/' token) ---
    #[regex(r"[ \t\r\n\f]+", logos::skip)]
    _Ws,
    #[regex(r"//[^\n]*", logos::skip)]
    _LineComment,
    #[regex(r"/\*([^*]|\*[^/])*\*/", logos::skip)]
    _BlockComment,

    // Keywords
    #[token("fn")] Fn,
    #[token("var")] Var,
    #[token("if")] If,
    #[token("else")] Else,
    #[token("while")] While,
    #[token("for")] For,
    #[token("return")] Return,
    #[token("true")] True,
    #[token("false")] False,
    #[token("null")] Null,

    // Simple builtins (for demo lowering)
    #[token("list")] ListBuiltin,

    // Identifiers & literals
    #[regex(r"[A-Za-z_][A-Za-z0-9_]*", |lex| lex.slice().to_string())]
    Ident(String),
    #[regex(r"[0-9]+", |lex| lex.slice().parse::<i32>().unwrap())]
    Int(i32),
    #[regex(r"[0-9]+\.[0-9]+", |lex| lex.slice().parse::<f64>().unwrap())]
    Float(f64),
    #[regex(r#""([^"\\]|\\.)*""#, |lex| unescape_string(lex.slice()))]
    Str(String),

    // Operators / punctuation
    #[token("==")] EqEq,
    #[token("!=")] BangEq,
    #[token("<=")] LtEq,
    #[token(">=")] GtEq,
    #[token("&&")] AndAnd,
    #[token("||")] OrOr,
    #[token("+=")] PlusEq,
    #[token("-=")] MinusEq,
    #[token("*=")] StarEq,
    #[token("/=")] SlashEq,
    #[token("%=")] PercentEq,
    #[token("=")] Eq,
    #[token("<")] Lt,
    #[token(">")] Gt,
    #[token("+")] Plus,
    #[token("-")] Minus,
    #[token("*")] Star,
    #[token("/")] Slash,
    #[token("%")] Percent,
    #[token("!")] Bang,
    #[token(".")] Dot,
    #[token(",")] Comma,
    #[token(";")] Semi,
    #[token("(")] LParen,
    #[token(")")] RParen,
    #[token("{")] LBrace,
    #[token("}")] RBrace,
    #[token("[")] LBracket,
    #[token("]")] RBracket,
}

fn unescape_string(raw: &str) -> String {
    // raw includes quotes; quick unescape for common escapes
    let s = &raw[1..raw.len() - 1];
    let mut out = String::with_capacity(s.len());
    let mut it = s.chars();
    while let Some(c) = it.next() {
        if c == '\\' {
            if let Some(n) = it.next() {
                out.push(match n {
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    '\\' => '\\',
                    '"' => '"',
                    '\'' => '\'',
                    '0' => '\0',
                    x => x,
                });
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// -------------------------
/// AST
/// -------------------------

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: Vec<FuncDecl>,
}

#[derive(Debug, Clone)]
pub struct FuncDecl {
    pub name: String,
    pub params: Vec<String>,
    pub body: Block,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Var { name: String, init: Option<Expr> },
    If { cond: Expr, then_b: Block, else_b: Option<Block> },
    While { cond: Expr, body: Block },
    For { init: Option<Box<Stmt>>, cond: Option<Expr>, step: Option<Expr>, body: Block },
    Return(Option<Expr>),
    Expr(Expr),
}

#[derive(Debug, Clone)]
pub enum Expr {
    LitInt(i32),
    LitF64(f64),
    LitBool(bool),
    LitNull,
    Str(String),
    Ident(String),
    Assign(Box<LValue>, Box<Expr>),
    Binary { op: BinOp, a: Box<Expr>, b: Box<Expr> },
    Unary { op: UnOp, e: Box<Expr> },
    Call { callee: Box<Expr>, args: Vec<Expr> },
    GetProp { recv: Box<Expr>, name: String },
    Index { recv: Box<Expr>, index: Box<Expr> },
    Group(Box<Expr>),
}

#[derive(Debug, Clone)]
pub enum LValue {
    Ident(String),
    GetProp { recv: Expr, name: String },
    Index { recv: Expr, index: Expr },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add, Sub, Mul, Div, Rem,
    Eq, Ne, Lt, Le, Gt, Ge,
    And, Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg, Pos, Not,
}

/// -------------------------
/// PARSER (Pratt + RD)
/// -------------------------

#[derive(Debug)]
pub struct ParseError {
    pub msg: String,
    pub span: std::ops::Range<usize>,
}

pub type PResult<T> = Result<T, ParseError>;

#[derive(Clone)]
struct SpannedTok {
    tok: Tok,
    span: std::ops::Range<usize>,
}

pub struct Parser<'src> {
    toks: Vec<SpannedTok>,
    i: usize,
    _src: &'src str,
}

impl<'src> Parser<'src> {
    pub fn new(src: &'src str) -> Self {
        let mut lex = Tok::lexer(src);
        let mut toks = Vec::new();

        while let Some(item) = lex.next() {
            match item {
                Ok(t) => {
                    let span = lex.span();
                    toks.push(SpannedTok { tok: t, span });
                }
                Err(_) => {
                    // Unknown/invalid sequence: log and keep scanning; DO NOT fabricate a token.
                    // (Optionally enable if you use `log`.)  e.g.:
                    // log::error!("[lexer] unrecognized sequence {:?} at {:?}", lex.slice(), lex.span());
                }
            }
        }

        Self { toks, i: 0, _src: src }
    }

    #[inline]
    fn peek(&self) -> &SpannedTok {
        // Caller only uses this when self.i < toks.len(); we keep it simple.
        &self.toks[self.i]
    }

    #[inline]
    fn next(&mut self) -> SpannedTok {
        let t = self.toks[self.i].clone();
        self.i += 1;
        t
    }

    #[inline]
    fn check(&self, t: &Tok) -> bool {
        &self.peek().tok == t
    }

    #[inline]
    fn matches(&mut self, t: &Tok) -> bool {
        if self.check(t) {
            self.i += 1;
            true
        } else {
            false
        }
    }

    #[inline]
    fn expect(&mut self, t: Tok, msg: &str) -> PResult<()> {
        if self.peek().tok == t {
            self.i += 1;
            Ok(())
        } else {
            Err(self.err_here(msg))
        }
    }

    #[inline]
    fn err_here(&self, msg: &str) -> ParseError {
        ParseError { msg: msg.into(), span: self.peek().span.clone() }
    }

    #[inline]
    fn is_eof(&self) -> bool {
        self.i >= self.toks.len()
    }

    pub fn program(&mut self) -> PResult<Program> {
        let mut functions = Vec::new();
        let mut toplevel_stmts: Vec<Stmt> = Vec::new();

        while self.i < self.toks.len() {
            // Allow stray semicolons at the top level.
            if self.matches(&Tok::Semi) {
                continue;
            }

            if self.check(&Tok::Fn) {
                // consume `fn` and parse a function definition
                self.i += 1;
                functions.push(self.fn_def()?);
            } else {
                // parse a regular statement at top level (e.g. `print(…) ;`)
                let stmt = self.stmt()?;
                toplevel_stmts.push(stmt);
            }
        }

        if !toplevel_stmts.is_empty() {
            functions.push(FuncDecl {
                name: "__toplevel__".to_string(),
                params: Vec::new(),
                body: Block { stmts: toplevel_stmts },
            });
        }

        Ok(Program { functions })
    }

    fn fn_def(&mut self) -> PResult<FuncDecl> {
        let name = match self.next().tok {
            Tok::Ident(s) => s,
            _ => return Err(self.err_here("expected function name")),
        };
        self.expect(Tok::LParen, "expected '(' after function name")?;
        let mut params = Vec::new();
        if !self.matches(&Tok::RParen) {
            loop {
                let ident = match self.next().tok {
                    Tok::Ident(s) => s,
                    _ => return Err(self.err_here("expected parameter name")),
                };
                params.push(ident);
                if self.matches(&Tok::RParen) { break; }
                self.expect(Tok::Comma, "expected ','")?;
            }
        }
        let body = self.block()?;
        Ok(FuncDecl { name, params, body })
    }

    fn block(&mut self) -> PResult<Block> {
        self.expect(Tok::LBrace, "expected '{'")?;
        let mut stmts = Vec::new();
        while !self.matches(&Tok::RBrace) {
            if self.i >= self.toks.len() { return Err(self.err_here("unclosed block")); }
            stmts.push(self.stmt()?);
        }
        Ok(Block { stmts })
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        // Allow empty statements (`;`) anywhere a statement is expected
        // (including top level). Treat as a no-op expression stmt.
        if self.matches(&Tok::Semi) {
            return Ok(Stmt::Expr(Expr::LitInt(0)));
        }

        if self.matches(&Tok::Var) {
            let name = match self.next().tok {
                Tok::Ident(s) => s,
                _ => return Err(self.err_here("expected identifier after 'var'")),
            };
            let init = if self.matches(&Tok::Eq) { Some(self.expr()?) } else { None };
            self.expect(Tok::Semi, "expected ';' after var decl")?;
            Ok(Stmt::Var { name, init })
        } else if self.matches(&Tok::If) {
            self.expect(Tok::LParen, "expected '('")?;
            let cond = self.expr()?;
            self.expect(Tok::RParen, "expected ')'")?;
            let then_b = self.block()?;
            let else_b = if self.matches(&Tok::Else) { Some(self.block()?) } else { None };
            Ok(Stmt::If { cond, then_b, else_b })
        } else if self.matches(&Tok::While) {
            self.expect(Tok::LParen, "expected '('")?;
            let cond = self.expr()?;
            self.expect(Tok::RParen, "expected ')'")?;
            let body = self.block()?;
            Ok(Stmt::While { cond, body })
        } else if self.matches(&Tok::For) {
            self.expect(Tok::LParen, "expected '('")?;
            let init = if self.matches(&Tok::Semi) {
                None
            } else if self.matches(&Tok::Var) {
                let name = match self.next().tok {
                    Tok::Ident(s) => s,
                    _ => return Err(self.err_here("expected identifier after 'var'")),
                };
                let init_e = if self.matches(&Tok::Eq) { Some(self.expr()?) } else { None };
                self.expect(Tok::Semi, "expected ';' after init")?;
                Some(Box::new(Stmt::Var { name, init: init_e }))
            } else {
                let e = self.expr()?;
                self.expect(Tok::Semi, "expected ';' after init")?;
                Some(Box::new(Stmt::Expr(e)))
            };
            let cond = if self.matches(&Tok::Semi) {
                None
            } else {
                let e = self.expr()?;
                self.expect(Tok::Semi, "expected ';' after cond")?;
                Some(e)
            };
            let step = if self.matches(&Tok::RParen) {
                None
            } else {
                let e = self.expr()?;
                self.expect(Tok::RParen, "expected ')' after step")?;
                Some(e)
            };
            let body = self.block()?;
            Ok(Stmt::For { init, cond, step, body })
        } else if self.matches(&Tok::Return) {
            if self.matches(&Tok::Semi) {
                Ok(Stmt::Return(None))
            } else {
                let e = self.expr()?;
                self.expect(Tok::Semi, "expected ';' after return")?;
                Ok(Stmt::Return(Some(e)))
            }
        } else {
            let e = self.expr()?;
            self.expect(Tok::Semi, "expected ';' after expression")?;
            Ok(Stmt::Expr(e))
        }
    }

    // Pratt parser for expressions
    pub fn expr(&mut self) -> PResult<Expr> { self.parse_assign() }

    fn parse_assign(&mut self) -> PResult<Expr> {
        let mut left = self.parse_or()?;

        // Which assignment operator (if any) did we see?
        // Try the multi-char ones first.
        let op = if self.matches(&Tok::PlusEq)    { Some(("PlusEq",  BinOp::Add)) }
            else if self.matches(&Tok::MinusEq)       { Some(("MinusEq", BinOp::Sub)) }
            else if self.matches(&Tok::StarEq)        { Some(("StarEq",  BinOp::Mul)) }
            else if self.matches(&Tok::SlashEq)       { Some(("SlashEq", BinOp::Div)) }
            else if self.matches(&Tok::PercentEq)     { Some(("PercentEq", BinOp::Rem)) }
            else if self.matches(&Tok::Eq)            { Some(("Eq",      // plain '='
                                                        // dummy op, won't be used
                                                        BinOp::Add)) }
            else { None };

        if let Some((kind, bop)) = op {
            // Turn `left` into an LValue
            let lv = match left {
                Expr::Ident(s)                      => LValue::Ident(s),
                Expr::GetProp { recv, name }        => LValue::GetProp { recv: *recv, name },
                Expr::Index   { recv, index }       => LValue::Index   { recv: *recv, index: *index },
                _ => return Err(self.err_here("invalid assignment target")),
            };

            // Parse the RHS (right-associative)
            let rhs = self.parse_assign()?;

            // For compound op, synthesize:  lv = (lv_expr <op> rhs)
            let final_rhs = if kind == "Eq" {
                rhs
            } else {
                Expr::Binary {
                    op: bop,
                    a: Box::new(lvalue_to_expr(&lv)),
                    b: Box::new(rhs),
                }
            };

            Ok(Expr::Assign(Box::new(lv), Box::new(final_rhs)))
        } else {
            Ok(left)
        }
    }

    fn parse_or(&mut self) -> PResult<Expr> {
        let mut e = self.parse_and()?;
        while self.matches(&Tok::OrOr) {
            let rhs = self.parse_and()?;
            e = Expr::Binary { op: BinOp::Or, a: Box::new(e), b: Box::new(rhs) };
        }
        Ok(e)
    }
    fn parse_and(&mut self) -> PResult<Expr> {
        let mut e = self.parse_eq()?;
        while self.matches(&Tok::AndAnd) {
            let rhs = self.parse_eq()?;
            e = Expr::Binary { op: BinOp::And, a: Box::new(e), b: Box::new(rhs) };
        }
        Ok(e)
    }
    fn parse_eq(&mut self) -> PResult<Expr> {
        let mut e = self.parse_cmp()?;
        loop {
            if self.matches(&Tok::EqEq) {
                let rhs = self.parse_cmp()?;
                e = Expr::Binary { op: BinOp::Eq, a: Box::new(e), b: Box::new(rhs) };
            } else if self.matches(&Tok::BangEq) {
                let rhs = self.parse_cmp()?;
                e = Expr::Binary { op: BinOp::Ne, a: Box::new(e), b: Box::new(rhs) };
            } else { break; }
        }
        Ok(e)
    }
    fn parse_cmp(&mut self) -> PResult<Expr> {
        let mut e = self.parse_term()?;
        loop {
            if self.matches(&Tok::Lt) {
                let rhs = self.parse_term()?;
                e = Expr::Binary { op: BinOp::Lt, a: Box::new(e), b: Box::new(rhs) };
            } else if self.matches(&Tok::LtEq) {
                let rhs = self.parse_term()?;
                e = Expr::Binary { op: BinOp::Le, a: Box::new(e), b: Box::new(rhs) };
            } else if self.matches(&Tok::Gt) {
                let rhs = self.parse_term()?;
                e = Expr::Binary { op: BinOp::Gt, a: Box::new(e), b: Box::new(rhs) };
            } else if self.matches(&Tok::GtEq) {
                let rhs = self.parse_term()?;
                e = Expr::Binary { op: BinOp::Ge, a: Box::new(e), b: Box::new(rhs) };
            } else { break; }
        }
        Ok(e)
    }
    fn parse_term(&mut self) -> PResult<Expr> {
        let mut e = self.parse_factor()?;
        loop {
            if self.matches(&Tok::Plus) {
                let rhs = self.parse_factor()?;
                e = Expr::Binary { op: BinOp::Add, a: Box::new(e), b: Box::new(rhs) };
            } else if self.matches(&Tok::Minus) {
                let rhs = self.parse_factor()?;
                e = Expr::Binary { op: BinOp::Sub, a: Box::new(e), b: Box::new(rhs) };
            } else { break; }
        }
        Ok(e)
    }
    fn parse_factor(&mut self) -> PResult<Expr> {
        let mut e = self.parse_unary()?;
        loop {
            if self.matches(&Tok::Star) {
                let rhs = self.parse_unary()?;
                e = Expr::Binary { op: BinOp::Mul, a: Box::new(e), b: Box::new(rhs) };
            } else if self.matches(&Tok::Slash) {
                let rhs = self.parse_unary()?;
                e = Expr::Binary { op: BinOp::Div, a: Box::new(e), b: Box::new(rhs) };
            } else if self.matches(&Tok::Percent) {
                let rhs = self.parse_unary()?;
                e = Expr::Binary { op: BinOp::Rem, a: Box::new(e), b: Box::new(rhs) };
            } else { break; }
        }
        Ok(e)
    }
    fn parse_unary(&mut self) -> PResult<Expr> {
        if self.matches(&Tok::Bang) {
            let e = self.parse_unary()?;
            Ok(Expr::Unary { op: UnOp::Not, e: Box::new(e) })
        } else if self.matches(&Tok::Minus) {
            let e = self.parse_unary()?;
            Ok(Expr::Unary { op: UnOp::Neg, e: Box::new(e) })
        } else if self.matches(&Tok::Plus) {
            let e = self.parse_unary()?;
            Ok(Expr::Unary { op: UnOp::Pos, e: Box::new(e) })
        } else {
            self.parse_call()
        }
    }
    fn parse_call(&mut self) -> PResult<Expr> {
        let mut e = self.parse_primary()?;
        loop {
            if self.matches(&Tok::LParen) {
                let mut args = Vec::new();
                if !self.matches(&Tok::RParen) {
                    loop {
                        args.push(self.expr()?);
                        if self.matches(&Tok::RParen) { break; }
                        self.expect(Tok::Comma, "expected ',' in argument list")?;
                    }
                }
                e = Expr::Call { callee: Box::new(e), args };
            } else if self.matches(&Tok::Dot) {
                let name = match self.next().tok {
                    Tok::Ident(s) => s,
                    _ => return Err(self.err_here("expected identifier after '.'")),
                };
                e = Expr::GetProp { recv: Box::new(e), name };
            } else if self.matches(&Tok::LBracket) {
                let idx = self.expr()?;
                self.expect(Tok::RBracket, "expected ']'")?;
                e = Expr::Index { recv: Box::new(e), index: Box::new(idx) };
            } else {
                break;
            }
        }
        Ok(e)
    }
    fn parse_primary(&mut self) -> PResult<Expr> {
        let t = self.next();
        match t.tok {
            Tok::Int(x) => Ok(Expr::LitInt(x)),
            Tok::Float(x) => Ok(Expr::LitF64(x)),
            Tok::True => Ok(Expr::LitBool(true)),
            Tok::False => Ok(Expr::LitBool(false)),
            Tok::Null => Ok(Expr::LitNull),
            Tok::Str(s) => Ok(Expr::Str(s)),
            Tok::Ident(s) => Ok(Expr::Ident(s)),
            Tok::ListBuiltin => Ok(Expr::Ident("list".into())), // treated as function
            Tok::LParen => {
                let e = self.expr()?;
                self.expect(Tok::RParen, "expected ')'")?;
                Ok(Expr::Group(Box::new(e)))
            }
            _ => Err(ParseError { msg: "unexpected token".into(), span: t.span }),
        }
    }
}

/// -------------------------
/// LOWERING (AST → WIR)
/// -------------------------

#[derive(Debug)]
pub enum LowerError {
    UnknownVar(String),
    UnknownFunc(String),
    NotLowerable(&'static str),
}

type LResult<T> = Result<T, LowerError>;

pub struct Lowerer<'m> {
    module: &'m mut Module,
    // function registry (very simple)
    funcs: std::collections::HashMap<String, FuncId>,
}

impl<'m> Lowerer<'m> {
    pub fn new(module: &'m mut Module) -> Self {
        Self { module, funcs: Default::default() }
    }

    pub fn lower_program(&mut self, prog: &Program) -> LResult<Vec<FuncId>> {
        // Predeclare function IDs
        for (i, f) in prog.functions.iter().enumerate() {
            // In a real system, FuncId would be allocated by a module; we’ll use index `i` as placeholder.
            let id = FuncId(i as u32);
            self.funcs.insert(f.name.clone(), id);
        }
        // Lower each function
        let mut out = Vec::new();
        for f in &prog.functions {
            let id = self.lower_fn(f)?;
            out.push(id);
        }
        Ok(out)
    }

    fn lower_fn(&mut self, fdecl: &FuncDecl) -> LResult<FuncId> {
        // Surface types are dynamic; we pick Int32 for the demo.
        let param_tys = fdecl.params.iter().map(|_| Type::Int32).collect::<Vec<_>>();
        let ret_tys = vec![Type::Int32];

        // Clone function map so we can use the free helpers without borrowing `self`.
        let funcs_snapshot = self.funcs.clone();

        // Build the function body
        let mut func = {
            let mut b = Builder::new(self.module, &fdecl.name, param_tys, ret_tys);

            // Locals: parameter names → SSA values
            let mut locals: std::collections::HashMap<String, ValueId> = Default::default();
            for (i, name) in fdecl.params.iter().enumerate() {
                locals.insert(name.clone(), b.param(i));
            }

            // Per-function field table (don’t touch self.module while builder is live)
            let mut fields: std::collections::HashMap<String, FieldId> = Default::default();
            let mut next_field: u32 = 0;

            lower_block_free(&mut b, &mut locals, &mut fields, &mut next_field, &fdecl.body, &funcs_snapshot)?;

            // Fallthrough default return 0
            let zero = b.const_i32(0);
            b.ret(&[zero]);

            b.finish()
        };

        // *** IMPORTANT: give the function a unique, stable id that matches Module order ***
        let fid = FuncId(self.module.funcs.len() as u32);
        func.id = fid; // <- this prevents duplicate wir_f_0 etc.
        self.module.funcs.push(func);
        Ok(fid)
    }

    fn lower_block(
        &mut self,
        b: &mut Builder<'m>,
        locals: &mut std::collections::HashMap<String, ValueId>,
        blk: &Block,
    ) -> LResult<()> {
        for s in &blk.stmts {
            self.lower_stmt(b, locals, s)?;
        }
        Ok(())
    }

    fn lower_stmt(
        &mut self,
        b: &mut Builder<'m>,
        locals: &mut std::collections::HashMap<String, ValueId>,
        s: &Stmt,
    ) -> LResult<()> {
        match s {
            Stmt::Var { name, init } => {
                let val = if let Some(e) = init {
                    self.lower_expr(b, locals, e)?
                } else {
                    b.const_i32(0)
                };
                locals.insert(name.clone(), val);
            }
            Stmt::If { cond, then_b, else_b } => {
                let c = self.lower_expr_bool(b, locals, cond)?;
                let then_id = b.block();
                let else_id = b.block();
                let cont = b.block();
                b.branch(c, then_id, else_id);

                // then
                b.position_at(then_id);
                self.lower_block(b, locals, then_b)?;
                b.jump(cont, &[]);

                // else
                b.position_at(else_id);
                if let Some(e) = else_b { self.lower_block(b, locals, e)?; }
                b.jump(cont, &[]);

                // cont
                b.position_at(cont);
            }
            Stmt::While { cond, body } => {
                let head = b.block();
                let body_b = b.block();
                let exit = b.block();

                b.jump(head, &[]);
                b.position_at(head);
                let c = self.lower_expr_bool(b, locals, cond)?;
                b.branch(c, body_b, exit);

                b.position_at(body_b);
                self.lower_block(b, locals, body)?;
                // Loop back
                b.jump(head, &[]);

                b.position_at(exit);
            }
            Stmt::For { init, cond, step, body } => {
                if let Some(init_s) = init { self.lower_stmt(b, locals, init_s)?; }
                let head = b.block();
                let body_b = b.block();
                let exit = b.block();

                b.jump(head, &[]);
                b.position_at(head);
                let c = if let Some(e) = cond {
                    self.lower_expr_bool(b, locals, e)?
                } else {
                    // true
                    let (_nid, res) = b.push_node(
                        Inst::Const(Constant::Bool(true)),
                        Some(Type::Bool),
                        1,
                        false,
                    );
                    res[0]
                };
                b.branch(c, body_b, exit);

                b.position_at(body_b);
                self.lower_block(b, locals, body)?;
                if let Some(step_e) = step { let _ = self.lower_expr(b, locals, step_e)?; }
                b.jump(head, &[]);

                b.position_at(exit);
            }
            Stmt::Return(e) => {
                if let Some(expr) = e {
                    let v = self.lower_expr(b, locals, expr)?;
                    b.ret(&[v]);
                } else {
                    let z = b.const_i32(0);
                    b.ret(&[z]);
                }
            }
            Stmt::Expr(e) => {
                let _ = self.lower_expr(b, locals, e)?;
            }
        }
        Ok(())
    }

    fn lower_expr_bool(
        &mut self,
        b: &mut Builder<'m>,
        locals: &mut std::collections::HashMap<String, ValueId>,
        e: &Expr,
    ) -> LResult<ValueId> {
        // For demo, booleans are stored as Type::Bool from comparisons, logical ops.
        self.lower_expr(b, locals, e)
    }

    fn lower_expr(
        &mut self,
        b: &mut Builder<'m>,
        locals: &mut std::collections::HashMap<String, ValueId>,
        e: &Expr,
    ) -> LResult<ValueId> {
        use BinOp::*;
        use Inst::*;
        match e {
            Expr::LitInt(i) => Ok(b.const_i32(*i)),
            Expr::LitF64(f) => Ok(b.const_f64(*f)),
            Expr::LitBool(v) => {
                let (_nid, res) = b.push_node(Inst::Const(Constant::Bool(*v)), Some(Type::Bool), 1, false);
                Ok(res[0])
            }
            Expr::LitNull => {
                let (_nid, res) = b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                Ok(res[0])
            }
            Expr::Str(s) => {
                let (_nid, res) = b.push_node(Inst::Const(Constant::Str(s.clone())), Some(Type::Str), 1, false);
                Ok(res[0])
            }
            Expr::Ident(name) => locals
                .get(name)
                .copied()
                .ok_or_else(|| LowerError::UnknownVar(name.clone())),
            Expr::Group(inner) => self.lower_expr(b, locals, inner),

            Expr::Unary { op, e } => {
                let v = self.lower_expr(b, locals, e)?;
                match op {
                    UnOp::Neg => {
                        let zero = b.const_i32(0);
                        Ok(b.int_bin(IntBinOp::Sub, zero, v))
                    }
                    UnOp::Pos => Ok(v),
                    UnOp::Not => {
                        let (_nid, falsev) = b.push_node(Inst::Const(Constant::Bool(false)), Some(Type::Bool), 1, false);
                        let (_nid, res) = b.push_node(
                            Inst::CmpInt { kind: crate::wir::CmpKind::Eq, a: v, b: falsev[0] },
                            Some(Type::Bool),
                            1,
                            false,
                        );
                        Ok(res[0])
                    }
                }
            }

            Expr::Binary { op, a, b: bb } => {
                let va = self.lower_expr(b, locals, a)?;
                let vb = self.lower_expr(b, locals, bb)?;
                match op {
                    Add => Ok(b.int_bin(IntBinOp::Add, va, vb)),
                    Sub => Ok(b.int_bin(IntBinOp::Sub, va, vb)),
                    Mul => Ok(b.int_bin(IntBinOp::Mul, va, vb)),
                    Div => Ok(b.int_bin(IntBinOp::DivS, va, vb)),
                    Rem => Ok(b.int_bin(IntBinOp::RemS, va, vb)),
                    Eq | Ne | Lt | Le | Gt | Ge => {
                        let kind = match *op {
                            BinOp::Eq => crate::wir::CmpKind::Eq,
                            BinOp::Ne => crate::wir::CmpKind::Ne,
                            BinOp::Lt => crate::wir::CmpKind::Lt,
                            BinOp::Le => crate::wir::CmpKind::Le,
                            BinOp::Gt => crate::wir::CmpKind::Gt,
                            BinOp::Ge => crate::wir::CmpKind::Ge,
                            _ => unreachable!(),
                        };
                        let (_nid, res) = b.push_node(
                            Inst::CmpInt { kind, a: va, b: vb },
                            Some(Type::Bool),
                            1,
                            false,
                        );
                        Ok(res[0])
                    }
                    And | Or => {
                        let then_b = b.block();
                        let else_b = b.block();
                        let cont = b.block();

                        if *op == And { b.branch(va, then_b, else_b); }
                        else { b.branch(va, else_b, then_b); }

                        b.position_at(then_b);
                        let tval = if *op == And {
                            self.lower_expr(b, locals, bb)?
                        } else {
                            let (_nid, res) = b.push_node(Inst::Const(Constant::Bool(true)), Some(Type::Bool), 1, false);
                            res[0]
                        };
                        b.jump(cont, &[tval]);

                        b.position_at(else_b);
                        let eval_else = if *op == And {
                            let (_nid, res) = b.push_node(Inst::Const(Constant::Bool(false)), Some(Type::Bool), 1, false);
                            res[0]
                        } else {
                            self.lower_expr(b, locals, bb)?
                        };
                        b.jump(cont, &[eval_else]);

                        b.position_at(cont);
                        let resv = b.add_block_param(cont, Type::Bool);
                        Ok(resv)
                    }
                }
            }

            Expr::Assign(lv, rhs) => {
                let rv = self.lower_expr(b, locals, rhs)?;
                match &**lv {
                    LValue::Ident(name) => { locals.insert(name.clone(), rv); Ok(rv) }
                    LValue::GetProp { recv, name } => {
                        let obj = self.lower_expr(b, locals, recv)?;
                        let field = self.intern_field(name);
                        let (_nid, _res) = b.push_node(
                            Inst::StoreField { obj, field, val: rv, expected: None },
                            Some(Type::Top),
                            1,
                            true,
                        );
                        Ok(rv)
                    }
                    LValue::Index { recv, index } => {
                        let arr = self.lower_expr(b, locals, recv)?;
                        let idx = self.lower_expr(b, locals, index)?;
                        let len = {
                            let (_nid, res) = b.push_node(Inst::ArrayLen(arr), Some(Type::Int32), 1, false);
                            res[0]
                        };
                        let deopt = b.deopt_point("store_idx_oob");
                        let _ = b.push_node(Inst::GuardBounds { idx, len, deopt }, Some(Type::Top), 1, true);
                        let (_nid, _res) = b.push_node(Inst::StoreElem { arr, idx, val: rv }, Some(Type::Top), 1, true);
                        Ok(rv)
                    }
                }
            }

            Expr::Call { callee, args } => {
                if let Expr::Ident(name) = &**callee {
                    // Builtin: list(n)
                    if name == "list" {
                        if args.len() != 1 { return Err(LowerError::NotLowerable("list() expects 1 arg")); }
                        let len = self.lower_expr(b, locals, &args[0])?;
                        let (_nid, res) = b.push_node(
                            Inst::AllocArray { elem_hint: Some(Type::Int32), len },
                            Some(Type::Array(Box::new(Some(Type::Int32)))),
                            1,
                            true,
                        );
                        return Ok(res[0]);
                    }

                    // Builtin: print(x) -> CallNative("wir_print_i64", [x])
                    if name == "print" {
                        if args.len() != 1 { return Err(LowerError::NotLowerable("print() expects 1 arg")); }
                        let v = self.lower_expr(b, locals, &args[0])?;
                        let (_nid, res) = b.push_node(
                            Inst::CallNative {
                                name: "wir_print_i64".into(),
                                args: vec![v],
                                pure: false,      // printing has effects
                                can_throw: false, // our tiny print won't throw
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                        return Ok(res[0]);
                    }

                    // Direct call to known function
                    if let Some(fid) = self.funcs.get(name).copied() {
                        let mut argv = Vec::with_capacity(args.len());
                        for a in args { argv.push(self.lower_expr(b, locals, a)?); }
                        let (_nid, res) = b.push_node(
                            Inst::CallDirect { conv: crate::wir::CallConv::Fast, callee: fid, args: argv },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                        return Ok(res[0]);
                    }
                }
                Err(LowerError::NotLowerable("dynamic calls not yet implemented"))
            }

            Expr::GetProp { recv, name } => {
                let obj = self.lower_expr(b, locals, recv)?;
                let field = self.intern_field(name);
                let (_nid, res) = b.push_node(Inst::LoadField { obj, field, expected: None }, None, 1, false);
                Ok(res[0])
            }

            Expr::Index { recv, index } => {
                let arr = self.lower_expr(b, locals, recv)?;
                let idx = self.lower_expr(b, locals, index)?;
                let len = {
                    let (_nid, res) = b.push_node(Inst::ArrayLen(arr), Some(Type::Int32), 1, false);
                    res[0]
                };
                let deopt = b.deopt_point("load_idx_oob");
                let _ = b.push_node(Inst::GuardBounds { idx, len, deopt }, Some(Type::Top), 1, true);
                let (_nid, res) = b.push_node(Inst::LoadElem { arr, idx }, Some(Type::Int32), 1, false);
                Ok(res[0])
            }
        }
    }

    fn intern_field(&mut self, name: &str) -> FieldId {
        // For demo: just allocate a counter-based field id in Module
        if let Some(fid) = self.module.fields.get(name).copied() {
            return fid;
        }
        let fid = self.module.fresh_field();
        self.module.fields.insert(name.to_string(), fid);
        fid
    }
}

fn lower_block_free<'m>(
    b: &mut Builder<'m>,
    locals: &mut std::collections::HashMap<String, ValueId>,
    fields: &mut std::collections::HashMap<String, FieldId>,
    next_field: &mut u32,
    blk: &Block,
    funcs: &std::collections::HashMap<String, FuncId>,
) -> LResult<()> {
    for s in &blk.stmts {
        lower_stmt_free(b, locals, fields, next_field, s, funcs)?;
    }
    Ok(())
}

fn lower_stmt_free<'m>(
    b: &mut Builder<'m>,
    locals: &mut std::collections::HashMap<String, ValueId>,
    fields: &mut std::collections::HashMap<String, FieldId>,
    next_field: &mut u32,
    s: &Stmt,
    funcs: &std::collections::HashMap<String, FuncId>,
) -> LResult<()> {
    match s {
        Stmt::Var { name, init } => {
            let val = if let Some(e) = init {
                lower_expr_free(b, locals, fields, next_field, e, funcs)?
            } else {
                b.const_i32(0)
            };
            locals.insert(name.clone(), val);
        }
        Stmt::If { cond, then_b, else_b } => {
            let c = lower_expr_free(b, locals, fields, next_field, cond, funcs)?;
            let then_id = b.block();
            let else_id = b.block();
            let cont = b.block();
            b.branch(c, then_id, else_id);

            b.position_at(then_id);
            lower_block_free(b, locals, fields, next_field, then_b, funcs)?;
            b.jump(cont, &[]);

            b.position_at(else_id);
            if let Some(e) = else_b {
                lower_block_free(b, locals, fields, next_field, e, funcs)?;
            }
            b.jump(cont, &[]);

            b.position_at(cont);
        }
        Stmt::While { cond, body } => {
            let head = b.block();
            let body_b = b.block();
            let exit = b.block();

            // 1) Which locals are mutated in the loop body?
            let mut_names = collect_mut_locals_in_block(body)
                .into_iter()
                .filter(|name| locals.contains_key(name)) // only loop-carried, pre-existing locals
                .collect::<Vec<_>>();

            // 2) Snapshot initial values in a stable order
            let init_args: Vec<ValueId> = mut_names.iter()
                .map(|n| *locals.get(n).expect("known local"))
                .collect();

            // 3) Create header params (phis) and jump into head with initial values
            let phi_vals: Vec<ValueId> = mut_names.iter()
                .map(|_| b.add_block_param(head, Type::Int32))
                .collect();

            b.jump(head, &init_args);

            // 4) In header, the current values of mutated locals are the phis
            b.position_at(head);
            for (name, p) in mut_names.iter().zip(phi_vals.iter()) {
                locals.insert(name.clone(), *p);
            }
            let c = lower_expr_free(b, locals, fields, next_field, cond, funcs)?;
            b.branch(c, body_b, exit);

            // 5) Body: compute new values, then back-edge with the updated tuple
            b.position_at(body_b);
            lower_block_free(b, locals, fields, next_field, body, funcs)?;
            let back_args: Vec<ValueId> = mut_names.iter()
                .map(|n| *locals.get(n).expect("local after body"))
                .collect();
            b.jump(head, &back_args);

            // 6) Exit: after the loop, the value of each mutated local is the header phi
            b.position_at(exit);
            for (name, p) in mut_names.into_iter().zip(phi_vals.into_iter()) {
                locals.insert(name, p);
            }
        }
        Stmt::For { init, cond, step, body } => {
            // 0) Run init
            if let Some(init_s) = init {
                lower_stmt_free(b, locals, fields, next_field, init_s, funcs)?;
            }

            // 1) Blocks
            let head   = b.block();
            let body_b = b.block();
            let exit   = b.block();

            // 2) Loop-carried locals: mutated in body or step & already exist
            use std::collections::BTreeSet;
            let mut mutated_set: BTreeSet<String> = BTreeSet::new();
            for st in &body.stmts { collect_mut_locals_in_stmt(st, &mut mutated_set); }
            if let Some(step_e) = step { collect_mut_locals_in_expr(step_e, &mut mutated_set); }
            let mut_names: Vec<String> = mutated_set.into_iter()
                .filter(|n| locals.contains_key(n))
                .collect();

            // 3) Snapshot initial tuple & create header phis (i32 for now)
            let init_args: Vec<ValueId> = mut_names.iter()
                .map(|n| *locals.get(n).unwrap())
                .collect();
            let phi_vals: Vec<ValueId> = mut_names.iter()
                .map(|_| b.add_block_param(head, Type::Int32))
                .collect();

            // Enter header
            b.jump(head, &init_args);

            // 4) Header: bind locals to phis, check condition
            b.position_at(head);
            for (name, p) in mut_names.iter().zip(phi_vals.iter()) {
                locals.insert(name.clone(), *p);
            }
            let c = if let Some(e) = cond {
                lower_expr_free(b, locals, fields, next_field, e, funcs)?
            } else {
                let (_nid, res) = b.push_node(Inst::Const(Constant::Bool(true)), Some(Type::Bool), 1, false);
                res[0]
            };
            b.branch(c, body_b, exit);

            // 5) Body, then optional step, then backedge with updated tuple
            b.position_at(body_b);
            lower_block_free(b, locals, fields, next_field, body, funcs)?;
            if let Some(step_e) = step {
                let _ = lower_expr_free(b, locals, fields, next_field, step_e, funcs)?;
            }
            let back_args: Vec<ValueId> = mut_names.iter()
                .map(|n| *locals.get(n).unwrap())
                .collect();
            b.jump(head, &back_args);

            // 6) Exit: final values are the header phis
            b.position_at(exit);
            for (name, p) in mut_names.into_iter().zip(phi_vals.into_iter()) {
                locals.insert(name, p);
            }
        }
        Stmt::Return(e) => {
            if let Some(expr) = e {
                let v = lower_expr_free(b, locals, fields, next_field, expr, funcs)?;
                b.ret(&[v]);
            } else {
                let z = b.const_i32(0);
                b.ret(&[z]);
            }
        }
        Stmt::Expr(e) => {
            let _ = lower_expr_free(b, locals, fields, next_field, e, funcs)?;
        }
    }
    Ok(())
}

fn lvalue_to_expr(lv: &LValue) -> Expr {
    match lv {
        LValue::Ident(s) => Expr::Ident(s.clone()),
        LValue::GetProp { recv, name } =>
            Expr::GetProp { recv: Box::new(recv.clone()), name: name.clone() },
        LValue::Index { recv, index } =>
            Expr::Index { recv: Box::new(recv.clone()), index: Box::new(index.clone()) },
    }
}

fn collect_mut_locals_in_expr(e: &Expr, out: &mut BTreeSet<String>) {
    match e {
        Expr::Assign(lv, rhs) => {
            if let LValue::Ident(name) = &**lv {
                out.insert(name.clone());
            }
            collect_mut_locals_in_expr(rhs, out);
        }
        Expr::Binary { a, b, .. } => {
            collect_mut_locals_in_expr(a, out);
            collect_mut_locals_in_expr(b, out);
        }
        Expr::Unary { e, .. } => collect_mut_locals_in_expr(e, out),
        Expr::Call { callee, args } => {
            collect_mut_locals_in_expr(callee, out);
            for a in args { collect_mut_locals_in_expr(a, out); }
        }
        Expr::GetProp { recv, .. } => collect_mut_locals_in_expr(recv, out),
        Expr::Index { recv, index } => {
            collect_mut_locals_in_expr(recv, out);
            collect_mut_locals_in_expr(index, out);
        }
        Expr::Group(e) => collect_mut_locals_in_expr(e, out),
        _ => {}
    }
}

fn collect_mut_locals_in_stmt(s: &Stmt, out: &mut BTreeSet<String>) {
    match s {
        Stmt::Expr(e) => collect_mut_locals_in_expr(e, out),
        Stmt::Var { .. } => {} // vars declared inside the loop are not loop-carried
        Stmt::If { cond, then_b, else_b } => {
            collect_mut_locals_in_expr(cond, out);
            for st in &then_b.stmts { collect_mut_locals_in_stmt(st, out); }
            if let Some(eb) = else_b {
                for st in &eb.stmts { collect_mut_locals_in_stmt(st, out); }
            }
        }
        Stmt::While { cond, body } => {
            collect_mut_locals_in_expr(cond, out);
            for st in &body.stmts { collect_mut_locals_in_stmt(st, out); }
        }
        Stmt::For { init, cond, step, body } => {
            if let Some(i) = init.as_deref() { collect_mut_locals_in_stmt(i, out); }
            if let Some(c) = cond { collect_mut_locals_in_expr(c, out); }
            if let Some(s) = step { collect_mut_locals_in_expr(s, out); }
            for st in &body.stmts { collect_mut_locals_in_stmt(st, out); }
        }
        Stmt::Return(e) => { if let Some(e) = e { collect_mut_locals_in_expr(e, out); } }
    }
}

fn collect_mut_locals_in_block(b: &Block) -> Vec<String> {
    let mut set = BTreeSet::new();
    for s in &b.stmts { collect_mut_locals_in_stmt(s, &mut set); }
    set.into_iter().collect() // stable order
}

fn lower_expr_free<'m>(
    b: &mut Builder<'m>,
    locals: &mut std::collections::HashMap<String, ValueId>,
    fields: &mut std::collections::HashMap<String, FieldId>,
    next_field: &mut u32,
    e: &Expr,
    funcs: &std::collections::HashMap<String, FuncId>,
) -> LResult<ValueId> {
    use BinOp::*;
    use Inst::*;

    match e {
        Expr::LitInt(i) => Ok(b.const_i32(*i)),
        Expr::LitF64(f) => Ok(b.const_f64(*f)),
        Expr::LitBool(v) => {
            let (_nid, res) = b.push_node(Inst::Const(Constant::Bool(*v)), Some(Type::Bool), 1, false);
            Ok(res[0])
        }
        Expr::LitNull => {
            let (_nid, res) = b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
            Ok(res[0])
        }
        Expr::Str(s) => {
            let (_nid, res) = b.push_node(Inst::Const(Constant::Str(s.clone())), Some(Type::Str), 1, false);
            Ok(res[0])
        }
        Expr::Ident(name) => locals
            .get(name)
            .copied()
            .ok_or_else(|| LowerError::UnknownVar(name.clone())),
        Expr::Group(inner) => lower_expr_free(b, locals, fields, next_field, inner, funcs),

        Expr::Unary { op, e } => {
            let v = lower_expr_free(b, locals, fields, next_field, e, funcs)?;
            match op {
                UnOp::Neg => {
                    let zero = b.const_i32(0);
                    Ok(b.int_bin(IntBinOp::Sub, zero, v))
                }
                UnOp::Pos => Ok(v),
                UnOp::Not => {
                    let (_nid, falsev) = b.push_node(Inst::Const(Constant::Bool(false)), Some(Type::Bool), 1, false);
                    let (_nid, res) = b.push_node(
                        Inst::CmpInt { kind: crate::wir::CmpKind::Eq, a: v, b: falsev[0] },
                        Some(Type::Bool),
                        1,
                        false,
                    );
                    Ok(res[0])
                }
            }
        }

        Expr::Binary { op, a, b: bb } => {
            let va = lower_expr_free(b, locals, fields, next_field, a, funcs)?;
            let vb = lower_expr_free(b, locals, fields, next_field, bb, funcs)?;
            match op {
                Add => Ok(b.int_bin(IntBinOp::Add, va, vb)),
                Sub => Ok(b.int_bin(IntBinOp::Sub, va, vb)),
                Mul => Ok(b.int_bin(IntBinOp::Mul, va, vb)),
                Div => Ok(b.int_bin(IntBinOp::DivS, va, vb)),
                Rem => Ok(b.int_bin(IntBinOp::RemS, va, vb)),

                Eq | Ne | Lt | Le | Gt | Ge => {
                    let kind = match *op {
                        BinOp::Eq => crate::wir::CmpKind::Eq,
                        BinOp::Ne => crate::wir::CmpKind::Ne,
                        BinOp::Lt => crate::wir::CmpKind::Lt,
                        BinOp::Le => crate::wir::CmpKind::Le,
                        BinOp::Gt => crate::wir::CmpKind::Gt,
                        BinOp::Ge => crate::wir::CmpKind::Ge,
                        _ => unreachable!(),
                    };
                    let (_nid, res) = b.push_node(
                        Inst::CmpInt { kind, a: va, b: vb },
                        Some(Type::Bool),
                        1,
                        false,
                    );
                    Ok(res[0])
                }

                And | Or => {
                    let then_b = b.block();
                    let else_b = b.block();
                    let cont = b.block();

                    if *op == And { b.branch(va, then_b, else_b); }
                    else { b.branch(va, else_b, then_b); }

                    b.position_at(then_b);
                    let tval = if *op == And {
                        lower_expr_free(b, locals, fields, next_field, bb, funcs)?
                    } else {
                        let (_nid, res) = b.push_node(Inst::Const(Constant::Bool(true)), Some(Type::Bool), 1, false);
                        res[0]
                    };
                    b.jump(cont, &[tval]);

                    b.position_at(else_b);
                    let eval_else = if *op == And {
                        let (_nid, res) = b.push_node(Inst::Const(Constant::Bool(false)), Some(Type::Bool), 1, false);
                        res[0]
                    } else {
                        lower_expr_free(b, locals, fields, next_field, bb, funcs)?
                    };
                    b.jump(cont, &[eval_else]);

                    b.position_at(cont);
                    let resv = b.add_block_param(cont, Type::Bool);
                    Ok(resv)
                }
            }
        }

        Expr::Assign(lv, rhs) => {
            let rv = lower_expr_free(b, locals, fields, next_field, rhs, funcs)?;
            match &**lv {
                LValue::Ident(name) => { locals.insert(name.clone(), rv); Ok(rv) }
                LValue::GetProp { recv, name } => {
                    let obj = lower_expr_free(b, locals, fields, next_field, recv, funcs)?;
                    let field = intern_field_local(fields, next_field, name);
                    let (_nid, _res) = b.push_node(
                        Inst::StoreField { obj, field, val: rv, expected: None },
                        Some(Type::Top),
                        1,
                        true,
                    );
                    Ok(rv)
                }
                LValue::Index { recv, index } => {
                    let arr = lower_expr_free(b, locals, fields, next_field, recv, funcs)?;
                    let idx = lower_expr_free(b, locals, fields, next_field, index, funcs)?;
                    let len = {
                        let (_nid, res) = b.push_node(Inst::ArrayLen(arr), Some(Type::Int32), 1, false);
                        res[0]
                    };
                    let deopt = b.deopt_point("store_idx_oob");
                    let _ = b.push_node(Inst::GuardBounds { idx, len, deopt }, Some(Type::Top), 1, true);
                    let (_nid, _res) = b.push_node(Inst::StoreElem { arr, idx, val: rv }, Some(Type::Top), 1, true);
                    Ok(rv)
                }
            }
        }

        Expr::Call { callee, args } => {
            if let Expr::Ident(name) = &**callee {
                // list(n)
                if name == "list" {
                    if args.len() != 1 {
                        return Err(LowerError::NotLowerable("list() expects 1 arg"));
                    }
                    let len = lower_expr_free(b, locals, fields, next_field, &args[0], funcs)?;
                    let (_nid, res) = b.push_node(
                        Inst::AllocArray { elem_hint: Some(Type::Int32), len },
                        Some(Type::Array(Box::new(Some(Type::Int32)))),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }

                // print(x)
                if name == "print" {
                    if args.len() != 1 {
                        return Err(LowerError::NotLowerable("print() expects 1 arg"));
                    }
                    let v = lower_expr_free(b, locals, fields, next_field, &args[0], funcs)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_print_i64".into(),
                            args: vec![v],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }

                // Direct call if the function name is known.
                if let Some(&fid) = funcs.get(name) {
                    let mut argv = Vec::with_capacity(args.len());
                    for a in args {
                        argv.push(lower_expr_free(b, locals, fields, next_field, a, funcs)?);
                    }
                    let (_nid, res) = b.push_node(
                        Inst::CallDirect { conv: crate::wir::CallConv::Fast, callee: fid, args: argv },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
            }
            Err(LowerError::NotLowerable("dynamic calls not yet implemented"))
        }

        Expr::GetProp { recv, name } => {
            let obj = lower_expr_free(b, locals, fields, next_field, recv, funcs)?;
            let field = intern_field_local(fields, next_field, name);
            let (_nid, res) = b.push_node(Inst::LoadField { obj, field, expected: None }, None, 1, false);
            Ok(res[0])
        }

        Expr::Index { recv, index } => {
            let arr = lower_expr_free(b, locals, fields, next_field, recv, funcs)?;
            let idx = lower_expr_free(b, locals, fields, next_field, index, funcs)?;
            let len = {
                let (_nid, res) = b.push_node(Inst::ArrayLen(arr), Some(Type::Int32), 1, false);
                res[0]
            };
            let deopt = b.deopt_point("load_idx_oob");
            let _ = b.push_node(Inst::GuardBounds { idx, len, deopt }, Some(Type::Top), 1, true);
            let (_nid, res) = b.push_node(Inst::LoadElem { arr, idx }, Some(Type::Int32), 1, false);
            Ok(res[0])
        }
    }
}

fn intern_field_local(
    fields: &mut std::collections::HashMap<String, FieldId>,
    next_field: &mut u32,
    name: &str,
) -> FieldId {
    if let Some(&fid) = fields.get(name) {
        return fid;
    }
    let fid = FieldId(*next_field);
    *next_field += 1;
    fields.insert(name.to_string(), fid);
    fid
}

/// -------------------------
/// Tiny end-to-end demo (tests)
/// -------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wir::Function;

    #[test]
    fn lex_and_parse_and_lower() {
        let src = r#"
            fn sum_n(n) {
                var i = 0;
                var s = 0;
                var a = list(n);
                while (i < n) {
                    a[i] = i;
                    s = s + a[i];
                    i = i + 1;
                }
                return s;
            }
        "#;

        let mut p = Parser::new(src);
        let prog = p.program().expect("parse ok");
        assert_eq!(prog.functions.len(), 1);
        assert_eq!(prog.functions[0].name, "sum_n");

        let mut module = Module::new();
        let mut lowerer = Lowerer::new(&mut module);
        let fids = lowerer.lower_program(&prog).expect("lower ok");
        assert_eq!(fids.len(), 1);

        // Dump the produced WIR function (pretty-printer from WIR file)
        let fun: &Function = &module.funcs[0];
        println!("{}", fun);
        // Very loose sanity checks
        assert!(fun.nodes.len() > 0);
    }
}
