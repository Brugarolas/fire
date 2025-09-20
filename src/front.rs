// src/front.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

use logos::Logos;
use std::{collections::BTreeSet, ops::Deref};
use ahash::{AHashSet as HashSet, AHashMap as HashMap};
use std::collections::hash_map::Entry;
use smallbox::SmallBox;

// Bring in the WIR types from your other file/module.
use crate::wir::{
    Builder, Constant, FieldId, FuncId, Inst, IntBinOp, Module, Type, ValueId,
    MethodInfo, AccessorInfo, BindingId,
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
    #[token("function")] Function,
    #[token("var")] Var,
    #[token("let")] Let,
    #[token("const")] Const,
    #[token("if")] If,
    #[token("unless")] Unless,
    #[token("else")] Else,
    #[token("while")] While,
    #[token("for")] For,
    #[token("return")] Return,
    #[token("true")] True,
    #[token("false")] False,
    #[token("null")] Null,
    #[token("in")] In,
    #[token("delete")] Delete,

    // Class support
    #[token("class")] Class,
    #[token("extends")] Extends,
    #[token("static")] Static,
    #[token("constructor")] Constructor,
    #[token("destructor")] Destructor,
    #[token("get")] Get,
    #[token("set")] Set,
    #[token("new")] New,
    #[token("this")] This,
    #[token("super")] Super,

    // Async/await & defer/errdefer
    #[token("async")] Async,
    #[token("await")] Await,
    #[token("defer")] Defer,
    #[token("errdefer")] ErrDefer,

    // Import/export
    #[token("import")] Import,
    #[token("export")] Export,
    #[token("from")] From,
    #[token("as")] As,

    // Simple builtins
    #[token("Array")] ListBuiltin,
    #[token("Promise")] PromiseBuiltin,
    #[token("Deferred")] DeferredBuiltin,

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
    #[token("|")] Pipe,
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
    #[token(":")] Colon,
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
    pub classes:   Vec<ClassDecl>,
    pub imports:   Vec<ImportDecl>,
    pub exports:   Vec<ExportDecl>,
}

#[derive(Debug, Clone)]
pub struct ClassDecl {
    pub name: String,
    pub base: Option<String>,        // name after `extends`
    pub members: Vec<ClassMember>,
}

#[derive(Debug, Clone)]
pub enum ClassMember {
    // `var name [ : Type ] [= init]? ;`   (instance or static)
    Stored {
        is_static: bool,
        name: String,
        type_ann: Option<String>,    // parsed after ':', kept as raw for now
        init: Option<Expr>,          // optional initializer
    },

    // `var name { get(){...} set(x){...} }` (either/both accessors; instance or static)
    Accessor {
        is_static: bool,
        name: String,
        getter: Option<Block>,       // body of `get()`
        setter_param: Option<String>,
        setter_body: Option<Block>,  // body of `set(param)`
    },

    // `fn name(params) { ... }`     (instance)   or  `static fn name(...) { ... }`
    Method {
        is_static: bool,
        name: String,
        params: Vec<String>,
        body: Block,
        is_async: bool,
    },

    // `constructor(params) { ... }`
    Constructor {
        params: Vec<String>,
        body: Block,
        is_async: bool,              // allow `async constructor` now or later
    },

    // `destructor() { ... }`
    Destructor {
        body: Block,
    },
}

#[derive(Debug, Clone)]
pub struct FuncDecl {
    pub name: String,
    pub params: Vec<String>,
    pub body: Block,
    pub is_async: bool,
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
    For { init: Option<SmallBox<Stmt, u8>>, cond: Option<Expr>, step: Option<Expr>, body: Block },
    Return(Option<Expr>),
    Expr(Expr),
    Listen(ListenDecl),
}

#[derive(Debug, Clone)]
pub enum PropKey {
    Ident(String),  // identifier property name (interned later)
    Str(String),    // string-literal property name
}

#[derive(Debug, Clone)]
pub enum Expr {
    LitInt(i32),
    LitF64(f64),
    LitBool(bool),
    LitNull,
    Str(String),
    Ident(String),

    Assign(SmallBox<LValue, u8>, SmallBox<Expr, u8>),
    Binary { op: BinOp, a: SmallBox<Expr, u8>, b: SmallBox<Expr, u8> },
    Unary { op: UnOp, e: SmallBox<Expr, u8> },
    Call { callee: SmallBox<Expr, u8>, args: Vec<Expr> },

    GetProp { recv: SmallBox<Expr, u8>, name: String },
    Index { recv: SmallBox<Expr, u8>, index: SmallBox<Expr, u8> },
    Group(SmallBox<Expr, u8>),
    FnLit { params: Vec<String>, body: Block },
    FnRef { name: String },
    ArrayLit(Vec<Expr>),

    This,                                   // `this`
    SuperProp(String),                      // `super.m`
    SuperCall(Vec<Expr>),                   // `super(args...)` (only valid in derived ctor)
    New { class: String, args: Vec<Expr> }, // `new ClassName(args...)`

    ObjLit(Vec<(PropKey, Expr)>),                                                    // { a: 1, "b": 2, c: x+y }
    GetPropObj { obj: SmallBox<Expr, u8>, key: PropKey },                            // obj.x   or   obj["x"]
    SetPropObj { obj: SmallBox<Expr, u8>, key: PropKey, value: SmallBox<Expr, u8> }, // obj.x = value   or   obj["x"] = value
    In { key: SmallBox<Expr, u8>, obj: SmallBox<Expr, u8> },                         // "<key>" in obj
    DeleteProp { obj: SmallBox<Expr, u8>, key: PropKey },                            // delete obj.x / delete obj["x"]

    Await(SmallBox<Expr, u8>) // await <expression>
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Private,
}

#[derive(Debug, Clone)]
pub enum SuperRef {
    // super(...) in a constructor
    Ctor(Vec<Expr>),
    // (add more variants later if we need them)
}

#[derive(Debug, Clone)]
pub enum NewTarget {
    // new Ident(args...)
    Ident(String),
    // (add more variants later if we need them)
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

#[derive(Debug, Clone)]
pub enum ImportItem {
    // import { name } from ...
    // import { name as alias } from ...
    Named { name: String, alias: Option<String> },

    // import * as ns from ...
    Namespace { alias: String },
}

#[derive(Debug, Clone)]
pub struct ImportDecl {
    pub specifier: String,          // "./math", "../lib/util", etc.
    pub items: Vec<ImportItem>,     // vacío => import "path"; (solo efectos)
}

#[derive(Debug, Clone)]
pub enum ExportDecl {
    // export { a, b as c };
    Named { items: Vec<(String, Option<String>)> },

    // export { a, b as c } from "path";
    From  { specifier: String, items: Vec<(String, Option<String>)> },

    // export * from "path";
    AllFrom { specifier: String },

    // export var/let / fn / class (referencia al símbolo local exportado)
    Var(String),
    Func(String),
    Class(String),
}

#[derive(Debug, Clone)]
pub struct ListenDecl {
    pub addr: String,
    pub routes: Vec<RouteDecl>,
}

#[derive(Debug, Clone)]
pub struct RouteDecl {
    pub method: String,  // e.g. "GET"
    pub pattern: Expr,   // we store it as an Expr (usually ArrayLit of strings)
    pub handler: Expr,   // a FnLit / hoisted FnRef
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

    #[inline(always)]
    fn peek(&self) -> &SpannedTok {
        // Caller only uses this when self.i < toks.len(); we keep it simple.
        &self.toks[self.i]
    }

    #[inline(always)]
    fn next(&mut self) -> SpannedTok {
        let t = self.toks[self.i].clone();
        self.i += 1;
        t
    }

    #[inline(always)]
    fn check(&self, t: &Tok) -> bool {
        &self.peek().tok == t
    }

    #[inline(always)]
    fn matches(&mut self, t: &Tok) -> bool {
        if self.check(t) {
            self.i += 1;
            true
        } else {
            false
        }
    }

    #[inline(always)]
    fn expect(&mut self, t: Tok, msg: &str) -> PResult<()> {
        if self.peek().tok == t {
            self.i += 1;
            Ok(())
        } else {
            Err(self.err_here(msg))
        }
    }

    #[inline(always)]
    fn err_here(&self, msg: &str) -> ParseError {
        ParseError { msg: msg.into(), span: self.peek().span.clone() }
    }

    #[inline(always)]
    fn is_eof(&self) -> bool {
        self.i >= self.toks.len()
    }

    #[inline(always)]
    fn check_ident(&self, s: &str) -> bool {
        matches!(&self.peek().tok, Tok::Ident(name) if name == s)
    }

    #[inline(always)]
    fn matches_ident(&mut self, s: &str) -> bool {
        if self.check_ident(s) { self.i += 1; true } else { false }
    }

    pub fn program(&mut self) -> PResult<Program> {
        let mut functions  = Vec::new();
        let mut classes   = Vec::new();
        let mut toplevel_stmts: Vec<Stmt> = Vec::new();

        let mut imports = Vec::new();
        let mut exports = Vec::new();

        while self.i < self.toks.len() {
            if self.matches(&Tok::Semi) { continue; }

            if self.check(&Tok::Import) {
                imports.push(self.parse_import_decl()?);
            } else if self.check(&Tok::Export) {
                self.next(); // consume 'export'
                self.parse_export_decl(&mut functions, &mut classes, &mut toplevel_stmts, &mut exports)?;
            } else if self.check(&Tok::Class) {
                classes.push(self.class_decl()?);
            } else if self.check(&Tok::Fn) || self.check(&Tok::Function) || self.check(&Tok::Async) {
                let is_async = if self.matches(&Tok::Async) {
                    self.expect(Tok::Fn, "expected 'fn'/'function' after 'async'")?;
                    true
                } else {
                    self.i += 1; // consume Fn
                    false
                };
                functions.push(self.fn_def_with_async(is_async)?);
            } else {
                let stmt = self.stmt()?;
                toplevel_stmts.push(stmt);
            }
        }

        if !toplevel_stmts.is_empty() {
            functions.push(FuncDecl {
                name: "__toplevel__".to_string(),
                params: Vec::new(),
                body: Block { stmts: toplevel_stmts },
                is_async: true, // Allows top-level async
            });
        }

        Ok(Program { functions, classes, imports, exports })
    }

    fn class_decl(&mut self) -> PResult<ClassDecl> {
        self.expect(Tok::Class, "expected 'class'")?;
        let name = match self.next().tok {
            Tok::Ident(s) => s,
            _ => return Err(self.err_here("expected class name")),
        };

        let base = if self.matches(&Tok::Extends) {
            match self.next().tok {
                Tok::Ident(s) => Some(s),
                _ => return Err(self.err_here("expected base class name after 'extends'")),
            }
        } else { None };

        self.expect(Tok::LBrace, "expected '{' after class header")?;
        let mut members = Vec::new();
        while !self.matches(&Tok::RBrace) {
            members.push(self.class_member()?);
        }

        Ok(ClassDecl { name, base, members })
    }

    fn class_member(&mut self) -> PResult<ClassMember> {
        // optional `static`
        let is_static = self.matches(&Tok::Static);

        // constructor
        if self.matches(&Tok::Constructor) {
            let params = self.parse_fn_param_names()?;
            let body   = self.block()?;
            return Ok(ClassMember::Constructor { params, body, is_async: false });
        }

        // destructor
        if self.matches(&Tok::Destructor) {
            let body = self.block()?;
            return Ok(ClassMember::Destructor { body });
        }

        // stored field: var name [: Type]? (= expr)? ;
        if self.matches(&Tok::Var) {
            let name = match self.next().tok {
                Tok::Ident(s) => s,
                _ => return Err(self.err_here("expected field name after 'var'")),
            };

            // ignore optional type annotation for now
            let _ = self.maybe_skip_type_annot()?;

            let init = if self.matches(&Tok::Eq) { Some(self.expr()?) } else { None };
            self.expect(Tok::Semi, "expected ';' after field")?;
            return Ok(ClassMember::Stored {
                is_static,
                name,
                type_ann: None,
                init,
            });
        }

        // accessors: get name() { ... }  |  set name(param) { ... }
        if self.matches(&Tok::Get) {
            let name = match self.next().tok {
                Tok::Ident(s) => s,
                _ => return Err(self.err_here("expected property name after 'get'")),
            };
            self.expect(Tok::LParen, "expected '(' after getter name")?;
            self.expect(Tok::RParen, "expected ')' after getter params")?;
            let getter = self.block()?;
            return Ok(ClassMember::Accessor {
                is_static,
                name,
                getter: Some(getter),
                setter_param: None,
                setter_body: None,
            });
        }
        if self.matches(&Tok::Set) {
            let name = match self.next().tok {
                Tok::Ident(s) => s,
                _ => return Err(self.err_here("expected property name after 'set'")),
            };
            self.expect(Tok::LParen, "expected '(' after setter name")?;
            let param = match self.next().tok {
                Tok::Ident(s) => s,
                _ => return Err(self.err_here("expected setter parameter name")),
            };
            self.expect(Tok::RParen, "expected ')' after setter parameter")?;
            let body = self.block()?;
            return Ok(ClassMember::Accessor {
                is_static,
                name,
                getter: None,
                setter_param: Some(param),
                setter_body: Some(body),
            });
        }

        // methods: [static] [async] [fn|function]? Ident(params) { block }
        // Accept JS-style methods without the `fn` keyword.
        let is_async = if self.matches(&Tok::Async) { true } else { false };

        // Optional `fn` / `function` keyword (ignored if present)
        let _ = self.matches(&Tok::Fn) || self.matches(&Tok::Function);

        // Method name
        let name = match self.next().tok {
            Tok::Ident(s) => s,
            _ => return Err(self.err_here("expected method name")),
        };

        self.expect(Tok::LParen, "expected '(' after method name")?;
        let params = self.parse_param_list()?;
        let body = self.block()?;

        Ok(ClassMember::Method { is_static, name, params, body, is_async })
    }

    fn maybe_skip_type_annot(&mut self) -> PResult<()> {
        // Allow and ignore: : Ident [.<Ident>]*  (super minimal)
        if self.matches(&Tok::Colon) {
            // eat at least one token of the type
            match &self.peek().tok {
                Tok::Ident(_) => { self.i += 1; }
                _ => {}
            }
            // consume any dotted qualifiers (rough)
            while self.matches(&Tok::Dot) {
                if matches!(&self.peek().tok, Tok::Ident(_)) { self.i += 1; }
                else { break; }
            }
        }
        Ok(())
    }

    fn parse_import_decl(&mut self) -> PResult<ImportDecl> {
        self.expect(Tok::Import, "expected 'import'")?;

        // 1) import "path";
        if let Tok::Str(spec) = self.peek().tok.clone() {
            let _ = self.next();
            self.expect(Tok::Semi, "expected ';' after import")?;
            return Ok(ImportDecl { specifier: spec, items: vec![] });
        }

        // 2) import * as ns from "path";
        if self.matches(&Tok::Star) {
            self.expect(Tok::As, "expected 'as' after '*'")?;
            let alias = match self.next().tok {
                Tok::Ident(s) => s,
                _ => return Err(self.err_here("expected identifier after 'as'")),
            };
            self.expect(Tok::From, "expected 'from'")?;
            let spec = match self.next().tok {
                Tok::Str(s) => s,
                _ => return Err(self.err_here("expected string literal after 'from'")),
            };
            self.expect(Tok::Semi, "expected ';' after import")?;
            return Ok(ImportDecl { specifier: spec, items: vec![ImportItem::Namespace { alias }] });
        }

        // 3) import { a, b as c } from "path";
        self.expect(Tok::LBrace, "expected '{' after 'import'")?;
        let mut items = Vec::new();
        if !self.matches(&Tok::RBrace) {
            loop {
                let name = match self.next().tok {
                    Tok::Ident(s) => s,
                    _ => return Err(self.err_here("expected imported name")),
                };
                let alias = if self.matches(&Tok::As) {
                    match self.next().tok {
                        Tok::Ident(s) => Some(s),
                        _ => return Err(self.err_here("expected alias name after 'as'")),
                    }
                } else { None };
                items.push(ImportItem::Named { name, alias });
                if self.matches(&Tok::RBrace) { break; }
                self.expect(Tok::Comma, "expected ',' in import list")?;
            }
        }
        self.expect(Tok::From, "expected 'from' after import list")?;
        let spec = match self.next().tok {
            Tok::Str(s) => s,
            _ => return Err(self.err_here("expected string literal after 'from'")),
        };
        self.expect(Tok::Semi, "expected ';' after import")?;
        Ok(ImportDecl { specifier: spec, items })
    }

    fn parse_export_decl(
        &mut self,
        functions: &mut Vec<FuncDecl>,
        classes:   &mut Vec<ClassDecl>,
        toplevel:  &mut Vec<Stmt>,
        exports:   &mut Vec<ExportDecl>,
    ) -> PResult<()> {
        // export fn / export async fn
        if self.check(&Tok::Async) || self.check(&Tok::Fn) {
            let is_async = if self.matches(&Tok::Async) {
                self.expect(Tok::Fn, "expected 'fn' after 'async'")?;
                true
            } else {
                self.expect(Tok::Fn, "expected 'fn' after 'export'")?;
                false
            };
            let f = self.fn_def_with_async(is_async)?;
            exports.push(ExportDecl::Func(f.name.clone()));
            functions.push(f);
            return Ok(());
        }

        // export function / export async function
        if self.check(&Tok::Async) || self.check(&Tok::Function) {
            let is_async = if self.matches(&Tok::Async) {
                self.expect(Tok::Function, "expected 'function' after 'async'")?;
                true
            } else {
                self.expect(Tok::Function, "expected 'function' after 'export'")?;
                false
            };
            let f = self.fn_def_with_async(is_async)?;
            exports.push(ExportDecl::Func(f.name.clone()));
            functions.push(f);
            return Ok(());
        }

        // export class ...
        if self.check(&Tok::Class) {
            let c = self.class_decl()?;
            exports.push(ExportDecl::Class(c.name.clone()));
            classes.push(c);
            return Ok(());
        }

        // export var/let X = ... ;
        if self.matches(&Tok::Var) || self.matches(&Tok::Let) || self.matches(&Tok::Const) {
            let name = match self.next().tok {
                Tok::Ident(s) => s,
                _ => return Err(self.err_here("expected identifier after 'export var/let'")),
            };
            let init = if self.matches(&Tok::Eq) { Some(self.expr()?) } else { None };
            self.expect(Tok::Semi, "expected ';' after export var/let")?;
            toplevel.push(Stmt::Var { name: name.clone(), init });
            exports.push(ExportDecl::Var(name));
            return Ok(());
        }

        // export * from "path";
        if self.matches(&Tok::Star) {
            self.expect(Tok::From, "expected 'from'")?;
            let spec = match self.next().tok {
                Tok::Str(s) => s,
                _ => return Err(self.err_here("expected string literal after 'from'")),
            };
            self.expect(Tok::Semi, "expected ';' after export")?;
            exports.push(ExportDecl::AllFrom { specifier: spec });
            return Ok(());
        }

        // export { a, b as c } [from "path"] ;
        if self.matches(&Tok::LBrace) {
            let mut items: Vec<(String, Option<String>)> = Vec::new();
            if !self.matches(&Tok::RBrace) {
                loop {
                    let name = match self.next().tok {
                        Tok::Ident(s) => s,
                        _ => return Err(self.err_here("expected exported name")),
                    };
                    let alias = if self.matches(&Tok::As) {
                        match self.next().tok {
                            Tok::Ident(s) => Some(s),
                            _ => return Err(self.err_here("expected alias name after 'as'")),
                        }
                    } else { None };
                    items.push((name, alias));
                    if self.matches(&Tok::RBrace) { break; }
                    self.expect(Tok::Comma, "expected ',' in export list")?;
                }
            }
            if self.matches(&Tok::From) {
                let spec = match self.next().tok {
                    Tok::Str(s) => s,
                    _ => return Err(self.err_here("expected string literal after 'from'")),
                };
                self.expect(Tok::Semi, "expected ';' after export")?;
                exports.push(ExportDecl::From { specifier: spec, items });
            } else {
                self.expect(Tok::Semi, "expected ';' after export list")?;
                exports.push(ExportDecl::Named { items });
            }
            return Ok(());
        }

        Err(self.err_here("invalid export form"))
    }

    fn parse_fn_param_names(&mut self) -> PResult<Vec<String>> {
        self.expect(Tok::LParen, "expected '('")?;
        self.parse_param_list()
    }

    fn parse_method_tail(&mut self) -> PResult<(String, Vec<String>, Block)> {
        let name = match self.next().tok {
            Tok::Ident(s) => s,
            _ => return Err(self.err_here("expected method name")),
        };
        self.expect(Tok::LParen, "expected '(' after method name")?;
        let params = self.parse_param_list()?;
        let body = self.block()?;
        Ok((name, params, body))
    }

    fn fn_def_with_async(&mut self, is_async: bool) -> PResult<FuncDecl> {
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
        Ok(FuncDecl { name, params, body, is_async })
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

    fn parse_param_list(&mut self) -> PResult<Vec<String>> {
        let mut params = Vec::new();
        if !self.matches(&Tok::RParen) {
            loop {
                let name = match self.next().tok {
                    Tok::Ident(s) => s,
                    _ => return Err(self.err_here("expected parameter name")),
                };
                params.push(name);
                if self.matches(&Tok::RParen) { break; }
                self.expect(Tok::Comma, "expected ',' in parameter list")?;
            }
        }
        Ok(params)
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        // Allow empty statements (`;`) anywhere a statement is expected
        // (including top level). Treat as a no-op expression stmt.
        if self.matches(&Tok::Semi) {
            return Ok(Stmt::Expr(Expr::LitInt(0)));
        }

        if self.check_ident("listen") {
            return self.parse_listen_stmt();
        }

        if self.matches(&Tok::Var) || self.matches(&Tok::Let) || self.matches(&Tok::Const) {
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

            // else { … } | else if (…) { … } | else unless (…) { … }
            let else_b = if self.matches(&Tok::Else) {
                if self.matches(&Tok::If) || self.matches(&Tok::Unless) {
                    // Was it "else unless"?
                    let negated = if self.toks[self.i - 1].tok == Tok::Unless { true } else { false };

                    self.expect(Tok::LParen, "expected '('")?;
                    let mut cond2 = self.expr()?;
                    self.expect(Tok::RParen, "expected ')'")?;
                    if negated {
                        cond2 = Expr::Unary { op: UnOp::Not, e: SmallBox::new(cond2) };
                    }
                    let then2 = self.block()?;

                    // Optional trailing else after the else-if/unless chain
                    let tail_else = if self.matches(&Tok::Else) {
                        Some(self.block()?)
                    } else {
                        None
                    };

                    // Desugar into: else { if (cond2) then2 else tail_else }
                    Some(Block {
                        stmts: vec![Stmt::If { cond: cond2, then_b: then2, else_b: tail_else }]
                    })
                } else {
                    // Plain "else { … }"
                    Some(self.block()?)
                }
            } else {
                None
            };

            Ok(Stmt::If { cond, then_b, else_b })
        } else if self.matches(&Tok::Unless) {
            // unless (cond) { then } [ else { ... } | else if (...) { ... } | else unless (...) { ... } ]
            self.expect(Tok::LParen, "expected '('")?;
            let cond0 = self.expr()?;
            self.expect(Tok::RParen, "expected ')'")?;
            let cond = Expr::Unary { op: UnOp::Not, e: SmallBox::new(cond0) };
            let then_b = self.block()?;

            // else { … } | else if (…) { … } | else unless (…) { … }
            let else_b = if self.matches(&Tok::Else) {
                // “else if …” or “else unless …”
                if self.matches(&Tok::If) || self.matches(&Tok::Unless) {
                    let was_unless = matches!(self.toks[self.i - 1].tok, Tok::Unless);
                    self.expect(Tok::LParen, "expected '('")?;
                    let mut cond2 = self.expr()?;
                    self.expect(Tok::RParen, "expected ')'")?;
                    if was_unless {
                        cond2 = Expr::Unary { op: UnOp::Not, e: SmallBox::new(cond2) };
                    }
                    let then2 = self.block()?;

                    // Optional trailing else after the else-if/unless
                    let tail_else = if self.matches(&Tok::Else) {
                        Some(self.block()?)
                    } else {
                        None
                    };

                    // Desugar into: else { if (cond2) then2 else tail_else }
                    Some(Block {
                        stmts: vec![Stmt::If { cond: cond2, then_b: then2, else_b: tail_else }],
                    })
                } else {
                    // Plain "else { … }"
                    Some(self.block()?)
                }
            } else {
                None
            };

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
                Some(SmallBox::new(Stmt::Var { name, init: init_e }))
            } else {
                let e = self.expr()?;
                self.expect(Tok::Semi, "expected ';' after init")?;
                Some(SmallBox::new(Stmt::Expr(e)))
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
                Expr::Ident(s) => LValue::Ident(s),
                Expr::GetProp { recv, name } => {
                    let recv_expr = (*recv).clone();         // or: recv.as_ref().clone()
                    LValue::GetProp { recv: recv_expr, name }
                }
                Expr::Index { recv, index } => {
                    let recv_expr  = (*recv).clone();
                    let index_expr = (*index).clone();
                    LValue::Index { recv: recv_expr, index: index_expr }
                }
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
                    a: SmallBox::new(lvalue_to_expr(&lv)),
                    b: SmallBox::new(rhs),
                }
            };

            Ok(Expr::Assign(SmallBox::new(lv), SmallBox::new(final_rhs)))
        } else {
            Ok(left)
        }
    }

    fn parse_or(&mut self) -> PResult<Expr> {
        let mut e = self.parse_and()?;
        while self.matches(&Tok::OrOr) {
            let rhs = self.parse_and()?;
            e = Expr::Binary { op: BinOp::Or, a: SmallBox::new(e), b: SmallBox::new(rhs) };
        }
        Ok(e)
    }
    fn parse_and(&mut self) -> PResult<Expr> {
        let mut e = self.parse_eq()?;
        while self.matches(&Tok::AndAnd) {
            let rhs = self.parse_eq()?;
            e = Expr::Binary { op: BinOp::And, a: SmallBox::new(e), b: SmallBox::new(rhs) };
        }
        Ok(e)
    }
    fn parse_eq(&mut self) -> PResult<Expr> {
        let mut e = self.parse_cmp()?;
        loop {
            if self.matches(&Tok::EqEq) {
                let rhs = self.parse_cmp()?;
                e = Expr::Binary { op: BinOp::Eq, a: SmallBox::new(e), b: SmallBox::new(rhs) };
            } else if self.matches(&Tok::BangEq) {
                let rhs = self.parse_cmp()?;
                e = Expr::Binary { op: BinOp::Ne, a: SmallBox::new(e), b: SmallBox::new(rhs) };
            } else { break; }
        }
        Ok(e)
    }
    fn parse_cmp(&mut self) -> PResult<Expr> {
        let mut e = self.parse_term()?;
        loop {
            if self.matches(&Tok::Lt) {
                let rhs = self.parse_term()?;
                e = Expr::Binary { op: BinOp::Lt, a: SmallBox::new(e), b: SmallBox::new(rhs) };
            } else if self.matches(&Tok::LtEq) {
                let rhs = self.parse_term()?;
                e = Expr::Binary { op: BinOp::Le, a: SmallBox::new(e), b: SmallBox::new(rhs) };
            } else if self.matches(&Tok::Gt) {
                let rhs = self.parse_term()?;
                e = Expr::Binary { op: BinOp::Gt, a: SmallBox::new(e), b: SmallBox::new(rhs) };
            } else if self.matches(&Tok::GtEq) {
                let rhs = self.parse_term()?;
                e = Expr::Binary { op: BinOp::Ge, a: SmallBox::new(e), b: SmallBox::new(rhs) };
            } else if self.matches(&Tok::In) {
                let rhs = self.parse_term()?;
                // left "in" right → Expr::In { key: left, obj: right }
                e = Expr::In { key: SmallBox::new(e), obj: SmallBox::new(rhs) };
            } else {
                break;
            }
        }
        Ok(e)
    }
    fn parse_term(&mut self) -> PResult<Expr> {
        let mut e = self.parse_factor()?;
        loop {
            if self.matches(&Tok::Plus) {
                let rhs = self.parse_factor()?;
                e = Expr::Binary { op: BinOp::Add, a: SmallBox::new(e), b: SmallBox::new(rhs) };
            } else if self.matches(&Tok::Minus) {
                let rhs = self.parse_factor()?;
                e = Expr::Binary { op: BinOp::Sub, a: SmallBox::new(e), b: SmallBox::new(rhs) };
            } else { break; }
        }
        Ok(e)
    }
    fn parse_factor(&mut self) -> PResult<Expr> {
        let mut e = self.parse_unary()?;
        loop {
            if self.matches(&Tok::Star) {
                let rhs = self.parse_unary()?;
                e = Expr::Binary { op: BinOp::Mul, a: SmallBox::new(e), b: SmallBox::new(rhs) };
            } else if self.matches(&Tok::Slash) {
                let rhs = self.parse_unary()?;
                e = Expr::Binary { op: BinOp::Div, a: SmallBox::new(e), b: SmallBox::new(rhs) };
            } else if self.matches(&Tok::Percent) {
                let rhs = self.parse_unary()?;
                e = Expr::Binary { op: BinOp::Rem, a: SmallBox::new(e), b: SmallBox::new(rhs) };
            } else { break; }
        }
        Ok(e)
    }
    fn parse_unary(&mut self) -> PResult<Expr> {
        if self.matches(&Tok::Await) {
            // await <unary>
            let e = self.parse_unary()?;
            return Ok(Expr::Await(SmallBox::new(e)));
        } if self.matches(&Tok::Bang) {
            let e = self.parse_unary()?;
            Ok(Expr::Unary { op: UnOp::Not, e: SmallBox::new(e) })
        } else if self.matches(&Tok::Minus) {
            let e = self.parse_unary()?;
            Ok(Expr::Unary { op: UnOp::Neg, e: SmallBox::new(e) })
        } else if self.matches(&Tok::Plus) {
            let e = self.parse_unary()?;
            Ok(Expr::Unary { op: UnOp::Pos, e: SmallBox::new(e) })
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
                e = Expr::Call { callee: SmallBox::new(e), args };
            } else if self.matches(&Tok::Dot) {
                let name = match self.next().tok {
                    Tok::Ident(s) => s,
                    _ => return Err(self.err_here("expected identifier after '.'")),
                };
                e = Expr::GetProp { recv: SmallBox::new(e), name };
            } else if self.matches(&Tok::LBracket) {
                let idx = self.expr()?;
                self.expect(Tok::RBracket, "expected ']'")?;
                e = Expr::Index { recv: SmallBox::new(e), index: SmallBox::new(idx) };
            } else {
                break;
            }
        }
        Ok(e)
    }
    fn parse_primary(&mut self) -> PResult<Expr> {
        let t = self.next();
        match t.tok {
            Tok::This  => Ok(Expr::This),

            Tok::Super => {
                if self.check(&Tok::LParen) {
                    // super(...)
                    self.i += 1; // consume '('
                    let mut args = Vec::new();
                    if !self.matches(&Tok::RParen) {
                        loop {
                            args.push(self.expr()?);
                            if self.matches(&Tok::RParen) { break; }
                            self.expect(Tok::Comma, "expected ',' in super(...)")?;
                        }
                    }
                    Ok(Expr::SuperCall(args))
                } else if self.matches(&Tok::Dot) {
                    // super.name
                    let name = match self.next().tok {
                        Tok::Ident(s) => s,
                        _ => return Err(self.err_here("expected identifier after 'super.'")),
                    };
                    Ok(Expr::SuperProp(name))
                } else {
                    Err(self.err_here("`super` must be used as `super(...)` or `super.name`"))
                }
            }

            Tok::New => {
                // new <Ident>(args...)
                let class = match self.next().tok {
                    Tok::Ident(s) => s,
                    _ => return Err(self.err_here("expected class name after 'new'")),
                };
                self.expect(Tok::LParen, "expected '(' after class name")?;
                let mut args = Vec::new();
                if !self.matches(&Tok::RParen) {
                    loop {
                        args.push(self.expr()?);
                        if self.matches(&Tok::RParen) { break; }
                        self.expect(Tok::Comma, "expected ',' in argument list")?;
                    }
                }
                Ok(Expr::New { class, args })
            }

            Tok::Int(x) => Ok(Expr::LitInt(x)),
            Tok::Float(x) => Ok(Expr::LitF64(x)),
            Tok::True => Ok(Expr::LitBool(true)),
            Tok::False => Ok(Expr::LitBool(false)),
            Tok::Null => Ok(Expr::LitNull),
            Tok::Str(s) => Ok(Expr::Str(s)),
            Tok::Ident(s) => Ok(Expr::Ident(s)),
            Tok::ListBuiltin => Ok(Expr::Ident("Array".into())),
            Tok::PromiseBuiltin => Ok(Expr::Ident("Promise".into())),
            Tok::DeferredBuiltin => Ok(Expr::Ident("Deferred".into())),
            Tok::LParen => {
                let e = self.expr()?;
                self.expect(Tok::RParen, "expected ')'")?;
                Ok(Expr::Group(SmallBox::new(e)))
            }
            Tok::LBracket => {
                let mut elems = Vec::new();
                if !self.matches(&Tok::RBracket) {
                    loop {
                        elems.push(self.expr()?);
                        // ] ends the literal
                        if self.matches(&Tok::RBracket) { break; }
                        // expect comma; allow trailing comma
                        self.expect(Tok::Comma, "expected ',' in array literal")?;
                        if self.matches(&Tok::RBracket) { break; }
                    }
                }
                Ok(Expr::ArrayLit(elems))
            }
            Tok::Fn | Tok::Function => {
                // Stage #1: only the anonymous form inside expressions.
                // Expect '(' immediately (no name allowed here).
                self.expect(Tok::LParen, "expected '(' after 'fn'/'function' in function literal")?;
                let params = self.parse_param_list()?;
                let body = self.block()?;
                Ok(Expr::FnLit { params, body })
            }
            Tok::Pipe => {
                // parse `|x, y|`
                let mut params = Vec::new();
                if !self.matches(&Tok::Pipe) {
                    loop {
                        let name = match self.next().tok {
                            Tok::Ident(s) => s,
                            _ => return Err(self.err_here("expected parameter name")),
                        };
                        params.push(name);
                        if self.matches(&Tok::Pipe) { break; }
                        self.expect(Tok::Comma, "expected ',' in lambda params")?;
                    }
                }
                // body: either { block } or a single expression (implicitly returned)
                if self.check(&Tok::LBrace) {
                    let body = self.block()?;
                    Ok(Expr::FnLit { params, body })
                } else {
                    // expression-body -> synthesize a block with an implicit return
                    let expr = self.expr()?;
                    let body = Block { stmts: vec![Stmt::Return(Some(expr))] };
                    Ok(Expr::FnLit { params, body })
                }
            }
            Tok::LBrace => self.parse_object_literal(),
            Tok::Delete => self.parse_delete(),
            _ => Err(ParseError { msg: "unexpected token".into(), span: t.span }),
        }
    }

    fn parse_listen_stmt(&mut self) -> PResult<Stmt> {
        // consume 'listen'
        let _ = self.next(); // Ident("listen")
        // "addr"
        let addr = match self.next().tok {
            Tok::Str(s) => s,
            _ => return Err(self.err_here("expected string address after 'listen'")),
        };
        // body
        self.expect(Tok::LBrace, "expected '{' after listen address")?;
        let mut routes = Vec::new();
        while !self.matches(&Tok::RBrace) {
            routes.push(self.parse_route_decl()?);
        }
        Ok(Stmt::Listen(ListenDecl { addr, routes }))
    }

    fn parse_route_decl(&mut self) -> PResult<RouteDecl> {
        // route "METHOD" [pattern] (params) => { body } ;
        if !self.matches_ident("route") {
            return Err(self.err_here("expected 'route'"));
        }

        // "METHOD" (accept also bare Ident for convenience)
        let method = match self.next().tok {
            Tok::Str(s) => s,
            Tok::Ident(s) => s, // allow: route GET [...]
            _ => return Err(self.err_here("expected HTTP method (string or identifier)")),
        };

        // [ pattern parts ]  -- we parse a general array expression to keep it flexible
        self.expect(Tok::LBracket, "expected '[' after method")?;
        let mut elems = Vec::new();
        if !self.matches(&Tok::RBracket) {
            loop {
                // keep it general: any expression (usually "literal" strings like "/","users",":id")
                elems.push(self.expr()?);
                if self.matches(&Tok::RBracket) { break; }
                self.expect(Tok::Comma, "expected ',' in route pattern")?;
            }
        }
        let pattern_expr = Expr::ArrayLit(elems);

        // ( params )
        self.expect(Tok::LParen, "expected '(' before route handler params")?;
        let params = self.parse_param_list()?;

        // =>
        self.expect(Tok::Eq, "expected '=>' after params (first '=')")?;
        self.expect(Tok::Gt, "expected '=>' after params (second '>')")?;

        // body: block or single expression (we'll allow both; single expr becomes 'return expr;')
        let handler_body = if self.check(&Tok::LBrace) {
            self.block()?
        } else {
            // expression-body → implicit return
            let e = self.expr()?;
            Block { stmts: vec![Stmt::Return(Some(e))] }
        };

        // optional ';' after a block is allowed by your grammar, require it for consistency
        self.expect(Tok::Semi, "expected ';' after route")?;

        let handler = Expr::FnLit { params, body: handler_body };
        Ok(RouteDecl { method, pattern: pattern_expr, handler })
    }

    // Parse an object literal: { a: 1, "b": 2, c: x+y }
    fn parse_object_literal(&mut self) -> PResult<Expr> {
        // self.expect(Tok::LBrace, "expected '{'")?; // already consumed
        let mut props = Vec::new();

        if !self.check(&Tok::RBrace) {
            loop {
                // key: Ident | Str
                let key = match &self.peek().tok {
                    Tok::Ident(s) => {
                        let s = if let Tok::Ident(s) = self.next().tok { s } else { unreachable!() };
                        PropKey::Ident(s)
                    }
                    Tok::Str(_) => {
                        let s = if let Tok::Str(s) = self.next().tok { s } else { unreachable!() };
                        PropKey::Str(s)
                    }
                    _ => return Err(self.err_here("expected property name (identifier or string)")),
                };

                self.expect(Tok::Colon, "expected ':' after property name")?;
                let value = self.expr()?;
                props.push((key, value));

                if self.matches(&Tok::Comma) {
                    if self.matches(&Tok::RBrace) { break; } // trailing comma
                    continue;
                }
                break;
            }
        }

        self.expect(Tok::RBrace, "expected '}' to close object literal")?;
        Ok(Expr::ObjLit(props))
    }

    // delete obj.x   |   delete obj["x"]
    fn parse_delete(&mut self) -> PResult<Expr> {
        // receiver
        let recv = self.parse_primary()?;

        if self.matches(&Tok::Dot) {
            // delete obj.ident
            let name = match self.next().tok {
                Tok::Ident(s) => s,
                _ => return Err(self.err_here("expected identifier after '.' in delete")),
            };
            return Ok(Expr::DeleteProp { obj: SmallBox::new(recv), key: PropKey::Ident(name) });
        }

        if self.matches(&Tok::LBracket) {
            match &self.peek().tok {
                Tok::Str(_) => {
                    let s = if let Tok::Str(s) = self.next().tok { s } else { unreachable!() };
                    self.expect(Tok::RBracket, "expected ']'")?;
                    return Ok(Expr::DeleteProp { obj: SmallBox::new(recv), key: PropKey::Str(s) });
                }
                Tok::Ident(_) => {
                    let name = if let Tok::Ident(s) = self.next().tok { s } else { unreachable!() };
                    self.expect(Tok::RBracket, "expected ']'")?;
                    return Ok(Expr::DeleteProp { obj: SmallBox::new(recv), key: PropKey::Ident(name) });
                }
                _ => {
                    // general: delete obj[expr]  (keep MVP behavior per your comment)
                    let idx = self.expr()?;
                    self.expect(Tok::RBracket, "expected ']'")?;
                    return Ok(Expr::Unary {
                        op: UnOp::Pos,
                        e: SmallBox::new(Expr::Index { recv: SmallBox::new(recv), index: SmallBox::new(idx) }),
                    });
                }
            }
        }

        Err(self.err_here("delete expects a property access (obj.x or obj[...])"))
}
}

fn lvalue_to_expr(lv: &LValue) -> Expr {
    match lv {
        LValue::Ident(s) => Expr::Ident(s.clone()),
        LValue::GetProp { recv, name } =>
            Expr::GetProp { recv: SmallBox::new(recv.clone()), name: name.clone() },
        LValue::Index { recv, index } =>
            Expr::Index { recv: SmallBox::new(recv.clone()), index: SmallBox::new(index.clone()) },
    }
}
