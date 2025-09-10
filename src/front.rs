// src/front.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

use logos::Logos;
use std::{collections::BTreeSet, ops::Deref};
use ahash::AHashMap as HashMap;
use smallbox::SmallBox;

// Bring in the WIR types from your other file/module.
use crate::wir::{
    Builder, Constant, FieldId, FuncId, Inst, IntBinOp, Module, Type, ValueId,
    MethodInfo, AccessorInfo, ClassInfo
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
    #[token("let")] Let,
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

    This,                            // `this`
    Super,                           // `super` (used with member access or super(...) in ctor)
    New { class: String, args: Vec<Expr> }, // `new ClassName(args...)`

    // { a: 1, "b": 2, c: x+y }
    ObjLit(Vec<(PropKey, Expr)>),

    // obj.x   or   obj["x"]
    GetPropObj { obj: SmallBox<Expr, u8>, key: PropKey },

    // obj.x = value   or   obj["x"] = value
    SetPropObj { obj: SmallBox<Expr, u8>, key: PropKey, value: SmallBox<Expr, u8> },

    // "<key>" in obj   — key is a general Expr; at lowering we'll coerce to string/symbol
    In { key: SmallBox<Expr, u8>, obj: SmallBox<Expr, u8> },

    // delete obj.x / delete obj["x"]
    DeleteProp { obj: SmallBox<Expr, u8>, key: PropKey },

    // await <expression>
    Await(SmallBox<Expr, u8>)
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
        let mut functions = Vec::new();
        let mut classes   = Vec::new();
        let mut toplevel_stmts: Vec<Stmt> = Vec::new();

        while self.i < self.toks.len() {
            if self.matches(&Tok::Semi) { continue; }

            if self.check(&Tok::Class) {
                classes.push(self.class_decl()?);
            } else if self.check(&Tok::Fn) || self.check(&Tok::Async) {
                let is_async = if self.matches(&Tok::Async) {
                    self.expect(Tok::Fn, "expected 'fn' after 'async'")?;
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

        Ok(Program { functions, classes })
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
        // optional 'static'
        let is_static = self.matches(&Tok::Static);

        // constructor / destructor
        if self.matches(&Tok::Constructor) {
            self.expect(Tok::LParen, "expected '(' after 'constructor'")?;
            let params = self.parse_param_list()?;
            let body = self.block()?;
            return Ok(ClassMember::Constructor { params, body, is_async: false });
        }
        if self.matches(&Tok::Destructor) {
            self.expect(Tok::LParen, "expected '(' after 'destructor'")?;
            self.expect(Tok::RParen, "expected ')' after 'destructor('")?;
            let body = self.block()?;
            return Ok(ClassMember::Destructor { body });
        }

        // async fn (method)
        let mut is_async = false;
        if self.matches(&Tok::Async) {
            self.expect(Tok::Fn, "expected 'fn' after 'async' in class")?;
            is_async = true;
            let (name, params, body) = self.parse_method_tail()?;
            return Ok(ClassMember::Method { is_static, name, params, body, is_async });
        }

        // fn (method)
        if self.matches(&Tok::Fn) {
            let (name, params, body) = self.parse_method_tail()?;
            return Ok(ClassMember::Method { is_static, name, params, body, is_async: false });
        }

        // var ...  (stored or accessor)
        if self.matches(&Tok::Var) {
            // name
            let name = match self.next().tok {
                Tok::Ident(s) => s,
                _ => return Err(self.err_here("expected identifier after 'var' in class")),
            };

            // Accessor form:  var name { get() { ... } set(x){...} }
            if self.matches(&Tok::LBrace) {
                let mut getter: Option<Block> = None;
                let mut setter_param: Option<String> = None;
                let mut setter_body: Option<Block> = None;

                while !self.matches(&Tok::RBrace) {
                    if self.matches(&Tok::Get) {
                        self.expect(Tok::LParen, "expected '(' after 'get'")?;
                        self.expect(Tok::RParen, "get() takes no params")?;
                        let body = self.block()?;
                        getter = Some(body);
                    } else if self.matches(&Tok::Set) {
                        self.expect(Tok::LParen, "expected '(' after 'set'")?;
                        let param = match self.next().tok {
                            Tok::Ident(s) => s,
                            _ => return Err(self.err_here("expected setter parameter name")),
                        };
                        self.expect(Tok::RParen, "expected ')' after setter parameter")?;
                        let body = self.block()?;
                        setter_param = Some(param);
                        setter_body  = Some(body);
                    } else {
                        return Err(self.err_here("expected 'get' or 'set' in accessor block"));
                    }
                }

                return Ok(ClassMember::Accessor { is_static, name, getter, setter_param, setter_body });
            }

            // Stored form:  var name [: Type] [= init]? ;
            let mut type_ann: Option<String> = None;
            if self.matches(&Tok::Colon) {
                // parse a simple type name (Identifier) for now
                match self.next().tok {
                    Tok::Ident(s) => type_ann = Some(s),
                    _ => return Err(self.err_here("expected type name after ':'")),
                }
            }

            let init = if self.matches(&Tok::Eq) {
                Some(self.expr()?)
            } else { None };

            self.expect(Tok::Semi, "expected ';' after class var")?;
            return Ok(ClassMember::Stored { is_static, name, type_ann, init });
        }

        Err(self.err_here("expected class member (var/fn/constructor/destructor)"))
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

        if self.matches(&Tok::Var) || self.matches(&Tok::Let){
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
            Tok::Super => Ok(Expr::Super),

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
            Tok::Fn => {
                // Stage #1: only the anonymous form inside expressions.
                // Expect '(' immediately (no name allowed here).
                self.expect(Tok::LParen, "expected '(' after 'fn' in function literal")?;
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

fn hoist_fn_lits_program(prog: &Program) -> (Program, HashMap<String, Vec<String>>) {
    // name -> sorted capture list (stable order)
    let mut lam_captures: HashMap<String, Vec<String>> = HashMap::new();

    // Generate unique lam names avoiding collisions with existing functions.
    let mut used: BTreeSet<String> = prog.functions.iter().map(|f| f.name.clone()).collect();
    let mut counter: u32 = 0;
    fn fresh(used: &mut BTreeSet<String>, counter: &mut u32) -> String {
        loop {
            let name = format!("__lam_{}", *counter);
            *counter += 1;
            if used.insert(name.clone()) { return name; }
        }
    }

    // Collect {defs, uses} inside a block
    fn collect_defs_uses_block(b: &Block, defs: &mut BTreeSet<String>, uses: &mut BTreeSet<String>) {
        for s in &b.stmts { collect_defs_uses_stmt(s, defs, uses); }
    }
    fn collect_defs_uses_stmt(s: &Stmt, defs: &mut BTreeSet<String>, uses: &mut BTreeSet<String>) {
        match s {
            Stmt::Var { name, init } => {
                defs.insert(name.clone());
                if let Some(e) = init { collect_uses_expr(e, uses); }
            }
            Stmt::If { cond, then_b, else_b } => {
                collect_uses_expr(cond, uses);
                collect_defs_uses_block(then_b, defs, uses);
                if let Some(b) = else_b { collect_defs_uses_block(b, defs, uses); }
            }
            Stmt::While { cond, body } => {
                collect_uses_expr(cond, uses);
                collect_defs_uses_block(body, defs, uses);
            }
            Stmt::For { init, cond, step, body } => {
                if let Some(i) = init.as_deref() { collect_defs_uses_stmt(i, defs, uses); }
                if let Some(c) = cond { collect_uses_expr(c, uses); }
                if let Some(st) = step { collect_uses_expr(st, uses); }
                collect_defs_uses_block(body, defs, uses);
            }
            Stmt::Return(e) => { if let Some(e) = e { collect_uses_expr(e, uses); } }
            Stmt::Expr(e) => collect_uses_expr(e, uses),
            Stmt::Listen(ld) => {
                for r in &ld.routes {
                    collect_uses_expr(&r.pattern, uses);
                    collect_uses_expr(&r.handler, uses);
                }
            }
        }
    }

    fn collect_uses_expr(e: &Expr, uses: &mut BTreeSet<String>) {
        match e {
            Expr::Ident(s) => { uses.insert(s.clone()); }
            Expr::Assign(lv, rhs) => {
                match &**lv {
                    LValue::Ident(s) => { uses.insert(s.clone()); }
                    LValue::GetProp { recv, .. } => collect_uses_expr(recv, uses),
                    LValue::Index { recv, index } => { collect_uses_expr(recv, uses); collect_uses_expr(index, uses); }
                }
                collect_uses_expr(rhs, uses);
            }
            Expr::Binary { a, b, .. } => { collect_uses_expr(a, uses); collect_uses_expr(b, uses); }
            Expr::Unary  { e, .. }    => { collect_uses_expr(e, uses); }
            Expr::Call   { callee, args } => {
                collect_uses_expr(callee, uses);
                for a in args { collect_uses_expr(a, uses); }
            }
            Expr::GetProp { recv, .. } => collect_uses_expr(recv, uses),
            Expr::Index { recv, index } => { collect_uses_expr(recv, uses); collect_uses_expr(index, uses); }
            Expr::Group(g) => collect_uses_expr(g, uses),
            Expr::FnLit { .. } | Expr::FnRef { .. } => { /* handled at outer level */ }
            Expr::LitInt(_) | Expr::LitF64(_) | Expr::LitBool(_) | Expr::LitNull | Expr::Str(_) => {}

            Expr::ArrayLit(elems) => {
                for el in elems {
                    collect_uses_expr(el, uses);
                }
            }

            Expr::ObjLit(props) => {
                for (_, v) in props {
                    collect_uses_expr(v, uses);
                }
            }

            Expr::GetPropObj { obj, .. } => {
                collect_uses_expr(obj, uses);
            }

            Expr::SetPropObj { obj, value, .. } => {
                collect_uses_expr(obj, uses);
                collect_uses_expr(value, uses);
            }

            Expr::In { key, obj } => {
                collect_uses_expr(key, uses);
                collect_uses_expr(obj, uses);
            }

            Expr::DeleteProp { obj, .. } => {
                collect_uses_expr(obj, uses);
            }

            _ => { /* other expr types have no uses */ }
        }
    }

    // Rewrite helpers
    fn rw_block(
        b: &Block,
        used: &mut BTreeSet<String>,
        counter: &mut u32,
        enclosing_locals: &BTreeSet<String>,
        out_funcs: &mut Vec<FuncDecl>,
        lam_caps_out: &mut HashMap<String, Vec<String>>,
    ) -> Block {
        // Start with the incoming scope, then extend as we see new `var`s.
        let mut scope = enclosing_locals.clone();
        let mut out_stmts = Vec::with_capacity(b.stmts.len());

        for s in &b.stmts {
            match s {
                // `var` introduces a name *after* its initializer; rewrite init with current scope,
                // then add the binding to the scope for following statements.
                Stmt::Var { name, init } => {
                    let init_rw = init.as_ref()
                        .map(|e| rw_expr(e, used, counter, &scope, out_funcs, lam_caps_out));
                    out_stmts.push(Stmt::Var { name: name.clone(), init: init_rw });
                    scope.insert(name.clone());
                }

                // `for` init can introduce a name that is visible to cond/step/body.
                Stmt::For { init, cond, step, body } => {
                    // The `for` sub-scope starts from the scope *before* the loop,
                    // then (if init is a `var`) it gains that binding.
                    let mut for_scope = scope.clone();

                    let init_rw = if let Some(i0) = init.as_deref() {
                        // Rewrite the init using the current for_scope.
                        let rewritten = SmallBox::new(rw_stmt(i0, used, counter, &for_scope, out_funcs, lam_caps_out));
                        // If the init is `var id = ...;`, extend for_scope for the rest.
                        if let Stmt::Var { name, .. } = i0 {
                            for_scope.insert(name.clone());
                        }
                        Some(rewritten)
                    } else {
                        None
                    };

                    let cond_rw = cond.as_ref().map(|e| rw_expr(e, used, counter, &for_scope, out_funcs, lam_caps_out));
                    let step_rw = step.as_ref().map(|e| rw_expr(e, used, counter, &for_scope, out_funcs, lam_caps_out));
                    let body_rw = rw_block(body, used, counter, &for_scope, out_funcs, lam_caps_out);

                    out_stmts.push(Stmt::For { init: init_rw, cond: cond_rw, step: step_rw, body: body_rw });
                }

                // Everything else: rewrite with the current scope.
                _ => {
                    let srw = rw_stmt(s, used, counter, &scope, out_funcs, lam_caps_out);
                    out_stmts.push(srw);
                }
            }
        }

        Block { stmts: out_stmts }
    }

    fn rw_stmt(
        s: &Stmt,
        used: &mut BTreeSet<String>,
        counter: &mut u32,
        enclosing_locals: &BTreeSet<String>,
        out_funcs: &mut Vec<FuncDecl>,
        lam_caps_out: &mut HashMap<String, Vec<String>>,
    ) -> Stmt {
        match s {
            Stmt::Var { name, init } => Stmt::Var {
                name: name.clone(),
                init: init.as_ref().map(|e| rw_expr(e, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
            },
            Stmt::If { cond, then_b, else_b } => Stmt::If {
                cond: rw_expr(cond, used, counter, enclosing_locals, out_funcs, lam_caps_out),
                then_b: rw_block(then_b, used, counter, enclosing_locals, out_funcs, lam_caps_out),
                else_b: else_b.as_ref().map(|b| rw_block(b, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
            },
            Stmt::While { cond, body } => Stmt::While {
                cond: rw_expr(cond, used, counter, enclosing_locals, out_funcs, lam_caps_out),
                body: rw_block(body, used, counter, enclosing_locals, out_funcs, lam_caps_out),
            },
            Stmt::For { init, cond, step, body } => Stmt::For {
                init: init.as_deref().map(|i| SmallBox::new(rw_stmt(i, used, counter, enclosing_locals, out_funcs, lam_caps_out))),
                cond: cond.as_ref().map(|e| rw_expr(e, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                step: step.as_ref().map(|e| rw_expr(e, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                body: rw_block(body, used, counter, enclosing_locals, out_funcs, lam_caps_out),
            },
            Stmt::Return(e) =>
                Stmt::Return(e.as_ref().map(|x| rw_expr(x, used, counter, enclosing_locals, out_funcs, lam_caps_out))),
            Stmt::Expr(e) => Stmt::Expr(rw_expr(e, used, counter, enclosing_locals, out_funcs, lam_caps_out)),

            Stmt::Listen(ld) => {
                let mut routes = Vec::with_capacity(ld.routes.len());
                for r in &ld.routes {
                    let pattern_rw = rw_expr(&r.pattern, used, counter, enclosing_locals, out_funcs, lam_caps_out);
                    let handler_rw = rw_expr(&r.handler, used, counter, enclosing_locals, out_funcs, lam_caps_out);
                    routes.push(RouteDecl {
                        method: r.method.clone(),
                        pattern: pattern_rw,
                        handler: handler_rw,
                    });
                }
                Stmt::Listen(ListenDecl { addr: ld.addr.clone(), routes })
            }
        }
    }

    fn rw_lvalue(
        lv: &LValue,
        used: &mut BTreeSet<String>,
        counter: &mut u32,
        enclosing_locals: &BTreeSet<String>,
        out_funcs: &mut Vec<FuncDecl>,
        lam_caps_out: &mut HashMap<String, Vec<String>>,
    ) -> LValue {
        match lv {
            LValue::Ident(s) => LValue::Ident(s.clone()),
            LValue::GetProp { recv, name } =>
                LValue::GetProp { recv: rw_expr(recv, used, counter, enclosing_locals, out_funcs, lam_caps_out), name: name.clone() },
            LValue::Index { recv, index } =>
                LValue::Index { recv: rw_expr(recv, used, counter, enclosing_locals, out_funcs, lam_caps_out),
                                index: rw_expr(index, used, counter, enclosing_locals, out_funcs, lam_caps_out) },
        }
    }

    fn rw_expr(
        e: &Expr,
        used: &mut BTreeSet<String>,
        counter: &mut u32,
        enclosing_locals: &BTreeSet<String>,
        out_funcs: &mut Vec<FuncDecl>,
        lam_caps_out: &mut HashMap<String, Vec<String>>,
    ) -> Expr {
        match e {
            Expr::Assign(lv, rhs) => Expr::Assign(
                SmallBox::new(rw_lvalue(lv, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                SmallBox::new(rw_expr(rhs, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
            ),
            Expr::Binary { op, a, b } => Expr::Binary {
                op: *op,
                a: SmallBox::new(rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                b: SmallBox::new(rw_expr(b, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
            },
            Expr::Unary { op, e } => Expr::Unary { op: *op, e: SmallBox::new(rw_expr(e, used, counter, enclosing_locals, out_funcs, lam_caps_out)) },
            Expr::Call { callee, args } => Expr::Call {
                callee: SmallBox::new(rw_expr(callee, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                args: args.iter().map(|a| rw_expr(a, used, counter, enclosing_locals, out_funcs, lam_caps_out)).collect(),
            },
            Expr::GetProp { recv, name } =>
                Expr::GetProp { recv: SmallBox::new(rw_expr(recv, used, counter, enclosing_locals, out_funcs, lam_caps_out)), name: name.clone() },
            Expr::Index { recv, index } =>
                Expr::Index { recv: SmallBox::new(rw_expr(recv, used, counter, enclosing_locals, out_funcs, lam_caps_out)), index: SmallBox::new(rw_expr(index, used, counter, enclosing_locals, out_funcs, lam_caps_out)) },
            Expr::Group(g) => Expr::Group(SmallBox::new(rw_expr(g, used, counter, enclosing_locals, out_funcs, lam_caps_out))),

            // Core: hoist to a top-level function with extra hidden `__env` param; replace with FnRef
            Expr::FnLit { params, body } => {
                // names defined inside the lambda
                let mut inner_defs: BTreeSet<String> = params.iter().cloned().collect();
                let mut uses: BTreeSet<String> = BTreeSet::new();
                collect_defs_uses_block(body, &mut inner_defs, &mut uses);

                // captures = (uses ∩ enclosing_locals) \ params
                let mut caps = Vec::<String>::new();
                for u in uses {
                    if enclosing_locals.contains(&u) && !params.contains(&u) {
                        caps.push(u);
                    }
                }
                caps.sort();

                // Fresh name
                let lam_name = fresh(used, counter);

                // Record capture list
                lam_caps_out.insert(lam_name.clone(), caps.clone());

                // Create the hoisted function: first param is "__env", then user's params
                let mut lam_params = Vec::<String>::with_capacity(params.len() + 1);
                lam_params.push("__env".to_string());
                lam_params.extend(params.iter().cloned());

                // IMPORTANT: recursively hoist inside the lambda body.
                // Enclosing scope for nested lambdas = lambda params ∪ captured names.
                let mut lam_enclosing: BTreeSet<String> = params.iter().cloned().collect();
                for c in &caps { lam_enclosing.insert(c.clone()); }
                let body_rewritten = rw_block(
                    body,
                    used,
                    counter,
                    &lam_enclosing,
                    out_funcs,
                    lam_caps_out,
                );

                out_funcs.push(FuncDecl {
                    name: lam_name.clone(),
                    params: lam_params,
                    body: body_rewritten,
                    is_async: false,
                });

                // Replace literal with a named lam reference
                Expr::FnRef { name: lam_name }
            }

            // Already a reference (created earlier)
            Expr::FnRef { name } => Expr::FnRef { name: name.clone() },

            // terminals
            Expr::LitInt(_) | Expr::LitF64(_) | Expr::LitBool(_) | Expr::LitNull | Expr::Str(_) | Expr::Ident(_) => e.clone(),

            Expr::ArrayLit(elems) => {
                Expr::ArrayLit(
                    elems.iter()
                        .map(|el| rw_expr(el, used, counter, enclosing_locals, out_funcs, lam_caps_out))
                        .collect()
                )
            }

            Expr::ObjLit(props) => {
                Expr::ObjLit(
                    props.iter()
                        .map(|(k, v)| (k.clone(),
                            rw_expr(v, used, counter, enclosing_locals, out_funcs, lam_caps_out)))
                        .collect()
                )
            }

            Expr::GetPropObj { obj, key } => {
                Expr::GetPropObj {
                    obj: SmallBox::new(rw_expr(obj, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                    key: key.clone(),
                }
            }

            Expr::SetPropObj { obj, key, value } => {
                Expr::SetPropObj {
                    obj: SmallBox::new(rw_expr(obj, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                    key: key.clone(),
                    value: SmallBox::new(rw_expr(value, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                }
            }

            Expr::In { key, obj } => {
                Expr::In {
                    key: SmallBox::new(rw_expr(key, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                    obj: SmallBox::new(rw_expr(obj, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                }
            }

            Expr::DeleteProp { obj, key } => {
                Expr::DeleteProp {
                    obj: SmallBox::new(rw_expr(obj, used, counter, enclosing_locals, out_funcs, lam_caps_out)),
                    key: key.clone(),
                }
            }

            Expr::Await(inner) => Expr::Await(SmallBox::new(rw_expr(inner, used, counter, enclosing_locals, out_funcs, lam_caps_out))),
        }
    }

    // Walk functions, threading the set of enclosing locals (toplevel has none).
    let mut out_funcs: Vec<FuncDecl> = Vec::new();
    for f in &prog.functions {
        // at top-level of a function, enclosing locals = its params (can be captured by nested lambdas)
        let enclosing: BTreeSet<String> = f.params.iter().cloned().collect();
        let rew_body = rw_block(&f.body, &mut used, &mut counter, &enclosing, &mut out_funcs, &mut lam_captures);
        out_funcs.push(FuncDecl { name: f.name.clone(), params: f.params.clone(), body: rew_body, is_async: f.is_async });
    }

    (Program { functions: out_funcs }, lam_captures)
}

// -------------------------
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
    funcs: HashMap<String, FuncId>,
    lam_captures: HashMap<String, Vec<String>>,
}

impl<'m> Lowerer<'m> {
    pub fn new(module: &'m mut Module) -> Self {
        Self {
            module,
            funcs: Default::default(),
            lam_captures: Default::default(),
        }
    }

    pub fn lower_program(&mut self, prog: &Program) -> LResult<Vec<FuncId>> {
        // Stage 3 hoist: produce lam functions with __env + capture table, and FnRef at sites
        let (prog, lam_caps) = hoist_fn_lits_program(prog);
        self.lam_captures = lam_caps;

        // Predeclare all functions, including hoisted lambdas (so direct calls resolve)
        self.funcs.clear();
        for (i, f) in prog.functions.iter().enumerate() {
            self.funcs.insert(f.name.clone(), FuncId(i as u32));
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
        use crate::wir::{Inst, Type};

        // Capture list for this (hoisted) function, if any.
        let lam_caps_for_this = self
            .lam_captures
            .get(&fdecl.name)
            .cloned()
            .unwrap_or_default();

        // Param types: default i32; if the first param is "__env", treat it as an Array (env).
        let mut param_tys: Vec<Type> = fdecl.params.iter().map(|_| Type::Int32).collect();
        if matches!(fdecl.params.first().map(|s| s.as_str()), Some("__env")) {
            param_tys[0] = Type::Array(Box::new(None));
        }

        // We model returns uniformly as a single Int32 slot (your dynamic value).
        let ret_tys = vec![Type::Int32];

        // Snapshot the function table so we can resolve direct calls without borrowing &mut self.
        let funcs_snapshot = self.funcs.clone();
        let func_name = fdecl.name.clone();
        let is_async = fdecl.is_async;

        // Build the function body.
        let mut func = {
            let mut b = Builder::new(self.module, &func_name, param_tys, ret_tys);

            // Bind parameters as locals.
            let mut locals: HashMap<String, ValueId> = Default::default();
            for (i, name) in fdecl.params.iter().enumerate() {
                locals.insert(name.clone(), b.param(i));
            }

            // If this is a hoisted lambda, param 0 is "__env" and we must bind each captured name
            // to its corresponding box (array slot) from the env.
            if !lam_caps_for_this.is_empty() {
                let env_arr = *locals
                    .get("__env")
                    .expect("__env param must be present for hoisted lambdas");
                for (i, cap) in lam_caps_for_this.iter().enumerate() {
                    let idx = b.const_i32(i as i32);
                    let (_nid, boxv) = b.push_node(
                        Inst::CallNative {
                            name: "wir_array_get".into(),
                            args: vec![env_arr, idx],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    locals.insert(cap.clone(), boxv[0]);
                    locals.insert(boxed_key(cap), boxv[0]);
                }
            }

            // Per-function table for "fast field" interning.
            let mut fields: HashMap<String, FieldId> = Default::default();
            let mut next_field: u32 = 0;

            if is_async {
                // --- Async prologue: d = Deferred()
                let (_nid, d_res) = b.push_node(
                    Inst::CallNative { name: "wir_deferred_new".into(), args: vec![], pure: false, can_throw: false },
                    None,
                    1,
                    true,
                );
                let d = d_res[0];
                locals.insert("__deferred".to_string(), d);

                // Lower body with async-aware lowering.
                lower_block_free_async(
                    &mut b,
                    &mut locals,
                    &mut fields,
                    &mut next_field,
                    &fdecl.body,
                    &funcs_snapshot,
                    &self.lam_captures,
                    true, // in_async
                )?;

                // Fallthrough: if the body didn’t explicitly return, resolve with 0 and return d.
                if !b.current_block_terminated() {
                    let zero = b.const_i32(0);
                    let dloc = *locals.get("__deferred").expect("__deferred present");
                    let (_nid, _) = b.push_node(
                        Inst::CallNative {
                            name: "wir_deferred_resolve".into(),
                            args: vec![dloc, zero],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    b.ret(&[dloc]);
                }
            } else {
                // --- Sync function: old path
                lower_block_free(
                    &mut b,
                    &mut locals,
                    &mut fields,
                    &mut next_field,
                    &fdecl.body,
                    &funcs_snapshot,
                    &self.lam_captures,
                )?;

                // Fallthrough return 0 (matches previous convention).
                if !b.current_block_terminated() {
                    let zero = b.const_i32(0);
                    b.ret(&[zero]);
                }
            }

            b.finish()
        };

        // Publish into the module with the expected ID (sequential, matching predecl order).
        let fid = FuncId(self.module.funcs.len() as u32);
        func.id = fid;
        self.module.funcs.push(func);
        Ok(fid)
    }
}

fn lower_block_free<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    blk: &Block,
    funcs: &HashMap<String, FuncId>,
    lam_caps: &HashMap<String, Vec<String>>,
) -> LResult<()> {
    for s in &blk.stmts {
        lower_stmt_free(b, locals, fields, next_field, s, funcs, lam_caps)?; // <-- pass through
    }
    Ok(())
}

fn lower_stmt_free<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    s: &Stmt,
    funcs: &HashMap<String, FuncId>,
    lam_caps: &HashMap<String, Vec<String>>,   // <-- new
) -> LResult<()> {
    match s {
        Stmt::Var { name, init } => {
            let val = if let Some(e) = init {
                lower_expr_free(b, locals, fields, next_field, e, funcs, lam_caps)? // <-- pass
            } else {
                b.const_i32(0)
            };
            locals.insert(name.clone(), val);
        }
        Stmt::If { cond, then_b, else_b } => {
            let c = lower_expr_free(b, locals, fields, next_field, cond, funcs, lam_caps)?; // <-- pass
            let then_id  = b.block();
            let else_id  = b.block();
            let then_end = b.block();
            let else_end = b.block();
            let cont_id  = b.block();

            b.branch(c, then_id, else_id);

            let incoming = locals.clone();

            b.position_at(then_id);
            let mut locals_then = incoming.clone();
            lower_block_free(b, &mut locals_then, fields, next_field, then_b, funcs, lam_caps)?; // <-- pass
            if !b.current_block_terminated() { b.jump(then_end, &[]); }
            b.position_at(then_end);

            b.position_at(else_id);
            let mut locals_else = incoming.clone();
            if let Some(eb) = else_b {
                lower_block_free(b, &mut locals_else, fields, next_field, eb, funcs, lam_caps)?; // <-- pass
            }
            if !b.current_block_terminated() { b.jump(else_end, &[]); }
            b.position_at(else_end);

            let mut phi_vars: Vec<String> = Vec::new();
            for (name, &vin) in incoming.iter() {
                let vt = *locals_then.get(name).unwrap_or(&vin);
                let ve = *locals_else.get(name).unwrap_or(&vin);
                if vt != ve { phi_vars.push(name.clone()); }
            }
            phi_vars.sort();

            let mut phi_params = Vec::with_capacity(phi_vars.len());
            for _ in &phi_vars { phi_params.push(b.add_block_param(cont_id, Type::Int32)); }

            let mut args_then = Vec::with_capacity(phi_vars.len());
            let mut args_else = Vec::with_capacity(phi_vars.len());
            for name in &phi_vars {
                let vin = *incoming.get(name).unwrap();
                args_then.push(*locals_then.get(name).unwrap_or(&vin));
                args_else.push(*locals_else.get(name).unwrap_or(&vin));
            }

            b.position_at(then_end); b.jump(cont_id, &args_then);
            b.position_at(else_end); b.jump(cont_id, &args_else);

            b.position_at(cont_id);
            for (i, name) in phi_vars.iter().enumerate() {
                locals.insert(name.clone(), phi_params[i]);
            }
        }
        Stmt::While { cond, body } => {
            let head = b.block();
            let body_b = b.block();
            let exit = b.block();

            let mut_names = collect_mut_locals_in_block(body)
                .into_iter()
                .filter(|n| locals.contains_key(n))
                .collect::<Vec<_>>();

            let init_args: Vec<ValueId> = mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
            let phi_vals: Vec<ValueId> = mut_names.iter().map(|_| b.add_block_param(head, Type::Int32)).collect();

            b.jump(head, &init_args);

            b.position_at(head);
            for (nm, p) in mut_names.iter().zip(phi_vals.iter()) {
                locals.insert(nm.clone(), *p);
            }
            let c = lower_expr_free(b, locals, fields, next_field, cond, funcs, lam_caps)?; // <-- pass
            b.branch(c, body_b, exit);

            b.position_at(body_b);
            lower_block_free(b, locals, fields, next_field, body, funcs, lam_caps)?; // <-- pass
            let back_args: Vec<ValueId> = mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
            b.jump(head, &back_args);

            b.position_at(exit);
            for (nm, p) in mut_names.into_iter().zip(phi_vals.into_iter()) {
                locals.insert(nm, p);
            }
        }
        Stmt::For { init, cond, step, body } => {
            if let Some(i) = init { lower_stmt_free(b, locals, fields, next_field, i, funcs, lam_caps)?; } // <-- pass

            let head = b.block();
            let body_b = b.block();
            let exit = b.block();

            let mut mutated_set: BTreeSet<String> = BTreeSet::new();
            for st in &body.stmts { collect_mut_locals_in_stmt(st, &mut mutated_set); }
            if let Some(se) = step { collect_mut_locals_in_expr(se, &mut mutated_set); }
            let mut_names: Vec<String> = mutated_set.into_iter().filter(|n| locals.contains_key(n)).collect();

            let init_args: Vec<ValueId> = mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
            let phi_vals: Vec<ValueId> = mut_names.iter().map(|_| b.add_block_param(head, Type::Int32)).collect();

            b.jump(head, &init_args);

            b.position_at(head);
            for (nm, p) in mut_names.iter().zip(phi_vals.iter()) { locals.insert(nm.clone(), *p); }
            let c = if let Some(e) = cond {
                lower_expr_free(b, locals, fields, next_field, e, funcs, lam_caps)? // <-- pass
            } else {
                let (_nid, res) = b.push_node(Inst::Const(Constant::Bool(true)), Some(Type::Bool), 1, false);
                res[0]
            };
            b.branch(c, body_b, exit);

            b.position_at(body_b);
            lower_block_free(b, locals, fields, next_field, body, funcs, lam_caps)?; // <-- pass
            if let Some(se) = step { let _ = lower_expr_free(b, locals, fields, next_field, se, funcs, lam_caps)?; } // <-- pass
            let back_args: Vec<ValueId> = mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
            b.jump(head, &back_args);

            b.position_at(exit);
            for (nm, p) in mut_names.into_iter().zip(phi_vals.into_iter()) { locals.insert(nm, p); }
        }
        Stmt::Return(e) => {
            if let Some(e) = e {
                let v = lower_expr_free(b, locals, fields, next_field, e, funcs, lam_caps)?; // <-- pass
                b.ret(&[v]);
            } else {
                let z = b.const_i32(0);
                b.ret(&[z]);
            }
        }
        Stmt::Listen(ld) => {
            // server id = wir_server_create(addr)
            let (_nid_addr, addr_r) = b.push_node(
                Inst::Const(Constant::Str(ld.addr.clone())),
                Some(Type::Str), 1, false
            );
            let addr_v = addr_r[0];
            let (_nid_sid, sid_r) = b.push_node(
                Inst::CallNative {
                    name: "wir_server_create".into(),
                    args: vec![addr_v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32), // server id
                1,
                true,
            );
            let sid = sid_r[0];

            // add routes
            for rt in &ld.routes {
                let pat_v = lower_expr_free(b, locals, fields, next_field, &rt.pattern, funcs, lam_caps)?;
                let hnd_v = lower_expr_free(b, locals, fields, next_field, &rt.handler, funcs, lam_caps)?;
                let (_mid, mr) = b.push_node(
                    Inst::Const(Constant::Str(rt.method.clone())),
                    Some(Type::Str),
                    1,
                    false,
                );
                let m_str = mr[0];

                let _ = b.push_node(
                    Inst::CallNative {
                        name: "wir_server_add_route".into(),
                        args: vec![sid, m_str, pat_v, hnd_v],  // <-- pass the string pointer
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
            }

            // listen
            let _ = b.push_node(
                Inst::CallNative {
                    name: "wir_server_listen".into(),
                    args: vec![sid],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );
        }

        Stmt::Expr(e) => { let _ = lower_expr_free(b, locals, fields, next_field, e, funcs, lam_caps)?; } // <-- pass
    }

    Ok(())
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

        Stmt::Listen(ld) => {
            for r in &ld.routes {
                collect_mut_locals_in_expr(&r.pattern, out);
                collect_mut_locals_in_expr(&r.handler, out);
            }
        }
    }
}

fn collect_mut_locals_in_block(b: &Block) -> Vec<String> {
    let mut set = BTreeSet::new();
    for s in &b.stmts { collect_mut_locals_in_stmt(s, &mut set); }
    set.into_iter().collect() // stable order
}

fn lower_block_free_async<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    blk: &Block,
    funcs: &HashMap<String, FuncId>,
    lam_caps: &HashMap<String, Vec<String>>,
    in_async: bool,
) -> LResult<()> {
    for s in &blk.stmts {
        lower_stmt_free_async(b, locals, fields, next_field, s, funcs, lam_caps, in_async)?;
    }
    Ok(())
}

fn lower_stmt_free_async<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    s: &Stmt,
    funcs: &HashMap<String, FuncId>,
    lam_caps: &HashMap<String, Vec<String>>,
    in_async: bool,
) -> LResult<()> {
    match s {
        Stmt::Return(eopt) if in_async => {
            let d = *locals.get("__deferred").expect("__deferred present");
            let v = if let Some(e) = eopt {
                lower_expr_free_async(b, locals, fields, next_field, e, funcs, lam_caps, in_async)?
            } else {
                b.const_i32(0)
            };
            let (_nid, _r) = b.push_node(
                Inst::CallNative { name: "wir_deferred_resolve".into(), args: vec![d, v], pure: false, can_throw: false },
                None, 1, true
            );
            b.ret(&[d]);
            Ok(())
        }
        Stmt::Listen(ld) => {
            // server id = wir_server_create(addr)
            let (_nid_addr, addr_r) = b.push_node(
                Inst::Const(Constant::Str(ld.addr.clone())),
                Some(Type::Str), 1, false
            );
            let addr_v = addr_r[0];
            let (_nid_sid, sid_r) = b.push_node(
                Inst::CallNative {
                    name: "wir_server_create".into(),
                    args: vec![addr_v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32), // server id
                1,
                true,
            );
            let sid = sid_r[0];

            // add routes
            for rt in &ld.routes {
                let pat_v = lower_expr_free(b, locals, fields, next_field, &rt.pattern, funcs, lam_caps)?;
                let hnd_v = lower_expr_free(b, locals, fields, next_field, &rt.handler, funcs, lam_caps)?;
                let (_mid, mr) = b.push_node(
                    Inst::Const(Constant::Str(rt.method.clone())),
                    Some(Type::Str),
                    1,
                    false,
                );
                let m_str = mr[0];

                let _ = b.push_node(
                    Inst::CallNative {
                        name: "wir_server_add_route".into(),
                        args: vec![sid, m_str, pat_v, hnd_v],  // <-- pass the string pointer
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
            }

            // listen
            let _ = b.push_node(
                Inst::CallNative {
                    name: "wir_server_listen".into(),
                    args: vec![sid],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Int32),
                1,
                true,
            );

            Ok(())
        }
        _ => {
            // Forward to the old lowering, but via the *_async versions
            match s {
                Stmt::Var { name, init } => {
                    let val = if let Some(e) = init {
                        lower_expr_free_async(b, locals, fields, next_field, e, funcs, lam_caps, in_async)?
                    } else { b.const_i32(0) };
                    locals.insert(name.clone(), val);
                    Ok(())
                }
                Stmt::If { cond, then_b, else_b } => {
                    let c = lower_expr_free_async(b, locals, fields, next_field, cond, funcs, lam_caps, in_async)?;
                    // (rest identical to your If lowering, but using lower_block_free_async)
                    // ...
                    // Keep your existing structure, just swap the called helpers:
                    let then_id  = b.block();
                    let else_id  = b.block();
                    let then_end = b.block();
                    let else_end = b.block();
                    let cont_id  = b.block();

                    b.branch(c, then_id, else_id);

                    let incoming = locals.clone();

                    b.position_at(then_id);
                    let mut locals_then = incoming.clone();
                    lower_block_free_async(b, &mut locals_then, fields, next_field, then_b, funcs, lam_caps, in_async)?;
                    if !b.current_block_terminated() { b.jump(then_end, &[]); }
                    b.position_at(then_end);

                    b.position_at(else_id);
                    let mut locals_else = incoming.clone();
                    if let Some(eb) = else_b {
                        lower_block_free_async(b, &mut locals_else, fields, next_field, eb, funcs, lam_caps, in_async)?;
                    }
                    if !b.current_block_terminated() { b.jump(else_end, &[]); }
                    b.position_at(else_end);

                    let mut phi_vars: Vec<String> = Vec::new();
                    for (name, &vin) in incoming.iter() {
                        let vt = *locals_then.get(name).unwrap_or(&vin);
                        let ve = *locals_else.get(name).unwrap_or(&vin);
                        if vt != ve { phi_vars.push(name.clone()); }
                    }
                    phi_vars.sort();

                    let mut phi_params = Vec::with_capacity(phi_vars.len());
                    for _ in &phi_vars { phi_params.push(b.add_block_param(cont_id, Type::Int32)); }

                    let mut args_then = Vec::with_capacity(phi_vars.len());
                    let mut args_else = Vec::with_capacity(phi_vars.len());
                    for name in &phi_vars {
                        let vin = *incoming.get(name).unwrap();
                        args_then.push(*locals_then.get(name).unwrap_or(&vin));
                        args_else.push(*locals_else.get(name).unwrap_or(&vin));
                    }

                    b.position_at(then_end); b.jump(cont_id, &args_then);
                    b.position_at(else_end); b.jump(cont_id, &args_else);

                    b.position_at(cont_id);
                    for (i, name) in phi_vars.iter().enumerate() {
                        locals.insert(name.clone(), phi_params[i]);
                    }

                    Ok(())
                }
                // While / For / Expr … call lower_*_async respectively
                Stmt::While { cond, body } => {
                    // same as your While, but using lower_expr_free_async / lower_block_free_async
                    let head = b.block();
                    let body_b = b.block();
                    let exit = b.block();

                    let mut_names = collect_mut_locals_in_block(body)
                        .into_iter()
                        .filter(|n| locals.contains_key(n))
                        .collect::<Vec<_>>();

                    let init_args: Vec<ValueId> = mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
                    let phi_vals: Vec<ValueId> = mut_names.iter().map(|_| b.add_block_param(head, Type::Int32)).collect();

                    b.jump(head, &init_args);

                    b.position_at(head);
                    for (nm, p) in mut_names.iter().zip(phi_vals.iter()) {
                        locals.insert(nm.clone(), *p);
                    }
                    let c = lower_expr_free_async(b, locals, fields, next_field, cond, funcs, lam_caps, in_async)?;
                    b.branch(c, body_b, exit);

                    b.position_at(body_b);
                    lower_block_free_async(b, locals, fields, next_field, body, funcs, lam_caps, in_async)?;
                    let back_args: Vec<ValueId> = mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
                    b.jump(head, &back_args);

                    b.position_at(exit);
                    for (nm, p) in mut_names.into_iter().zip(phi_vals.into_iter()) {
                        locals.insert(nm, p);
                    }
                    Ok(())
                }
                Stmt::For { init, cond, step, body } => {
                    if let Some(i) = init { lower_stmt_free_async(b, locals, fields, next_field, i, funcs, lam_caps, in_async)?; }

                    let head = b.block();
                    let body_b = b.block();
                    let exit = b.block();

                    let mut mutated_set: BTreeSet<String> = BTreeSet::new();
                    for st in &body.stmts { collect_mut_locals_in_stmt(st, &mut mutated_set); }
                    if let Some(se) = step { collect_mut_locals_in_expr(se, &mut mutated_set); }
                    let mut_names: Vec<String> = mutated_set.into_iter().filter(|n| locals.contains_key(n)).collect();

                    let init_args: Vec<ValueId> = mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
                    let phi_vals: Vec<ValueId> = mut_names.iter().map(|_| b.add_block_param(head, Type::Int32)).collect();

                    b.jump(head, &init_args);

                    b.position_at(head);
                    for (nm, p) in mut_names.iter().zip(phi_vals.iter()) { locals.insert(nm.clone(), *p); }
                    let c = if let Some(e) = cond {
                        lower_expr_free_async(b, locals, fields, next_field, e, funcs, lam_caps, in_async)?
                    } else {
                        let (_nid, res) = b.push_node(Inst::Const(Constant::Bool(true)), Some(Type::Bool), 1, false);
                        res[0]
                    };
                    b.branch(c, body_b, exit);

                    b.position_at(body_b);
                    lower_block_free_async(b, locals, fields, next_field, body, funcs, lam_caps, in_async)?;
                    if let Some(se) = step { let _ = lower_expr_free_async(b, locals, fields, next_field, se, funcs, lam_caps, in_async)?; }
                    let back_args: Vec<ValueId> = mut_names.iter().map(|n| *locals.get(n).unwrap()).collect();
                    b.jump(head, &back_args);

                    b.position_at(exit);
                    for (nm, p) in mut_names.into_iter().zip(phi_vals.into_iter()) { locals.insert(nm, p); }
                    Ok(())
                }
                Stmt::Expr(e) => { let _ = lower_expr_free_async(b, locals, fields, next_field, e, funcs, lam_caps, in_async)?; Ok(()) }

                Stmt::Listen(_) => unreachable!(), // handled in the outer match arm
                Stmt::Return(_) => unreachable!(), // handled above when in_async
            }
        }
    }
}

fn lower_expr_free_async<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    e: &Expr,
    funcs: &HashMap<String, FuncId>,
    lam_caps: &HashMap<String, Vec<String>>,
    in_async: bool,
) -> LResult<ValueId> {
    match e {
        Expr::Await(inner) => {
            if !in_async {
                return Err(LowerError::NotLowerable("await outside async function"));
            }
            let pv = lower_expr_free_async(b, locals, fields, next_field, inner, funcs, lam_caps, in_async)?;
            let (_nid, res) = b.push_node(
                Inst::CallNative { name: "wir_await".into(), args: vec![pv], pure: false, can_throw: false },
                None, 1, true
            );
            Ok(res[0])
        }
        _ => {
            // fall back to your original lowerer
            lower_expr_free(b, locals, fields, next_field, e, funcs, lam_caps)
        }
    }
}

fn lower_array_method_call<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    _fields: &mut HashMap<String, FieldId>,
    _next_field: &mut u32,
    recv: &Expr,
    name: &str,
    args: &[Expr],
    funcs: &HashMap<String, FuncId>,
    lam_caps: &HashMap<String, Vec<String>>,
) -> LResult<Option<ValueId>> {
    use crate::wir::{Inst, Type};

    let arr = lower_expr_free(b, locals, _fields, _next_field, recv, funcs, lam_caps)?;

    // Small helper to call a simple native
    macro_rules! cn {
        ($fname:expr, [$($argv:expr),*], $ty:expr) => {{
            let (_nid, res) = b.push_node(
                Inst::CallNative {
                    name: $fname.into(),
                    args: vec![$($argv),*],
                    pure: false,
                    can_throw: false,
                },
                $ty,
                1,
                true,
            );
            Ok(Some(res[0]))
        }};
    }

    match name {
        // ---- property-like method kept for back-compat
        "length" => {
            if !args.is_empty() { return Err(LowerError::NotLowerable("length() expects 0 args")); }
            return cn!("wir_array_len", [arr], Some(Type::Int32));
        }

        // ---- basic mutators that already worked via natives
        "setLength" => {
            if args.len() != 1 { return Err(LowerError::NotLowerable("setLength expects 1 arg")); }
            let n = lower_expr_free(b, locals, _fields, _next_field, &args[0], funcs, lam_caps)?;
            return cn!("wir_array_set_len", [arr, n], Some(Type::Int32));
        }
        "push" => {
            if args.len() != 1 { return Err(LowerError::NotLowerable("push expects 1 arg")); }
            let v = lower_expr_free(b, locals, _fields, _next_field, &args[0], funcs, lam_caps)?;
            return cn!("wir_array_push", [arr, v], Some(Type::Int32));
        }
        "pop" => {
            if !args.is_empty() { return Err(LowerError::NotLowerable("pop expects 0 args")); }
            return cn!("wir_array_pop", [arr], Some(Type::Int32));
        }
        "shift" => {
            if !args.is_empty() { return Err(LowerError::NotLowerable("shift expects 0 args")); }
            return cn!("wir_array_shift", [arr], Some(Type::Int32));
        }
        "unshift" => {
            if args.len() != 1 { return Err(LowerError::NotLowerable("unshift expects 1 arg")); }
            let v = lower_expr_free(b, locals, _fields, _next_field, &args[0], funcs, lam_caps)?;
            return cn!("wir_array_unshift", [arr, v], Some(Type::Int32));
        }

        // ---- map: build loop in WIR, call the closure for each element
        "map" => {
            if args.len() != 1 { return Err(LowerError::NotLowerable("map expects 1 arg")); }
            let fun = lower_expr_free(b, locals, _fields, _next_field, &args[0], funcs, lam_caps)?;

            // len
            let (_nid, len_res) = b.push_node(
                Inst::CallNative { name: "wir_array_len".into(), args: vec![arr], pure: false, can_throw: false },
                Some(Type::Int32), 1, true);
            let len = len_res[0];

            // out = new array len
            let (_nid, out_res) = b.push_node(
                Inst::CallNative { name: "wir_array_new".into(), args: vec![len], pure: false, can_throw: false },
                Some(Type::Array(Box::new(None))), 1, true);
            let out = out_res[0];

            let zero = b.const_i32(0);
            let one  = b.const_i32(1);

            let head = b.block();
            let body = b.block();
            let exit = b.block();

            // loop var phi
            let i_phi = b.add_block_param(head, Type::Int32);

            b.jump(head, &[zero]);
            b.position_at(head);

            let (_nid, cnd) = b.push_node(
                Inst::CmpInt { kind: crate::wir::CmpKind::Lt, a: i_phi, b: len },
                Some(Type::Bool), 1, false);
            b.branch(cnd[0], body, exit);

            b.position_at(body);
            let (_nid, elr) = b.push_node(
                Inst::CallNative { name: "wir_array_get".into(), args: vec![arr, i_phi], pure: false, can_throw: false },
                None, 1, true);
            let el = elr[0];

            let (_nid, mapped) = b.push_node(
                Inst::CallClosure { conv: crate::wir::CallConv::Fast, fun, args: vec![el] },
                Some(Type::Int32), 1, true);

            let (_nid, _s) = b.push_node(
                Inst::CallNative { name: "wir_array_set".into(), args: vec![out, i_phi, mapped[0]], pure: false, can_throw: false },
                Some(Type::Int32), 1, true);

            let next = b.int_bin(crate::wir::IntBinOp::Add, i_phi, one);
            b.jump(head, &[next]);

            b.position_at(exit);
            return Ok(Some(out));
        }

        // ---- filter: out = []; if pred(el) push(out, el)
        "filter" => {
            if args.len() != 1 { return Err(LowerError::NotLowerable("filter expects 1 arg")); }
            let fun = lower_expr_free(b, locals, _fields, _next_field, &args[0], funcs, lam_caps)?;

            let (_nid, len_res) = b.push_node(
                Inst::CallNative { name: "wir_array_len".into(), args: vec![arr], pure: false, can_throw: false },
                Some(Type::Int32), 1, true);
            let len = len_res[0];

            let zero = b.const_i32(0);
            let one  = b.const_i32(1);

            // out = list(0)
            let (_nid, out_res) = b.push_node(
                Inst::CallNative { name: "wir_array_new".into(), args: vec![zero], pure: false, can_throw: false },
                Some(Type::Array(Box::new(None))), 1, true);
            let out = out_res[0];

            let head = b.block();
            let body = b.block();
            let exit = b.block();

            let i_phi = b.add_block_param(head, Type::Int32);
            b.jump(head, &[zero]);
            b.position_at(head);
            let (_nid, cnd) = b.push_node(
                Inst::CmpInt { kind: crate::wir::CmpKind::Lt, a: i_phi, b: len },
                Some(Type::Bool), 1, false);
            b.branch(cnd[0], body, exit);

            b.position_at(body);
            let (_nid, elr) = b.push_node(
                Inst::CallNative { name: "wir_array_get".into(), args: vec![arr, i_phi], pure: false, can_throw: false },
                None, 1, true);
            let el = elr[0];

            let (_nid, pred) = b.push_node(
                Inst::CallClosure { conv: crate::wir::CallConv::Fast, fun, args: vec![el] },
                Some(Type::Bool), 1, true);

            let then_b = b.block();
            let cont_b = b.block();
            b.branch(pred[0], then_b, cont_b);

            b.position_at(then_b);
            let (_nid, _pushed) = b.push_node(
                Inst::CallNative { name: "wir_array_push".into(), args: vec![out, el], pure: false, can_throw: false },
                Some(Type::Int32), 1, true);
            b.jump(cont_b, &[]);

            b.position_at(cont_b);
            let next = b.int_bin(crate::wir::IntBinOp::Add, i_phi, one);
            b.jump(head, &[next]);

            b.position_at(exit);
            return Ok(Some(out));
        }

        // ---- forEach: just invoke, return 0
        "forEach" => {
            if args.len() != 1 { return Err(LowerError::NotLowerable("forEach expects 1 arg")); }
            let fun = lower_expr_free(b, locals, _fields, _next_field, &args[0], funcs, lam_caps)?;

            let (_nid, len_res) = b.push_node(
                Inst::CallNative { name: "wir_array_len".into(), args: vec![arr], pure: false, can_throw: false },
                Some(Type::Int32), 1, true);
            let len = len_res[0];

            let zero = b.const_i32(0);
            let one  = b.const_i32(1);

            let head = b.block();
            let body = b.block();
            let exit = b.block();

            let i_phi = b.add_block_param(head, Type::Int32);
            b.jump(head, &[zero]);
            b.position_at(head);
            let (_nid, cnd) = b.push_node(
                Inst::CmpInt { kind: crate::wir::CmpKind::Lt, a: i_phi, b: len },
                Some(Type::Bool), 1, false);
            b.branch(cnd[0], body, exit);

            b.position_at(body);
            let (_nid, elr) = b.push_node(
                Inst::CallNative { name: "wir_array_get".into(), args: vec![arr, i_phi], pure: false, can_throw: false },
                None, 1, true);
            let el = elr[0];

            let (_nid, _ignored) = b.push_node(
                Inst::CallClosure { conv: crate::wir::CallConv::Fast, fun, args: vec![el] },
                Some(Type::Int32), 1, true);

            let next = b.int_bin(crate::wir::IntBinOp::Add, i_phi, one);
            b.jump(head, &[next]);

            b.position_at(exit);
            let z = b.const_i32(0);
            return Ok(Some(z));
        }

        // ---- reduce: closure(acc, el)
        "reduce" => {
            use crate::wir::{CallConv, CmpKind, IntBinOp, Inst, Type};

            if !(args.len() == 1 || args.len() == 2) {
                return Err(LowerError::NotLowerable("reduce expects (fn) or (fn, init)"));
            }

            let fun = lower_expr_free(b, locals, _fields, _next_field, &args[0], funcs, lam_caps)?;

            // len(arr)
            let (_nid, len_res) = b.push_node(
                Inst::CallNative { name: "wir_array_len".into(), args: vec![arr], pure: false, can_throw: false },
                Some(Type::Int32), 1, true,
            );
            let len = len_res[0];

            let zero = b.const_i32(0);
            let one  = b.const_i32(1);

            // --- Seed (i0, acc0)
            // Use init if provided, else: if len==0 -> (0,0), else -> (1, arr[0])
            let seed_join = b.block();
            let seed_i    = b.add_block_param(seed_join, Type::Int32);
            let seed_acc  = b.add_block_param(seed_join, Type::Int32);

            if args.len() == 2 {
                let init = lower_expr_free(b, locals, _fields, _next_field, &args[1], funcs, lam_caps)?;
                b.jump(seed_join, &[zero, init]);
            } else {
                let empty_b    = b.block();
                let nonempty_b = b.block();

                let (_nid, is_empty) = b.push_node(
                    Inst::CmpInt { kind: CmpKind::Eq, a: len, b: zero },
                    Some(Type::Bool), 1, false,
                );
                b.branch(is_empty[0], empty_b, nonempty_b);

                b.position_at(empty_b);
                b.jump(seed_join, &[zero, zero]);

                b.position_at(nonempty_b);
                let (_nid, first_r) = b.push_node(
                    Inst::CallNative { name: "wir_array_get".into(), args: vec![arr, zero], pure: false, can_throw: false },
                    None, 1, true,
                );
                b.jump(seed_join, &[one, first_r[0]]);
            }

            // --- Main loop: phis (i, acc)
            b.position_at(seed_join);

            let head = b.block();
            let body = b.block();
            let exit = b.block();
            let cont = b.block();
            let res  = b.add_block_param(cont, Type::Int32);

            let i_phi   = b.add_block_param(head, Type::Int32);
            let acc_phi = b.add_block_param(head, Type::Int32);
            b.jump(head, &[seed_i, seed_acc]);

            b.position_at(head);
            let (_nid, cnd) = b.push_node(
                Inst::CmpInt { kind: CmpKind::Lt, a: i_phi, b: len },
                Some(Type::Bool), 1, false,
            );
            b.branch(cnd[0], body, exit); // <-- no direct branch to cont

            b.position_at(body);
            let (_nid, el_r) = b.push_node(
                Inst::CallNative { name: "wir_array_get".into(), args: vec![arr, i_phi], pure: false, can_throw: false },
                None, 1, true,
            );
            let el = el_r[0];

            let (_nid, acc2) = b.push_node(
                Inst::CallClosure { conv: CallConv::Fast, fun, args: vec![acc_phi, el] },
                Some(Type::Int32), 1, true,
            );

            let next_i = b.int_bin(IntBinOp::Add, i_phi, one);
            b.jump(head, &[next_i, acc2[0]]);

            b.position_at(exit);
            b.jump(cont, &[acc_phi]);     // <-- pass the phi into cont

            b.position_at(cont);
            return Ok(Some(res));
        }

        // ---- find: return first matching element, else 0
        "find" => {
            if args.len() != 1 { return Err(LowerError::NotLowerable("find expects 1 arg")); }
            let fun = lower_expr_free(b, locals, _fields, _next_field, &args[0], funcs, lam_caps)?;

            let (_nid, len_res) = b.push_node(
                Inst::CallNative { name: "wir_array_len".into(), args: vec![arr], pure: false, can_throw: false },
                Some(Type::Int32), 1, true);
            let len = len_res[0];

            let zero = b.const_i32(0);
            let one  = b.const_i32(1);

            let head = b.block();
            let body = b.block();
            let exit = b.block();
            let cont = b.block();
            let resp = b.add_block_param(cont, Type::Int32);

            let i_phi = b.add_block_param(head, Type::Int32);
            b.jump(head, &[zero]);

            b.position_at(head);
            let (_nid, cnd) = b.push_node(
                Inst::CmpInt { kind: crate::wir::CmpKind::Lt, a: i_phi, b: len },
                Some(Type::Bool), 1, false);
            b.branch(cnd[0], body, exit);

            b.position_at(body);
            let (_nid, elr) = b.push_node(
                Inst::CallNative { name: "wir_array_get".into(), args: vec![arr, i_phi], pure: false, can_throw: false },
                None, 1, true);
            let el = elr[0];

            let (_nid, hit) = b.push_node(
                Inst::CallClosure { conv: crate::wir::CallConv::Fast, fun, args: vec![el] },
                Some(Type::Bool), 1, true);

            let then_b = b.block();
            let cont_b = b.block();
            b.branch(hit[0], then_b, cont_b);

            b.position_at(then_b);
            b.jump(cont, &[el]);

            b.position_at(cont_b);
            let next = b.int_bin(crate::wir::IntBinOp::Add, i_phi, one);
            b.jump(head, &[next]);

            b.position_at(exit);
            b.jump(cont, &[zero]);

            b.position_at(cont);
            return Ok(Some(resp));
        }

        // ---- findIndex: return index or -1
        "findIndex" => {
            if args.len() != 1 { return Err(LowerError::NotLowerable("findIndex expects 1 arg")); }
            let fun = lower_expr_free(b, locals, _fields, _next_field, &args[0], funcs, lam_caps)?;

            let (_nid, len_res) = b.push_node(
                Inst::CallNative { name: "wir_array_len".into(), args: vec![arr], pure: false, can_throw: false },
                Some(Type::Int32), 1, true);
            let len = len_res[0];

            let zero = b.const_i32(0);
            let one  = b.const_i32(1);
            let neg1 = b.const_i32(-1);

            let head = b.block();
            let body = b.block();
            let exit = b.block();
            let cont = b.block();
            let resp = b.add_block_param(cont, Type::Int32);

            let i_phi = b.add_block_param(head, Type::Int32);
            b.jump(head, &[zero]);

            b.position_at(head);
            let (_nid, cnd) = b.push_node(
                Inst::CmpInt { kind: crate::wir::CmpKind::Lt, a: i_phi, b: len },
                Some(Type::Bool), 1, false);
            b.branch(cnd[0], body, exit);

            b.position_at(body);
            let (_nid, elr) = b.push_node(
                Inst::CallNative { name: "wir_array_get".into(), args: vec![arr, i_phi], pure: false, can_throw: false },
                None, 1, true);
            let el = elr[0];

            let (_nid, hit) = b.push_node(
                Inst::CallClosure { conv: crate::wir::CallConv::Fast, fun, args: vec![el] },
                Some(Type::Bool), 1, true);

            let then_b = b.block();
            let cont_b = b.block();
            b.branch(hit[0], then_b, cont_b);

            b.position_at(then_b);
            b.jump(cont, &[i_phi]);

            b.position_at(cont_b);
            let next = b.int_bin(crate::wir::IntBinOp::Add, i_phi, one);
            b.jump(head, &[next]);

            b.position_at(exit);
            b.jump(cont, &[neg1]);

            b.position_at(cont);
            return Ok(Some(resp));
        }

        _ => {}
    }

    Ok(None)
}

fn lower_expr_free<'m>(
    b: &mut Builder<'m>,
    locals: &mut HashMap<String, ValueId>,
    fields: &mut HashMap<String, FieldId>,
    next_field: &mut u32,
    e: &Expr,
    funcs: &HashMap<String, FuncId>,
    lam_caps: &HashMap<String, Vec<String>>,
) -> LResult<ValueId> {
    use BinOp::*;

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

        // If 'await' ever reaches the sync lowerer, give a precise error.
        Expr::Await(_) => {
            return Err(LowerError::NotLowerable("await outside async function"));
        }
        // Unhoisted function literal shouldn't reach the lowerer
        Expr::FnLit { .. } => {
            return Err(LowerError::NotLowerable("unhoisted function literal reached lowerer"));
        }

        // locals first, else known function -> a closure with null env
        Expr::Ident(name) => {
            // If this local is "boxed" (captured), read box[0].
            if locals.get(&boxed_key(name)).is_some() {
                let box_arr = *locals.get(name).ok_or_else(|| LowerError::UnknownVar(name.clone()))?;
                let zero = b.const_i32(0);
                let (_nid, res) = b.push_node(
                    Inst::CallNative { name: "wir_array_get".into(), args: vec![box_arr, zero], pure: false, can_throw: false },
                    None,
                    1,
                    true,
                );
                Ok(res[0])
            } else if let Some(&v) = locals.get(name) {
                Ok(v)
            } else if let Some(&fid) = funcs.get(name) {
                // Name is a global function: return a closure with null env.
                let (_nid, env_null) = b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                let (_nid, clos) = b.push_node(
                    Inst::MakeClosure { callee: fid, env: env_null[0] },
                    Some(Type::Closure(None)),
                    1,
                    false,
                );
                Ok(clos[0])
            } else {
                Err(LowerError::UnknownVar(name.clone()))
            }
        }

        Expr::Group(inner) => lower_expr_free(b, locals, fields, next_field, inner, funcs, lam_caps),

        Expr::Unary { op, e } => {
            let v = lower_expr_free(b, locals, fields, next_field, e, funcs, lam_caps)?;
            match op {
                UnOp::Neg => { let zero = b.const_i32(0); Ok(b.int_bin(IntBinOp::Sub, zero, v)) }
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
            let va = lower_expr_free(b, locals, fields, next_field, a, funcs, lam_caps)?;
            let vb = lower_expr_free(b, locals, fields, next_field, bb, funcs, lam_caps)?;
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
                    let (_nid, res) = b.push_node(Inst::CmpInt { kind, a: va, b: vb }, Some(Type::Bool), 1, false);
                    Ok(res[0])
                }
                And | Or => {
                    let then_b = b.block();
                    let else_b = b.block();
                    let cont   = b.block();
                    let res_param = b.add_block_param(cont, Type::Bool);

                    if *op == And { b.branch(va, then_b, else_b); } else { b.branch(va, else_b, then_b); }

                    b.position_at(then_b);
                    let tval = if *op == And {
                        lower_expr_free(b, locals, fields, next_field, bb, funcs, lam_caps)?
                    } else {
                        let (_nid, res) = b.push_node(Inst::Const(Constant::Bool(true)), Some(Type::Bool), 1, false);
                        res[0]
                    };
                    b.jump(cont, &[tval]);

                    b.position_at(else_b);
                    let fval = if *op == And {
                        let (_nid, res) = b.push_node(Inst::Const(Constant::Bool(false)), Some(Type::Bool), 1, false);
                        res[0]
                    } else {
                        lower_expr_free(b, locals, fields, next_field, bb, funcs, lam_caps)?
                    };
                    b.jump(cont, &[fval]);

                    b.position_at(cont);
                    Ok(res_param)
                }
            }
        }

        Expr::Assign(lv, rhs) => {
            let rv = lower_expr_free(b, locals, fields, next_field, rhs, funcs, lam_caps)?;
            match &**lv {
                // o.a = rv      (dot write)
                LValue::GetProp { recv, name } => {
                    let obj = lower_expr_free(b, locals, fields, next_field, recv, funcs, lam_caps)?;

                    // Special-case: arr.length = n
                    if name == "length" {
                        let (_nid, _r) = b.push_node(
                            Inst::CallNative {
                                name: "wir_array_set_len".into(),
                                args: vec![obj, rv],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                        return Ok(rv);
                    }

                    // 1) Store fast field
                    let field = intern_field_local(fields, next_field, name);
                    let _ = b.push_node(
                        Inst::StoreField { obj, field, val: rv, expected: None },
                        Some(Type::Top),
                        1,
                        true,
                    );

                    // 2) Mirror into string table
                    let (_nid_sconst, ks) =
                        b.push_node(Inst::Const(Constant::Str(name.clone())), Some(Type::Str), 1, false);
                    let _ = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_set_str".into(),
                            args: vec![obj, ks[0], rv],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );

                    Ok(rv)
                }

                // o["a"] = rv     (bracket write with string)
                LValue::Index { recv, index } if matches!(index, Expr::Str(_)) => {
                    let obj = lower_expr_free(b, locals, fields, next_field, recv, funcs, lam_caps)?;
                    let s = if let Expr::Str(s) = index { s } else { unreachable!() };

                    // 1) Store fast field
                    let field = intern_field_local(fields, next_field, s);
                    let _ = b.push_node(
                        Inst::StoreField { obj, field, val: rv, expected: None },
                        Some(Type::Top),
                        1,
                        true,
                    );

                    // 2) Mirror into string table
                    let (_nid, ks) = b.push_node(Inst::Const(Constant::Str(s.clone())), Some(Type::Str), 1, false);
                    let _ = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_set_str".into(),
                            args: vec![obj, ks[0], rv],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );

                    Ok(rv)
                }

                // --- inside Expr::Assign(lv, rhs) match ---
                LValue::Index { recv, index } if !matches!(index, Expr::Str(_)) => {
                    let obj  = lower_expr_free(b, locals, fields, next_field, recv,  funcs, lam_caps)?;
                    let idxv = lower_expr_free(b, locals, fields, next_field, index, funcs, lam_caps)?;

                    let (_nid_is, is_str) = b.push_node(
                        Inst::CallNative { name: "wir_is_str".into(), args: vec![idxv], pure: false, can_throw: false },
                        Some(Type::Bool), 1, true,
                    );

                    let str_b = b.block();
                    let arr_b = b.block();
                    let cont  = b.block();

                    b.branch(is_str[0], str_b, arr_b);

                    // object["key"] = rv  (also mirror into fast field if you want symmetry)
                    b.position_at(str_b);
                    let (_nid_set_s, _r_s) = b.push_node(
                        Inst::CallNative { name: "wir_obj_set_str".into(), args: vec![obj, idxv, rv], pure: false, can_throw: false },
                        Some(Type::Int32), 1, true,
                    );
                    b.jump(cont, &[]);

                    // array[index] = rv
                    b.position_at(arr_b);
                    let (_nid_set_a, _r_a) = b.push_node(
                        Inst::CallNative { name: "wir_array_set".into(), args: vec![obj, idxv, rv], pure: false, can_throw: false },
                        Some(Type::Int32), 1, true,
                    );
                    b.jump(cont, &[]);

                    b.position_at(cont);
                    Ok(rv)
                }

                // x = rv          (local write, with capture boxing support)
                LValue::Ident(name) => {
                    if locals.get(&boxed_key(name)).is_some() {
                        let box_arr = *locals.get(name).ok_or_else(|| LowerError::UnknownVar(name.clone()))?;
                        let zero = b.const_i32(0);
                        let (_nid, _res) = b.push_node(
                            Inst::CallNative {
                                name: "wir_array_set".into(),
                                args: vec![box_arr, zero, rv],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Int32),
                            1,
                            true,
                        );
                        Ok(rv)
                    } else {
                        if locals.contains_key(name) {
                            locals.insert(name.clone(), rv);
                            Ok(rv)
                        } else {
                            Err(LowerError::UnknownVar(name.clone()))
                        }
                    }
                }

                _ => Err(LowerError::NotLowerable("invalid lvalue"))
            }
        }

        // obj.<propKey>  where propKey is an identifier or string
        Expr::GetPropObj { obj, key } => {
            let o = lower_expr_free(b, locals, fields, next_field, obj, funcs, lam_caps)?;
            let (field_name, is_ident) = match key {
                PropKey::Ident(s) => (s.clone(), true),
                PropKey::Str(s)   => (s.clone(), false),
            };

            // Fast field first, then string table fallback
            let field   = intern_field_local(fields, next_field, &field_name);
            let fid_smi = b.const_i32(field.0 as i32);

            let (_nid_h, hasf) = b.push_node(
                Inst::CallNative { name: "wir_obj_has_field".into(), args: vec![o, fid_smi], pure: false, can_throw: false },
                Some(Type::Bool), 1, true,
            );

            let then_b = b.block();
            let else_b = b.block();
            let cont   = b.block();
            let out    = b.add_block_param(cont, Type::Int32);

            b.branch(hasf[0], then_b, else_b);

            b.position_at(then_b);
            let (_nid_f, fv) = b.push_node(Inst::LoadField { obj: o, field, expected: None }, None, 1, false);
            b.jump(cont, &[fv[0]]);

            b.position_at(else_b);
            let (_nid_sc, ks) = b.push_node(Inst::Const(Constant::Str(field_name)), Some(Type::Str), 1, false);
            let (_nid_s, sv)  = b.push_node(
                Inst::CallNative { name: "wir_obj_get_str".into(), args: vec![o, ks[0]], pure: false, can_throw: false },
                None, 1, true,
            );
            b.jump(cont, &[sv[0]]);

            b.position_at(cont);
            Ok(out)
        }

        // obj.<propKey> = value   (identifier or string propKey)
        Expr::SetPropObj { obj, key, value } => {
            let o  = lower_expr_free(b, locals, fields, next_field, obj, funcs, lam_caps)?;
            let v  = lower_expr_free(b, locals, fields, next_field, value, funcs, lam_caps)?;
            let field_name = match key {
                PropKey::Ident(s) => s.clone(),
                PropKey::Str(s)   => s.clone(),
            };

            // 1) fast field store
            let field = intern_field_local(fields, next_field, &field_name);
            let _ = b.push_node(
                Inst::StoreField { obj: o, field, val: v, expected: None },
                Some(Type::Top), 1, true,
            );

            // 2) mirror in string table
            let (_nid_sc, ks) = b.push_node(Inst::Const(Constant::Str(field_name)), Some(Type::Str), 1, false);
            let _ = b.push_node(
                Inst::CallNative { name: "wir_obj_set_str".into(), args: vec![o, ks[0], v], pure: false, can_throw: false },
                Some(Type::Int32), 1, true,
            );

            Ok(v)
        }

        // Calls / builtins
        Expr::Call { callee, args } => {
            // 0) Promise methods: p.then(...) / p.catch(...)
            if let Expr::GetProp { recv, name } = &**callee {
                if name == "then" {
                    // p.then(onFulfilled?, onRejected?)
                    let p   = lower_expr_free(b, locals, fields, next_field, recv, funcs, lam_caps)?;
                    let z   = b.const_i32(0); // sentinel "no callback"
                    let onf = if args.len() >= 1 {
                        lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?
                    } else { z };
                    let onr = if args.len() >= 2 {
                        lower_expr_free(b, locals, fields, next_field, &args[1], funcs, lam_caps)?
                    } else { z };
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_promise_then".into(),
                            args: vec![p, onf, onr],
                            pure: false, can_throw: false,
                        },
                        None, 1, true,
                    );
                    return Ok(res[0]);
                }
                if name == "catch" {
                    // p.catch(onRejected?)
                    let p   = lower_expr_free(b, locals, fields, next_field, recv, funcs, lam_caps)?;
                    let z   = b.const_i32(0);
                    let onr = if args.len() >= 1 {
                        lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?
                    } else { z };
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_promise_catch".into(),
                            args: vec![p, onr],
                            pure: false, can_throw: false,
                        },
                        None, 1, true,
                    );
                    return Ok(res[0]);
                }

                if name == "resolve" {
                    let p = lower_expr_free(b, locals, fields, next_field, recv, funcs, lam_caps)?;
                    // default to null if no value was given
                    let (_nid, nul) = b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                    let val = if args.len() >= 1 {
                        lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?
                    } else { nul[0] };
                    let (_nid, res) = b.push_node(
                        Inst::CallNative { name: "wir_deferred_resolve".into(), args: vec![p, val], pure: false, can_throw: false },
                        None, 1, true,
                    );
                    return Ok(res[0]); // returns the same deferred for optional chaining
                }
                if name == "reject" {
                    let p = lower_expr_free(b, locals, fields, next_field, recv, funcs, lam_caps)?;
                    let (_nid, nul) = b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                    let reason = if args.len() >= 1 {
                        lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?
                    } else { nul[0] };
                    let (_nid, res) = b.push_node(
                        Inst::CallNative { name: "wir_deferred_reject".into(), args: vec![p, reason], pure: false, can_throw: false },
                        None, 1, true,
                    );
                    return Ok(res[0]);
                }

                            // --- http.* helpers ---
            if let Expr::GetProp { recv, name } = &**callee {
                // --- http.* helpers ---
                if let Expr::Ident(obj) = &**recv {
                    if obj == "http" {
                        match name.as_str() {
                            "startStream" => {
                                if args.len() != 3 {
                                    return Err(LowerError::NotLowerable("http.startStream(req, status, headers)"));
                                }
                                let req    = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                                let status = lower_expr_free(b, locals, fields, next_field, &args[1], funcs, lam_caps)?;
                                let hdrs   = lower_expr_free(b, locals, fields, next_field, &args[2], funcs, lam_caps)?;
                                let (_nid, res) = b.push_node(
                                    Inst::CallNative {
                                        name: "wir_http_start_stream_from_req".into(),
                                        args: vec![req, status, hdrs],
                                        pure: false,
                                        can_throw: false,
                                    },
                                    Some(Type::Int32), 1, true
                                );
                                return Ok(res[0]);
                            }
                            "streamWrite" => {
                                if args.len() != 3 {
                                    return Err(LowerError::NotLowerable("http.streamWrite(serverId, reqId, chunk)"));
                                }
                                let sid   = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                                let rid   = lower_expr_free(b, locals, fields, next_field, &args[1], funcs, lam_caps)?;
                                let chunk = lower_expr_free(b, locals, fields, next_field, &args[2], funcs, lam_caps)?;
                                let (_nid, res) = b.push_node(
                                    Inst::CallNative {
                                        name: "wir_http_stream_write".into(),
                                        args: vec![sid, rid, chunk],
                                        pure: false,
                                        can_throw: false,
                                    },
                                    Some(Type::Int32), 1, true
                                );
                                return Ok(res[0]);
                            }
                            "streamEnd" => {
                                if args.len() != 2 {
                                    return Err(LowerError::NotLowerable("http.streamEnd(serverId, reqId)"));
                                }
                                let sid = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                                let rid = lower_expr_free(b, locals, fields, next_field, &args[1], funcs, lam_caps)?;
                                let (_nid, res) = b.push_node(
                                    Inst::CallNative {
                                        name: "wir_http_stream_end".into(),
                                        args: vec![sid, rid],
                                        pure: false,
                                        can_throw: false,
                                    },
                                    Some(Type::Int32), 1, true
                                );
                                return Ok(res[0]);
                            }
                            _ => {}
                        }
                    }

                    if obj == "json" {
                        // Allow json(body) or json(status, body[, headers])
                        let (_nid_null, nul) = b.push_node(
                            Inst::Const(Constant::Null),
                            Some(Type::Null),
                            1,
                            false
                        );

                        let (status_v, body_v, headers_v) = match args.len() {
                            1 => {
                                let body = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                                let status = b.const_i32(200);    // default 200
                                (status, body, nul[0])
                            }
                            2 => {
                                let status = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                                let body   = lower_expr_free(b, locals, fields, next_field, &args[1], funcs, lam_caps)?;
                                (status, body, nul[0])
                            }
                            3 => {
                                let status  = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                                let body    = lower_expr_free(b, locals, fields, next_field, &args[1], funcs, lam_caps)?;
                                let headers = lower_expr_free(b, locals, fields, next_field, &args[2], funcs, lam_caps)?;
                                (status, body, headers)
                            }
                            _ => return Err(LowerError::NotLowerable("json expects (body) or (status, body[, headers])")),
                        };

                        // Call a native that formats/sends a JSON response.
                        // Name it to match your runtime; adjust if you use a different symbol.
                        let (_nid, res) = b.push_node(
                            Inst::CallNative {
                                name: "wir_http_send_json".into(),
                                args: vec![status_v, body_v, headers_v],
                                pure: false,
                                can_throw: false,
                            },
                            None,
                            1,
                            true,
                        );
                        return Ok(res[0]);
                    }
                }
            }

            // 1) Array methods (existing)
            if let Some(v) = lower_array_method_call(
                    b, locals, fields, next_field, recv, name, args, funcs, lam_caps
                )? {
                    return Ok(v);
                }
            }

            // 1) Array methods: a.push(x), a.map(f), ...
            if let Expr::GetProp { recv, name } = &**callee {
                if let Some(v) = lower_array_method_call(
                    b, locals, fields, next_field, recv, name, args, funcs, lam_caps
                )? {
                    return Ok(v);
                }
            }

            if let Expr::Ident(name) = &**callee {
                if name == "setTimeout" {
                    if args.len() != 2 { return Err(LowerError::NotLowerable("setTimeout(fn, ms)")); }
                    let fun = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                    let ms  = lower_expr_free(b, locals, fields, next_field, &args[1], funcs, lam_caps)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_set_timeout".into(),
                            args: vec![fun, ms],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32), // returns timer id (i64/SMI-ish, treat as int)
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "setInterval" {
                    if args.len() != 2 { return Err(LowerError::NotLowerable("setInterval(fn, ms)")); }
                    let fun = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                    let ms  = lower_expr_free(b, locals, fields, next_field, &args[1], funcs, lam_caps)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_set_interval".into(),
                            args: vec![fun, ms],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "clearTimeout" {
                    if args.len() != 1 { return Err(LowerError::NotLowerable("clearTimeout(id)")); }
                    let id = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_clear_timeout".into(),
                            args: vec![id],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
                if name == "clearInterval" {
                    if args.len() != 1 { return Err(LowerError::NotLowerable("clearInterval(id)")); }
                    let id = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_clear_interval".into(),
                            args: vec![id],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
            }

            // 2) Builtin functions: list(n), print(x)
            if let Expr::Ident(name) = &**callee {
                if name == "Array" {
                    if args.len() != 1 { return Err(LowerError::NotLowerable("list() expects 1 arg")); }
                    let len = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_array_new".into(),
                            args: vec![len],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Array(Box::new(None))),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }

                if name == "Promise" {
                    if args.len() != 1 { return Err(LowerError::NotLowerable("Promise() expects 1 arg")); }

                    let exec = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative { name: "wir_promise_new".into(), args: vec![exec], pure: false, can_throw: false },
                        None, 1, true,
                    );
                    return Ok(res[0]);
                }
                if name == "Deferred" {
                    if !args.is_empty() { return Err(LowerError::NotLowerable("Deferred() expects 0 args")); }
                    let (_nid, res) = b.push_node(
                        Inst::CallNative { name: "wir_deferred_new".into(), args: vec![], pure: false, can_throw: false },
                        None, 1, true,
                    );
                    return Ok(res[0]);
                }

                if name == "get" {
                    if args.len() != 1 { return Err(LowerError::NotLowerable("get(url) expects 1 arg")); }
                    let url = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_http_get".into(),
                            args: vec![url],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]); // resolves to a promise; `await` will use wir_await
                }

                if name == "print" {
                    if args.len() != 1 { return Err(LowerError::NotLowerable("print() expects 1 arg")); }

                    // 1) If it’s a string literal, use the string printer directly.
                    if matches!(args[0], Expr::Str(_)) {
                        let v = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                        let (_nid, res) = b.push_node(
                            Inst::CallNative {
                                name: "wir_print_str".into(),
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

                    // 2) If it’s “bool-ish”, coerce Bool → i32 {false:0, true:1} then print as i64.
                    let is_boolish = matches!(
                        args[0],
                        // comparisons / equality
                        Expr::Binary { op: BinOp::Eq  , .. }
                        | Expr::Binary { op: BinOp::Ne , .. }
                        | Expr::Binary { op: BinOp::Lt , .. }
                        | Expr::Binary { op: BinOp::Le , .. }
                        | Expr::Binary { op: BinOp::Gt , .. }
                        | Expr::Binary { op: BinOp::Ge , .. }
                        // logical operators (already return Bool)
                        | Expr::Binary { op: BinOp::And, .. }
                        | Expr::Binary { op: BinOp::Or , .. }
                        // unary not
                        | Expr::Unary  { op: UnOp::Not, .. }
                        // the `in` operator
                        | Expr::In { .. }
                    );

                    let v0 = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;

                    // If bool-ish, branch to synthesize 0/1; else, pass the value directly.
                    let v_to_print = if is_boolish {
                        let then_b = b.block();
                        let else_b = b.block();
                        let cont   = b.block();
                        let out_i  = b.add_block_param(cont, Type::Int32);

                        b.branch(v0, then_b, else_b);

                        b.position_at(then_b);
                        let one = b.const_i32(1);
                        b.jump(cont, &[one]);

                        b.position_at(else_b);
                        let zero = b.const_i32(0);
                        b.jump(cont, &[zero]);

                        b.position_at(cont);
                        out_i
                    } else {
                        v0
                    };

                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_print_i64".into(),
                            args: vec![v_to_print],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }

                if name == "getJSON" {
                    if args.len() != 1 { return Err(LowerError::NotLowerable("getJSON(url) expects 1 arg")); }
                    let url = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_http_get_json".into(),
                            args: vec![url],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }

                if name == "postJSON" {
                    if !(args.len() == 2 || args.len() == 3) {
                        return Err(LowerError::NotLowerable("postJSON(url, body, headers?)"));
                    }
                    let url  = lower_expr_free(b, locals, fields, next_field, &args[0], funcs, lam_caps)?;
                    let body = lower_expr_free(b, locals, fields, next_field, &args[1], funcs, lam_caps)?;
                    // headers is optional → default null
                    let (_nid_null, nul) = b.push_node(Inst::Const(Constant::Null), Some(Type::Null), 1, false);
                    let headers = if args.len() == 3 {
                        lower_expr_free(b, locals, fields, next_field, &args[2], funcs, lam_caps)?
                    } else {
                        nul[0]
                    };
                    let (_nid, res) = b.push_node(
                        Inst::CallNative {
                            name: "wir_http_post_json".into(),
                            args: vec![url, body, headers],
                            pure: false,
                            can_throw: false,
                        },
                        None,
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }

                if let Some(&fid) = funcs.get(name) {
                    let mut argv = Vec::with_capacity(args.len());
                    for a in args { argv.push(lower_expr_free(b, locals, fields, next_field, a, funcs, lam_caps)?); }
                    let (_nid, res) = b.push_node(
                        Inst::CallDirect { conv: crate::wir::CallConv::Fast, callee: fid, args: argv },
                        Some(Type::Int32),
                        1,
                        true,
                    );
                    return Ok(res[0]);
                }
            }

            // generic: fun value + CallClosure
            let funv = lower_expr_free(b, locals, fields, next_field, callee, funcs, lam_caps)?;
            let mut argv = Vec::with_capacity(args.len());
            for a in args { argv.push(lower_expr_free(b, locals, fields, next_field, a, funcs, lam_caps)?); }
            let (_nid, res) = b.push_node(
                Inst::CallClosure { conv: crate::wir::CallConv::Fast, fun: funv, args: argv },
                Some(Type::Int32),
                1,
                true,
            );
            Ok(res[0])
        }

        // Property / Index
        Expr::GetProp { recv, name } => {
            // Special-case: arr.length
            if name == "length" {
                let arr = lower_expr_free(b, locals, fields, next_field, recv, funcs, lam_caps)?;
                let (_nid, res) = b.push_node(
                    Inst::CallNative {
                        name: "wir_array_len".into(),
                        args: vec![arr],
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
                return Ok(res[0]);
            }

            // Unify: prefer fast field if present, else string table
            let obj     = lower_expr_free(b, locals, fields, next_field, recv, funcs, lam_caps)?;
            let field   = intern_field_local(fields, next_field, name);
            let fid_smi = b.const_i32(field.0 as i32);

            let (_nid_h, hasf) = b.push_node(
                Inst::CallNative {
                    name: "wir_obj_has_field".into(),
                    args: vec![obj, fid_smi],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Bool),
                1,
                true,
            );

            let then_b = b.block();
            let else_b = b.block();
            let cont   = b.block();
            let out    = b.add_block_param(cont, Type::Int32);

            b.branch(hasf[0], then_b, else_b);

            b.position_at(then_b);
            let (_nid_f, fv) = b.push_node(
                Inst::LoadField { obj, field, expected: None },
                None,
                1,
                false,
            );
            b.jump(cont, &[fv[0]]);

            b.position_at(else_b);
            let (_nid_sc, ks) = b.push_node(
                Inst::Const(Constant::Str(name.clone())),
                Some(Type::Str),
                1,
                false,
            );
            let (_nid_s, sv) = b.push_node(
                Inst::CallNative {
                    name: "wir_obj_get_str".into(),
                    args: vec![obj, ks[0]],
                    pure: false,
                    can_throw: false,
                },
                None,
                1,
                true,
            );
            b.jump(cont, &[sv[0]]);

            b.position_at(cont);
            Ok(out)
        }

        Expr::Index { recv, index } => {
            // Fast path: string literal → unify with field access (fast-field if present, else string table)
            if let Expr::Str(s) = &**index {
                let obj     = lower_expr_free(b, locals, fields, next_field, recv, funcs, lam_caps)?;
                let field   = intern_field_local(fields, next_field, s);
                let fid_smi = b.const_i32(field.0 as i32);

                let (_nid_h, hasf) = b.push_node(
                    Inst::CallNative { name: "wir_obj_has_field".into(), args: vec![obj, fid_smi], pure: false, can_throw: false },
                    Some(Type::Bool), 1, true,
                );

                let then_b = b.block();
                let else_b = b.block();
                let cont   = b.block();
                let out    = b.add_block_param(cont, Type::Int32);

                b.branch(hasf[0], then_b, else_b);

                b.position_at(then_b);
                let (_nid_f, fv) = b.push_node(Inst::LoadField { obj, field, expected: None }, None, 1, false);
                b.jump(cont, &[fv[0]]);

                b.position_at(else_b);
                let (_nid_sc, ks) = b.push_node(Inst::Const(Constant::Str(s.clone())), Some(Type::Str), 1, false);
                let (_nid_s, sv)  = b.push_node(
                    Inst::CallNative { name: "wir_obj_get_str".into(), args: vec![obj, ks[0]], pure: false, can_throw: false },
                    None, 1, true,
                );
                b.jump(cont, &[sv[0]]);

                b.position_at(cont);
                return Ok(out);
            }

            // Generic path: decide at runtime. If index is a string → object["key"]; else → array[index].
            let obj  = lower_expr_free(b, locals, fields, next_field, recv,  funcs, lam_caps)?;
            let idxv = lower_expr_free(b, locals, fields, next_field, index, funcs, lam_caps)?;

            // Requires a tiny native: bool wir_is_str(value)
            let (_nid_is, is_str) = b.push_node(
                Inst::CallNative { name: "wir_is_str".into(), args: vec![idxv], pure: false, can_throw: false },
                Some(Type::Bool), 1, true,
            );

            let str_b = b.block();
            let arr_b = b.block();
            let cont  = b.block();
            let out   = b.add_block_param(cont, Type::Int32);

            b.branch(is_str[0], str_b, arr_b);

            // object["key"]
            b.position_at(str_b);
            let (_nid_s, sv) = b.push_node(
                Inst::CallNative { name: "wir_obj_get_str".into(), args: vec![obj, idxv], pure: false, can_throw: false },
                None, 1, true,
            );
            b.jump(cont, &[sv[0]]);

            // array[index]
            b.position_at(arr_b);
            let (_nid_a, av) = b.push_node(
                Inst::CallNative { name: "wir_array_get".into(), args: vec![obj, idxv], pure: false, can_throw: false },
                None, 1, true,
            );
            b.jump(cont, &[av[0]]);

            b.position_at(cont);
            Ok(out)
        }

        Expr::ArrayLit(elems) => {
            // Allocate array
            let len_v = b.const_i32(elems.len() as i32);
            let (_nid_new, new_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_array_new".into(),
                    args: vec![len_v],
                    pure: false,
                    can_throw: false,
                },
                Some(Type::Array(Box::new(None))),
                1,
                true,
            );
            let arr_v = new_res[0];
            // Back-compat alias in case older code still uses `arr`
            let arr = arr_v;

            // Fill it
            for (i, el) in elems.iter().enumerate() {
                let v   = lower_expr_free(b, locals, fields, next_field, el, funcs, lam_caps)?;
                let idx = b.const_i32(i as i32);
                let _ = b.push_node(
                    Inst::CallNative {
                        name: "wir_array_set".into(),
                        args: vec![arr, idx, v],
                        pure: false,
                        can_throw: false,
                    },
                    Some(Type::Int32),
                    1,
                    true,
                );
            }

            Ok(arr)
        }

        // Closure creation from hoisted lambda
        Expr::FnRef { name } => {
            let fid = *funcs.get(name).ok_or_else(|| LowerError::UnknownFunc(name.clone()))?;
            let caps = lam_caps.get(name).cloned().unwrap_or_default();

            // For each capture, if it is not boxed yet in this scope, box it now:
            //   box = Array(1); box[0] = current_value; rebind local to box; mark boxed.
            for cap in &caps {
                if locals.get(&boxed_key(cap)).is_none() {
                    let cur = *locals.get(cap).ok_or_else(|| LowerError::UnknownVar(cap.clone()))?;
                    let one = b.const_i32(1);
                    let (_nid, box_res) = b.push_node(
                        Inst::CallNative { name: "wir_array_new".into(), args: vec![one], pure: false, can_throw: false },
                        Some(Type::Array(Box::new(None))),
                        1, true);
                    let box_arr = box_res[0];
                    let zero = b.const_i32(0);
                    let _ = b.push_node(
                        Inst::CallNative { name: "wir_array_set".into(), args: vec![box_arr, zero, cur], pure: false, can_throw: false },
                        Some(Type::Int32),
                        1, true);
                    locals.insert(cap.clone(), box_arr);
                    locals.insert(boxed_key(cap), box_arr);
                }
            }

            // Build env array out of *boxes* (so inner lambda can mutate them)
            let len = b.const_i32(caps.len() as i32);
            let (_nid, env_res) = b.push_node(
                Inst::CallNative { name: "wir_array_new".into(), args: vec![len], pure: false, can_throw: false },
                Some(Type::Array(Box::new(None))),
                1, true);
            let env = env_res[0];
            for (i, cap) in caps.iter().enumerate() {
                let idx = b.const_i32(i as i32);
                let box_arr = *locals.get(cap).expect("boxed local present");
                let _ = b.push_node(
                    Inst::CallNative { name: "wir_array_set".into(), args: vec![env, idx, box_arr], pure: false, can_throw: false },
                    Some(Type::Int32),
                    1, true);
            }

            let (_nid, clos) = b.push_node(
                Inst::MakeClosure { callee: fid, env },
                Some(Type::Closure(None)),
                1,
                false,
            );
            Ok(clos[0])
        }

        Expr::ObjLit(props) => {
            // obj = wir_obj_new()
            let (_nid, obj_res) = b.push_node(
                Inst::CallNative {
                    name: "wir_obj_new".into(),
                    args: vec![],
                    pure: false,
                    can_throw: false,
                },
                None, // dynamic object
                1,
                true,
            );
            let obj = obj_res[0];

            for (key, val_e) in props {
                let v = lower_expr_free(b, locals, fields, next_field, val_e, funcs, lam_caps)?;
                match key {
                    PropKey::Ident(name) => {
                        // Use your fast slot path (stable, same as obj.x)
                        let field = intern_field_local(fields, next_field, name);
                        let _ = b.push_node(
                            Inst::StoreField { obj, field, val: v, expected: None },
                            Some(Type::Top),
                            1,
                            true,
                        );
                    }
                    PropKey::Str(s) => {
                        // General string key → native set(obj, "k", v)
                        let (_nid, ks) = b.push_node(Inst::Const(Constant::Str(s.clone())), Some(Type::Str), 1, false);
                        let _ = b.push_node(
                            Inst::CallNative {
                                name: "wir_obj_set_str".into(),
                                args: vec![obj, ks[0], v],
                                pure: false,
                                can_throw: false,
                            },
                            Some(Type::Int32), // ignore result
                            1,
                            true,
                        );
                    }
                }
            }

            Ok(obj)
        }

        Expr::DeleteProp { obj, key } => {
            let o = lower_expr_free(b, locals, fields, next_field, obj, funcs, lam_caps)?;

            match key {
                // delete o.a  — delete both field and string
                PropKey::Ident(name) => {
                    let field   = intern_field_local(fields, next_field, name);
                    let fid_smi = b.const_i32(field.0 as i32);

                    // del fast field
                    let (_nid_f, _rf) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_del_field".into(),
                            args: vec![o, fid_smi],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    // del string key (mirror)
                    let (_nid_sc, ks) = b.push_node(
                        Inst::Const(Constant::Str(name.clone())),
                        Some(Type::Str),
                        1,
                        false,
                    );
                    let (_nid_s, rs) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_del_str".into(),
                            args: vec![o, ks[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    Ok(rs[0]) // return last result (truthy if deleted)
                }

                // delete o["a"] — delete both string and field
                PropKey::Str(s) => {
                    // del string key
                    let (_nid_sc, ks) = b.push_node(
                        Inst::Const(Constant::Str(s.clone())),
                        Some(Type::Str),
                        1,
                        false,
                    );
                    let (_nid_s, rs) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_del_str".into(),
                            args: vec![o, ks[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    // del fast field mirror (safe even if not an identifier originally)
                    let field   = intern_field_local(fields, next_field, s);
                    let fid_smi = b.const_i32(field.0 as i32);
                    let (_nid_f, _rf) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_del_field".into(),
                            args: vec![o, fid_smi],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    Ok(rs[0])
                }
            }
        }

        Expr::In { key, obj } => {
            let o = lower_expr_free(b, locals, fields, next_field, obj, funcs, lam_caps)?;

            match &**key {
                // identifier key:  a in o
                Expr::Ident(name) => {
                    let field   = intern_field_local(fields, next_field, name);
                    let fid_smi = b.const_i32(field.0 as i32);

                    // fast-slot check
                    let (_nid_f, hf) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_has_field".into(),
                            args: vec![o, fid_smi],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    // string-table check
                    let (_nid_sc, ks) = b.push_node(
                        Inst::Const(Constant::Str(name.clone())),
                        Some(Type::Str),
                        1,
                        false,
                    );
                    let (_nid_s, hs) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_has_str".into(),
                            args: vec![o, ks[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    Ok(build_bool_or(b, hf[0], hs[0]))
                }

                // string-literal key:  "a" in o
                Expr::Str(s) => {
                    let field   = intern_field_local(fields, next_field, s);
                    let fid_smi = b.const_i32(field.0 as i32);

                    let (_nid_f, hf) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_has_field".into(),
                            args: vec![o, fid_smi],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    let (_nid_sc, ks) = b.push_node(
                        Inst::Const(Constant::Str(s.clone())),
                        Some(Type::Str),
                        1,
                        false,
                    );
                    let (_nid_s, hs) = b.push_node(
                        Inst::CallNative {
                            name: "wir_obj_has_str".into(),
                            args: vec![o, ks[0]],
                            pure: false,
                            can_throw: false,
                        },
                        Some(Type::Bool),
                        1,
                        true,
                    );

                    Ok(build_bool_or(b, hf[0], hs[0]))
                }

                _ => unreachable!(),
            }
        }

        _ => Err(LowerError::NotLowerable("expression type not supported"))
    }
}

fn intern_field_local(
    fields: &mut HashMap<String, FieldId>,
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

fn build_bool_or(b: &mut Builder, lhs: ValueId, rhs: ValueId) -> ValueId {
    // if lhs then true else rhs
    let then_b = b.block();
    let else_b = b.block();
    let cont   = b.block();
    let out    = b.add_block_param(cont, Type::Bool);

    b.branch(lhs, then_b, else_b);

    b.position_at(then_b);
    let (_nid_t, t) = b.push_node(Inst::Const(Constant::Bool(true)), Some(Type::Bool), 1, false);
    b.jump(cont, &[t[0]]);

    b.position_at(else_b);
    b.jump(cont, &[rhs]);

    b.position_at(cont);
    out
}

fn http_method_smi(method: &str) -> i32 {
    match method {
        "GET" | "get" => 1,
        "POST" | "post" => 2,
        "PUT" | "put" => 3,
        "DELETE" | "delete" => 4,
        "PATCH" | "patch" => 5,
        "OPTIONS" | "options" => 6,
        "HEAD" | "head" => 7,
        "*" | "ANY" | "any" => 0,
        _ => 0, // default ANY
    }
}

fn boxed_key(name: &str) -> String {
    format!("__boxed:{}", name)
}
