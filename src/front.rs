// src/front.rs
#![allow(unused_imports)]
#![allow(unused_variables)]

use logos::Logos;
use std::{collections::BTreeSet, ops::Deref};
use ahash::{AHashSet as HashSet, AHashMap as HashMap};
use std::collections::hash_map::Entry;
use smallbox::SmallBox;
use std::{path::PathBuf};
use hybrid_rc::Arc;
use ariadne::{Report, ReportKind, Label, Color, Source, FileCache, FnCache};

// Bring in the WIR types from your other file/module.
use crate::wir::{
    Builder, Constant, FieldId, FuncId, Inst, IntBinOp, Module, Type, ValueId,
    MethodInfo, AccessorInfo, BindingId, next_id,
};
use crate::modules::{ModuleId, ModulesCTX, ProgramBuilder, FSLoader, ModuleLoader};

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
    pub modules:   Vec<ModuleAST<'static>>,
}

#[derive(Debug, Clone)]
pub struct ModuleAST<'a> {
    pub id: ModuleId,
    pub path: Arc<PathBuf>,
    pub exports: HashMap<&'a str, ExportItem<'a>>,
    pub imports: HashMap<Arc<PathBuf>, ImportRequest<'a>>,
}

#[derive(Debug, Clone)]
pub struct ExportItem<'a> {
    pub name: &'a str,
    pub binding: BindingId,
}

#[derive(Debug, Clone)]
pub struct ImportRequest<'a> {
    pub from_path: Arc<PathBuf>,
    pub names: Vec<&'a str>,
    pub resolved: Vec<( &'a str, BindingId )>,
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
    pub fid: FuncId,
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
    DeleteIndex { obj: SmallBox<Expr, u8>, index: SmallBox<Expr, u8> },              // delete obj[expr]

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

#[derive(Debug, Clone)]
pub struct ParseError {
    pub msg: String,
    pub span: std::ops::Range<usize>,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} at {}", self.msg, self.span.start)
    }
}

pub type PResult<T> = Result<T, ParseError>;

#[derive(Clone)]
struct SpannedTok {
    tok: Tok,
    span: std::ops::Range<usize>,
}

impl ParseError {
    pub fn print(&self, src: &str, filename: Option<&str>) {
        let filename_str = filename.unwrap_or("<unknown>");
        let id = filename_str.to_string();
        let span_id = (id.clone(), self.span.clone());
        let report = Report::build(ReportKind::Error, span_id.clone())
            .with_message(&self.msg)
            .with_label(
                Label::new(span_id)
                    .with_message("error occurred here")
                    .with_color(Color::Red),
            )
            .finish();

        let mut cache = FnCache::new(move |file_id: &String| -> Result<String, &'static str> {
            if file_id == &id {
                Ok(src.to_string())
            } else {
                Err("Unknown file")
            }
        });
        let _ = report.eprint(&mut cache);
    }
}

pub struct Parser<'src> {
    toks: Vec<SpannedTok>,
    i: usize,
    _src: &'src str,

    lexer_errors: Vec<ParseError>,

    module_ptr: Option<*mut ModuleAST<'static>>,
    ctx: Option<*const ModulesCTX>,
    resolver: Option<*const ProgramBuilder>,
    referrer: Option<Arc<PathBuf>>,
}

impl<'src> Parser<'src> {
    pub fn new(
        src: &'src str,
    ) -> Self {
        let mut lex = Tok::lexer(src);
        let mut toks = Vec::new();
        let mut lexer_errors = Vec::new();

        while let Some(item) = lex.next() {
            match item {
                Ok(t) => {
                    let span = lex.span();
                    toks.push(SpannedTok { tok: t, span });
                }
                Err(_) => {
                    let span = lex.span();
                    let msg = format!("unrecognized sequence: {}", lex.slice());
                    lexer_errors.push(ParseError { msg, span });
                }
            }
        }

        Self { toks, i: 0, _src: src, lexer_errors, module_ptr: None, ctx: None, resolver: None, referrer: None }
    }

    pub fn with_module<'a>(
        src: &'src str,
        ctx: &'a ModulesCTX,
        resolver: &'a ProgramBuilder,
        module_ptr: *mut ModuleAST<'a>,
        referrer: Arc<PathBuf>,
    ) -> Self {
        let mut p = Self::new(src);
        p.module_ptr = Some(module_ptr as *mut ModuleAST<'static>);
        p.ctx = Some(ctx as *const _);
        p.resolver = Some(resolver as *const _);
        p.referrer = Some(referrer);
        p
    }

    #[inline(always)]
    fn peek(&self) -> Option<&SpannedTok> {
        if self.i < self.toks.len() {
            Some(&self.toks[self.i])
        } else {
            None
        }
    }

    fn next(&mut self) -> PResult<SpannedTok> {
        if self.is_eof() {
            let span = if let Some(last) = self.toks.last() {
                last.span.end..self._src.len()
            } else {
                0..0
            };
            Err(ParseError {
                msg: "unexpected end of file".to_string(),
                span,
            })
        } else {
            let t = self.toks[self.i].clone();
            self.i += 1;
            Ok(t)
        }
    }

    #[inline(always)]
    fn check(&self, t: &Tok) -> bool {
        if let Some(p) = self.peek() {
            &p.tok == t
        } else {
            false
        }
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
        if self.check(&t) {
            self.i += 1;
            Ok(())
        } else if self.is_eof() {
            let span = if let Some(last) = self.toks.last() {
                last.span.end..self._src.len()
            } else {
                0..0
            };
            Err(ParseError {
                msg: format!("unexpected end of file, {}", msg),
                span,
            })
        } else {
            let found = if let Some(p) = self.peek() {
                format!("found {:?}", p.tok)
            } else {
                "reached end of file".to_string()
            };
            Err(ParseError {
                msg: format!("{}; {}", msg, found),
                span: self.peek().map(|p| p.span.clone()).unwrap_or(0..0),
            })
        }
    }

    fn err_here(&self, msg: &str) -> ParseError {
        let span = if let Some(p) = self.peek() {
            p.span.clone()
        } else {
            if let Some(last) = self.toks.last() {
                last.span.end..self._src.len()
            } else {
                0..0
            }
        };
        ParseError {
            msg: msg.to_string(),
            span,
        }
    }

    #[inline(always)]
    fn is_eof(&self) -> bool {
        self.i >= self.toks.len()
    }

    #[inline(always)]
    fn check_ident(&self, s: &str) -> bool {
        if let Some(p) = self.peek() {
            matches!(&p.tok, Tok::Ident(name) if name == s)
        } else {
            false
        }
    }

    #[inline(always)]
    fn matches_ident(&mut self, s: &str) -> bool {
        if self.check_ident(s) {
            self.i += 1;
            true
        } else {
            false
        }
    }

    pub fn program(&mut self) -> PResult<Program> {
        if !self.lexer_errors.is_empty() {
            // Return the first lexer error as representative
            return Err(self.lexer_errors[0].clone());
        }

        let mut functions  = Vec::new();
        let mut classes   = Vec::new();
        let mut toplevel_stmts: Vec<Stmt> = Vec::new();

        let mut imports = Vec::new();
        let mut exports = Vec::new();

        while !self.is_eof() {
            if self.matches(&Tok::Semi) { continue; }

            if self.check(&Tok::Import) {
                imports.push(self.parse_import_decl()?);
            } else if self.check(&Tok::Export) {
                self.next()?; // consume 'export'
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
                fid: FuncId(next_id()),
                name: "__toplevel__".to_string(),
                params: Vec::new(),
                body: Block { stmts: toplevel_stmts },
                is_async: true, // Allows top-level async
            });
        }

        #[cfg(debug_assertions)]
        {
            // 1) Lo que el parser recogió por sintaxis (Program)
            eprintln!(
                "[parser:end] prog.syntactic imports={}, exports={}",
                imports.len(), exports.len()
            );

            // 2) Si tenemos ModuleAST real, dump de la cajita del módulo
            if let Some(m_ptr) = self.module_ptr {
                unsafe {
                    let m = &*m_ptr;
                    eprintln!(
                        "  [module-box] path={:?} imports={} exports={}",
                        m.path, m.imports.len(), m.exports.len()
                    );
                    if m.imports.is_empty() {
                        eprintln!("    [imports] (none)");
                    } else {
                        eprintln!("    [imports]");
                        for (key_path, req) in &m.imports {
                            let names = if req.names.is_empty() {
                                "(side-effect only)".to_string()
                            } else {
                                req.names.iter().map(|s| *s).collect::<Vec<_>>().join(", ")
                            };
                            eprintln!(
                                "      - key={:?}\n        from_path={:?}\n        names=[{}]\n        resolved_items={}",
                                key_path, req.from_path, names, req.resolved.len()
                            );
                        }
                    }
                    if m.exports.is_empty() {
                        eprintln!("    [exports] (none)");
                    } else {
                        eprintln!("    [exports]");
                        for (name, item) in &m.exports {
                            eprintln!("      - {} -> binding {:?}", name, item.binding);
                        }
                    }
                }
            }
        }

        if let (Some(res_ptr), Some(ctx_ptr)) = (self.resolver, self.ctx) {
            unsafe {
                let _ = (&*res_ptr).parse_next(&*ctx_ptr);
            }
        }

        Ok(Program { functions, classes, imports, exports, modules: Vec::new() })
    }

    fn record_export(&mut self, name: &str) {
        self.record_export_with_binding(name, None)
    }

    fn record_export_with_binding(&mut self, name: &str, bind_opt: Option<BindingId>) {
        // Solo si estamos en modo "con módulo"
        if let (Some(m_ptr), Some(ctx_ptr)) = (self.module_ptr, self.ctx) {
            unsafe {
                let ctx = &*ctx_ptr;
                // Interna el nombre en la arena de ctx para que viva lo mismo que ModuleAST
                let name_intern: &'static str = {
                    // lifehack: vive en arena -> válido mientras viva ctx/ModuleAST
                    let s = ctx.arena.alloc_str(name);
                    std::mem::transmute::<&str, &'static str>(s)
                };
                let m: &mut ModuleAST<'static> = &mut *m_ptr;

                let binding = bind_opt.unwrap_or_else(|| BindingId(next_id()));
                m.exports.insert(
                    name_intern,
                    ExportItem { name: name_intern, binding },
                );
            }
        }
    }

    fn record_import_and_enqueue(&mut self, spec: &str, item_names_local: &[String]) -> Result<(), ParseError> {
        if let (Some(m_ptr), Some(ctx_ptr), Some(res_ptr), Some(referrer)) =
            (self.module_ptr, self.ctx, self.resolver, self.referrer.clone())
        {
            // Resolver a ruta absoluta con el loader de FS
            let loader = FSLoader;
            let abs = loader
                .resolve(&referrer, spec)
                .map_err(|_| self.err_here("cannot resolve import path"))?;

            unsafe {
                let ctx = &*ctx_ptr;
                let m: &mut ModuleAST<'static> = &mut *m_ptr;

                // Internar cada nombre en la arena y construir ImportRequest
                let mut names_bumped: Vec<&'static str> = Vec::with_capacity(item_names_local.len());
                for n in item_names_local {
                    let s = ctx.arena.alloc_str(n);
                    names_bumped.push(std::mem::transmute::<&str, &'static str>(s));
                }

                let req = ImportRequest {
                    from_path: Arc::new(abs.clone()),
                    names: names_bumped,
                    resolved: Vec::new(),
                };

                m.imports.insert(Arc::new(abs.clone()), req);

                // Encolar en el resolver para parsearlo cuando toque
                let resolver = &*res_ptr;
                resolver.note_pending(Arc::new(abs));
            }
        }
        Ok(())
    }

    fn class_decl(&mut self) -> PResult<ClassDecl> {
        self.expect(Tok::Class, "expected 'class' keyword")?;
        let t = self.next()?;
        let name = match t.tok {
            Tok::Ident(s) => s,
            ref tok => return Err(ParseError {
                msg: format!("expected class name (identifier), found {:?}", tok),
                span: t.span,
            }),
        };

        let base = if self.matches(&Tok::Extends) {
            let t = self.next()?;
            match t.tok {
                Tok::Ident(s) => Some(s),
                ref tok => return Err(ParseError {
                    msg: format!("expected base class name after 'extends', found {:?}", tok),
                    span: t.span,
                }),
            }
        } else { None };

        self.expect(Tok::LBrace, "expected opening brace after class declaration")?;

        let mut members = Vec::new();
        loop {
            if self.check(&Tok::RBrace) {
                let _ = self.next()?; // consume RBrace
                break;
            }
            if self.is_eof() {
                return Err(self.err_here("unexpected end of file in class body"));
            }
            members.push(self.class_member()?);
        }

        Ok(ClassDecl { name, base, members })
    }

    fn class_member(&mut self) -> PResult<ClassMember> {
        // optional `static`
        let is_static = self.matches(&Tok::Static);

        // optional `async` for methods and constructor
        let is_async = self.matches(&Tok::Async);

        // constructor
        if self.matches(&Tok::Constructor) {
            let params = self.parse_fn_param_names()?;
            let body   = self.block()?;
            return Ok(ClassMember::Constructor { params, body, is_async });
        }

        // destructor
        if self.matches(&Tok::Destructor) {
            if is_async {
                return Err(self.err_here("'async' not allowed for destructor"));
            }
            let body = self.block()?;
            return Ok(ClassMember::Destructor { body });
        }

        // stored field: var name [: Type]? (= expr)? ;
        if self.matches(&Tok::Var) {
            if is_async {
                return Err(self.err_here("'async' not allowed for stored fields"));
            }
            let t = self.next()?;
            let name = match t.tok {
                Tok::Ident(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected field name after 'var', found {:?}", tok),
                    span: t.span,
                }),
            };

            // ignore optional type annotation for now
            let _ = self.maybe_skip_type_annot()?;

            let init = if self.matches(&Tok::Eq) { Some(self.expr()?) } else { None };
            self.expect(Tok::Semi, "expected ';' after field declaration")?;
            return Ok(ClassMember::Stored {
                is_static,
                name,
                type_ann: None,
                init,
            });
        }

        // accessors: get name() { ... }  |  set name(param) { ... }
        if self.matches(&Tok::Get) {
            if is_async {
                return Err(self.err_here("'async' not allowed for getters"));
            }
            let t = self.next()?;
            let name = match t.tok {
                Tok::Ident(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected property name after 'get', found {:?}", tok),
                    span: t.span,
                }),
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
            if is_async {
                return Err(self.err_here("'async' not allowed for setters"));
            }
            let t = self.next()?;
            let name = match t.tok {
                Tok::Ident(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected property name after 'set', found {:?}", tok),
                    span: t.span,
                }),
            };
            self.expect(Tok::LParen, "expected '(' after setter name")?;
            let t = self.next()?;
            let param = match t.tok {
                Tok::Ident(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected setter parameter name, found {:?}", tok),
                    span: t.span,
                }),
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
        // Optional `fn` / `function` keyword (ignored if present)
        let _ = self.matches(&Tok::Fn) || self.matches(&Tok::Function);

        // Method name
        let t = self.next()?;
        let name = match t.tok {
            Tok::Ident(s) => s,
            ref tok => return Err(ParseError {
                msg: format!("expected method name (identifier), found {:?}", tok),
                span: t.span,
            }),
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
            if let Some(p) = self.peek() {
                if matches!(&p.tok, Tok::Ident(_)) {
                    let _ = self.next()?;
                } else {
                    return Err(self.err_here("expected type identifier after ':'"));
                }
            } else {
                return Err(self.err_here("unexpected end of file after ':' in type annotation"));
            }
            // consume any dotted qualifiers (rough)
            while self.matches(&Tok::Dot) {
                if let Some(p) = self.peek() {
                    if matches!(&p.tok, Tok::Ident(_)) {
                        let _ = self.next()?;
                    } else {
                        return Err(self.err_here("expected identifier after '.' in type"));
                    }
                } else {
                    return Err(self.err_here("unexpected end of file after '.' in type"));
                }
            }
        }
        Ok(())
    }

    fn parse_import_decl(&mut self) -> PResult<ImportDecl> {
        self.expect(Tok::Import, "expected 'import' keyword")?;

        // 1) import "path";
        if matches!(self.peek(), Some(SpannedTok { tok: Tok::Str(_), .. })) {
            let t = self.next()?;
            let spec = match t.tok {
                Tok::Str(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected string literal for import specifier, found {:?}", tok),
                    span: t.span,
                }),
            };
            self.expect(Tok::Semi, "expected ';' after import specifier")?;
            // side-effect import: sin items → no hay nombres, pero igualmente encolamos
            self.record_import_and_enqueue(&spec, &[])?;
            return Ok(ImportDecl { specifier: spec, items: vec![] });
        }

        // 2) import * as ns from "path";
        if self.matches(&Tok::Star) {
            self.expect(Tok::As, "expected 'as' after '*'")?;
            let t = self.next()?;
            let alias = match t.tok {
                Tok::Ident(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected identifier after 'as', found {:?}", tok),
                    span: t.span,
                }),
            };
            self.expect(Tok::From, "expected 'from'")?;
            let t = self.next()?;
            let spec = match t.tok {
                Tok::Str(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected string literal after 'from', found {:?}", tok),
                    span: t.span,
                }),
            };
            self.expect(Tok::Semi, "expected ';' after import")?;

            // nombres locales = [alias]
            self.record_import_and_enqueue(&spec, &[alias.clone()])?;

            return Ok(ImportDecl { specifier: spec, items: vec![ImportItem::Namespace { alias }] });
        }

        // 3) import { a, b as c } from "path";
        self.expect(Tok::LBrace, "expected '{' after 'import'")?;
        let mut items = Vec::new();
        let mut locals = Vec::new(); // << para registrar en ModuleAST
        loop {
            if self.check(&Tok::RBrace) {
                let _ = self.next()?; // consume RBrace
                break;
            }
            if self.is_eof() {
                return Err(self.err_here("unexpected end of file in import list"));
            }
            let t = self.next()?;
            let name = match t.tok {
                Tok::Ident(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected imported name (identifier), found {:?}", tok),
                    span: t.span,
                }),
            };
            let alias = if self.matches(&Tok::As) {
                let t = self.next()?;
                match t.tok {
                    Tok::Ident(s) => { locals.push(s.clone()); Some(s) }
                    ref tok => return Err(ParseError {
                        msg: format!("expected alias name (identifier) after 'as', found {:?}", tok),
                        span: t.span,
                    }),
                }
            } else {
                locals.push(name.clone());
                None
            };
            items.push(ImportItem::Named { name, alias });
            if self.check(&Tok::RBrace) {
                let _ = self.next()?; // consume RBrace
                break;
            }
            self.expect(Tok::Comma, "expected ',' or '}' in import list")?;
        }
        self.expect(Tok::From, "expected 'from' after import list")?;
        let t = self.next()?;
        let spec = match t.tok {
            Tok::Str(s) => s,
            ref tok => return Err(ParseError {
                msg: format!("expected string literal after 'from', found {:?}", tok),
                span: t.span,
            }),
        };
        self.expect(Tok::Semi, "expected ';' after import")?;

        // Registrar en cajita + encolarlo para parseo posterior
        self.record_import_and_enqueue(&spec, &locals)?;

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
            self.record_export_with_binding(&f.name, Some(BindingId(f.fid.0)));
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
            self.record_export_with_binding(&f.name, Some(BindingId(f.fid.0)));
            exports.push(ExportDecl::Func(f.name.clone()));
            functions.push(f);
            return Ok(());
        }

        // export class ...
        if self.check(&Tok::Class) {
            let c = self.class_decl()?;
            exports.push(ExportDecl::Class(c.name.clone()));
            self.record_export(&c.name);
            classes.push(c);
            return Ok(());
        }

        // export var/let X = ... ;
        if self.matches(&Tok::Var) || self.matches(&Tok::Let) || self.matches(&Tok::Const) {
            let t = self.next()?;
            let name = match t.tok {
                Tok::Ident(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected identifier after 'export var/let/const', found {:?}", tok),
                    span: t.span,
                }),
            };
            let init = if self.matches(&Tok::Eq) { Some(self.expr()?) } else { None };
            self.expect(Tok::Semi, "expected ';' after export var/let/const")?;
            toplevel.push(Stmt::Var { name: name.clone(), init });
            self.record_export(&name);
            exports.push(ExportDecl::Var(name));
            return Ok(());
        }

        // export * from "path";
        if self.matches(&Tok::Star) {
            self.expect(Tok::From, "expected 'from' after '*'")?;
            let t = self.next()?;
            let spec = match t.tok {
                Tok::Str(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected string literal after 'from', found {:?}", tok),
                    span: t.span,
                }),
            };
            self.expect(Tok::Semi, "expected ';' after export")?;
            exports.push(ExportDecl::AllFrom { specifier: spec });
            return Ok(());
        }

        // export { a, b as c } [from "path"] ;
        if self.matches(&Tok::LBrace) {
            let mut items: Vec<(String, Option<String>)> = Vec::new();
            loop {
                if self.check(&Tok::RBrace) {
                    let _ = self.next()?; // consume RBrace
                    break;
                }
                if self.is_eof() {
                    return Err(self.err_here("unexpected end of file in export list"));
                }
                let t = self.next()?;
                let name = match t.tok {
                    Tok::Ident(s) => s,
                    ref tok => return Err(ParseError {
                        msg: format!("expected exported name (identifier), found {:?}", tok),
                        span: t.span,
                    }),
                };
                let alias = if self.matches(&Tok::As) {
                    let t = self.next()?;
                    match t.tok {
                        Tok::Ident(s) => Some(s),
                        ref tok => return Err(ParseError {
                            msg: format!("expected alias name (identifier) after 'as', found {:?}", tok),
                            span: t.span,
                        }),
                    }
                } else { None };
                items.push((name, alias));
                // TODO Record export with the alias
                if self.check(&Tok::RBrace) {
                    let _ = self.next()?; // consume RBrace
                    break;
                }
                self.expect(Tok::Comma, "expected ',' or '}' in export list")?;
            }
            if self.matches(&Tok::From) {
                let t = self.next()?;
                let spec = match t.tok {
                    Tok::Str(s) => s,
                    ref tok => return Err(ParseError {
                        msg: format!("expected string literal after 'from', found {:?}", tok),
                        span: t.span,
                    }),
                };
                self.expect(Tok::Semi, "expected ';' after export")?;
                for (exp_name, _) in &items {
                    self.record_export(exp_name);
                }
                exports.push(ExportDecl::From { specifier: spec, items });
            } else {
                self.expect(Tok::Semi, "expected ';' after export list")?;
                for (exp_name, _) in &items {
                    self.record_export(exp_name);
                }
                exports.push(ExportDecl::Named { items });
            }
            return Ok(());
        }

        Err(self.err_here("invalid export syntax; expected 'async', 'fn', 'function', 'class', 'var', 'let', 'const', '*', or '{'"))
    }

    fn parse_fn_param_names(&mut self) -> PResult<Vec<String>> {
        self.expect(Tok::LParen, "expected '(' for parameters")?;
        self.parse_param_list()
    }

    fn parse_method_tail(&mut self) -> PResult<(String, Vec<String>, Block)> {
        let t = self.next()?;
        let name = match t.tok {
            Tok::Ident(s) => s,
            ref tok => return Err(ParseError {
                msg: format!("expected method name, found {:?}", tok),
                span: t.span,
            }),
        };
        self.expect(Tok::LParen, "expected '(' after method name")?;
        let params = self.parse_param_list()?;
        let body = self.block()?;
        Ok((name, params, body))
    }

    fn fn_def_with_async(&mut self, is_async: bool) -> PResult<FuncDecl> {
        let t = self.next()?;
        let name = match t.tok {
            Tok::Ident(s) => s,
            ref tok => return Err(ParseError {
                msg: format!("expected function name (identifier), found {:?}", tok),
                span: t.span,
            }),
        };
        self.expect(Tok::LParen, "expected '(' after function name")?;
        let mut params = Vec::new();
        loop {
            if self.check(&Tok::RParen) {
                let _ = self.next()?; // consume RParen
                break;
            }
            if self.is_eof() {
                return Err(self.err_here("unexpected end of file in parameter list"));
            }
            let t = self.next()?;
            let ident = match t.tok {
                Tok::Ident(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected parameter name (identifier), found {:?}", tok),
                    span: t.span,
                }),
            };
            params.push(ident);
            if self.check(&Tok::RParen) {
                let _ = self.next()?; // consume RParen
                break;
            }
            self.expect(Tok::Comma, "expected ',' between parameters")?;
        }
        let body = self.block()?;
        Ok(FuncDecl { fid: FuncId(next_id()), name, params, body, is_async })
    }

    fn block(&mut self) -> PResult<Block> {
        self.expect(Tok::LBrace, "expected opening brace for block")?;
        let mut stmts = Vec::new();
        loop {
            if self.check(&Tok::RBrace) {
                let _ = self.next()?; // consume RBrace
                break;
            }
            if self.is_eof() {
                return Err(self.err_here("unexpected end of file; expected closing brace for block"));
            }
            stmts.push(self.stmt()?);
        }
        Ok(Block { stmts })
    }

    fn parse_param_list(&mut self) -> PResult<Vec<String>> {
        let mut params = Vec::new();
        loop {
            if self.check(&Tok::RParen) {
                let _ = self.next()?; // consume RParen
                break;
            }
            if self.is_eof() {
                return Err(self.err_here("unexpected end of file in parameter list"));
            }
            let t = self.next()?;
            let name = match t.tok {
                Tok::Ident(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected parameter name (identifier), found {:?}", tok),
                    span: t.span,
                }),
            };
            params.push(name);
            if self.check(&Tok::RParen) {
                let _ = self.next()?; // consume RParen
                break;
            }
            self.expect(Tok::Comma, "expected ',' in parameter list")?;
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
            let t = self.next()?;
            let name = match t.tok {
                Tok::Ident(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected identifier after 'var'/'let'/'const', found {:?}", tok),
                    span: t.span,
                }),
            };
            let init = if self.matches(&Tok::Eq) { Some(self.expr()?) } else { None };
            self.expect(Tok::Semi, "expected ';' after variable declaration")?;
            Ok(Stmt::Var { name, init })
        } else if self.matches(&Tok::If) {
            self.expect(Tok::LParen, "expected '(' after 'if'")?;
            let cond = self.expr()?;
            self.expect(Tok::RParen, "expected ')' after 'if' condition")?;
            let then_b = self.block()?;

            // else { … } | else if (…) { … } | else unless (…) { … }
            let else_b = if self.matches(&Tok::Else) {
                if self.matches(&Tok::If) || self.matches(&Tok::Unless) {
                    // Was it "else unless"?
                    let negated = if self.toks.get(self.i.saturating_sub(1)).map(|tt| tt.tok == Tok::Unless).unwrap_or(false) { true } else { false };

                    self.expect(Tok::LParen, "expected '(' after 'else if'/'else unless'")?;
                    let mut cond2 = self.expr()?;
                    self.expect(Tok::RParen, "expected ')' after condition")?;
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
            self.expect(Tok::LParen, "expected '(' after 'unless'")?;
            let cond0 = self.expr()?;
            self.expect(Tok::RParen, "expected ')' after 'unless' condition")?;
            let cond = Expr::Unary { op: UnOp::Not, e: SmallBox::new(cond0) };
            let then_b = self.block()?;

            // else { … } | else if (…) { … } | else unless (…) { … }
            let else_b = if self.matches(&Tok::Else) {
                // “else if …” or “else unless …”
                if self.matches(&Tok::If) || self.matches(&Tok::Unless) {
                    let was_unless = matches!(self.toks.get(self.i.saturating_sub(1)).map(|tt| &tt.tok), Some(Tok::Unless));
                    self.expect(Tok::LParen, "expected '(' after 'else if'/'else unless'")?;
                    let mut cond2 = self.expr()?;
                    self.expect(Tok::RParen, "expected ')' after condition")?;
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
            self.expect(Tok::LParen, "expected '(' after 'while'")?;
            let cond = self.expr()?;
            self.expect(Tok::RParen, "expected ')' after 'while' condition")?;
            let body = self.block()?;
            Ok(Stmt::While { cond, body })
        } else if self.matches(&Tok::For) {
            self.expect(Tok::LParen, "expected '(' after 'for'")?;
            let init = if self.matches(&Tok::Semi) {
                None
            } else if self.matches(&Tok::Var) {
                let t = self.next()?;
                let name = match t.tok {
                    Tok::Ident(s) => s,
                    ref tok => return Err(ParseError {
                        msg: format!("expected identifier after 'var' in for init, found {:?}", tok),
                        span: t.span,
                    }),
                };
                let init_e = if self.matches(&Tok::Eq) { Some(self.expr()?) } else { None };
                self.expect(Tok::Semi, "expected ';' after for init")?;
                Some(SmallBox::new(Stmt::Var { name, init: init_e }))
            } else {
                let e = self.expr()?;
                self.expect(Tok::Semi, "expected ';' after for init")?;
                Some(SmallBox::new(Stmt::Expr(e)))
            };
            let cond = if self.matches(&Tok::Semi) {
                None
            } else {
                let e = self.expr()?;
                self.expect(Tok::Semi, "expected ';' after for condition")?;
                Some(e)
            };
            let step = if self.matches(&Tok::RParen) {
                None
            } else {
                let e = self.expr()?;
                self.expect(Tok::RParen, "expected ')' after for step")?;
                Some(e)
            };
            let body = self.block()?;
            Ok(Stmt::For { init, cond, step, body })
        } else if self.matches(&Tok::Return) {
            if self.matches(&Tok::Semi) {
                Ok(Stmt::Return(None))
            } else {
                let e = self.expr()?;
                self.expect(Tok::Semi, "expected ';' after return expression")?;
                Ok(Stmt::Return(Some(e)))
            }
        } else {
            let e = self.expr()?;
            self.expect(Tok::Semi, "expected ';' after statement")?;
            Ok(Stmt::Expr(e))
        }
    }

    // Pratt parser for expressions
    pub fn expr(&mut self) -> PResult<Expr> { 
        if self.is_eof() {
            return Err(self.err_here("expected expression"));
        }
        self.parse_assign() 
    }

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
                _ => return Err(self.err_here("invalid left-hand side in assignment; expected identifier, property access, or index")),
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
                loop {
                    if self.check(&Tok::RParen) {
                        let _ = self.next()?; // consume RParen
                        break;
                    }
                    if self.is_eof() {
                        return Err(self.err_here("unexpected end of file in argument list"));
                    }
                    args.push(self.expr()?);
                    if self.check(&Tok::RParen) {
                        let _ = self.next()?; // consume RParen
                        break;
                    }
                    self.expect(Tok::Comma, "expected ',' in argument list")?;
                }
                e = Expr::Call { callee: SmallBox::new(e), args };
            } else if self.matches(&Tok::Dot) {
                let t = self.next()?;
                let name = match t.tok {
                    Tok::Ident(s) => s,
                    ref tok => return Err(ParseError {
                        msg: format!("expected identifier after '.', found {:?}", tok),
                        span: t.span,
                    }),
                };
                e = Expr::GetProp { recv: SmallBox::new(e), name };
            } else if self.matches(&Tok::LBracket) {
                let idx = self.expr()?;
                self.expect(Tok::RBracket, "expected ']' after index")?;
                e = Expr::Index { recv: SmallBox::new(e), index: SmallBox::new(idx) };
            } else {
                break;
            }
        }
        Ok(e)
    }
    fn parse_primary(&mut self) -> PResult<Expr> { 
        if self.is_eof() {
            return Err(self.err_here("expected primary expression"));
        }
        let t = self.next()?;
        match t.tok {
            Tok::This  => Ok(Expr::This),

            Tok::Super => {
                if self.check(&Tok::LParen) {
                    // super(...)
                    self.i += 1; // consume '('
                    let mut args = Vec::new();
                    loop {
                        if self.check(&Tok::RParen) {
                            let _ = self.next()?; // consume RParen
                            break;
                        }
                        if self.is_eof() {
                            return Err(self.err_here("unexpected end of file in super call"));
                        }
                        args.push(self.expr()?);
                        if self.check(&Tok::RParen) {
                            let _ = self.next()?; // consume RParen
                            break;
                        }
                        self.expect(Tok::Comma, "expected ',' in super call arguments")?;
                    }
                    Ok(Expr::SuperCall(args))
                } else if self.matches(&Tok::Dot) {
                    // super.name
                    let t = self.next()?;
                    let name = match t.tok {
                        Tok::Ident(s) => s,
                        ref tok => return Err(ParseError {
                            msg: format!("expected identifier after 'super.', found {:?}", tok),
                            span: t.span,
                        }),
                    };
                    Ok(Expr::SuperProp(name))
                } else {
                    Err(self.err_here("expected '(' for super call or '.' for super property after 'super'"))
                }
            }

            Tok::New => {
                // new <Ident>(args...)
                let t = self.next()?;
                let class = match t.tok {
                    Tok::Ident(s) => s,
                    ref tok => return Err(ParseError {
                        msg: format!("expected class name (identifier) after 'new', found {:?}", tok),
                        span: t.span,
                    }),
                };
                self.expect(Tok::LParen, "expected '(' after class name in new expression")?;
                let mut args = Vec::new();
                loop {
                    if self.check(&Tok::RParen) {
                        let _ = self.next()?; // consume RParen
                        break;
                    }
                    if self.is_eof() {
                        return Err(self.err_here("unexpected end of file in new arguments"));
                    }
                    args.push(self.expr()?);
                    if self.check(&Tok::RParen) {
                        let _ = self.next()?; // consume RParen
                        break;
                    }
                    self.expect(Tok::Comma, "expected ',' in new arguments")?;
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
                self.expect(Tok::RParen, "expected ')' to close grouped expression")?;
                Ok(Expr::Group(SmallBox::new(e)))
            }
            Tok::LBracket => {
                let mut elems = Vec::new();
                loop {
                    if self.check(&Tok::RBracket) {
                        let _ = self.next()?; // consume RBracket
                        break;
                    }
                    if self.is_eof() {
                        return Err(self.err_here("unexpected end of file in array literal"));
                    }
                    elems.push(self.expr()?);
                    // ] ends the literal
                    if self.check(&Tok::RBracket) {
                        let _ = self.next()?; // consume RBracket
                        break;
                    }
                    // expect comma; allow trailing comma
                    self.expect(Tok::Comma, "expected ',' in array literal")?;
                    if self.check(&Tok::RBracket) {
                        let _ = self.next()?; // consume RBracket
                        break;
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
                loop {
                    if self.check(&Tok::Pipe) {
                        let _ = self.next()?; // consume closing Pipe
                        break;
                    }
                    if self.is_eof() {
                        return Err(self.err_here("unexpected end of file in lambda parameters"));
                    }
                    let t = self.next()?;
                    let name = match t.tok {
                        Tok::Ident(s) => s,
                        ref tok => return Err(ParseError {
                            msg: format!("expected parameter name (identifier) in lambda, found {:?}", tok),
                            span: t.span,
                        }),
                    };
                    params.push(name);
                    if self.check(&Tok::Pipe) {
                        let _ = self.next()?; // consume closing Pipe
                        break;
                    }
                    self.expect(Tok::Comma, "expected ',' in lambda params")?;
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
            ref tok => Err(ParseError {
                msg: format!("unexpected token {:?}, expected literal, identifier, 'this', 'super', 'new', '(', '[', '{{', 'fn', 'function', '|', or 'delete'", tok),
                span: t.span,
            }),
        }
    }

    fn parse_listen_stmt(&mut self) -> PResult<Stmt> {
        // consume 'listen'
        let _ = self.next()?; // Ident("listen")
        // "addr"
        let t = self.next()?;
        let addr = match t.tok {
            Tok::Str(s) => s,
            ref tok => return Err(ParseError {
                msg: format!("expected string literal for address after 'listen', found {:?}", tok),
                span: t.span,
            }),
        };
        // body
        self.expect(Tok::LBrace, "expected '{' after listen address")?;
        let mut routes = Vec::new();
        loop {
            if self.check(&Tok::RBrace) {
                let _ = self.next()?; // consume RBrace
                break;
            }
            if self.is_eof() {
                return Err(self.err_here("unexpected end of file in listen block"));
            }
            routes.push(self.parse_route_decl()?);
        }
        Ok(Stmt::Listen(ListenDecl { addr, routes }))
    }

    fn parse_route_decl(&mut self) -> PResult<RouteDecl> {
        // route "METHOD" [pattern] (params) => { body } ;
        if !self.matches_ident("route") {
            return Err(self.err_here("expected 'route' keyword"));
        }

        // "METHOD" (accept also bare Ident for convenience)
        let t = self.next()?;
        let method = match t.tok {
            Tok::Str(s) => s,
            Tok::Ident(s) => s, // allow: route GET [...]
            ref tok => return Err(ParseError {
                msg: format!("expected HTTP method (string literal or identifier), found {:?}", tok),
                span: t.span,
            }),
        };

        // [ pattern parts ]  -- we parse a general array expression to keep it flexible
        self.expect(Tok::LBracket, "expected '[' after route method")?;
        let mut elems = Vec::new();
        loop {
            if self.check(&Tok::RBracket) {
                let _ = self.next()?; // consume RBracket
                break;
            }
            if self.is_eof() {
                return Err(self.err_here("unexpected end of file in route pattern"));
            }
            // keep it general: any expression (usually "literal" strings like "/","users",":id")
            elems.push(self.expr()?);
            if self.check(&Tok::RBracket) {
                let _ = self.next()?; // consume RBracket
                break;
            }
            self.expect(Tok::Comma, "expected ',' in route pattern")?;
        }
        let pattern_expr = Expr::ArrayLit(elems);

        // ( params )
        self.expect(Tok::LParen, "expected '(' before route handler params")?;
        let params = self.parse_param_list()?;

        // =>
        self.expect(Tok::Eq, "expected '=' in '=>' after params")?;
        self.expect(Tok::Gt, "expected '>' in '=>' after params")?;

        // body: block or single expression (we'll allow both; single expr becomes 'return expr;')
        let handler_body = if self.check(&Tok::LBrace) {
            self.block()?
        } else {
            // expression-body → implicit return
            let e = self.expr()?;
            Block { stmts: vec![Stmt::Return(Some(e))] }
        };

        // optional ';' after a block is allowed by your grammar, require it for consistency
        self.expect(Tok::Semi, "expected ';' after route declaration")?;

        let handler = Expr::FnLit { params, body: handler_body };
        Ok(RouteDecl { method, pattern: pattern_expr, handler })
    }

    // Parse an object literal: { a: 1, "b": 2, c: x+y }
    fn parse_object_literal(&mut self) -> PResult<Expr> {
        // already consumed LBrace
        let mut props = Vec::new();
        let mut seen_keys = HashSet::new(); // to detect duplicates

        loop {
            if self.check(&Tok::RBrace) {
                let _ = self.next()?; // consume RBrace
                break;
            }
            if self.is_eof() {
                return Err(self.err_here("unexpected end of file in object literal"));
            }

            // key: Ident | Str
            let key = {
                let tok_opt = self.peek().as_ref().map(|p| p.tok.clone());
                if let Some(tok) = tok_opt {
                    self.next()?; // consume after borrow ends
                    match tok {
                        Tok::Ident(s) => {
                            if seen_keys.contains(&s) {
                                return Err(self.err_here(&format!("duplicate key '{}' in object literal", s)));
                            }
                            seen_keys.insert(s.clone());
                            PropKey::Ident(s)
                        },
                        Tok::Str(s) => {
                            if seen_keys.contains(&s) {
                                return Err(self.err_here(&format!("duplicate key \"{}\" in object literal", s)));
                            }
                            seen_keys.insert(s.clone());
                            PropKey::Str(s)
                        },
                        _ => return Err(self.err_here("expected property name (identifier or string literal) in object literal")),
                    }
                } else {
                    return Err(self.err_here("unexpected end of file; expected property name in object literal"));
                }
            };

            self.expect(Tok::Colon, "expected ':' after property key")?;
            let value = self.expr()?;
            props.push((key, value));

            if self.check(&Tok::RBrace) {
                let _ = self.next()?; // consume RBrace
                break;
            }
            self.expect(Tok::Comma, "expected ',' after property")?;
        }

        Ok(Expr::ObjLit(props))
    }

    // delete obj.x   |   delete obj["x"]
    fn parse_delete(&mut self) -> PResult<Expr> {
        // receiver
        let recv = self.parse_primary()?;

        if self.matches(&Tok::Dot) {
            // delete obj.ident
            let t = self.next()?;
            let name = match t.tok {
                Tok::Ident(s) => s,
                ref tok => return Err(ParseError {
                    msg: format!("expected identifier after '.' in delete, found {:?}", tok),
                    span: t.span,
                }),
            };
            return Ok(Expr::DeleteProp { obj: SmallBox::new(recv), key: PropKey::Ident(name) });
        }

        if self.matches(&Tok::LBracket) {
            let key_opt = self.peek().as_ref().and_then(|p| match &p.tok {
                Tok::Str(s) => Some(PropKey::Str(s.clone())),
                Tok::Ident(s) => Some(PropKey::Ident(s.clone())),
                _ => None,
            });

            if let Some(key) = key_opt {
                self.next()?; // consume key
                self.expect(Tok::RBracket, "expected ']' after key in delete")?;
                return Ok(Expr::DeleteProp { obj: SmallBox::new(recv), key });
            } else {
                // general: delete obj[expr]
                let index = self.expr()?;
                self.expect(Tok::RBracket, "expected ']' after index in delete")?;
                return Ok(Expr::DeleteIndex { obj: SmallBox::new(recv), index: SmallBox::new(index) });
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