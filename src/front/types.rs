//! Optional, TypeScript-like type annotations.
//!
//! Annotations are parsed into a small syntax tree that lives next to the
//! untyped AST.  The checker in `typeck.rs` consumes them, reports static
//! errors, inserts runtime guards on dynamic boundaries and selects faster
//! lowering paths.  Code without annotations parses exactly as before.

use super::*;

#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpr {
    /// `number`, `string`, `Foo`, `Array<T>`, `Map<K, V>`, `T`, ...
    Name { name: String, args: Vec<TypeExpr> },
    /// `T[]`
    Array(Box<TypeExpr>),
    /// `A | B`
    Union(Vec<TypeExpr>),
    Literal(TypeLiteral),
    Tuple(Vec<TypeExpr>),
    KeyOf(Box<TypeExpr>),
    Indexed(Box<TypeExpr>, Box<TypeExpr>),
    Mapped {
        param: String,
        keys: Box<TypeExpr>,
        value: Box<TypeExpr>,
        optional: Option<bool>,
    },
    Conditional {
        check: Box<TypeExpr>,
        extends: Box<TypeExpr>,
        yes: Box<TypeExpr>,
        no: Box<TypeExpr>,
    },
    Infer(String),
    /// `{ x: number; y?: string; m(a: number): string }`
    Object(Vec<TypeMember>),
    /// `(a: A, b?: B) => R`
    Function {
        type_params: Vec<TypeParam>,
        params: Vec<TypeExpr>,
        min_args: usize,
        ret: Box<TypeExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum TypeLiteral {
    Number(f64),
    String(String),
    Bool(bool),
}

impl TypeExpr {
    pub fn named(name: &str) -> Self {
        TypeExpr::Name {
            name: name.to_string(),
            args: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeMember {
    pub name: String,
    pub optional: bool,
    pub ty: TypeExpr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeParam {
    pub name: String,
    pub constraint: Option<TypeExpr>,
}

/// Annotations of a function-like declaration.  Absent when nothing is annotated.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct FnTypes {
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Option<TypeExpr>>,
    pub optional: Vec<bool>,
    pub ret: Option<TypeExpr>,
}

impl FnTypes {
    fn build(
        type_params: Vec<TypeParam>,
        params: Vec<Option<TypeExpr>>,
        optional: Vec<bool>,
        ret: Option<TypeExpr>,
    ) -> Option<Box<FnTypes>> {
        let annotated = !type_params.is_empty()
            || ret.is_some()
            || params.iter().any(Option::is_some)
            || optional.iter().any(|o| *o);
        annotated.then(|| {
            Box::new(FnTypes {
                type_params,
                params,
                optional,
                ret,
            })
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeDecl {
    Interface {
        name: String,
        type_params: Vec<TypeParam>,
        extends: Vec<TypeExpr>,
        members: Vec<TypeMember>,
    },
    Alias {
        name: String,
        type_params: Vec<TypeParam>,
        ty: TypeExpr,
    },
}

impl TypeDecl {
    pub fn name(&self) -> &str {
        match self {
            TypeDecl::Interface { name, .. } | TypeDecl::Alias { name, .. } => name,
        }
    }
}

/// Runtime shape test used by checked boundaries.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum RtCheck {
    Any,
    Never,
    Literal(TypeLiteral),
    Number,
    Str,
    Bool,
    Null,
    Array,
    Function,
    Map,
    Set,
    /// A plain object (or class instance) exposing every listed member.
    Shape(Vec<String>),
    AnyOf(Vec<RtCheck>),
    Elements(Box<RtCheck>),
    Tuple(Vec<RtCheck>),
    MapEntries(Box<RtCheck>, Box<RtCheck>),
    SetElements(Box<RtCheck>),
    Properties(Vec<(String, bool, RtCheck)>),
    Define(String, Box<RtCheck>),
    Ref(String),
}

/// Operations produced by the parser (`TypeArgs`, `Cast`) or selected by the
/// checker from static types.  Parser-only operations never reach lowering.
#[derive(Debug, Clone, PartialEq)]
pub enum TypedOp {
    /// Explicit generic arguments around a `Call`/`New`: `f<T>(x)`.
    TypeArgs(Vec<TypeExpr>),
    /// `expr as T`.
    Cast(TypeExpr),
    /// Evaluate `args[0]`, throw a `TypeError` string unless it matches.
    Assert { check: RtCheck, message: String },
    /// `string + string`.
    StrConcat,
    /// `string == string` / `!=`.
    StrEq { negate: bool },
    /// Equality of two non-string primitives (identity compare).
    PrimEq { negate: bool },
    /// `array.length`.
    ArrayLen,
    /// `string.length`.
    StrLen,
    /// `array[index]` with a numeric index.
    ArrayGet,
    /// `array[index] = value` with a numeric index.
    ArraySet,
}

impl Parser<'_> {
    #[inline]
    pub(super) fn peek_tok_at(&self, offset: usize) -> Option<&Tok> {
        self.toks.get(self.i + offset).map(|t| &t.tok)
    }

    pub(super) fn type_mark(&self) -> (usize, usize) {
        (self.i, self.token_splits.len())
    }

    /// Rewind a speculative type parse, undoing any `>>` token splits.
    pub(super) fn type_rewind(&mut self, mark: (usize, usize)) {
        while self.token_splits.len() > mark.1 {
            let (index, original) = self.token_splits.pop().unwrap();
            self.toks.remove(index + 1);
            self.toks[index].tok = original;
        }
        self.i = mark.0;
    }

    /// Consume a `>` closing a type argument list, splitting `>>`, `>>>` and `>=`.
    fn expect_type_close(&mut self) -> PResult<()> {
        let rest = match self.peek().map(|t| &t.tok) {
            Some(Tok::Gt) => {
                self.i += 1;
                return Ok(());
            }
            Some(Tok::Shr) => Tok::Gt,
            Some(Tok::ShrU) => Tok::Shr,
            Some(Tok::GtEq) => Tok::Eq,
            _ => return Err(self.err_here("expected '>' to close type arguments")),
        };
        let index = self.i;
        let original = std::mem::replace(&mut self.toks[index].tok, Tok::Gt);
        let span = self.toks[index].span.clone();
        self.toks.insert(index + 1, SpannedTok { tok: rest, span });
        self.token_splits.push((index, original));
        self.i += 1;
        Ok(())
    }

    pub(super) fn parse_type(&mut self) -> PResult<TypeExpr> {
        self.parse_type_with(true)
    }

    fn parse_type_with(&mut self, allow_union: bool) -> PResult<TypeExpr> {
        let first = self.parse_union_type(allow_union)?;
        if self.matches(&Tok::Extends) {
            let extends = self.parse_union_type(true)?;
            self.expect(Tok::Question, "expected '?' in conditional type")?;
            let yes = self.parse_type()?;
            self.expect(Tok::Colon, "expected ':' in conditional type")?;
            let no = self.parse_type_with(allow_union)?;
            return Ok(TypeExpr::Conditional {
                check: Box::new(first), extends: Box::new(extends),
                yes: Box::new(yes), no: Box::new(no),
            });
        }
        Ok(first)
    }

    fn parse_union_type(&mut self, allow_union: bool) -> PResult<TypeExpr> {
        if allow_union { self.matches(&Tok::Pipe); }
        let first = self.parse_postfix_type()?;
        if !allow_union || !self.check(&Tok::Pipe) { return Ok(first); }
        let mut members = vec![first];
        while self.matches(&Tok::Pipe) { members.push(self.parse_postfix_type()?); }
        Ok(TypeExpr::Union(members))
    }

    fn parse_postfix_type(&mut self) -> PResult<TypeExpr> {
        if self.check_ident("keyof") {
            self.i += 1;
            return Ok(TypeExpr::KeyOf(Box::new(self.parse_postfix_type()?)));
        }
        let mut ty = self.parse_primary_type()?;
        while self.matches(&Tok::LBracket) {
            ty = if self.matches(&Tok::RBracket) {
                TypeExpr::Array(Box::new(ty))
            } else {
                let key = self.parse_type()?;
                self.expect(Tok::RBracket, "expected ']' in indexed access type")?;
                TypeExpr::Indexed(Box::new(ty), Box::new(key))
            };
        }
        Ok(ty)
    }

    fn parse_primary_type(&mut self) -> PResult<TypeExpr> {
        let token = self.next()?;
        let mut name = match token.tok {
            Tok::LParen => {
                let mark = self.type_mark();
                if let Ok(function) = self.parse_function_type_tail() {
                    return Ok(function);
                }
                self.type_rewind(mark);
                let inner = self.parse_type()?;
                self.expect(Tok::RParen, "expected ')' to close parenthesized type")?;
                return Ok(inner);
            }
            Tok::Str(value) => return Ok(TypeExpr::Literal(TypeLiteral::String(value))),
            Tok::True => return Ok(TypeExpr::Literal(TypeLiteral::Bool(true))),
            Tok::False => return Ok(TypeExpr::Literal(TypeLiteral::Bool(false))),
            Tok::Int(value) => return value.parse::<f64>()
                .map(|n| TypeExpr::Literal(TypeLiteral::Number(n)))
                .map_err(|_| self.err_here("invalid numeric literal type")),
            Tok::Float(value) => return Ok(TypeExpr::Literal(TypeLiteral::Number(value))),
            Tok::Minus => {
                let value = self.parse_primary_type()?;
                if let TypeExpr::Literal(TypeLiteral::Number(n)) = value {
                    return Ok(TypeExpr::Literal(TypeLiteral::Number(-n)));
                }
                return Err(self.err_here("expected a number after '-' in literal type"));
            }
            Tok::LBracket => {
                let mut items = Vec::new();
                while !self.matches(&Tok::RBracket) {
                    items.push(self.parse_type()?);
                    if !self.check(&Tok::RBracket) {
                        self.expect(Tok::Comma, "expected ',' in tuple type")?;
                    }
                }
                return Ok(TypeExpr::Tuple(items));
            }
            Tok::Lt => {
                self.i -= 1;
                let type_params = self.parse_opt_type_params()?;
                self.expect(Tok::LParen, "expected '(' in generic function type")?;
                let mut ty = self.parse_function_type_tail()?;
                if let TypeExpr::Function { type_params: params, .. } = &mut ty {
                    *params = type_params;
                }
                return Ok(ty);
            }
            Tok::LBrace => {
                if self.matches(&Tok::LBracket) {
                    let param = self.parse_any_identifier()?;
                    self.expect(Tok::In, "expected 'in' in mapped type")?;
                    let keys = self.parse_type()?;
                    self.expect(Tok::RBracket, "expected ']' in mapped type")?;
                    let optional = if self.matches(&Tok::Minus) {
                        self.expect(Tok::Question, "expected '?' after '-' in mapped type")?;
                        Some(false)
                    } else {
                        self.matches(&Tok::Plus);
                        self.matches(&Tok::Question).then_some(true)
                    };
                    self.expect(Tok::Colon, "expected ':' in mapped type")?;
                    let value = self.parse_type()?;
                    self.matches(&Tok::Semi);
                    self.expect(Tok::RBrace, "expected '}' in mapped type")?;
                    return Ok(TypeExpr::Mapped {
                        param, keys: Box::new(keys), value: Box::new(value), optional,
                    });
                }
                return Ok(TypeExpr::Object(self.parse_type_members()?));
            }
            Tok::Ident(name) if name == "infer" => {
                return Ok(TypeExpr::Infer(self.parse_any_identifier()?));
            }
            Tok::Null => "null".to_string(),
            Tok::Ident(name) => name,
            Tok::ListBuiltin => "Array".to_string(),
            Tok::MapBuiltin => "Map".to_string(),
            Tok::SetBuiltin => "Set".to_string(),
            Tok::PromiseBuiltin => "Promise".to_string(),
            Tok::ProxyBuiltin => "Proxy".to_string(),
            Tok::DeferredBuiltin => "Deferred".to_string(),
            ref other => {
                return Err(
                    self.make_error(format!("expected a type, found {:?}", other), token.span)
                );
            }
        };
        while self.matches(&Tok::Dot) {
            name.push('.');
            name.push_str(&self.parse_any_identifier()?);
        }
        let args = if self.check(&Tok::Lt) {
            self.parse_type_args()?
        } else {
            Vec::new()
        };
        Ok(TypeExpr::Name { name, args })
    }

    /// After `(`: `name: T, other?: U) => R` or `T, U) => R`.
    fn parse_function_type_tail(&mut self) -> PResult<TypeExpr> {
        let mut params = Vec::new();
        let mut min_args = 0;
        let mut seen_optional = false;
        while !self.matches(&Tok::RParen) {
            let named = matches!(self.peek_tok_at(0), Some(Tok::Ident(_)))
                && matches!(
                    self.peek_tok_at(1),
                    Some(Tok::Colon) | Some(Tok::Question)
                );
            let mut optional = false;
            if named {
                self.i += 1;
                optional = self.matches(&Tok::Question);
                self.expect(Tok::Colon, "expected ':' in function type parameter")?;
            }
            params.push(self.parse_type()?);
            if optional {
                seen_optional = true;
            } else if !seen_optional {
                min_args = params.len();
            }
            if !self.check(&Tok::RParen) {
                self.expect(Tok::Comma, "expected ',' in function type parameters")?;
            }
        }
        self.expect(Tok::Eq, "expected '=>' in function type")?;
        self.expect(Tok::Gt, "expected '=>' in function type")?;
        let ret = Box::new(self.parse_type()?);
        Ok(TypeExpr::Function {
            type_params: Vec::new(),
            params,
            min_args,
            ret,
        })
    }

    /// After `{`: members separated by `;` or `,`, closed by `}`.
    fn parse_type_members(&mut self) -> PResult<Vec<TypeMember>> {
        let mut members = Vec::new();
        while !self.matches(&Tok::RBrace) {
            if self.is_eof() {
                return Err(self.err_here("unexpected end of file in object type"));
            }
            let name = match self.peek().map(|t| t.tok.clone()) {
                Some(Tok::Str(s)) => {
                    self.i += 1;
                    s
                }
                _ => self.parse_any_identifier()?,
            };
            let optional = self.matches(&Tok::Question);
            let ty = if self.check(&Tok::LParen) || self.check(&Tok::Lt) {
                let type_params = self.parse_opt_type_params()?;
                self.expect(Tok::LParen, "expected '(' in method signature")?;
                let (_, param_types, optional_params) = self.parse_typed_params(Tok::RParen)?;
                let ret = self.parse_opt_return_type()?;
                let min_args = optional_params
                    .iter()
                    .position(|optional| *optional)
                    .unwrap_or(optional_params.len());
                TypeExpr::Function {
                    type_params,
                    params: param_types
                        .into_iter()
                        .map(|t| t.unwrap_or_else(|| TypeExpr::named("any")))
                        .collect(),
                    min_args,
                    ret: Box::new(ret.unwrap_or_else(|| TypeExpr::named("any"))),
                }
            } else {
                self.expect(Tok::Colon, "expected ':' after member name in type")?;
                self.parse_type()?
            };
            members.push(TypeMember { name, optional, ty });
            if !self.matches(&Tok::Semi) && !self.matches(&Tok::Comma) && !self.check(&Tok::RBrace)
            {
                return Err(self.err_here("expected ';', ',' or '}' in object type"));
            }
        }
        Ok(members)
    }

    /// `<A, B>` (the `<` has not been consumed yet).
    pub(super) fn parse_type_args(&mut self) -> PResult<Vec<TypeExpr>> {
        self.expect(Tok::Lt, "expected '<' to open type arguments")?;
        let mut args = vec![self.parse_type()?];
        while self.matches(&Tok::Comma) {
            args.push(self.parse_type()?);
        }
        self.expect_type_close()?;
        Ok(args)
    }

    /// Explicit generic arguments before a call: `f<T>(...)`.  Rewinds when the
    /// tokens turn out to be comparisons.
    pub(super) fn try_parse_call_type_args(&mut self) -> Option<Vec<TypeExpr>> {
        let mark = self.type_mark();
        match self.parse_type_args() {
            Ok(args) if self.check(&Tok::LParen) => Some(args),
            _ => {
                self.type_rewind(mark);
                None
            }
        }
    }

    /// Optional `<T, U extends Bound>` declaration list.
    pub(super) fn parse_opt_type_params(&mut self) -> PResult<Vec<TypeParam>> {
        if !self.matches(&Tok::Lt) {
            return Ok(Vec::new());
        }
        let mut params = Vec::new();
        loop {
            let token = self.next()?;
            let Tok::Ident(name) = token.tok else {
                return Err(self.make_error("expected type parameter name", token.span));
            };
            let constraint = if self.matches(&Tok::Extends) {
                Some(self.parse_type()?)
            } else {
                None
            };
            params.push(TypeParam { name, constraint });
            if !self.matches(&Tok::Comma) {
                break;
            }
        }
        self.expect_type_close()?;
        Ok(params)
    }

    pub(super) fn parse_opt_type_annotation(&mut self) -> PResult<Option<TypeExpr>> {
        if self.matches(&Tok::Colon) {
            Ok(Some(self.parse_type()?))
        } else {
            Ok(None)
        }
    }

    pub(super) fn parse_opt_return_type(&mut self) -> PResult<Option<TypeExpr>> {
        self.parse_opt_type_annotation()
    }

    /// Parameter list after the opening token, up to `close` (`)` or `|`).
    /// Lambda parameters (`close == Pipe`) cannot use union types because `|`
    /// ends the parameter list.
    pub(super) fn parse_typed_params(
        &mut self,
        close: Tok,
    ) -> PResult<(Vec<String>, Vec<Option<TypeExpr>>, Vec<bool>)> {
        let mut names = Vec::new();
        let mut types = Vec::new();
        let mut optional = Vec::new();
        loop {
            if self.matches(&close) {
                break;
            }
            if self.is_eof() {
                return Err(self.err_here("unexpected end of file in parameter list"));
            }
            let token = self.next()?;
            let Tok::Ident(name) = token.tok else {
                return Err(self.make_error(
                    format!("expected parameter name (identifier), found {:?}", token.tok),
                    token.span,
                ));
            };
            let is_optional = self.matches(&Tok::Question);
            if !is_optional && optional.iter().any(|o| *o) {
                return Err(self.err_here("a required parameter cannot follow an optional one"));
            }
            let ty = if self.matches(&Tok::Colon) {
                Some(self.parse_type_with(close != Tok::Pipe)?)
            } else {
                None
            };
            names.push(name);
            types.push(ty);
            optional.push(is_optional);
            if self.matches(&close) {
                break;
            }
            self.expect(Tok::Comma, "expected ',' in parameter list")?;
        }
        Ok((names, types, optional))
    }

    /// `(params) [: Ret]` for functions, methods and function literals.
    pub(super) fn parse_signature(
        &mut self,
        type_params: Vec<TypeParam>,
    ) -> PResult<(Vec<String>, Option<Box<FnTypes>>)> {
        self.expect(Tok::LParen, "expected '(' for parameters")?;
        let (names, types, optional) = self.parse_typed_params(Tok::RParen)?;
        let ret = self.parse_opt_return_type()?;
        Ok((names, FnTypes::build(type_params, types, optional, ret)))
    }

    pub(super) fn lambda_types(
        types: Vec<Option<TypeExpr>>,
        optional: Vec<bool>,
    ) -> Option<Box<FnTypes>> {
        FnTypes::build(Vec::new(), types, optional, None)
    }

    pub(super) fn at_type_declaration(&self) -> bool {
        let named = matches!(self.peek_tok_at(1), Some(Tok::Ident(_)));
        (self.check_ident("interface") && named)
            || (self.check_ident("type")
                && named
                && matches!(self.peek_tok_at(2), Some(Tok::Eq) | Some(Tok::Lt)))
    }

    /// `interface Name<T> extends A, B { ... }` or `type Name<T> = Type;`
    pub(super) fn type_declaration(&mut self) -> PResult<TypeDecl> {
        let is_interface = self.check_ident("interface");
        self.i += 1;
        let token = self.next()?;
        let Tok::Ident(name) = token.tok else {
            return Err(self.make_error("expected type name", token.span));
        };
        if is_builtin_type_name(&name) {
            return Err(self.make_error(
                format!("cannot redeclare built-in type `{}`", name),
                token.span,
            ));
        }
        let type_params = self.parse_opt_type_params()?;
        if is_interface {
            let mut extends = Vec::new();
            if self.matches(&Tok::Extends) {
                loop {
                    extends.push(self.parse_postfix_type()?);
                    if !self.matches(&Tok::Comma) {
                        break;
                    }
                }
            }
            self.expect(Tok::LBrace, "expected '{' to open interface body")?;
            let members = self.parse_type_members()?;
            Ok(TypeDecl::Interface {
                name,
                type_params,
                extends,
                members,
            })
        } else {
            self.expect(Tok::Eq, "expected '=' in type alias")?;
            let ty = self.parse_type()?;
            self.expect(Tok::Semi, "expected ';' after type alias")?;
            Ok(TypeDecl::Alias {
                name,
                type_params,
                ty,
            })
        }
    }

    /// Parses a type declaration and records it; returns a no-op statement.
    pub(super) fn type_declaration_stmt(&mut self) -> PResult<Stmt> {
        let declaration = self.type_declaration()?;
        self.type_decls.push(declaration);
        Ok(stmt_unknown(StmtKind::Expr(expr_unknown(ExprKind::LitInt(
            0,
        )))))
    }
}

pub fn is_builtin_type_name(name: &str) -> bool {
    matches!(
        name,
        "number"
            | "string"
            | "boolean"
            | "any"
            | "unknown"
            | "void"
            | "never"
            | "null"
            | "undefined"
            | "Array"
            | "Map"
            | "Set"
            | "Promise"
            | "Function"
            | "object"
    )
}
