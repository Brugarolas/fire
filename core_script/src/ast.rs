// ast.rs

pub type Span = std::ops::Range<usize>;

#[derive(Debug, Clone)]
pub struct Script<'a> {
    pub body: Vec<Stmt<'a>>,
}

#[derive(Debug, Clone)]
pub enum Stmt<'a> {
    Class(ClassDecl<'a>),
    Import(ImportStmt<'a>),
    Var(VarDecl<'a>),
    Expr(Expr<'a>),
    For(ForStmt<'a>),
    If(IfStmt<'a>),
    While(WhileStmt<'a>),
    Return(ReturnStmt<'a>),
    Break(Span),
    Continue(Span),
    Block(Vec<Stmt<'a>>, Span),
}

#[derive(Debug, Clone)]
pub struct ClassDecl<'a> {
    pub is_foreign: bool,
    pub name: (&'a str, Span),
    pub superclass: Option<(&'a str, Span)>,
    pub body: Vec<Method<'a>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Method<'a> {
    pub is_static: bool,
    pub is_foreign: bool,
    pub signature: Signature<'a>,
    pub body: Vec<Stmt<'a>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Signature<'a> {
    pub is_constructor: bool,
    pub name: (&'a str, Span),
    pub params: Vec<(&'a str, Span)>,
    pub is_getter: bool,
}

#[derive(Debug, Clone)]
pub struct ImportStmt<'a> {
    pub path: (&'a str, Span),
    pub vars: Vec<((&'a str, Span), Option<(&'a str, Span)>)>, // (original, as_alias)
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct VarDecl<'a> {
    pub name: (&'a str, Span),
    pub initializer: Option<Expr<'a>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ForStmt<'a> {
    pub var_name: (&'a str, Span),
    pub sequence: Expr<'a>,
    pub body: Box<Stmt<'a>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct IfStmt<'a> {
    pub condition: Expr<'a>,
    pub then_branch: Box<Stmt<'a>>,
    pub else_branch: Option<Box<Stmt<'a>>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct WhileStmt<'a> {
    pub condition: Expr<'a>,
    pub body: Box<Stmt<'a>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ReturnStmt<'a> {
    pub value: Option<Expr<'a>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Expr<'a> {
    pub kind: ExprKind<'a>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExprKind<'a> {
    Literal(LiteralValue<'a>),
    This,
    Super,
    Identifier(&'a str),
    Unary(UnaryOp, Box<Expr<'a>>),
    Binary(Box<Expr<'a>>, InfixOp, Box<Expr<'a>>),
    Logical(Box<Expr<'a>>, LogicalOp, Box<Expr<'a>>),
    Ternary(Box<Expr<'a>>, Box<Expr<'a>>, Box<Expr<'a>>), // condition, then, else
    Call(Box<Expr<'a>>, Vec<Expr<'a>>),
    Get(Box<Expr<'a>>, (&'a str, Span)), // object, property
    Set(Box<Expr<'a>>, (&'a str, Span), Box<Expr<'a>>), // object, property, value
    SubscriptGet(Box<Expr<'a>>, Box<Expr<'a>>),
    SubscriptSet(Box<Expr<'a>>, Box<Expr<'a>>, Box<Expr<'a>>),
    Is(Box<Expr<'a>>, (&'a str, Span)),
    In(Box<Expr<'a>>, Box<Expr<'a>>),
    List(Vec<Expr<'a>>),
    Map(Vec<(Expr<'a>, Expr<'a>)>),
    Assignment(&'a str, Box<Expr<'a>>),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LiteralValue<'a> {
    Number(f64),
    String(&'a str),
    Bool(bool),
    Null,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg, // -
    Not, // !
    BitNot, // ~
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InfixOp {
    Add, Sub, Mul, Div, Mod,
    Eq, Neq, Lt, Lte, Gt, Gte,
    BitAnd, BitOr, BitXor,
    Shl, Shr,
    Range, RangeInclusive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicalOp {
    And, // &&
    Or, // ||
}
