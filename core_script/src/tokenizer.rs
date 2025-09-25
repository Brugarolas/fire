// tokenizer.rs

use logos::Logos;
use std::fmt;

#[derive(Logos, Debug, PartialEq, Clone, Copy, Eq, Hash)]
#[logos(skip r"[ \t\r\n\f]+")] // Ignore this regex pattern
#[logos(skip r"//[^\n]*")] // Ignore comments
#[logos(skip r"/\*([^*]|\*[^/])*\*/")] // Ignore block comments
pub enum Token<'a> {
    #[token("import")]
    Import,
    #[token("as")]
    As,
    #[token("for")]
    For,
    #[token("in")]
    In,
    #[token("is")]
    Is,
    #[token("class")]
    Class,
    #[token("foreign")]
    Foreign,
    #[token("var")]
    Var,
    #[token("construct")]
    Construct,
    #[token("static")]
    Static,
    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[token("while")]
    While,
    #[token("return")]
    Return,
    #[token("break")]
    Break,
    #[token("continue")]
    Continue,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("null")]
    Null,
    #[token("this")]
    This,
    #[token("super")]
    Super,

    // Operators
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,
    #[token("!")]
    Bang,
    #[token("=")]
    Eq,
    #[token("==")]
    EqEq,
    #[token("!=")]
    BangEq,
    #[token("<")]
    Lt,
    #[token("<=")]
    LtEq,
    #[token(">")]
    Gt,
    #[token(">=")]
    GtEq,
    #[token("&&")]
    AndAnd,
    #[token("||")]
    OrOr,
    #[token("..")]
    DotDot,
    #[token("...")]
    DotDotDot,
    #[token("?")]
    Question,
    #[token(":")]
    Colon,
    #[token("|")]
    Pipe,
    #[token("&")]
    And,
    #[token("^")]
    Caret,
    #[token("~")]
    Tilde,
    #[token("<<")]
    LtLt,
    #[token(">>")]
    GtGt,

    // Punctuation
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token(".")]
    Dot,
    #[token(",")]
    Comma,

    // Literals
    #[regex("[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice())]
    Identifier(&'a str),
    #[regex(r#""([^"\\]|\\.)*""#, |lex| lex.slice())]
    String(&'a str),
    #[regex("[0-9]+(\\.[0-9]+)?", |lex| lex.slice().parse().ok())]
    Number(f64),
}

impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
