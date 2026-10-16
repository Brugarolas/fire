// src/diag.rs
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use compact_str::CompactString;
use smallvec::SmallVec;
use std::io::Error;
use std::ops::Range;
use std::result::Result;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FileId(pub u32);

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct Span {
    pub range: Range<usize>,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span { range: start..end }
    }

    pub fn with_range(range: Range<usize>) -> Self {
        Span { range }
    }

    #[inline]
    pub fn set(&mut self, start: usize, end: usize) {
        self.range = start..end;
    }

    #[inline]
    pub fn set_span(&mut self, span: Range<usize>) {
        self.range = span;
    }

    #[inline]
    pub fn join_span(&mut self, b: &Span) {
        // Safe even if overlapping; assumes both in same file.
        self.range = self.range.start.min(b.range.start)..self.range.end.max(b.range.end)
    }

    #[inline]
    pub fn join_spans(&mut self, b: &Span, c: &Span) {
        self.range = self.range.start.min(b.range.start).min(c.range.start)
            ..self.range.end.max(b.range.end).max(c.range.end)
    }

    #[inline]
    pub fn covering(a: &Span, b: &Span) -> Span {
        let mut out = a.clone();
        out.join_span(b);
        out
    }
}

#[derive(Clone, Debug, Default)]
pub struct Meta {
    pub file: Option<FileId>,
    pub span: Span,
    pub stack_span: Vec<FrontErrorLabel>, // for the stack of calls
    pub escape: EscapeInfo,               // future: escape analysis
    pub purity: Purity,                   // future: purity analysis
    // Diagnostics are rare; keep their payload off every AST node's stack frame.
    pub front_error: Option<Box<FrontError>>,
}

#[derive(Clone, Debug)]
pub struct Node<T> {
    pub meta: Meta,
    pub kind: T,
}

impl<T> Node<T> {
    #[inline]
    pub fn new(meta: Meta, kind: T) -> Self {
        Self { meta, kind }
    }

    #[inline]
    pub fn unknown(kind: T) -> Self {
        Self {
            meta: Meta::unknown(),
            kind,
        }
    }

    #[inline]
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Node<U> {
        Node {
            meta: self.meta,
            kind: f(self.kind),
        }
    }

    #[inline]
    pub fn with_meta(mut self, meta: Meta) -> Self {
        self.meta = meta;
        self
    }

    #[inline]
    pub fn into_inner(self) -> T {
        self.kind
    }

    #[inline]
    pub fn meta(&self) -> &Meta {
        &self.meta
    }

    #[inline]
    pub fn meta_mut(&mut self) -> &mut Meta {
        &mut self.meta
    }

    #[inline]
    pub fn kind(&self) -> &T {
        &self.kind
    }

    #[inline]
    pub fn kind_mut(&mut self) -> &mut T {
        &mut self.kind
    }
}

impl<T> std::ops::Deref for Node<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.kind
    }
}

impl<T> std::ops::DerefMut for Node<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.kind
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum EscapeInfo {
    #[default]
    Unknown,
    NoEscape,
    Captured,
    Escapes,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Purity {
    #[default]
    Unknown,
    Pure,
    Impure,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct FrontError {
    pub file_name: CompactString,
    pub span: Span,
    pub message: FrontErrorMessage,
    pub code: ErrorCode,
    pub labels: Vec<FrontErrorLabel>, // for the stack of calls
    pub note: Option<FrontErrorMessage>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ErrorCode {
    SyntaxError,
    TypeError,
    NameError,
    AlreadyDefined,
    NotDefined,
    DefinedUnused,
    // ... add more
}

impl ErrorCode {
    pub fn as_str(&self) -> &'static str {
        match self {
            ErrorCode::SyntaxError => "E001",
            ErrorCode::TypeError => "E002",
            ErrorCode::NameError => "E003",
            ErrorCode::AlreadyDefined => "E004",
            ErrorCode::NotDefined => "E005",
            ErrorCode::DefinedUnused => "E006",
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct FrontErrorLabel {
    pub file_name: CompactString,
    pub span: Span,
    pub message: Option<FrontErrorMessage>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct FrontErrorMessage {
    pub text: CompactString,                     // e.g. "This is of type {}"
    pub highlighted_strings: Vec<CompactString>, // values to slot into {}
    pub color: RegisteredColors,                 // color used for the inserts (and label)
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum RegisteredColors {
    Red,
    Green,
    Blue,
    Yellow,
    Cyan,
    Magenta,
    White,
    Black,
    BrightRed,
    BrightGreen,
}

impl RegisteredColors {
    pub fn to_color(self) -> Color {
        match self {
            RegisteredColors::Red => Color::Red,
            RegisteredColors::Green => Color::Green,
            RegisteredColors::Blue => Color::Blue,
            RegisteredColors::Yellow => Color::Yellow,
            RegisteredColors::Cyan => Color::Cyan,
            RegisteredColors::Magenta => Color::Magenta,
            RegisteredColors::White => Color::White,
            RegisteredColors::Black => Color::Black,
            // Use ANSI 9/10 as "bright" variants (portable enough for terminals)
            RegisteredColors::BrightRed => Color::Fixed(9),
            RegisteredColors::BrightGreen => Color::Fixed(10),
        }
    }
}

impl FrontErrorMessage {
    pub fn plain<S: Into<CompactString>>(text: S) -> Self {
        FrontErrorMessage {
            text: text.into(),
            highlighted_strings: Vec::new(),
            color: RegisteredColors::BrightRed,
        }
    }

    /// Render `text` replacing each `{}` (first N occurrences) with a colored value from `highlighted_strings`.
    pub fn render(&self) -> String {
        let mut out = self.text.to_string();
        for s in &self.highlighted_strings {
            let colored = format!("{}", s.as_str().fg(self.color.to_color()));
            if let Some(pos) = out.find("{}") {
                // replace the first "{}"
                out.replace_range(pos..pos + 2, &colored);
            } else {
                // if there are more values than braces, append them
                if !out.ends_with(' ') {
                    out.push(' ');
                }
                out.push_str(&colored);
            }
        }
        out
    }
}

/// Convenience for formatting a colored message without constructing a FrontErrorMessage.
pub fn format_error(
    message: CompactString,
    params: Vec<CompactString>,
    color: RegisteredColors,
) -> CompactString {
    let m = FrontErrorMessage {
        text: message,
        highlighted_strings: params,
        color,
    };
    m.render().into()
}

impl FrontError {
    /// Emit a single-file ariadne report.
    /// `source` is (file_name, entire_file_contents).
    pub fn emit(&self, source: (&str, &str)) -> Result<(), Error> {
        let mut builder = Report::build(
            ReportKind::Error,
            (self.file_name.as_str(), self.span.range.clone()),
        )
        .with_code(self.code.as_str())
        .with_message(self.message.render());

        for lab in &self.labels {
            builder = builder.with_label(
                // If error message exists
                if let Some(msg) = &lab.message {
                    Label::new((lab.file_name.as_str(), lab.span.range.clone()))
                        .with_message(msg.render())
                        .with_color(msg.color.to_color())
                } else {
                    // No message, just a label with color
                    Label::new((lab.file_name.as_str(), lab.span.range.clone()))
                },
            );
        }

        if let Some(note) = &self.note {
            builder = builder.with_note(note.render());
        }

        let report = builder.finish().print((source.0, Source::from(source.1)));

        return report;
    }
}

impl Meta {
    pub fn new(file: FileId, span: Span) -> Self {
        Meta {
            file: Some(file),
            span,
            ..Default::default()
        }
    }

    pub fn unknown() -> Self {
        Meta {
            file: None,
            span: Span::new(0, 0),
            ..Default::default()
        }
    }

    #[inline]
    pub fn covering(a: &Meta, b: &Meta) -> Meta {
        let mut span = a.span.clone();
        span.join_span(&b.span);
        Meta {
            file: a.file.or(b.file),
            span,
            ..Default::default()
        }
    }
}
