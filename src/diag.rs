// src/diag.rs
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use smallvec::SmallVec;
use std::ops::Range;
use compact_str::CompactString;
use std::result::Result;
use std::io::Error;

pub type Span = Range<usize>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FileId(pub u32);

#[derive(Clone, Debug, Default)]
pub struct Meta {
    pub file: Option<FileId>,
    pub span: Span,
    pub escape: EscapeInfo, // future: escape analysis
    pub purity: Purity,     // future: purity analysis
    pub front_error: Option<FrontError>,
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
    pub labels: SmallVec<[FrontErrorLabel; 8]>,
    pub note: Option<FrontErrorMessage>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ErrorCode {
    SyntaxError,
    TypeError,
    NameError,
    // ... add more
}

impl ErrorCode {
    pub fn as_str(&self) -> &'static str {
        match self {
            ErrorCode::SyntaxError => "E001",
            ErrorCode::TypeError => "E002",
            ErrorCode::NameError => "E003",
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct FrontErrorLabel {
    pub file_name: CompactString,
    pub span: Span,
    pub message: FrontErrorMessage,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct FrontErrorMessage {
    pub text: CompactString,                             // e.g. "This is of type {}"
    pub highlighted_strings: SmallVec<[CompactString; 4]>, // values to slot into {}
    pub color: RegisteredColors,                         // color used for the inserts (and label)
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
    params: SmallVec<[CompactString; 4]>,
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
            (self.file_name.as_str(), self.span.clone()),
        )
        .with_code(self.code.as_str())
        .with_message(self.message.render());

        for lab in &self.labels {
            builder = builder.with_label(
                Label::new((lab.file_name.as_str(), lab.span.clone()))
                    .with_message(lab.message.render())
                    .with_color(lab.message.color.to_color()),
            );
        }

        if let Some(note) = &self.note {
            builder = builder.with_note(note.render());
        }

        let report= builder
            .finish()
            .print((source.0, Source::from(source.1)));

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
            span: 0..0,
            ..Default::default()
        }
    }
}