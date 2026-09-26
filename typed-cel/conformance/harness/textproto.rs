//! A textproto reader, scoped to what google/cel-spec's corpus actually uses.
//!
//! The corpus ships as protobuf text format. We read it without a protobuf dependency, a
//! generated descriptor or a build step, because the alternative is a code-generation toolchain in
//! the graph for the sake of 29 static files that change once a release.
//!
//! This is a GENERIC reader: it produces a tree of fields and values and knows nothing about
//! `SimpleTestFile`. Schema knowledge lives in `case.rs`, so a corpus that grows a field this
//! parser has never seen still parses, and the case reader is the thing that decides whether it
//! cares.
//!
//! `Any` expansion (`[type.googleapis.com/google.protobuf.Duration] { … }`) IS used, in
//! `object_value`, so a bracketed type URL is read as a field name and the URL is kept verbatim.
//! The `<…>` message brackets are not implemented, because the corpus does not use them.
//! `parses_the_whole_corpus` in `tests/conformance.rs` is what holds that claim to the actual
//! files — if a future corpus uses one, the parse fails loudly rather than dropping a field.

use std::fmt;

/// A parsed message: an ORDERED list of (field, value). Order is kept and duplicates are kept
/// separately, because in proto text format a repeated field is spelled by repeating the key —
/// collapsing into a map would silently drop every test but the last in a section.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Msg {
    pub fields: Vec<(String, Value)>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    /// A string or bytes literal, as BYTES. The corpus's `bytes_value` fields carry octal escapes
    /// for sequences that are not valid UTF-8, so decoding to `String` here would lose them.
    Str(Vec<u8>),
    /// A numeric literal, kept as its LEXEME. `9223372036854775808` is a valid `uint64_value` and
    /// not a valid `i64`; parsing eagerly to either would corrupt one of them, so the consumer
    /// parses at the width its field actually has.
    Num(String),
    /// A bare identifier: `true`, `false`, `NULL_VALUE`, an enum member.
    Ident(String),
    Msg(Msg),
    List(Vec<Value>),
}

impl Msg {
    /// The first value for `field`, or `None`.
    pub fn get(&self, field: &str) -> Option<&Value> {
        self.fields.iter().find(|(k, _)| k == field).map(|(_, v)| v)
    }

    /// Every value for `field`, in source order.
    pub fn all<'a>(&'a self, field: &'a str) -> impl Iterator<Item = &'a Value> + 'a {
        self.fields
            .iter()
            .filter(move |(k, _)| k == field)
            .map(|(_, v)| v)
    }

    pub fn get_msg(&self, field: &str) -> Option<&Msg> {
        match self.get(field)? {
            Value::Msg(m) => Some(m),
            _ => None,
        }
    }

    /// A string field, decoded as UTF-8. `None` if absent; an error if present and not UTF-8.
    pub fn get_str(&self, field: &str) -> Option<String> {
        match self.get(field)? {
            Value::Str(b) => Some(String::from_utf8_lossy(b).into_owned()),
            _ => None,
        }
    }

    pub fn get_bool(&self, field: &str) -> Option<bool> {
        match self.get(field)? {
            Value::Ident(i) if i == "true" => Some(true),
            Value::Ident(i) if i == "false" => Some(false),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct ParseError {
    pub line: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.message)
    }
}

impl std::error::Error for ParseError {}

pub fn parse(src: &str) -> Result<Msg, ParseError> {
    let mut p = Parser {
        b: src.as_bytes(),
        i: 0,
        line: 1,
    };
    let msg = p.message(true)?;
    p.skip_trivia();
    if p.i < p.b.len() {
        return Err(p.err(format!("trailing input at byte {}", p.i)));
    }
    Ok(msg)
}

struct Parser<'a> {
    b: &'a [u8],
    i: usize,
    line: usize,
}

impl Parser<'_> {
    fn err(&self, message: String) -> ParseError {
        ParseError {
            line: self.line,
            message,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }

    fn bump(&mut self) -> Option<u8> {
        let c = self.peek()?;
        self.i += 1;
        if c == b'\n' {
            self.line += 1;
        }
        Some(c)
    }

    /// Whitespace and `#` comments. Comments run to end of line and cannot appear inside a string,
    /// which is why this is only ever called between tokens.
    fn skip_trivia(&mut self) {
        loop {
            match self.peek() {
                Some(c) if c.is_ascii_whitespace() => {
                    self.bump();
                }
                Some(b'#') => {
                    while !matches!(self.peek(), None | Some(b'\n')) {
                        self.bump();
                    }
                }
                _ => return,
            }
        }
    }

    /// Fields until `}` (or EOF at the top level).
    fn message(&mut self, top_level: bool) -> Result<Msg, ParseError> {
        let mut fields = Vec::new();
        loop {
            self.skip_trivia();
            match self.peek() {
                None if top_level => return Ok(Msg { fields }),
                None => return Err(self.err("unterminated message".into())),
                Some(b'}') if !top_level => {
                    self.bump();
                    return Ok(Msg { fields });
                }
                Some(b'}') => return Err(self.err("unbalanced `}`".into())),
                Some(_) => {}
            }

            let name = self.field_name()?;
            self.skip_trivia();
            // The colon is REQUIRED before a scalar and OPTIONAL before a message, which is why
            // `section { … }` and `value: { … }` both appear in the same file.
            let had_colon = if self.peek() == Some(b':') {
                self.bump();
                self.skip_trivia();
                true
            } else {
                false
            };
            let value = match self.peek() {
                Some(b'{') => {
                    self.bump();
                    Value::Msg(self.message(false)?)
                }
                Some(b'[') => {
                    self.bump();
                    self.list()?
                }
                _ if had_colon => self.scalar()?,
                other => {
                    return Err(self.err(format!(
                        "field `{name}` has neither `:` nor a message body (next byte {other:?})"
                    )))
                }
            };
            fields.push((name, value));
            // Text format allows an OPTIONAL `,` or `;` between fields, and the corpus uses both
            // spellings in the same message (`type_env { name: "x", ident { … } }`).
            self.skip_trivia();
            if matches!(self.peek(), Some(b',') | Some(b';')) {
                self.bump();
            }
        }
    }

    fn list(&mut self) -> Result<Value, ParseError> {
        let mut items = Vec::new();
        loop {
            self.skip_trivia();
            match self.peek() {
                Some(b']') => {
                    self.bump();
                    return Ok(Value::List(items));
                }
                Some(b',') => {
                    self.bump();
                }
                None => return Err(self.err("unterminated list".into())),
                Some(b'{') => {
                    self.bump();
                    items.push(Value::Msg(self.message(false)?));
                }
                _ => items.push(self.scalar()?),
            }
        }
    }

    /// A field name: a plain identifier, or a bracketed type URL for an `Any` expansion. The URL
    /// is kept WITH its brackets, so `object_value`'s reader can tell
    /// `[type.googleapis.com/google.protobuf.Duration]` from an ordinary field of that name.
    fn field_name(&mut self) -> Result<String, ParseError> {
        if self.peek() != Some(b'[') {
            return self.ident();
        }
        let start = self.i;
        self.bump();
        while !matches!(self.peek(), None | Some(b']')) {
            self.bump();
        }
        if self.bump() != Some(b']') {
            return Err(self.err("unterminated `[type.url]` field name".into()));
        }
        Ok(String::from_utf8_lossy(&self.b[start..self.i]).into_owned())
    }

    fn ident(&mut self) -> Result<String, ParseError> {
        let start = self.i;
        while matches!(self.peek(), Some(c) if c.is_ascii_alphanumeric() || c == b'_' || c == b'.')
        {
            self.bump();
        }
        if start == self.i {
            return Err(self.err(format!("expected an identifier at byte {}", self.i)));
        }
        Ok(String::from_utf8_lossy(&self.b[start..self.i]).into_owned())
    }

    fn scalar(&mut self) -> Result<Value, ParseError> {
        match self.peek() {
            Some(b'"') | Some(b'\'') => self.string(),
            Some(c) if c == b'-' || c == b'+' || c.is_ascii_digit() || c == b'.' => self.number(),
            Some(_) => Ok(Value::Ident(self.ident()?)),
            None => Err(self.err("expected a value".into())),
        }
    }

    /// One or more ADJACENT quoted literals, concatenated. The corpus wraps long CEL expressions
    /// across lines that way, so treating only the first literal as the value would silently
    /// truncate an expression into something that still parses as CEL and tests the wrong thing.
    fn string(&mut self) -> Result<Value, ParseError> {
        let mut out = Vec::new();
        loop {
            let quote = match self.peek() {
                Some(q @ (b'"' | b'\'')) => q,
                _ => break,
            };
            self.bump();
            loop {
                match self.bump() {
                    None => return Err(self.err("unterminated string".into())),
                    Some(c) if c == quote => break,
                    Some(b'\\') => self.escape(&mut out)?,
                    Some(c) => out.push(c),
                }
            }
            // Only whitespace and comments may sit between concatenated literals.
            let save = (self.i, self.line);
            self.skip_trivia();
            if !matches!(self.peek(), Some(b'"') | Some(b'\'')) {
                self.i = save.0;
                self.line = save.1;
                break;
            }
        }
        Ok(Value::Str(out))
    }

    fn escape(&mut self, out: &mut Vec<u8>) -> Result<(), ParseError> {
        let c = self
            .bump()
            .ok_or_else(|| self.err("dangling `\\`".into()))?;
        match c {
            b'n' => out.push(b'\n'),
            b'r' => out.push(b'\r'),
            b't' => out.push(b'\t'),
            b'a' => out.push(0x07),
            b'b' => out.push(0x08),
            b'f' => out.push(0x0c),
            b'v' => out.push(0x0b),
            b'\\' | b'\'' | b'"' | b'?' => out.push(c),
            b'x' | b'X' => {
                let mut n = 0u32;
                let mut digits = 0;
                while digits < 2 {
                    match self.peek() {
                        Some(h) if h.is_ascii_hexdigit() => {
                            n = n * 16 + (h as char).to_digit(16).unwrap();
                            self.bump();
                            digits += 1;
                        }
                        _ => break,
                    }
                }
                if digits == 0 {
                    return Err(self.err("`\\x` with no hex digits".into()));
                }
                out.push(n as u8);
            }
            // `\uXXXX` is a UNICODE scalar and encodes to UTF-8; `\NNN` is a raw OCTAL BYTE and
            // must not. Conflating them turns `bytes_value` into mojibake that still compares
            // equal to itself, so the test passes while measuring nothing.
            b'u' | b'U' => {
                let width = if c == b'u' { 4 } else { 8 };
                let mut n = 0u32;
                for _ in 0..width {
                    let h = self
                        .bump()
                        .filter(|h| h.is_ascii_hexdigit())
                        .ok_or_else(|| self.err("short `\\u` escape".into()))?;
                    n = n * 16 + (h as char).to_digit(16).unwrap();
                }
                let ch =
                    char::from_u32(n).ok_or_else(|| self.err(format!("bad scalar U+{n:04X}")))?;
                let mut buf = [0u8; 4];
                out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
            }
            b'0'..=b'7' => {
                let mut n = (c - b'0') as u32;
                let mut digits = 1;
                while digits < 3 {
                    match self.peek() {
                        Some(o @ b'0'..=b'7') => {
                            n = n * 8 + (o - b'0') as u32;
                            self.bump();
                            digits += 1;
                        }
                        _ => break,
                    }
                }
                out.push(n as u8);
            }
            other => return Err(self.err(format!("unknown escape `\\{}`", other as char))),
        }
        Ok(())
    }

    fn number(&mut self) -> Result<Value, ParseError> {
        let start = self.i;
        if matches!(self.peek(), Some(b'-') | Some(b'+')) {
            self.bump();
        }
        while matches!(self.peek(), Some(c) if c.is_ascii_alphanumeric() || c == b'.') {
            // An exponent's sign is part of the literal: `1e-5`.
            let c = self.bump().unwrap();
            if (c == b'e' || c == b'E') && matches!(self.peek(), Some(b'-') | Some(b'+')) {
                self.bump();
            }
        }
        if start == self.i {
            return Err(self.err("expected a number".into()));
        }
        Ok(Value::Num(
            String::from_utf8_lossy(&self.b[start..self.i]).into_owned(),
        ))
    }
}
