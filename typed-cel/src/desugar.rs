//! The one alias: duration literals.
//!
//! `30s` becomes `duration('30s')`. That is the entire deviation from spec CEL that an author may
//! write, and it expands to a call the spec already defines — so the source the
//! parser, the checker and the evaluator see is standard CEL throughout.
//!
//! The rule, stated mechanically because a convenience added
//! here costs nothing locally and costs a non-standard language globally: **nothing may be added
//! to this pass without first deleting the duration alias.** A second rewrite is a deliberate
//! trade, never an accumulation.
//!
//! Two things this pass is NOT:
//!
//! - It is not a lexer. It walks the source once, tracking only enough state to know whether it is
//!   inside a string literal or a comment, because a regex over `\d+[a-z]+` rewrites
//!   `body.note == "call me in 30s"` and corrupts data rather than sugaring syntax.
//! - It is not where unsupported syntax is diagnosed. `?.`, `??`, `[?k]` and the rest pass through
//!   byte-identical and are rejected by the parser or the checker, which is where a diagnostic can
//!   say what the dialect does instead.

use std::fmt;

/// Why a source could not be desugared.
///
/// Both variants are about a duration literal, because that is the only construct this pass
/// interprets. Each carries the byte offset in the AUTHORED source, so the diagnostic points at
/// what was typed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DesugarError {
    /// `1d`. CEL's `duration()` has no day unit — `duration('1d')` is an evaluation-time
    /// `FunctionError` — so expanding it would produce source that parses and fails at revocation
    /// time, forever.
    DayUnit { at: usize, literal: String },
    /// `30x`, `30sec`, `30S`. Rejected at build rather than passed through as an identifier the
    /// checker later reports as undeclared, which would name the wrong mistake.
    UnknownUnit { at: usize, unit: String },
}

impl DesugarError {
    /// Byte offset in the authored source.
    pub fn at(&self) -> usize {
        match self {
            DesugarError::DayUnit { at, .. } | DesugarError::UnknownUnit { at, .. } => *at,
        }
    }
}

impl fmt::Display for DesugarError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DesugarError::DayUnit { literal, .. } => write!(
                f,
                "`{literal}`: CEL durations have no day unit; write `24h`"
            ),
            DesugarError::UnknownUnit { unit, .. } => write!(
                f,
                "`{unit}` is not a duration unit; the units are ms, s, m, h"
            ),
        }
    }
}

impl std::error::Error for DesugarError {}

/// Maps a byte offset in the DESUGARED source back to the AUTHORED source.
///
/// `30s` grows by 12 bytes when it becomes `duration('30s')`, so every offset after a rewrite
/// shifts. Without this a checker diagnostic carets a column the author never typed — which is
/// worse than no caret, because it points confidently at the wrong thing.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SpanMap(Vec<(usize, isize)>);

impl SpanMap {
    /// The authored offset for a desugared one. Saturating: an offset past the end of the last
    /// recorded region still lands somewhere in the authored source rather than panicking, because
    /// a diagnostic that panics is worse than a diagnostic that is a few columns off.
    pub fn to_authored(&self, offset: usize) -> usize {
        let delta = match self.0.binary_search_by_key(&offset, |(at, _)| *at) {
            Ok(i) => self.0[i].1,
            Err(0) => 0,
            Err(i) => self.0[i - 1].1,
        };
        offset.saturating_add_signed(delta)
    }

    /// Nothing was rewritten — offsets are already authored offsets.
    pub fn identity() -> SpanMap {
        SpanMap(Vec::new())
    }

    fn push(&mut self, desugared: usize, authored: usize) {
        self.0
            .push((desugared, authored as isize - desugared as isize));
    }
}

/// The duration units `duration()` accepts, longest first so `ms` wins over `m`.
const UNITS: &[&str] = &["ms", "s", "m", "h"];

/// `30s` -> `duration('30s')`, and nothing else.
///
/// Returns the desugared source plus the shifts needed to map a diagnostic back to what the author
/// typed. Run this BEFORE the source-length and depth bounds: the bounds are about what the parser
/// will see, and the desugared form is what the parser sees.
pub fn desugar(src: &str) -> Result<(String, SpanMap), DesugarError> {
    let b = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut spans = SpanMap::default();
    let mut i = 0usize;
    // The last byte consumed outside a literal, so a number can tell `a.30s` (a select, leave it
    // alone) from `> 30s` (a duration).
    let mut prev = 0u8;

    while i < b.len() {
        let c = b[i];

        // A line comment runs to the newline and is copied verbatim. Rewriting inside one would
        // corrupt prose for no benefit.
        if c == b'/' && b.get(i + 1) == Some(&b'/') {
            let end = src[i..].find('\n').map(|n| i + n).unwrap_or(b.len());
            out.push_str(&src[i..end]);
            i = end;
            continue;
        }

        // An identifier run is consumed whole, which is what keeps `x30s`, `a.b30s` and `p30s`
        // identifiers rather than an identifier abutting a duration. A run that turns out to be a
        // string prefix (`r'…'`, `b"…"`, `rb'…'`) hands off to the string scanner below.
        if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            out.push_str(&src[start..i]);
            let word = &src[start..i];
            if is_string_prefix(word) && matches!(b.get(i), Some(b'\'') | Some(b'"')) {
                let raw = word.bytes().any(|p| p == b'r' || p == b'R');
                let end = scan_string(b, i, raw);
                out.push_str(&src[i..end]);
                i = end;
            }
            prev = b[i - 1];
            continue;
        }

        if c == b'\'' || c == b'"' {
            let end = scan_string(b, i, false);
            out.push_str(&src[i..end]);
            i = end;
            prev = c;
            continue;
        }

        if c.is_ascii_digit() {
            // A number after `.` is a select's field position, not a literal we may rewrite.
            let selectish = prev == b'.';
            let (num_end, plain) = scan_number(b, i);
            if selectish || plain {
                out.push_str(&src[i..num_end]);
                prev = b[num_end - 1];
                i = num_end;
                continue;
            }
            match scan_duration(b, i)? {
                Some(end) => {
                    let literal = &src[i..end];
                    spans.push(out.len(), i);
                    out.push_str("duration('");
                    out.push_str(literal);
                    out.push_str("')");
                    spans.push(out.len(), end);
                    prev = b')';
                    i = end;
                }
                None => {
                    out.push_str(&src[i..num_end]);
                    prev = b[num_end - 1];
                    i = num_end;
                }
            }
            continue;
        }

        out.push(c as char);
        if !c.is_ascii_whitespace() {
            prev = c;
        }
        i += 1;
    }

    Ok((out, spans))
}

/// Is `word` one of CEL's string-literal prefixes (`r`, `b`, and the raw/bytes combinations)?
fn is_string_prefix(word: &str) -> bool {
    if word.is_empty() || word.len() > 2 {
        return false;
    }
    let mut r = 0;
    let mut bytes = 0;
    for ch in word.bytes() {
        match ch {
            b'r' | b'R' => r += 1,
            b'b' | b'B' => bytes += 1,
            _ => return false,
        }
    }
    r <= 1 && bytes <= 1
}

/// The end offset (exclusive) of the string literal starting at `open`.
///
/// Handles the triple-quoted forms and, for a non-raw literal, backslash escapes. An unterminated
/// literal runs to the end of the source — the parser reports it, and reporting it here as well
/// would mean two different messages for one mistake.
fn scan_string(b: &[u8], open: usize, raw: bool) -> usize {
    let quote = b[open];
    let triple = b.get(open + 1) == Some(&quote) && b.get(open + 2) == Some(&quote);
    let delim = if triple { 3 } else { 1 };
    let mut i = open + delim;
    while i < b.len() {
        if !raw && b[i] == b'\\' {
            i += 2;
            continue;
        }
        if b[i] == quote
            && (!triple || (b.get(i + 1) == Some(&quote) && b.get(i + 2) == Some(&quote)))
        {
            return (i + delim).min(b.len());
        }
        i += 1;
    }
    b.len()
}

/// Scan the numeric literal at `start`. Returns its end offset and whether it is PLAIN — a hex
/// literal or one carrying an exponent, neither of which can wear a duration unit.
fn scan_number(b: &[u8], start: usize) -> (usize, bool) {
    let mut i = start;
    if b[i] == b'0' && matches!(b.get(i + 1), Some(b'x') | Some(b'X')) {
        i += 2;
        while i < b.len() && b[i].is_ascii_hexdigit() {
            i += 1;
        }
        // A `u` suffix belongs to the hex literal, not to a unit.
        if matches!(b.get(i), Some(b'u') | Some(b'U')) {
            i += 1;
        }
        return (i, true);
    }
    while i < b.len() && b[i].is_ascii_digit() {
        i += 1;
    }
    if b.get(i) == Some(&b'.') && b.get(i + 1).is_some_and(|d| d.is_ascii_digit()) {
        i += 1;
        while i < b.len() && b[i].is_ascii_digit() {
            i += 1;
        }
    }
    if matches!(b.get(i), Some(b'e') | Some(b'E')) {
        let mut j = i + 1;
        if matches!(b.get(j), Some(b'+') | Some(b'-')) {
            j += 1;
        }
        if b.get(j).is_some_and(|d| d.is_ascii_digit()) {
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            return (j, true);
        }
    }
    (i, false)
}

/// The end offset of the duration literal starting at `start`, or `None` if the digits are just a
/// number.
///
/// A duration is one or more `<number><unit>` pairs — `1h30m` is one literal, handed to
/// `duration()` verbatim rather than added up here.
fn scan_duration(b: &[u8], start: usize) -> Result<Option<usize>, DesugarError> {
    let mut i = start;
    let mut pairs = 0usize;
    loop {
        let (num_end, plain) = scan_number(b, i);
        if num_end == i || plain {
            break;
        }
        let mut alpha = num_end;
        while alpha < b.len() && b[alpha].is_ascii_alphabetic() {
            alpha += 1;
        }
        if alpha == num_end {
            break;
        }
        let run = std::str::from_utf8(&b[num_end..alpha]).unwrap_or("");
        let unit = UNITS.iter().find(|u| run.starts_with(**u));
        match unit {
            // The remainder of the alpha run must itself start another pair, and it cannot: a unit
            // is followed by a digit or by nothing. `30sec` lands here.
            Some(u) if u.len() != run.len() => {
                return Err(DesugarError::UnknownUnit {
                    at: num_end,
                    unit: run.to_string(),
                })
            }
            Some(_) => {}
            None if run == "d" || run.starts_with('d') => {
                let end = alpha;
                return Err(DesugarError::DayUnit {
                    at: start,
                    literal: String::from_utf8_lossy(&b[start..end]).into_owned(),
                });
            }
            None => {
                return Err(DesugarError::UnknownUnit {
                    at: num_end,
                    unit: run.to_string(),
                })
            }
        }
        pairs += 1;
        i = alpha;
        if !b.get(i).is_some_and(|d| d.is_ascii_digit()) {
            break;
        }
    }
    if pairs == 0 {
        return Ok(None);
    }
    // A duration literal cannot abut an identifier character — that is an identifier we mis-split.
    if b.get(i)
        .is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_')
    {
        return Ok(None);
    }
    Ok(Some(i))
}
