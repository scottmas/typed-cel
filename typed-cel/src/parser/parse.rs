use std::num::ParseIntError;

/// Error type of [parse_string].
#[derive(Debug, PartialEq)]
pub enum ParseSequenceError {
    // #[error("invalid escape {escape} at {index} in {string}")]
    InvalidEscape {
        escape: String,
        index: usize,
        string: String,
    },
    // #[error("\\u could not be parsed at {index} in {string}: {source}")]
    InvalidUnicode {
        // #[source]
        source: ParseUnicodeError,
        index: usize,
        string: String,
    },
    MissingOpeningQuote,
    MissingClosingQuote,
}

/// Source error type of [`ParseSequenceError::InvalidUnicode`].
#[derive(Debug, PartialEq, Clone)]
pub enum ParseUnicodeError {
    // #[error("could not parse {string} as u32 hex: {source}")]
    Hex {
        // #[source]
        source: ParseIntError,
        string: String,
    },
    Oct {
        // #[source]
        source: ParseIntError,
        string: String,
    },
    // #[error("could not parse {value} as a unicode char")]
    Unicode {
        value: u32,
    },
}

/// The prefix flags and the body of a string/bytes literal, with delimiters removed.
///
/// ONE place that knows a literal's shape. The two visitors disagreed before: `visit_String`
/// passed the quotes through to a decoder that dispatched on the FIRST character, and
/// `visit_Bytes` pre-stripped a hardcoded `[2..len-1]` — which is why a triple-quoted bytes
/// literal kept two of its own delimiters in the value, and why a triple-quoted string containing
/// a lone quote did not parse at all.
struct Literal<'a> {
    /// `r`/`R` seen. A raw literal never reaches the escape table: every backslash is content,
    /// including the one before a quote.
    raw: bool,
    /// The literal text between the delimiters, undecoded.
    body: &'a str,
    /// How many characters precede `body` in the original. Carried so an `InvalidEscape` still
    /// points at a column in what the author WROTE rather than at an offset into a substring
    /// nobody has seen.
    offset: usize,
}

/// Longest delimiter first: two quotes strip to empty under the single-quote rule, and six are an
/// EMPTY triple-quoted literal, so trying the shorter delimiter first would claim both and leave a
/// stray quote in the body.
const DELIMITERS: [&str; 4] = ["'''", "\"\"\"", "'", "\""];

fn split_literal(text: &str) -> Result<Literal<'_>, ParseSequenceError> {
    let mut rest = text;
    let mut raw = false;
    let mut bytes = false;
    // Prefixes may appear in either order and in either case: `rb`, `bR`, `B`.
    loop {
        match rest.as_bytes().first() {
            Some(b'r' | b'R') if !raw => {
                raw = true;
                rest = &rest[1..];
            }
            Some(b'b' | b'B') if !bytes => {
                bytes = true;
                rest = &rest[1..];
            }
            _ => break,
        }
    }
    let prefix = text.len() - rest.len();
    for delim in DELIMITERS {
        let Some(inner) = rest.strip_prefix(delim) else {
            continue;
        };
        // The opening and closing delimiters must not be the same characters read twice: a lone
        // quote is an unterminated literal, not an empty one.
        return match inner.strip_suffix(delim) {
            Some(body) if rest.len() >= 2 * delim.len() => Ok(Literal {
                raw,
                body,
                offset: prefix + delim.len(),
            }),
            _ => Err(ParseSequenceError::MissingClosingQuote),
        };
    }
    Err(ParseSequenceError::MissingOpeningQuote)
}

/// The escapes that stand for one character and take no argument.
///
/// Returned as a `char` because the string decoder needs one; every value here is ASCII, so the
/// bytes decoder casts without loss. `\u`/`\U` are deliberately absent — they take an argument,
/// and they are string-only, because a bytes literal has no code points to name.
///
/// There is no pass-the-character-through fallback, and there must not be one: it would decode
/// `\q` to `q` and the decoder would stop being able to report a typo. The corpus cannot see that
/// — cel-spec has no case for an invalid escape — so
/// `tests/literals.rs::an_escape_the_dialect_does_not_have_is_still_an_error` is what holds it.
fn simple_escape(c: char) -> Option<char> {
    Some(match c {
        '\\' => '\\',
        '?' => '?',
        '"' => '"',
        '\'' => '\'',
        '`' => '`',
        'a' => '\u{07}',
        'b' => '\u{08}',
        'f' => '\u{0C}',
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        'v' => '\u{0B}',
        _ => return None,
    })
}

pub fn parse_bytes(s: &str) -> Result<Vec<u8>, ParseSequenceError> {
    let lit = split_literal(s)?;
    if lit.raw {
        return Ok(lit.body.as_bytes().to_vec());
    }
    decode_bytes(&lit, s)
}

fn decode_bytes(lit: &Literal<'_>, whole: &str) -> Result<Vec<u8>, ParseSequenceError> {
    let mut chars = lit.body.chars().enumerate();
    let mut res: Vec<u8> = Vec::with_capacity(lit.body.len());

    while let Some((idx, c)) = chars.next() {
        if c != '\\' {
            // Content that is not an escape is carried through as its UTF-8 bytes, which is what a
            // bytes literal spelling a character rather than an escape means.
            let mut buffer = [0; 4];
            res.extend_from_slice(c.encode_utf8(&mut buffer).as_bytes());
            continue;
        }
        let invalid = |escape: String, at: usize| ParseSequenceError::InvalidEscape {
            escape,
            index: lit.offset + at,
            string: String::from(whole),
        };
        let (idx, c2) = chars.next().ok_or_else(|| invalid(format!("{c}"), idx))?;
        let byte = match simple_escape(c2) {
            Some(simple) => simple as u8,
            None => match c2 {
                // BOTH cases. cel-spec spells `\X41` as often as `\x41`, and rejecting the
                // uppercase form outright was eight corpus rows on its own.
                'x' | 'X' => take_radix(&mut chars, 2, 16).map_err(|e| invalid(e, idx))?,
                n if ('0'..='3').contains(&n) => {
                    let mut octal = String::with_capacity(3);
                    octal.push(n);
                    take_digits(&mut chars, 2, &mut octal);
                    u8::from_str_radix(&octal, 8).map_err(|_| invalid(octal, idx))?
                }
                _ => return Err(invalid(format!("{c}{c2}"), idx)),
            },
        };
        res.push(byte);
    }
    Ok(res)
}

/// Parse the provided quoted string.
/// This function was adopted from [snailquote](https://docs.rs/snailquote/latest/snailquote/).
///
/// # Details
///
/// Parses a single, double or triple quoted string and interprets escape sequences such as
/// '\n', '\r', '\'', etc.
///
/// Supports raw strings prefixed with `r` or `R` in which case all escape sequences are ignored.
///
/// The full set of supported escapes between quotes may be found below:
///
/// | Escape     | Code       | Description                              |
/// |------------|------------|------------------------------------------|
/// | \a         | 0x07       | Bell                                     |
/// | \b         | 0x08       | Backspace                                |
/// | \v         | 0x0B       | Vertical tab                             |
/// | \f         | 0x0C       | Form feed                                |
/// | \n         | 0x0A       | Newline                                  |
/// | \r         | 0x0D       | Carriage return                          |
/// | \t         | 0x09       | Tab                                      |
/// | \\         | 0x5C       | Backslash                                |
/// | \?         | 0x3F       | Question mark                            |
/// | \"         | 0x22       | Double quote                             |
/// | \'         | 0x27       | Single quote                             |
/// | \`         | 0x60       | Backtick                                 |
/// | \xDD, \XDD | 0xDD       | Unicode character with hex code DD       |
/// | \uDDDD     | 0xDDDD     | Unicode character with hex code DDDD     |
/// | \UDDDDDDDD | 0xDDDDDDDD | Unicode character with hex code DDDDDDDD |
/// | \DDD       | 0DDD       | Unicode character with octal code DDD    |
///
/// `\'` and `\"` decode to the bare quote whichever delimiter encloses them. The decoder used to
/// keep the backslash on whichever one did not match its opening quote, so a double-quoted string
/// containing an escaped apostrophe came back one character longer than cel-spec wants.
///
/// # Errors
///
/// The returned result can display a human readable error if the string cannot be parsed as a
/// valid quoted string.
pub fn parse_string(s: &str) -> Result<String, ParseSequenceError> {
    let lit = split_literal(s)?;
    if lit.raw {
        return Ok(lit.body.to_string());
    }
    decode_string(&lit, s)
}

fn decode_string(lit: &Literal<'_>, whole: &str) -> Result<String, ParseSequenceError> {
    let mut chars = lit.body.chars().enumerate();
    let mut res = String::with_capacity(lit.body.len());

    while let Some((idx, c)) = chars.next() {
        if c != '\\' {
            res.push(c);
            continue;
        }
        let invalid = |escape: String, at: usize| ParseSequenceError::InvalidEscape {
            escape,
            index: lit.offset + at,
            string: String::from(whole),
        };
        let (idx, c2) = chars.next().ok_or_else(|| invalid(format!("{c}"), idx))?;
        if let Some(simple) = simple_escape(c2) {
            res.push(simple);
            continue;
        }
        let bad_unicode = |source: &ParseUnicodeError| ParseSequenceError::InvalidUnicode {
            source: source.clone(),
            index: lit.offset + idx,
            string: String::from(whole),
        };
        let value = match c2 {
            'x' | 'X' | 'u' | 'U' => {
                let length = match c2 {
                    'x' | 'X' => 2,
                    'u' => 4,
                    _ => 8,
                };
                parse_unicode_hex(length, &mut chars).map_err(|x| bad_unicode(&x))?
            }
            n if ('0'..='3').contains(&n) => {
                parse_unicode_oct(&n, &mut chars).map_err(|x| bad_unicode(&x))?
            }
            _ => return Err(invalid(format!("{c}{c2}"), idx)),
        };
        res.push(value);
    }
    Ok(res)
}

/// Take `n` characters and read them in `radix` as one byte. The `Err` is the digits it read, for
/// the caller to name in its own error.
fn take_radix<I>(chars: &mut I, n: usize, radix: u32) -> Result<u8, String>
where
    I: Iterator<Item = (usize, char)>,
{
    let mut digits = String::with_capacity(n);
    take_digits(chars, n, &mut digits);
    u8::from_str_radix(&digits, radix).map_err(|_| digits)
}

/// Append up to `n` characters. Running out is not silently tolerated: the caller's radix parse
/// fails on the short string and reports the escape it could not finish.
fn take_digits<I>(chars: &mut I, n: usize, out: &mut String)
where
    I: Iterator<Item = (usize, char)>,
{
    for _ in 0..n {
        match chars.next() {
            Some((_, c)) => out.push(c),
            None => return,
        }
    }
}

fn parse_unicode_hex<I>(length: usize, chars: &mut I) -> Result<char, ParseUnicodeError>
where
    I: Iterator<Item = (usize, char)>,
{
    let unicode_seq: String = chars.take(length).map(|(_, c)| c).collect();

    u32::from_str_radix(&unicode_seq, 16)
        .map_err(|e| ParseUnicodeError::Hex {
            source: e,
            string: unicode_seq,
        })
        .and_then(|u| char::from_u32(u).ok_or(ParseUnicodeError::Unicode { value: u }))
}

fn parse_unicode_oct<I>(first_char: &char, chars: &mut I) -> Result<char, ParseUnicodeError>
where
    I: Iterator<Item = (usize, char)>,
{
    let mut unicode_seq: String = String::with_capacity(3);
    unicode_seq.push(*first_char);
    chars.take(2).for_each(|(_, c)| unicode_seq.push(c));

    u32::from_str_radix(&unicode_seq, 8)
        .map_err(|e| ParseUnicodeError::Oct {
            source: e,
            string: unicode_seq,
        })
        .and_then(|u| {
            if u <= 255 {
                char::from_u32(u).ok_or(ParseUnicodeError::Unicode { value: u })
            } else {
                Err(ParseUnicodeError::Unicode { value: u })
            }
        })
}

#[cfg(test)]
mod tests {
    use super::{parse_bytes, parse_string, ParseSequenceError};

    #[test]
    fn single_quotes_interprets_escapes() {
        let tests: Vec<(&str, Result<String, ParseSequenceError>)> = vec![
            ("'Hello \\a'", Ok(String::from("Hello \u{07}"))),
            ("'Hello \\b'", Ok(String::from("Hello \u{08}"))),
            ("'Hello \\v'", Ok(String::from("Hello \u{0b}"))),
            ("'Hello \\f'", Ok(String::from("Hello \u{0c}"))),
            ("'Hello \\n'", Ok(String::from("Hello \u{0a}"))),
            ("'Hello \\r'", Ok(String::from("Hello \u{0d}"))),
            ("'Hello \\t'", Ok(String::from("Hello \u{09}"))),
            ("'Hello \\\\'", Ok(String::from("Hello \\"))),
            ("'Hello \\?'", Ok(String::from("Hello ?"))),
            ("'Hello \"'", Ok(String::from("Hello \""))),
            ("'Hello \\''", Ok(String::from("Hello '"))),
            ("'Hello \\`'", Ok(String::from("Hello `"))),
            ("'Hello \\x20'", Ok(String::from("Hello  "))),
            ("'Hello \\u270c'", Ok(String::from("Hello ✌"))),
            ("'Hello \\U0001f431'", Ok(String::from("Hello 🐱"))),
            ("'Hello \\040'", Ok(String::from("Hello  "))),
            (
                "Missing closing quote'",
                Err(ParseSequenceError::MissingOpeningQuote),
            ),
            (
                "'Missing closing quote",
                Err(ParseSequenceError::MissingClosingQuote),
            ),
            // Testing octal value is out of range
            (
                "'\\440'",
                Err(ParseSequenceError::InvalidEscape {
                    escape: String::from("\\4"),
                    index: 2,
                    string: String::from("'\\440'"),
                }),
            ),
        ];

        for (s, expected) in tests {
            let result = parse_string(s);
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn double_quotes_interprets_escapes() {
        let tests: Vec<(&str, Result<String, ParseSequenceError>)> = vec![
            ("\"Hello \\a\"", Ok(String::from("Hello \u{07}"))),
            ("\"Hello \\b\"", Ok(String::from("Hello \u{08}"))),
            ("\"Hello \\v\"", Ok(String::from("Hello \u{0b}"))),
            ("\"Hello \\f\"", Ok(String::from("Hello \u{0c}"))),
            ("\"Hello \\n\"", Ok(String::from("Hello \u{0a}"))),
            ("\"Hello \\r\"", Ok(String::from("Hello \u{0d}"))),
            ("\"Hello \\t\"", Ok(String::from("Hello \u{09}"))),
            ("\"Hello \\\\\"", Ok(String::from("Hello \\"))),
            ("\"Hello \\?\"", Ok(String::from("Hello ?"))),
            ("\"Hello \\\"\"", Ok(String::from("Hello \""))),
            // Re-pinned against cel-spec: `\'` decodes to the bare quote whichever delimiter
            // encloses it. Upstream kept the backslash on the one that did not match, which is
            // `parse/string_literals/double_quoted_escaped_punctuation` in the corpus.
            ("\"Hello \\'\"", Ok(String::from("Hello '"))),
            ("\"Hello \\`\"", Ok(String::from("Hello `"))),
            ("\"Hello \\x20 \"", Ok(String::from("Hello   "))),
            ("\"Hello \\x60\"", Ok(String::from("Hello `"))),
            ("\"Hello \\u270c\"", Ok(String::from("Hello ✌"))),
            ("\"Hello \\U0001f431\"", Ok(String::from("Hello 🐱"))),
            ("\"Hello \\040\"", Ok(String::from("Hello  "))),
            (
                "Missing closing quote\"",
                Err(ParseSequenceError::MissingOpeningQuote),
            ),
            (
                "\"Missing closing quote",
                Err(ParseSequenceError::MissingClosingQuote),
            ),
            // Testing octal value is out of range
            (
                "\"\\440\"",
                Err(ParseSequenceError::InvalidEscape {
                    escape: String::from("\\4"),
                    index: 2,
                    string: String::from("\"\\440\""),
                }),
            ),
        ];

        for (s, expected) in tests {
            let result = parse_string(s);
            assert_eq!(result, expected, "Testing {s}");
        }
    }

    #[test]
    fn raw_string_does_not_interpret_escapes() {
        // Re-pinned against cel-spec: a raw literal is ENTIRELY literal. Upstream dropped the
        // backslash before whichever quote did not open the literal, so `r"\\'"` came back one
        // character short — `parse/string_literals/raw_*_escapes` is the corpus row, and it
        // spells out every backslash it expects to survive.
        let tests: Vec<(&str, Result<String, ParseSequenceError>)> = vec![
            // Raw string in double quotes
            (
                "r\"Hello \\a \\\" ' \\' \\U0001f431 \"",
                Ok(String::from("Hello \\a \\\" ' \\' \\U0001f431 ")),
            ),
            (
                "R\"Hello \\a \\\" ' \\' \\U0001f431 \"",
                Ok(String::from("Hello \\a \\\" ' \\' \\U0001f431 ")),
            ),
            // Raw string in single quotes
            (
                "r'Hello \\a \\\" \" \\' \\U0001f431 '",
                Ok(String::from("Hello \\a \\\" \" \\' \\U0001f431 ")),
            ),
            (
                "R'Hello \\a \\\" \" \\' \\U0001f431 '",
                Ok(String::from("Hello \\a \\\" \" \\' \\U0001f431 ")),
            ),
        ];

        for (s, expected) in tests {
            let result = parse_string(s);
            assert_eq!(result, expected, "Testing {s}");
        }
    }

    #[test]
    fn parses_bytes() {
        // The WHOLE token now, prefix and delimiters included — one function knows a literal's
        // shape, so the caller no longer pre-strips.
        let bytes = parse_bytes("b'abc💖\\xFF\\376'").expect("Must parse!");
        assert_eq!([97, 98, 99, 240, 159, 146, 150, 255, 254], *bytes)
    }
}
