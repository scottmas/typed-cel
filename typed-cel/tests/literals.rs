//! String and bytes LITERALS, decoded end to end through the parser.
//!
//! Separate from `tests/dialect.rs` because this is not about what the dialect removed — it is the
//! one table in the crate that has to agree with cel-spec character for character, and the corpus
//! rows that check it (`parse/string_literals`, `parse/bytes_literals`) are 70 of the board's
//! failures. A table here is what makes a red legible: the corpus reports a byte vector, and
//! `\X41` versus `\x41` is not something anyone spots in a byte vector.
//!
//! Everything goes through `Program::compile`, so a literal is tested the way a policy reaches
//! it — the delimiter stripping, the prefix flags and the escape table are one question, and they
//! have been answered in two different places before.

use typed_cel::fork::objects::Value;
use typed_cel::fork::{Context, Program};

/// Evaluate `src` and return the string it produced, or the refusal.
fn string(src: &str) -> Result<String, String> {
    match value(src)? {
        Value::String(s) => Ok(s.to_string()),
        other => Err(format!("not a string: {other:?}")),
    }
}

/// Evaluate `src` and return the bytes it produced, or the refusal.
fn bytes(src: &str) -> Result<Vec<u8>, String> {
    match value(src)? {
        Value::Bytes(b) => Ok(b.to_vec()),
        other => Err(format!("not bytes: {other:?}")),
    }
}

fn value(src: &str) -> Result<Value, String> {
    Program::compile(src)
        .map_err(|e| format!("parse: {e}"))?
        .execute(&Context::default())
        .map_err(|e| format!("eval: {e}"))
}

/// A triple-quoted literal loses THREE delimiters at each end, not one.
///
/// The single-character assumption is why `b'''hello'''` kept two of its own quotes in the value
/// and `'''hello'''` did not parse at all: one caller stripped a fixed `[2..len-1]`, and the other
/// dispatched on the first character and never looked at the second or third.
#[test]
fn a_triple_quoted_string_strips_three_quotes() {
    for src in [
        "'''hello'''",
        "\"\"\"hello\"\"\"",
        "r'''hello'''",
        "R\"\"\"hello\"\"\"",
    ] {
        assert_eq!(string(src).as_deref(), Ok("hello"), "for {src}");
    }
}

#[test]
fn a_triple_quoted_bytes_literal_strips_three_quotes() {
    for src in [
        "b'''hello'''",
        "b\"\"\"hello\"\"\"",
        "br'''hello'''",
        "bR\"\"\"hello\"\"\"",
    ] {
        assert_eq!(bytes(src), Ok(b"hello".to_vec()), "for {src}");
    }
}

/// Inside a triple-quoted body, a lone quote is ordinary content.
///
/// This is the case a naive "strip three, then decode" gets wrong by scanning for a terminator it
/// has already found: the inner `"` is not the end of anything, and neither is the inner `'`.
#[test]
fn an_unescaped_quote_survives_a_triple_quoted_literal() {
    let expected = " ? \" ' ` ";
    assert_eq!(string("''' ? \" ' ` '''").as_deref(), Ok(expected));
    assert_eq!(string("\"\"\" ? \" ' ` \"\"\"").as_deref(), Ok(expected));
    assert_eq!(bytes("b''' ? \" ' ` '''"), Ok(expected.as_bytes().to_vec()));
    assert_eq!(
        bytes("b\"\"\" ? \" ' ` \"\"\""),
        Ok(expected.as_bytes().to_vec())
    );
}

/// The whole CEL escape table, in a string.
///
/// `\'` and `\"` decode to the bare quote REGARDLESS of which delimiter encloses them — the old
/// decoder kept the backslash on whichever one did not match, which is the difference between
/// `" \" "` and `" \\\" "` and is invisible until something compares the bytes.
#[test]
fn every_cel_escape_decodes_in_a_string() {
    let table: &[(&str, &str)] = &[
        (r"'\\'", "\\"),
        (r"'\?'", "?"),
        (r#"'\"'"#, "\""),
        (r"'\''", "'"),
        (r"'\`'", "`"),
        (r"'\a'", "\u{07}"),
        (r"'\b'", "\u{08}"),
        (r"'\f'", "\u{0C}"),
        (r"'\n'", "\n"),
        (r"'\r'", "\r"),
        (r"'\t'", "\t"),
        (r"'\v'", "\u{0B}"),
        (r"'\x41'", "A"),
        (r"'\X41'", "A"),
        (r"'\101'", "A"),
        (r"'✌'", "\u{270c}"),
        (r"'\U0001F600'", "\u{1F600}"),
        // …and the same escapes inside the OTHER delimiter, which is where `\'`/`\"` diverged.
        (r#""\'""#, "'"),
        (r#""\"""#, "\""),
        (r#"'''\'  \"  \X4c'''"#, "'  \"  L"),
    ];
    for (src, expected) in table {
        assert_eq!(string(src).as_deref(), Ok(*expected), "for {src}");
    }
}

/// The same table in a bytes literal, minus `\u`/`\U`, which are string-only: a bytes literal has
/// no code points to name.
#[test]
fn every_cel_escape_decodes_in_a_bytes_literal() {
    let table: &[(&str, &[u8])] = &[
        (r"b'\\'", b"\\"),
        (r"b'\?'", b"?"),
        (r#"b'\"'"#, b"\""),
        (r"b'\''", b"'"),
        (r"b'\`'", b"`"),
        (r"b'\a'", &[0x07]),
        (r"b'\b'", &[0x08]),
        (r"b'\f'", &[0x0C]),
        (r"b'\n'", b"\n"),
        (r"b'\r'", b"\r"),
        (r"b'\t'", b"\t"),
        (r"b'\v'", &[0x0B]),
        (r"b'\x41'", b"A"),
        (r"b'\X41'", b"A"),
        (r"b'\xFF'", &[0xFF]),
        (r"b'\377'", &[0xFF]),
        (r"b'\101'", b"A"),
        (r#"B"\'  \"  \X4c""#, b"'  \"  L"),
    ];
    for (src, expected) in table {
        assert_eq!(bytes(src).as_deref(), Ok(*expected), "for {src}");
    }
}

/// Widening the table must not turn the fallback into "pass the character through".
///
/// The corpus cannot see this: cel-spec has no case for an invalid escape, so a decoder that
/// silently yields `q` for `\q` scores exactly the same. What it loses is the ability to report a
/// typo in a policy, which is the whole reason a literal has a decoder rather than a memcpy.
#[test]
fn an_escape_the_dialect_does_not_have_is_still_an_error() {
    for src in [r"'\q'", r"b'\q'", r#""\e""#, r"'''\q'''"] {
        assert!(
            value(src).is_err(),
            "`{src}` decoded instead of reporting an unknown escape"
        );
    }
}

/// A raw literal never reaches the escape table — every backslash is content.
///
/// Including the backslash before a quote. The old decoder dropped that one, so
/// `r"\'"` came back as one character where cel-spec wants two.
#[test]
fn a_raw_string_keeps_its_backslashes() {
    assert_eq!(string(r"r'a\nb'").as_deref(), Ok(r"a\nb"));
    assert_eq!(string(r"r'''a\nb'''").as_deref(), Ok(r"a\nb"));
    assert_eq!(string(r"R'a\nb'").as_deref(), Ok(r"a\nb"));
    assert_eq!(string(r"r'a\nb'").map(|s| s.chars().count()), Ok(4));

    // The backslash-before-a-quote case, in every combination of delimiter and prefix.
    assert_eq!(string(r#"r' \" \` '"#).as_deref(), Ok(r#" \" \` "#));
    assert_eq!(string(r#"r" \' \` ""#).as_deref(), Ok(r" \' \` "));
    assert_eq!(string(r#"r''' \" \' '''"#).as_deref(), Ok(r#" \" \' "#));
    assert_eq!(bytes(r"br' \\ \a '"), Ok(br" \\ \a ".to_vec()));
}

/// A hex literal carries its SIGN in the token, so the sign has to come off before the radix test.
///
/// `"-0x55".strip_prefix("0x")` misses, and the fallback `"-0x55".parse::<i64>()` cannot read a
/// radix — so the negative spelling failed at parse while the decimal one worked.
#[test]
fn a_negative_hex_literal_parses() {
    assert_eq!(
        value("-0x55555555 == -1431655765").map(|v| format!("{v:?}")),
        Ok("Bool(true)".to_string())
    );
    // The boundary. Its magnitude is NOT representable as a positive `i64`, so a fix that parses
    // the digits and then negates overflows on exactly this value.
    assert_eq!(
        value("-0x8000000000000000 == -9223372036854775808").map(|v| format!("{v:?}")),
        Ok("Bool(true)".to_string())
    );
}

/// The regression guard on the arm being edited.
#[test]
fn a_hex_literal_still_parses() {
    assert_eq!(
        value("0x55555555 == 1431655765").map(|v| format!("{v:?}")),
        Ok("Bool(true)".to_string())
    );
    assert_eq!(
        value("0x7FFFFFFFFFFFFFFF == 9223372036854775807").map(|v| format!("{v:?}")),
        Ok("Bool(true)".to_string())
    );
}

/// An UPPERCASE hex prefix is not CEL, and that is the grammar's answer rather than ours.
///
/// Google's `CEL.g4` spells the token `NUM_INT : DIGIT+ | '0x' HEXDIGIT+` — lowercase only — so
/// `0XFF` dies in the LEXER, before any visitor sees it. Pinned rather than assumed: the sign fix
/// below reaches for `strip_prefix("0x")`, and the obvious "make it case-insensitive while I am
/// here" would add a literal spelling the reference implementation rejects. `src/parser/gen/` is
/// generated from Google's grammar and is not ours to edit.
#[test]
fn an_uppercase_hex_prefix_is_not_cel() {
    for src in ["0xFF == 255", "-0xFF == -255", "0xff == 255"] {
        assert_eq!(
            value(src).map(|v| format!("{v:?}")),
            Ok("Bool(true)".to_string()),
            "for {src}"
        );
    }
    for src in ["0XFF == 255", "-0XFF == -255"] {
        assert!(
            value(src).is_err(),
            "`{src}` parsed; the reference grammar has no uppercase hex prefix"
        );
    }
}
