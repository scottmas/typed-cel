//! The ONE alias.
//!
//! `30s` becomes `duration('30s')`, and that is the entire deviation from spec CEL this dialect
//! allows an author to write. Every test here asserts the exact output string AND that the output
//! parses, because a rewrite that produces something the parser rejects is worse than no rewrite:
//! the author sees a diagnostic about source they did not write.

#[path = "support/mod.rs"]
mod support;

use typed_cel::{desugar, DesugarError};

/// The rewritten source, asserting it parses. Every positive test goes through here.
fn sugar(src: &str) -> String {
    let (out, _spans) = desugar(src).unwrap_or_else(|e| panic!("desugar({src:?}) failed: {e}"));
    typed_cel::fork::parse(&out)
        .unwrap_or_else(|e| panic!("desugar({src:?}) produced unparseable {out:?}: {e}"));
    out
}

fn err(src: &str) -> DesugarError {
    match desugar(src) {
        Ok((out, _)) => panic!("desugar({src:?}) should have failed; produced {out:?}"),
        Err(e) => e,
    }
}

#[test]
fn durations_expand() {
    assert_eq!(sugar("30s"), "duration('30s')");
    assert_eq!(sugar("500ms"), "duration('500ms')");
    assert_eq!(sugar("2m"), "duration('2m')");
    assert_eq!(sugar("1h"), "duration('1h')");
    // The alias hands the literal to the parser VERBATIM — it does not do the arithmetic itself.
    assert_eq!(sugar("1h30m"), "duration('1h30m')");
    assert_eq!(sugar("1.5s"), "duration('1.5s')");

    // In context.
    assert_eq!(
        sugar("uptime > 40s && metrics.cpu.max[\"40s\"] < 0.05"),
        "uptime > duration('40s') && metrics.cpu.max[\"40s\"] < 0.05"
    );
}

#[test]
fn days_are_rejected() {
    // `duration('1d')` is `Err(FunctionError)` at EVALUATION — expanding `1d` would produce source
    // that parses and fails at revocation time, forever.
    let e = err("1d");
    assert!(
        matches!(e, DesugarError::DayUnit { .. }),
        "expected DayUnit, got {e:?}"
    );
    let msg = e.to_string();
    assert!(msg.contains("day"), "{msg}");
    assert!(msg.contains("24h"), "message must show the fix: {msg}");

    // And the claim behind it, so nobody "fixes" the rejection by expanding it after all.
    assert!(support::run_closed("duration('1d')").is_err());

    err("uptime > 1d");
    err("2d12h");
}

#[test]
fn an_unknown_unit_is_rejected() {
    for src in ["30x", "30sec", "30S", "5MS", "1y"] {
        let e = err(src);
        assert!(
            matches!(e, DesugarError::UnknownUnit { .. }),
            "{src}: expected UnknownUnit, got {e:?}"
        );
    }
}

#[test]
fn strings_are_not_touched() {
    // THE test that fails when the scanner is a regex.
    assert_eq!(
        sugar("body.note == \"call me in 30s\""),
        "body.note == \"call me in 30s\""
    );
    assert_eq!(sugar("body.note == 'in 30s'"), "body.note == 'in 30s'");
    // An escaped quote must not end the string early.
    assert_eq!(
        sugar("body.note == \"a \\\" 30s\" && x"),
        "body.note == \"a \\\" 30s\" && x"
    );
    // A `d` inside a string is not a day unit either.
    assert_eq!(sugar("body.note == 'in 1d'"), "body.note == 'in 1d'");
    // Raw and triple-quoted forms.
    assert_eq!(sugar("r'30s' == x"), "r'30s' == x");
    assert_eq!(sugar("\"\"\"30s\"\"\" == x"), "\"\"\"30s\"\"\" == x");
}

#[test]
fn identifiers_are_not_touched() {
    assert_eq!(sugar("x30s == 1"), "x30s == 1");
    assert_eq!(sugar("a.b30s == 1"), "a.b30s == 1");
    assert_eq!(sugar("p30s == 1"), "p30s == 1");
    // A member named for a unit is still a member.
    assert_eq!(sugar("a.ms == 1"), "a.ms == 1");
    // A bare number is a number.
    assert_eq!(sugar("body.amount > 100"), "body.amount > 100");
    assert_eq!(sugar("0.05 < x"), "0.05 < x");
    // A float's fractional part must not be read as a fresh literal.
    assert_eq!(sugar("1.5 > 1.0"), "1.5 > 1.0");
}

#[test]
fn nothing_else_is_rewritten() {
    // Each of these passes through BYTE-IDENTICAL and is then rejected by the parser or the
    // checker. The desugarer is not where unsupported syntax is diagnosed, and it must not
    // silently repair any of it.
    for src in [
        "files['/a']?.closed",
        "(files['/a'].count ?? 0) > 0",
        "a % b",
        "a.?f",
        "[?x]",
        "x ? y : z",
    ] {
        let (out, _) = desugar(src).unwrap_or_else(|e| panic!("{src}: {e}"));
        assert_eq!(out, src, "{src} must pass through byte-identical");
    }
}

#[test]
fn spans_map_back_to_the_authored_columns() {
    // `30s` -> `duration('30s')` grows by 12 bytes, so every offset after it shifts.
    let authored = "uptime > 30s && x.y";
    let (out, spans) = desugar(authored).unwrap();
    assert_eq!(out, "uptime > duration('30s') && x.y");

    // `x` in the desugared form...
    let dx = out.find("x.y").unwrap();
    // ...maps back to `x` in the authored form.
    assert_eq!(spans.to_authored(dx), authored.find("x.y").unwrap());

    // Offsets BEFORE the rewrite are unchanged.
    assert_eq!(spans.to_authored(0), 0);
    assert_eq!(
        spans.to_authored(out.find("uptime").unwrap()),
        authored.find("uptime").unwrap()
    );

    // Two rewrites compose.
    let authored = "a > 5s && b > 10ms && c";
    let (out, spans) = desugar(authored).unwrap();
    assert_eq!(out, "a > duration('5s') && b > duration('10ms') && c");
    assert_eq!(
        spans.to_authored(out.rfind('c').unwrap()),
        authored.rfind('c').unwrap()
    );
}

#[test]
fn desugaring_is_idempotent_on_plain_cel() {
    for src in [
        "duration('30s')",
        "files[\"/a\"].closed.elapsed > duration('5s')",
        "body.user_id == session.user_id",
    ] {
        let (once, _) = desugar(src).unwrap();
        assert_eq!(once, src, "{src} must be returned byte-identical");
        let (twice, _) = desugar(&once).unwrap();
        assert_eq!(twice, once);
    }
}
