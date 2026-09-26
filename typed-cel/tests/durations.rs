//! A duration's RANGE, which is CEL's and not `chrono`'s.
//!
//! The dialect's only temporal type, so this is the file with the most leverage per line in the
//! crate: every system expression is a span comparison (`uptime > 40s`,
//! `files["/a"].closed.elapsed > 5s`), and a duration that silently saturates or wraps is a
//! revocation condition that fires, or fails to fire, for a reason nobody can see in the policy.
//!
//! Two bounds are in play and they are NOT the same number, which is the whole difficulty:
//!
//! | bound | value | who enforces it |
//! |---|---|---|
//! | `chrono::TimeDelta` as nanoseconds | ±9223372036s, ~292 years | `Duration::nanoseconds`, by saturating |
//! | CEL | ±315576000000s, ~10000 years | this crate, or nobody |
//!
//! CEL's range is 34x WIDER than what fits in i64 nanoseconds, so a value can be perfectly legal in
//! the language and impossible to build through `Duration::nanoseconds` — which is how
//! `duration('320000000000s')` used to arrive as a plausible-looking 292-year span instead of an
//! error. A `checked_add` against `TimeDelta`'s range is not a check against the language's.

use typed_cel::fork::objects::Value;
use typed_cel::fork::{Context, Program};

fn eval(src: &str) -> Result<Value, String> {
    Program::compile(src)
        .map_err(|e| format!("parse: {e}"))?
        .execute(&Context::default())
        .map_err(|e| format!("eval: {e}"))
}

fn refused(src: &str) -> String {
    match eval(src) {
        Err(e) => e,
        Ok(v) => panic!("`{src}` produced {v:?}; it is outside CEL's duration range"),
    }
}

/// A literal past the range is an error, not a saturated value.
///
/// The old decoder multiplied out to `f64` nanoseconds and cast to `i64`, and a float-to-int cast
/// in Rust SATURATES — so the value did not overflow, it quietly became `i64::MAX` nanoseconds and
/// every comparison downstream answered against a number the policy never wrote.
#[test]
fn a_duration_past_the_cel_range_is_an_error() {
    for src in [
        "duration('320000000000s')",
        "duration('-320000000000s')",
        // 9e7 hours is 3.24e11 seconds — just past the bound, and expressed in a unit whose
        // multiplier is where a per-component check would have to catch it.
        "duration('90000000h')",
    ] {
        let err = refused(src);
        assert!(
            err.contains("TooLarge"),
            "`{src}` is refused but does not say the value is out of range: {err}"
        );
    }
}

/// …and so is arithmetic that leaves the range, which fixing the parser alone does NOT close.
///
/// Both operands are in range, so nothing rejects them on the way in, and their sum is well inside
/// `chrono::TimeDelta` — so `checked_add` returns `Some` and the wrong answer survives. This is the
/// case that proves the bound has to be the LANGUAGE's and checked at both sites.
#[test]
fn duration_arithmetic_that_leaves_the_range_is_an_error() {
    // Each operand on its own is legal: 200000000000s is inside ±315576000000s.
    assert!(eval("duration('200000000000s')").is_ok());
    assert!(eval("duration('-200000000000s')").is_ok());

    refused("duration('200000000000s') + duration('200000000000s')");
    refused("duration('-200000000000s') + duration('-200000000000s')");
    refused("duration('200000000000s') - duration('-200000000000s')");
    refused("duration('-200000000000s') - duration('200000000000s')");
}

/// The boundary itself is legal, and one second past it is not.
///
/// An off-by-one here is a policy that cannot express its own maximum. The sub-second case is the
/// one a truncating check gets wrong: `num_seconds()` rounds toward zero, so the bound plus one
/// nanosecond reports as exactly the bound and passes.
#[test]
fn the_boundary_duration_is_legal() {
    assert!(eval("duration('315576000000s')").is_ok());
    refused("duration('315576000001s')");
    refused("duration('315576000000s') + duration('1ns')");
    assert!(eval("duration('-315576000000s')").is_ok());
    refused("duration('-315576000000s') - duration('1ns')");
}

/// The regression guard: this change touches the code path EVERY system expression uses.
///
/// A range check that is wrong in the other direction breaks every policy at once and the corpus
/// would not notice, because cel-spec has no case for `30s`. The `30s` ALIAS itself is a desugar
/// step above this layer and is covered by `tests/desugar.rs`; what is asserted here is the call it
/// expands to.
#[test]
fn an_ordinary_policy_duration_is_untouched() {
    let table: &[(&str, &str)] = &[
        (
            "duration('30s') == duration('30s')",
            "the shape every system expression has",
        ),
        ("duration('40s') > duration('30s')", "ordering"),
        ("duration('1h30m') == duration('90m')", "compound units"),
        ("duration('500ms') < duration('1s')", "sub-second units"),
        ("duration('1.5h') == duration('90m')", "fractional units"),
        ("duration('5s') + duration('3s') == duration('8s')", "add"),
        ("duration('5s') - duration('3s') == duration('2s')", "sub"),
        ("duration('-30s') < duration('0s')", "negative"),
        ("duration('1ns') > duration('0s')", "the smallest unit"),
        (
            "duration('1.5ns') == duration('1ns')",
            "sub-nanosecond truncates",
        ),
    ];
    for (src, what) in table {
        assert_eq!(
            eval(src).map(|v| format!("{v:?}")),
            Ok("Bool(true)".to_string()),
            "{what}: {src}"
        );
    }
    assert_eq!(
        eval("duration('90s').getSeconds()").map(|v| format!("{v:?}")),
        Ok("Float(90.0)".to_string())
    );
}
