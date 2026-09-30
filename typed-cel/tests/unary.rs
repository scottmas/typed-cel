//! Unary `!` and `-`: no panic, and one application per operator.
//!
//! The panic is why this file exists. `-(-9223372036854775808)` once aborted INSIDE the evaluator, and
//! the rule is that a failure the caller could have inspected must never become a fatal one. This
//! evaluator stands in for a decision a host may make on every tick, so a caller that could have
//! handled an error instead gets a dead thread — which is a bug in its own terms and not only
//! against cel-spec.
//!
//! Everything here compiles through the checker a policy compiles through and runs on the backend.
//! The checker refuses `-false` at BUILD (`-` has no bool overload), so that one is asserted as the
//! refusal: it never reaches an activation.

#[path = "support/mod.rs"]
mod support;

use typed_cel::CelValue as Value;
use typed_cel::{CelEnvironment, CelError, CelLimits};

/// Deep enough for the corpus's runs of 32 operators: the default nesting bound (32) is a
/// policy limit, not what this file tests.
fn eval(src: &str) -> Result<Value, String> {
    let env = CelEnvironment::with_limits(CelLimits {
        max_depth: 64,
        ..CelLimits::default()
    });
    support::run(&env, src, &[]).map_err(|e| format!("eval: {e}"))
}

fn evaluates_to(src: &str, expected: &str) {
    assert_eq!(
        eval(src).map(|v| format!("{v:?}")),
        Ok(expected.to_string()),
        "for {src}"
    );
}

/// Negating `i64::MIN` returns control, and the exact value.
///
/// `self.0.neg()` on an i64 panicked in a debug build and wrapped in release — the two worst options
/// in one line. Integers negate in `i128` and land in whichever representation holds the answer:
/// `-i64::MIN` is `2^63`, a `u64`. Only `-u64::MAX`-sized answers overflow, as an error.
#[test]
fn negating_the_minimum_integer_is_exact_not_a_panic() {
    evaluates_to("-(-9223372036854775808)", "UInt(9223372036854775808)");
    evaluates_to("-(-9223372036854775807)", "Int(9223372036854775807)");
    evaluates_to("-(9223372036854775807)", "Int(-9223372036854775807)");
    evaluates_to("-(9223372036854775808)", "Int(-9223372036854775808)");
    evaluates_to("-19", "Int(-19)");
}

/// `-` has no meaning on a bool, and answering `true` is worse than refusing.
///
/// `Bool` implemented `Negator`, so arithmetic negation silently dispatched to LOGICAL not — an
/// operator the language does not have, quietly answering as if it did.
#[test]
fn negating_a_bool_is_an_error() {
    for src in ["-false", "-true"] {
        assert!(
            matches!(support::refused_closed(src), CelError::Check { .. }),
            "`{src}` must be refused by the checker"
        );
    }

    // `!` still works, and is the operator that was being impersonated.
    evaluates_to("!false", "Bool(true)");
    evaluates_to("!true", "Bool(false)");
}

/// A RUN of unary operators applies once per operator, not once per run.
///
/// Both parities, deliberately. A fold that collapses a run to a single application gives the right
/// answer for every ODD count by luck, so a test that checks only `!!true` or only `----19` passes
/// against the bug.
#[test]
fn repeated_unary_operators_apply_once_each() {
    // Even counts — the ones a single-application fold gets WRONG.
    evaluates_to("!!true", "Bool(true)");
    evaluates_to("!!!!true", "Bool(true)");
    evaluates_to("--19", "Int(19)");
    evaluates_to("----19", "Int(19)");

    // Odd counts — the ones it gets right by luck, kept so the fix cannot overshoot.
    evaluates_to("!true", "Bool(false)");
    evaluates_to("!!!true", "Bool(false)");
    evaluates_to("-19", "Int(-19)");
    evaluates_to("---19", "Int(-19)");

    // The corpus's own counts, which is where this was found: 32 of each.
    evaluates_to(&format!("{}true", "!".repeat(32)), "Bool(true)");
    evaluates_to(&format!("{}19", "-".repeat(32)), "Int(19)");
    evaluates_to(&format!("{}true", "!".repeat(31)), "Bool(false)");
    evaluates_to(&format!("{}19", "-".repeat(31)), "Int(-19)");
}
