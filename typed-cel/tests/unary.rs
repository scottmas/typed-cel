//! Unary `!` and `-`: no panic, and one application per operator.
//!
//! The panic is why this file exists. `-(-9223372036854775808)` once aborted INSIDE the evaluator, and
//! the rule is that a failure the caller could have inspected must never become a fatal one. This
//! evaluator stands in for a decision a host may make on every tick, so a caller that could have
//! handled an error instead gets a dead thread — which is a bug in its own terms and not only
//! against cel-spec.
//!
//! Everything here drives the evaluator directly rather than `CelEnvironment::compile`, because the
//! checker refuses two of these at BUILD: `-` has no bool overload, so `-false` never reaches an
//! activation through the dialect's front door. What is asserted is that the layer BELOW the
//! checker is still sound, since it is the layer the corpus runs against.

use typed_cel::fork::objects::Value;
use typed_cel::fork::{Context, Program};

fn eval(src: &str) -> Result<Value, String> {
    Program::compile(src)
        .map_err(|e| format!("parse: {e}"))?
        .execute(&Context::default())
        .map_err(|e| format!("eval: {e}"))
}

fn evaluates_to(src: &str, expected: &str) {
    assert_eq!(
        eval(src).map(|v| format!("{v:?}")),
        Ok(expected.to_string()),
        "for {src}"
    );
}

/// Negating what was `i64::MIN` returns control, and a value.
///
/// `self.0.neg()` on an i64 panicked in a debug build and wrapped in release — the two worst options
/// in one line. With one number kind (`removed: integer values`) there is no integer to overflow:
/// the literal is the nearest double and negating it is exact. What is asserted is still that
/// control comes BACK, now with the double's answer.
#[test]
fn negating_the_minimum_integer_is_a_double_not_a_panic() {
    evaluates_to("-(-9223372036854775808)", "Float(9.223372036854776e18)");
    evaluates_to("-(-9223372036854775807)", "Float(9.223372036854776e18)");
    evaluates_to("-(9223372036854775807)", "Float(-9.223372036854776e18)");
    evaluates_to("-19", "Float(-19.0)");
}

/// `-` has no meaning on a bool, and answering `true` is worse than refusing.
///
/// `Bool` implemented `Negator`, so arithmetic negation silently dispatched to LOGICAL not — an
/// operator the language does not have, quietly answering as if it did.
#[test]
fn negating_a_bool_is_an_error() {
    assert!(eval("-false").is_err(), "`-false` must not evaluate");
    assert!(eval("-true").is_err(), "`-true` must not evaluate");

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
    evaluates_to("--19", "Float(19.0)");
    evaluates_to("----19", "Float(19.0)");

    // Odd counts — the ones it gets right by luck, kept so the fix cannot overshoot.
    evaluates_to("!true", "Bool(false)");
    evaluates_to("!!!true", "Bool(false)");
    evaluates_to("-19", "Float(-19.0)");
    evaluates_to("---19", "Float(-19.0)");

    // The corpus's own counts, which is where this was found: 32 of each.
    evaluates_to(&format!("{}true", "!".repeat(32)), "Bool(true)");
    evaluates_to(&format!("{}19", "-".repeat(32)), "Float(19.0)");
    evaluates_to(&format!("{}true", "!".repeat(31)), "Bool(false)");
    evaluates_to(&format!("{}19", "-".repeat(31)), "Float(-19.0)");
}
