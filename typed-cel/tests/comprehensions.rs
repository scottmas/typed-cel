//! Absorption: a determined answer wins over an error, and ONLY a determined answer does.
//!
//! CEL's logical operators are absorbing rather than left-to-right short-circuiting. A `false`
//! operand makes `&&` false whatever the other operand did — including erroring — and a `true`
//! operand does the same for `||`. `all()` and `exists()` are comprehensions built on those
//! operators, so the rule reaches them: `[1, 2, 3].all(e, {1: true, 3: false}[e])` is `false`,
//! because the element at `e == 3` is false and that settles it, even though the element at
//! `e == 2` is a missing key. (The corpus case divides by zero; IEEE division has no error, so the
//! element's error here is a lookup.)
//!
//! The direction that must NOT move is the other one, and it is the reason this file is careful.
//! "An element errored, so keep going and answer false" is wrong in the UNSAFE direction: an
//! `all()` whose elements all error must be an `Err`, which a caller maps to a deny. Turning it
//! into `false` makes an unevaluatable assertion look like a cleanly failed one — and an
//! unevaluatable REVOCATION look like "do not revoke". Absorption needs a real `false`; it is not
//! error suppression.

#[path = "support/mod.rs"]
mod support;

use typed_cel::CelValue as Value;

/// The backend's answer for `src`, which must type-check: a program the checker refuses never
/// runs, so its answer would prove nothing.
fn eval(src: &str) -> Result<Value, String> {
    support::run_closed(src).map_err(|e| format!("eval: {e}"))
}

fn evaluates_to(src: &str, expected: &str) {
    assert_eq!(
        eval(src).map(|v| format!("{v:?}")),
        Ok(expected.to_string()),
        "for {src}"
    );
}

fn errors(src: &str) {
    if let Ok(v) = eval(src) {
        panic!("`{src}` answered {v:?}; nothing determined the result, so it must be an error");
    }
}

/// The corpus case's shape. `e == 2` errors; `e == 3` is false; false settles `all()`.
#[test]
fn all_absorbs_an_element_error_into_false() {
    evaluates_to("[1, 2, 3].all(e, {1: true, 3: false}[e])", "Bool(false)");
    // The absorbing element BEFORE the error, so the loop never reaches it — the same answer by a
    // different route, which is what proves the loop condition is not what is doing the work.
    evaluates_to("[3, 2, 1].all(e, {1: true, 3: false}[e])", "Bool(false)");
}

/// …and with nothing false to absorb it, the error stands.
///
/// The careless fix — swallow errors inside comprehensions — passes the test above and breaks this
/// one, which is the direction that matters.
#[test]
fn all_still_propagates_an_error_when_nothing_is_false() {
    // `e == 1` is true, `e == 2` errors. No false anywhere.
    errors("[1, 2].all(e, {1: true, 3: false}[e])");
    // The error FIRST, then a true. A later Ok must not clear a pending error just by being Ok.
    errors("[2, 1].all(e, {1: true, 3: false}[e])");
    // Every element errors.
    errors("[2].all(e, {1: true, 3: false}[e])");
}

/// The mirror, so the fix lives in the shared rule rather than in `all()`'s arm.
#[test]
fn exists_absorbs_an_element_error_into_true() {
    // `e == 2` errors, `e == 1` is true, and true settles `exists()`.
    evaluates_to("[2, 1].exists(e, {1: true, 3: false}[e])", "Bool(true)");
    evaluates_to("[1, 2].exists(e, {1: true, 3: false}[e])", "Bool(true)");
    // Nothing true to absorb it: `e == 3` is false, `e == 2` errors.
    errors("[2, 3].exists(e, {1: true, 3: false}[e])");
}

/// Absorption is a property of the OPERATOR, so the plain binary form has it too.
///
/// The corpus has no case for this, which is why it is asserted here: a fix made inside the
/// comprehension arm rather than in the operator leaves `a && b` wrong for a `false` beside an
/// error, and nothing would report it.
///
/// The erroring operand is a missing key into a map literal — a `bool` that fails, the only kind of
/// error a checked `&&`/`||` operand can be.
#[test]
fn the_plain_logical_operators_absorb_too() {
    evaluates_to("({'x': 1}['a'] == 1) && false", "Bool(false)");
    evaluates_to("false && ({'x': 1}['a'] == 1)", "Bool(false)");
    evaluates_to("({'x': 1}['a'] == 1) || true", "Bool(true)");
    evaluates_to("true || ({'x': 1}['a'] == 1)", "Bool(true)");

    // Nothing determines these, so the error decides.
    errors("({'x': 1}['a'] == 1) && true");
    errors("true && ({'x': 1}['a'] == 1)");
    errors("({'x': 1}['a'] == 1) || false");
}

/// The ordinary comprehensions are untouched: an error in a `map` or a `filter` still propagates.
///
/// There is no absorbing value for those — the accumulator is a list, not a truth value — so
/// carrying the error past the failing element must not turn it into a partial result.
#[test]
fn a_non_logical_comprehension_still_propagates() {
    errors("[1, 2, 3].map(e, {1: 6, 3: -6}[e])");
    errors("[1, 2, 3].filter(e, {1: true, 3: false}[e])");
    evaluates_to(
        "[1, 2, 3].map(e, e + 1)",
        "List([Float(2.0), Float(3.0), Float(4.0)])",
    );
    evaluates_to(
        "[1, 2, 3].filter(e, e > 1)",
        "List([Float(2.0), Float(3.0)])",
    );
}
