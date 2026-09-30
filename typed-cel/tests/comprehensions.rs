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
//! That lookup is a read the checker refuses (proven presence: `{1: true, 3: false}` is known not to
//! hold `2`), so this file compiles through the unchecked-presence door. What it pins is the
//! BACKEND's answer when a read fails anyway — every other check still applies.
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
    support::run_closed_unchecked_presence(src).map_err(|e| format!("eval: {e}"))
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
    evaluates_to("[1, 2, 3].map(e, e + 1)", "List([Int(2), Int(3), Int(4)])");
    evaluates_to("[1, 2, 3].filter(e, e > 1)", "List([Int(2), Int(3)])");
}

/// Every `exists` / `all` / `exists_one` lowers to a predicate loop (the predicate a branch, no
/// accumulator), and every `map` / `filter` to a loop appending in place; the expansion's literal
/// loop is the reference. Over every list of up to four
/// elements drawn from {1, 2, 3, 4}, with predicates that answer true, false or an error per
/// element — so an erroring element sits before, after and between deciding ones — both answer
/// the same, value or error text, over a bound list and over a literal one.
#[test]
fn a_predicate_loop_answers_as_the_expansion_does() {
    use typed_cel::{CelEnvironment, CelTy, FastProgram};
    // 1 → true, 2 → false, 3 → an error, 4 → as noted.
    const PREDICATES: &[&str] = &[
        "{1: true, 2: false}[e]",
        "{1: true, 2: false}[e] || e == 4",
        "{1: true, 2: false, 4: false}[e] && e < 4",
        "e != 3 && {1: true, 2: false, 4: true}[e]",
        // A nested loop, its own `@result` shadowing the outer one's.
        "[e].all(y, {1: true, 2: false, 4: true}[y])",
        "{1: true, 2: false}[e] || [4, 5].exists(y, y == e)",
    ];
    const MACROS: &[&str] = &["exists", "all", "exists_one", "filter", "map3"];
    let mut lists: Vec<Vec<u8>> = vec![vec![]];
    for len in 1..=4 {
        let prev: Vec<Vec<u8>> = lists
            .iter()
            .filter(|l| l.len() == len - 1)
            .cloned()
            .collect();
        for l in prev {
            for x in 1..=4u8 {
                let mut l = l.clone();
                l.push(x);
                lists.push(l);
            }
        }
    }
    let mut env = CelEnvironment::new();
    env.declare("xs", CelTy::list(CelTy::Num));
    let answer = |p: &FastProgram, xs: &[u8]| {
        let mut act = env.runtime().activation();
        act.bind_fact(
            "xs",
            Value::list(xs.iter().map(|x| Value::Num(f64::from(*x)))),
        );
        format!("{:?}", p.eval_result(&act))
    };
    let (mut compared, mut mismatches) = (0, Vec::new());
    // A two-argument `map` whose element errors (3, 4) or builds a nested list.
    for src in [
        "xs.map(e, {1: 10.0, 2: 20.0}[e])",
        "xs.map(e, [e, e + 1.0])",
        "size(xs.map(e, xs.filter(y, y < e))) >= 0.0",
    ] {
        let program = typed_cel::fork::compile_any_unchecked_presence(&env, src).expect("compiles");
        let recognized = FastProgram::new(&program).expect("lowers");
        let literal =
            typed_cel::with_literal_comprehensions(|| FastProgram::new(&program)).expect("lowers");
        assert_ne!(recognized.op_names(), literal.op_names(), "`{src}`");
        for xs in &lists {
            let (got, want) = (answer(&recognized, xs), answer(&literal, xs));
            compared += 1;
            if got != want {
                mismatches.push(format!(
                    "`{src}` over {xs:?}: {got} vs the expansion's {want}"
                ));
            }
        }
    }
    for m in MACROS {
        for pred in PREDICATES {
            // `map3` is the three-argument `map`: the predicate filters, the element doubles.
            let call = |range: &str| match *m {
                "map3" => format!("{range}.map(e, {pred}, e * 2.0)"),
                m => format!("{range}.{m}(e, {pred})"),
            };
            let src = call("xs");
            let program =
                typed_cel::fork::compile_any_unchecked_presence(&env, &src).expect("compiles");
            let recognized = FastProgram::new(&program).expect("lowers");
            let literal = typed_cel::with_literal_comprehensions(|| FastProgram::new(&program))
                .expect("lowers");
            assert_ne!(
                recognized.op_names(),
                literal.op_names(),
                "`{src}` was not recognized as a predicate loop"
            );
            for xs in &lists {
                let (got, want) = (answer(&recognized, xs), answer(&literal, xs));
                compared += 1;
                if got != want {
                    mismatches.push(format!(
                        "`{src}` over {xs:?}: {got} vs the expansion's {want}"
                    ));
                }
                if xs.len() > 3 {
                    continue;
                }
                let lit = call(&format!(
                    "[{}]",
                    xs.iter().map(u8::to_string).collect::<Vec<_>>().join(", ")
                ));
                let program =
                    typed_cel::fork::compile_any_unchecked_presence(&env, &lit).expect("compiles");
                let got = answer(&FastProgram::new(&program).expect("lowers"), &[]);
                let want = answer(
                    &typed_cel::with_literal_comprehensions(|| FastProgram::new(&program))
                        .expect("lowers"),
                    &[],
                );
                compared += 1;
                if got != want {
                    mismatches.push(format!("`{lit}`: {got} vs the expansion's {want}"));
                }
            }
        }
    }
    assert!(
        mismatches.is_empty(),
        "{} of {compared} answers differ:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// Every list of up to four elements drawn from 1-4, the empty one first.
fn small_lists() -> Vec<Vec<u8>> {
    let mut lists: Vec<Vec<u8>> = vec![vec![]];
    for len in 1..=4 {
        let prev: Vec<Vec<u8>> = lists
            .iter()
            .filter(|l| l.len() == len - 1)
            .cloned()
            .collect();
        for l in prev {
            for x in 1..=4u8 {
                let mut l = l.clone();
                l.push(x);
                lists.push(l);
            }
        }
    }
    lists
}

/// A loop whose predicate tests the element against a FIELD of a bound record — the field read on
/// the first element, then reused — answers as the literal expansion does: the same value, and
/// the same error where the field is missing, unbound, or unordered (NaN), for either operand
/// order and either string-test receiver.
#[test]
fn a_field_test_in_a_loop_answers_as_the_expansion_does() {
    use typed_cel::{CelEnvironment, CelKey, CelTy, FastProgram, Record};
    const NUM_PREDICATES: &[&str] = &[
        "e == r.n", "r.n == e", "e != r.n", "e < r.n", "r.n < e", "e >= r.n",
    ];
    const STR_PREDICATES: &[&str] = &[
        "r.s == e",
        "r.s.startsWith(e)",
        "e.startsWith(r.s)",
        "r.s.contains(e)",
        "e.endsWith(r.s)",
        // A concatenation tested unbuilt (`StrOp2`, `CondStrOp2F`), and a regex, literal or not.
        "r.s == e || r.s.startsWith(e + \"/\")",
        "r.s.startsWith(e + \"/\")",
        "r.s.endsWith(\"/\" + e)",
        "(e + \"/\").startsWith(r.s)",
        "e.matches(\"^2$\")",
        "e.matches(r.s)",
    ];
    const MACROS: &[&str] = &["exists", "all", "exists_one", "filter", "map3"];
    // The predicates whose loop scans: the test is the body's first op, on the element.
    const SCANNED: &[&str] = &[
        "e == r.n",
        "r.n == e",
        "e != r.n",
        "e < r.n",
        "r.n < e",
        "e >= r.n",
        "r.s == e",
        "r.s.startsWith(e)",
        "e.startsWith(r.s)",
        "r.s.contains(e)",
        "e.endsWith(r.s)",
        "r.s == e || r.s.startsWith(e + \"/\")",
        "r.s.startsWith(e + \"/\")",
        "e.matches(\"^2$\")",
        // Not `r.s.endsWith("/" + e)`: a constant BEFORE the element is not a `CondStrOp2F`, and
        // its `Const; ReadCached; StrOp2; Cond` is not a region.
    ];
    let mut env = CelEnvironment::new();
    env.declare("xs", CelTy::list(CelTy::Num));
    env.declare("ss", CelTy::list(CelTy::Str));
    env.declare(
        "r",
        CelTy::from(Record::new("r", [("n", CelTy::Num), ("s", CelTy::Str)])),
    );
    let record = |n: f64, s: &str| {
        Some(Value::record([
            (CelKey::new("n"), Value::Num(n)),
            (CelKey::new("s"), Value::Str(s.into())),
        ]))
    };
    // A present record, an unordered one, one missing both fields, and none bound at all.
    let bindings = [
        record(2.0, "2"),
        record(f64::NAN, ""),
        Some(Value::record([])),
        None,
        record(3.0, "2/x"),
        // Not a valid regex: `e.matches(r.s)` fails where it runs.
        record(1.0, "("),
    ];
    let lists = small_lists();
    let answer = |p: &FastProgram, xs: &[u8], r: &Option<Value>| {
        let mut act = env.runtime().activation();
        act.bind_fact(
            "xs",
            Value::list(xs.iter().map(|x| Value::Num(f64::from(*x)))),
        );
        act.bind_fact(
            "ss",
            Value::list(xs.iter().map(|x| Value::Str(x.to_string().into()))),
        );
        if let Some(r) = r {
            act.bind_fact("r", r.clone());
        }
        format!("{:?}", p.eval_result(&act))
    };
    let (mut compared, mut mismatches) = (0, Vec::new());
    let cases = NUM_PREDICATES
        .iter()
        .map(|p| ("xs", *p, "e * 2.0"))
        .chain(STR_PREDICATES.iter().map(|p| ("ss", *p, "e")));
    for (range, pred, mapped) in cases {
        for m in MACROS {
            let src = match *m {
                "map3" => format!("{range}.map(e, {pred}, {mapped})"),
                m => format!("{range}.{m}(e, {pred})"),
            };
            let program =
                typed_cel::fork::compile_any_unchecked_presence(&env, &src).expect("compiles");
            let recognized = FastProgram::new(&program).expect("lowers");
            let literal = typed_cel::with_literal_comprehensions(|| FastProgram::new(&program))
                .expect("lowers");
            assert_ne!(
                recognized.op_names(),
                literal.op_names(),
                "`{src}` was not recognized as a loop"
            );
            // A predicate loop scans; a `filter` or `map` never does (its kept elements would each
            // pay a failed test before the body runs them).
            if SCANNED.contains(&pred) && ["exists", "all", "exists_one"].contains(m) {
                assert!(
                    recognized.scanned_loops() > 0,
                    "`{src}`: its non-deciding elements are not scanned past:\n{}",
                    recognized.listing()
                );
            }
            for xs in &lists {
                for r in &bindings {
                    let (got, want) = (answer(&recognized, xs, r), answer(&literal, xs, r));
                    compared += 1;
                    if got != want {
                        mismatches.push(format!(
                            "`{src}` over {xs:?}, r = {r:?}: {got} vs the expansion's {want}"
                        ));
                    }
                }
            }
        }
    }
    assert!(compared >= 17 * 5 * 6 * 300, "compared only {compared}");
    assert!(
        mismatches.is_empty(),
        "{} of {compared} answers differ:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// A loop that scans — its non-deciding elements passed over inside its `IterNext`, every other
/// element handed to the loop's own ops — answers exactly as the same loop unscanned: the same
/// value and the same error, over NaN, empty and equal-length strings, missing and unbound fields,
/// map keys and a built list.
#[test]
fn a_scanned_loop_answers_as_its_unfused_twin() {
    use typed_cel::{CelEnvironment, CelKey, CelMap, CelMapKey, CelTy, FastProgram, Record};
    const SOURCES: &[&str] = &[
        "xs.exists(e, e == r.n)",
        "xs.all(e, e < r.n)",
        "xs.exists_one(e, e >= r.n)",
        "xs.exists(e, e < r.n)",
        "ss.exists(e, e == r.s)",
        "ss.all(e, e.startsWith(r.s))",
        "ss.exists(e, r.s.contains(e))",
        "m.exists(k, k == r.s)",
        "xs.map(x, x * 2.0).exists(y, y > r.n)",
        "xs.exists(e, e == 2.0)",
        "xs.all(e, e < 3.0)",
        "xs.exists(e, e > r.n && e < 3.0)",
        "xs.all(e, e > r.n || e == 2.0)",
        "ss.exists(e, r.s == e || r.s.startsWith(e + \"/\"))",
        "ss.all(e, r.s != e && !r.s.startsWith(e))",
        "xs.exists(e, (e > r.n || e == 1.0) && e != 3.0)",
        "ss.all(e, !r.s.startsWith(e + \"/\"))",
        // Past `split_chain`'s size: the chain's error register cleared by the fetch, raised after
        // the last leaf (`RaisePending`), then back to the head (`Jump`) — both in the region.
        "xs.exists(e, e > r.n || e < 0.5 || e > r.n || e < 1.5 || e > r.n || e < 2.5 || e > r.n \
         || e < 3.5 || e > r.n || e < 4.5 || e > r.n || e < 5.5 || e > r.n || e < 6.5)",
        // A record's member, selected from the element.
        "items.exists(i, i.id == r.s && i.qty > r.n)",
        "items.all(i, i.qty > r.n)",
        "items.exists(i, i.tags.exists(t, t == r.s))",
        // The map's value at the loop's key, from the iteration.
        "m.all(k, m[k] > r.n)",
        "m.exists(k, m[k] == r.n)",
        // A literal pattern (`CondMatches`), a pattern that does not compile (every element handed
        // to the body, which raises), and a known set (`CondMatch`, on a copy of the element).
        "ss.exists(e, e.matches(\"^2$\"))",
        "ss.all(e, !e.matches(\"[0-9]\"))",
        "ss.exists(e, e.matches(\"(\"))",
        "ss.exists(e, e == \"1\" || e == \"2\" || e == \"3\" || e == \"4\")",
        "ss.all(e, e.startsWith(\"a\") || e.startsWith(\"b\") || e.startsWith(\"c\") || e == \"x\")",
        // The same tests through the region walker: over map keys, and inside a chain.
        "m.exists(k, k.matches(\"^2$\"))",
        "m.all(k, k == \"1\" || k == \"2\" || k == \"3\" || k == \"4\")",
        "ss.exists(e, e.matches(\"^2$\") || e == r.s)",
        "ss.exists(e, (e == \"1\" || e == \"2\" || e == \"3\" || e == \"4\") && e != r.s)",
        // A substring against a field, the element the haystack (the `r.s = ""` binding: the
        // empty needle is in every string).
        "ss.exists(e, e.contains(r.s))",
        "ss.all(e, !e.contains(r.s))",
    ];
    let mut env = CelEnvironment::new();
    env.declare("xs", CelTy::list(CelTy::Num));
    env.declare("ss", CelTy::list(CelTy::Str));
    env.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    env.declare(
        "r",
        CelTy::from(Record::new("r", [("n", CelTy::Num), ("s", CelTy::Str)])),
    );
    env.declare(
        "items",
        CelTy::list(CelTy::from(Record::new(
            "item",
            [
                ("id", CelTy::Str),
                ("qty", CelTy::Num),
                ("tags", CelTy::list(CelTy::Str)),
            ],
        ))),
    );
    let item = |members: &[(&str, Value)]| {
        Value::record(members.iter().map(|(k, v)| (CelKey::new(k), v.clone())))
    };
    let tags = |t: &[&str]| Value::list(t.iter().map(|s| Value::Str((*s).into())));
    let (num, st) = (Value::Num, |s: &str| Value::Str(s.into()));
    // Records of one shape; one missing a member (its select raises); one with an extra member
    // that sorts first (every member at another index: the position hint misses); a NaN; a
    // repeated id.
    let item_lists = [
        Value::list([]),
        Value::list([item(&[
            ("id", st("2")),
            ("qty", num(1.0)),
            ("tags", tags(&["2", "x"])),
        ])]),
        Value::list([
            item(&[("id", st("1")), ("qty", num(3.0)), ("tags", tags(&[]))]),
            item(&[("id", st("2")), ("qty", num(2.0)), ("tags", tags(&["2"]))]),
            item(&[
                ("id", st("3")),
                ("qty", num(1.0)),
                ("tags", tags(&["a", "b"])),
            ]),
        ]),
        Value::list([
            item(&[("id", st("2")), ("qty", num(f64::NAN)), ("tags", tags(&[]))]),
            item(&[("id", st("2")), ("qty", num(2.0)), ("tags", tags(&["2/x"]))]),
        ]),
        Value::list([
            item(&[("id", st("1")), ("qty", num(3.0)), ("tags", tags(&[]))]),
            item(&[("id", st("1")), ("tags", tags(&["2"]))]),
            item(&[("id", st("3")), ("qty", num(0.5)), ("tags", tags(&[]))]),
        ]),
        Value::list([
            item(&[("id", st("0")), ("qty", num(5.0)), ("tags", tags(&[]))]),
            item(&[
                ("aaa", num(0.0)),
                ("id", st("2")),
                ("qty", num(4.0)),
                ("tags", tags(&["2"])),
            ]),
            item(&[("id", st("9")), ("qty", num(0.0)), ("tags", tags(&["9"]))]),
        ]),
    ];
    let record = |n: f64, s: &str| {
        Some(Value::record([
            (CelKey::new("n"), Value::Num(n)),
            (CelKey::new("s"), Value::Str(s.into())),
        ]))
    };
    let bindings = [
        record(2.0, "2"),
        record(f64::NAN, ""),
        Some(Value::record([])),
        None,
        record(3.0, "2/x"),
        record(1.0, "("),
    ];
    let smap = |kv: &[(&str, f64)]| {
        Value::Map(CelMap::new(
            kv.iter()
                .map(|(k, v)| (CelMapKey::Str(CelKey::new(k)), Value::Num(*v))),
        ))
    };
    let maps = [
        smap(&[]),
        smap(&[("2", 1.0)]),
        smap(&[("1", 1.0), ("2", 2.0), ("3", 3.0)]),
    ];
    // Each case: the numbers `xs`, and the strings `ss`.
    let mut data: Vec<(Vec<f64>, Vec<String>)> = small_lists()
        .into_iter()
        .map(|l| {
            (
                l.iter().map(|x| f64::from(*x)).collect(),
                l.iter().map(|x| x.to_string()).collect(),
            )
        })
        .collect();
    data.push((vec![f64::NAN], vec!["".into()]));
    data.push((vec![1.0, f64::NAN, 3.0], vec!["2".into(), "22".into()]));
    data.push((
        vec![3.0, 3.0, 3.0],
        vec!["2/x".into(), "é".into(), "2".into()],
    ));
    let answer = |p: &FastProgram,
                  xs: &[f64],
                  ss: &[String],
                  m: &Value,
                  items: &Value,
                  r: &Option<Value>| {
        let mut act = env.runtime().activation();
        act.bind_fact("items", items.clone());
        act.bind_fact("xs", Value::list(xs.iter().map(|x| Value::Num(*x))));
        act.bind_fact(
            "ss",
            Value::list(ss.iter().map(|s| Value::Str(s.as_str().into()))),
        );
        act.bind_fact("m", m.clone());
        if let Some(r) = r {
            act.bind_fact("r", r.clone());
        }
        format!("{:?}", p.eval_result(&act))
    };
    // A build loop never scans: each kept element would pay a failed test before the body ran it.
    for src in ["xs.filter(e, e > r.n)", "xs.map(e, e > r.n, e * 2.0)"] {
        let program = typed_cel::fork::compile_any_unchecked_presence(&env, src).expect("compiles");
        let p = FastProgram::new(&program).expect("lowers");
        assert_eq!(p.scanned_loops(), 0, "`{src}` scans:\n{}", p.listing());
    }
    let (mut compared, mut mismatches) = (0, Vec::new());
    for src in SOURCES {
        let program = typed_cel::fork::compile_any_unchecked_presence(&env, src).expect("compiles");
        let fused = FastProgram::new(&program).expect("lowers");
        let unfused = typed_cel::with_unfused_loops(|| FastProgram::new(&program)).expect("lowers");
        assert!(
            fused.scanned_loops() > 0,
            "`{src}` does not scan:\n{}",
            fused.listing()
        );
        assert!(
            unfused.scanned_loops() == 0,
            "`{src}` scans with loops unfused:\n{}",
            unfused.listing()
        );
        for (d, (xs, ss)) in data.iter().enumerate() {
            // Each list of records meets every map and binding, across the data cases.
            let items = &item_lists[d % item_lists.len()];
            for m in &maps {
                for r in &bindings {
                    let (got, want) = (
                        answer(&fused, xs, ss, m, items, r),
                        answer(&unfused, xs, ss, m, items, r),
                    );
                    compared += 1;
                    if got != want {
                        mismatches.push(format!(
                            "`{src}` over xs={xs:?} ss={ss:?} m={m:?} items={items:?} r={r:?}: \
                             {got} vs unfused {want}"
                        ));
                    }
                }
            }
        }
    }
    assert!(
        compared >= SOURCES.len() * 340 * 3 * 6,
        "compared only {compared}"
    );
    assert!(
        mismatches.is_empty(),
        "{} of {compared} answers differ:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// A loop over a bound MAP's keys — testing the key, or the map's value at the key — answers as
/// the literal expansion does, including where an inner loop rebinds the key's name.
#[test]
fn a_map_loop_answers_as_the_expansion_does() {
    use typed_cel::{CelEnvironment, CelKey, CelMap, CelMapKey, CelTy, FastProgram, Record};
    const PREDICATES: &[&str] = &[
        "k == r.s",
        "m[k] > 1.0",
        "m[k] > r.n",
        "m[k] == 2.0 || k == \"b\"",
        // An inner loop rebinds `k` (a number, over `n`); the outer `m[k]` after it is the outer
        // key's. (A computed key must come from a loop over the same collection: the checker
        // refuses `["a"].exists(k, m[k] > 0.0)`.)
        "n.exists(k, n[k] > 1.0) || m[k] > 1.0",
        "m[k] > 0.0 && m.exists(j, m[j] < m[k])",
    ];
    const MACROS: &[&str] = &["exists", "all", "exists_one", "filter", "map3"];
    let mut env = CelEnvironment::new();
    env.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    env.declare("n", CelTy::map(CelTy::Num, CelTy::Num));
    env.declare(
        "r",
        CelTy::from(Record::new("r", [("n", CelTy::Num), ("s", CelTy::Str)])),
    );
    let smap = |kv: &[(&str, f64)]| {
        Value::Map(CelMap::new(
            kv.iter()
                .map(|(k, v)| (CelMapKey::Str(CelKey::new(k)), Value::Num(*v))),
        ))
    };
    let maps = [
        smap(&[]),
        smap(&[("a", 1.0)]),
        smap(&[("a", 1.0), ("b", 2.0)]),
        smap(&[("a", 2.0), ("b", f64::NAN)]),
        smap(&[("b", 3.0), ("z", 0.5)]),
    ];
    let nmap = Value::Map(CelMap::new([
        (CelMapKey::Num(1), Value::Num(1.0)),
        (CelMapKey::Num(2), Value::Num(2.0)),
    ]));
    let record = |n: f64, s: &str| {
        Some(Value::record([
            (CelKey::new("n"), Value::Num(n)),
            (CelKey::new("s"), Value::Str(s.into())),
        ]))
    };
    let bindings = [
        record(1.5, "b"),
        record(f64::NAN, ""),
        Some(Value::record([])),
        None,
    ];
    let answer = |p: &FastProgram, m: &Value, r: &Option<Value>| {
        let mut act = env.runtime().activation();
        act.bind_fact("m", m.clone());
        act.bind_fact("n", nmap.clone());
        if let Some(r) = r {
            act.bind_fact("r", r.clone());
        }
        format!("{:?}", p.eval_result(&act))
    };
    let (mut compared, mut mismatches) = (0, Vec::new());
    let sources = MACROS
        .iter()
        .flat_map(|mac| {
            PREDICATES.iter().map(move |pred| match *mac {
                "map3" => format!("m.map(k, {pred}, k)"),
                mac => format!("m.{mac}(k, {pred})"),
            })
        })
        .chain(MACROS.iter().map(|mac| match *mac {
            "map3" => "n.map(k, n[k] < r.n, k)".to_string(),
            mac => format!("n.{mac}(k, n[k] < r.n)"),
        }));
    for src in sources {
        let program =
            typed_cel::fork::compile_any_unchecked_presence(&env, &src).expect("compiles");
        let recognized = FastProgram::new(&program).expect("lowers");
        let literal =
            typed_cel::with_literal_comprehensions(|| FastProgram::new(&program)).expect("lowers");
        assert_ne!(
            recognized.op_names(),
            literal.op_names(),
            "`{src}` was not recognized as a loop"
        );
        for m in &maps {
            for r in &bindings {
                let (got, want) = (answer(&recognized, m, r), answer(&literal, m, r));
                compared += 1;
                if got != want {
                    mismatches.push(format!(
                        "`{src}` over m = {m:?}, r = {r:?}: {got} vs the expansion's {want}"
                    ));
                }
            }
        }
    }
    assert!(compared >= 35 * 5 * 4, "compared only {compared}");
    assert!(
        mismatches.is_empty(),
        "{} of {compared} answers differ:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// An `&&`/`||` chain answers by the absorption rule, computed here from each leaf's OWN answer
/// (evaluated alone, no chain anywhere): an absorbing leaf decides; else the LAST failure is the
/// chain's; else the non-absorbing value. Every assignment of true / false / two distinct
/// failures to chains of two to four leaves, as a value, as a loop's predicate and as a
/// conditional's test — the positions `logic_chain` and `split_chain` lower differently.
#[test]
fn a_logic_chain_answers_by_the_absorption_rule() {
    use typed_cel::{CelEnvironment, CelTy, FastProgram};
    const VARS: [&str; 4] = ["a", "b", "c", "d"];
    let mut env = CelEnvironment::new();
    for v in VARS {
        env.declare(v, CelTy::Num);
    }
    // 1 → true, 2 → false, 3 and 4 → two different missing keys.
    let leaf = |v: &str| format!("{{1: true, 2: false}}[{v}]");
    let run = |src: &str, vals: &[u8]| -> String {
        let program = typed_cel::fork::compile_any_unchecked_presence(&env, src).expect("compiles");
        let fast = FastProgram::new(&program).expect("lowers");
        let mut act = env.runtime().activation();
        for (v, x) in VARS.iter().zip(vals) {
            act.bind_fact(v, Value::Num(f64::from(*x)));
        }
        for v in &VARS[vals.len()..] {
            act.bind_fact(v, Value::Num(1.0));
        }
        // An error's message only: its rendering also carries the whole program's source.
        match fast.eval_result(&act) {
            Err(typed_cel::CelError::Evaluation { message, .. }) => format!("Err({message})"),
            other => format!("{other:?}"),
        }
    };
    let alone: Vec<String> = (1..=4u8).map(|x| run(&leaf("a"), &[x])).collect();
    let (t, f) = (alone[0].clone(), alone[1].clone());
    assert_eq!(t, "Ok(Bool(true))");
    assert_eq!(f, "Ok(Bool(false))");
    assert_ne!(
        alone[2], alone[3],
        "the two failures must be distinguishable"
    );
    let (mut compared, mut mismatches) = (0, Vec::new());
    for len in 2..=4usize {
        for or in [true, false] {
            let op = if or { " || " } else { " && " };
            let chain = VARS[..len]
                .iter()
                .map(|v| leaf(v))
                .collect::<Vec<_>>()
                .join(op);
            let positions = [
                chain.clone(),
                format!("[0].exists(z, {chain})"),
                format!("({chain}) ? true : false"),
            ];
            for vals in (0..4usize.pow(len as u32)).map(|mut i| {
                (0..len)
                    .map(|_| {
                        let x = (i % 4) as u8 + 1;
                        i /= 4;
                        x
                    })
                    .collect::<Vec<u8>>()
            }) {
                let answers: Vec<&String> = vals.iter().map(|x| &alone[*x as usize - 1]).collect();
                let absorbing = if or { &t } else { &f };
                let want = if answers.iter().any(|a| *a == absorbing) {
                    absorbing.clone()
                } else if let Some(e) = answers.iter().rev().find(|a| **a != &t && **a != &f) {
                    (*e).clone()
                } else if or {
                    f.clone()
                } else {
                    t.clone()
                };
                for src in &positions {
                    let got = run(src, &vals);
                    compared += 1;
                    if got != want {
                        mismatches.push(format!(
                            "`{src}` over {vals:?}: {got}, the rule says {want}"
                        ));
                    }
                }
            }
        }
    }
    assert!(
        compared >= 3 * 2 * (16 + 64 + 256),
        "compared only {compared}"
    );
    assert!(
        mismatches.is_empty(),
        "{} of {compared} answers differ:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// A loop inside a loop's predicate — lowered as control flow, its pending error reset as it
/// starts and raised by the fetch that ends it — answers as the literal expansion does: an inner
/// failure raised exactly where the expansion raises it, and absorbed exactly where it absorbs.
#[test]
fn a_nested_loop_answers_as_the_expansion_does() {
    use typed_cel::{CelEnvironment, CelKey, CelTy, FastProgram, Record};
    const MACROS: &[&str] = &["exists", "all", "exists_one"];
    // 1 → true, 2 → false, 3 and 4 → a failure; against `r.n`, which may be NaN or missing.
    const PREDICATES: &[&str] = &["y == r.n", "y < r.n", "{1: true, 2: false}[y]"];
    let mut env = CelEnvironment::new();
    env.declare("xss", CelTy::list(CelTy::list(CelTy::Num)));
    env.declare("r", CelTy::from(Record::new("r", [("n", CelTy::Num)])));
    // `[3, 1]` and `[4, 2]` fail and THEN decide: a caught error left behind by a loop that
    // decided, which the next start of that loop must not see.
    let inner: [&[u8]; 6] = [&[], &[1], &[2, 3], &[3, 4], &[3, 1], &[4, 2]];
    let mut outer: Vec<Vec<&[u8]>> = vec![vec![]];
    for len in 1..=3 {
        let prev: Vec<Vec<&[u8]>> = outer
            .iter()
            .filter(|o| o.len() == len - 1)
            .cloned()
            .collect();
        for o in prev {
            for i in inner {
                let mut o = o.clone();
                o.push(i);
                outer.push(o);
            }
        }
    }
    let record = |n: f64| Some(Value::record([(CelKey::new("n"), Value::Num(n))]));
    let bindings = [record(2.0), record(f64::NAN), Some(Value::record([])), None];
    let answer = |p: &FastProgram, xss: &[&[u8]], r: &Option<Value>| {
        let mut act = env.runtime().activation();
        act.bind_fact(
            "xss",
            Value::list(
                xss.iter()
                    .map(|xs| Value::list(xs.iter().map(|x| Value::Num(f64::from(*x))))),
            ),
        );
        if let Some(r) = r {
            act.bind_fact("r", r.clone());
        }
        format!("{:?}", p.eval_result(&act))
    };
    let (mut compared, mut mismatches) = (0, Vec::new());
    for o in MACROS {
        for i in MACROS {
            for pred in PREDICATES {
                for src in [
                    format!("xss.{o}(xs, xs.{i}(y, {pred}))"),
                    format!("xss.{o}(xs, xs.{i}(y, {pred}) || size(xs) == 0.0)"),
                ] {
                    let program = typed_cel::fork::compile_any_unchecked_presence(&env, &src)
                        .expect("compiles");
                    let recognized = FastProgram::new(&program).expect("lowers");
                    let literal =
                        typed_cel::with_literal_comprehensions(|| FastProgram::new(&program))
                            .expect("lowers");
                    for xss in &outer {
                        for r in &bindings {
                            let (got, want) =
                                (answer(&recognized, xss, r), answer(&literal, xss, r));
                            compared += 1;
                            if got != want {
                                mismatches.push(format!(
                                    "`{src}` over {xss:?}, r = {r:?}: {got} vs the expansion's {want}"
                                ));
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(compared >= 9 * 3 * 2 * 259 * 4, "compared only {compared}");
    assert!(
        mismatches.is_empty(),
        "{} of {compared} answers differ:\n{}",
        mismatches.len(),
        mismatches
            .iter()
            .take(20)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}
