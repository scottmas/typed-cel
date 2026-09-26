//! Programs on the backend: the absorbed evaluator's own unit tests (`objects.rs`, `functions.rs`,
//! `lib.rs`), moved here and run on the one engine.
//!
//! Each absorbed test went one of three ways. PORTED: the checker admits the program, and it runs
//! on the backend with the same assertion. REFUSAL: the checker refuses it and that refusal is the
//! dialect's (a heterogeneous comparison, an operand of the wrong type, an undeclared name), so the
//! refusal is what is asserted. DROPPED: it tested only an evaluator arm no checked program
//! reaches (an opaque host value, a function registered on the evaluator) — those are gone, and
//! ATTRIBUTION.md says so.

#[path = "support/mod.rs"]
mod support;

use typed_cel::{
    CelEnvironment, CelError, CelKey, CelTy, CelValue as Value, ExecutionError, Record,
};

/// A string-keyed map (or record) value.
fn map(entries: &[(&str, Value)]) -> Value {
    Value::record(entries.iter().map(|(k, v)| (CelKey::new(k), v.clone())))
}

fn rec(origin: &str, fields: &[(&str, CelTy)]) -> CelTy {
    Record::new(origin, fields.iter().map(|(n, t)| (*n, t.clone()))).into()
}

/// `src`, closed, is `true` on the backend.
fn yes(src: &str) {
    assert_eq!(support::run_closed(src), Ok(Value::Bool(true)), "{src}");
}

/// `src` is refused before it runs, by the parser or the checker.
fn refused_in(env: &CelEnvironment, src: &str) -> CelError {
    match typed_cel::fork::compile_any(env, src) {
        Ok(_) => panic!("expected `{src}` to be refused, but it compiled"),
        Err(e) => e,
    }
}

// ---- src/lib.rs ------------------------------------------------------------------------------

#[test]
fn lib_parse() {
    typed_cel::fork::parse("1 + 1").unwrap();
    typed_cel::fork::parse("1.1").unwrap();
}

/// `foo.bar`, a list index, `size()`, over bound values. `str[0]` (a string is not indexable) is
/// the checker's refusal now, where the evaluator answered `NoSuchOverload`.
#[test]
fn lib_variables() {
    let mut env = CelEnvironment::new();
    env.declare("foo", rec("foo", &[("bar", CelTy::Num)]));
    env.declare("arr", CelTy::list(CelTy::Num));
    env.declare("str", CelTy::Str);
    let ctx: Vec<(&str, Value)> = vec![
        ("foo", (map(&[("bar", Value::Num(1.0))])).into()),
        ("arr", (Value::list([1.0, 2.0, 3.0].map(Value::Num))).into()),
        ("str", ("foobar").into()),
    ];
    for (src, want) in [
        ("size([1, 2, 3]) == 3", true),
        ("size([size([42]), 2, 3]) == 3", true),
        ("size([]) == 3", false),
        ("foo.bar == 1", true),
        ("arr[0] == 1", true),
    ] {
        assert_eq!(
            support::run(&env, src, &ctx),
            Ok(Value::Bool(want)),
            "{src}"
        );
    }
    assert!(matches!(refused_in(&env, "str[0]"), CelError::Check { .. }));
}

/// A missing key, an undeclared name, an unknown method or function: each is refused by the
/// checker now, where the evaluator failed it at run time. A `null` map key still checks, and still
/// fails at run time with the evaluator's error.
#[test]
fn lib_execution_errors() {
    let mut env = CelEnvironment::new();
    env.declare("foo", rec("foo", &[("bar", CelTy::Num)]));
    for src in [
        "foo.baz.bar == 1",
        "missing == 1",
        "1.missing()",
        "missing(1)",
    ] {
        assert!(
            matches!(refused_in(&env, src), CelError::Check { .. }),
            "`{src}` must be refused by the checker"
        );
    }
    assert_eq!(
        support::run(&env, "{null: true}", &[]),
        Err(ExecutionError::unsupported_key_type(Value::Null))
    );
}

/// The references a parsed tree names.
#[test]
fn lib_references() {
    let e = typed_cel::fork::parse("[1, 1].map(x, x * 2)").unwrap();
    assert!(e.references().has_variable("x"));
    assert_eq!(e.references().variables().len(), 1);
}

// ---- src/objects.rs --------------------------------------------------------------------------

#[test]
fn objects_indexed_map_access() {
    let mut env = CelEnvironment::new();
    env.declare("headers", CelTy::map(CelTy::Str, CelTy::Str));
    let ctx: Vec<(&str, Value)> = vec![(
        "headers",
        (map(&[("Content-Type", Value::from("application/json"))])).into(),
    )];
    assert_eq!(
        support::run(&env, "headers[\"Content-Type\"]", &ctx),
        Ok(Value::from("application/json"))
    );
}

#[test]
fn objects_numeric_compare() {
    yes("1 < 1.1");
    yes("0 > -10");
}

#[test]
fn objects_float_compare() {
    yes("1.0 > 0.0");
    assert_eq!(
        support::run_closed("0.0 / 0.0 == 0.0 / 0.0"),
        Ok(Value::Bool(false)),
        "NaN should not equal itself"
    );
    assert!(
        support::run_closed("1.0 > 0.0 / 0.0").is_err(),
        "NaN should not be comparable with inequality operators"
    );
}

/// Equality is homogeneous: a map beside a list is the checker's refusal.
#[test]
fn objects_invalid_compare_is_refused() {
    assert!(matches!(
        refused_in(&CelEnvironment::new(), "{} == []"),
        CelError::Check { .. }
    ));
}

#[test]
fn objects_size_fn_and_a_variable_named_size() {
    let mut env = CelEnvironment::new();
    env.declare("requests", CelTy::list(CelTy::Num));
    env.declare("size", CelTy::Num);
    let ctx: Vec<(&str, Value)> = vec![
        (
            "requests",
            (Value::list([Value::Num(42.0), Value::Num(42.0)])).into(),
        ),
        ("size", (Value::Num(3.0)).into()),
    ];
    assert_eq!(
        support::run(&env, "size(requests) + size == 5", &ctx),
        Ok(Value::Bool(true))
    );
}

/// `'foo' - 10`, `+`, `/`: an operand of the wrong type is the checker's refusal.
#[test]
fn objects_invalid_arithmetic_is_refused() {
    for src in ["'foo' - 10", "'foo' + 10", "'foo' / 10"] {
        assert!(
            matches!(
                refused_in(&CelEnvironment::new(), src),
                CelError::Check { .. }
            ),
            "`{src}`"
        );
    }
}

#[test]
fn objects_out_of_bound_list_access() {
    let mut env = CelEnvironment::new();
    env.declare("list", CelTy::list(CelTy::Num));
    let ctx: Vec<(&str, Value)> = vec![("list", (Value::list([])).into())];
    assert_eq!(
        support::run(&env, "list[10]", &ctx),
        Err(ExecutionError::IndexOutOfBounds(Value::Num(10.0)))
    );
    assert_eq!(
        support::run(&env, "list[-1]", &ctx),
        Err(ExecutionError::IndexOutOfBounds(Value::Num(-1.0)))
    );
}

#[test]
fn objects_short_circuit_and() {
    let mut env = CelEnvironment::new();
    env.declare("data", CelTy::map(CelTy::Str, CelTy::Str));
    let ctx: Vec<(&str, Value)> = vec![("data", (map(&[])).into())];
    assert!(
        support::run(&env, "has(data.x) && data.x.startsWith(\"foo\")", &ctx).is_ok(),
        "The AND expression should support short-circuit evaluation."
    );
}

/// A number is not a bool operand: `foo || …` over `foo: number` is the checker's refusal, where
/// the evaluator ran it and let the other operand decide.
#[test]
fn objects_a_non_bool_logical_operand_is_refused() {
    let mut env = CelEnvironment::new();
    env.declare("foo", CelTy::Num);
    env.declare("bar", CelTy::Num);
    for src in [
        "foo || bar > 0",
        "foo || bar < 0",
        "foo && bar < 0",
        "foo && bar > 0",
    ] {
        assert!(
            matches!(refused_in(&env, src), CelError::Check { .. }),
            "`{src}`"
        );
    }
}

/// `removed: integer values`: what was checked i64 arithmetic is IEEE double arithmetic.
/// Nothing overflows and nothing divides by zero — `1 / 0` is `+inf`.
#[test]
fn objects_number_math_is_double_math() {
    for (expr, want) in [
        ("1 / 0".to_string(), f64::INFINITY),
        ("7 / 2".to_string(), 3.5),
        (format!("{} + 1", i64::MAX), i64::MAX as f64 + 1.0),
        (format!("{} * 2", i64::MAX), i64::MAX as f64 * 2.0),
    ] {
        assert_eq!(support::run_closed(&expr), Ok(Value::Num(want)), "{expr}");
    }
}

#[test]
fn objects_index_missing_map_key() {
    let mut env = CelEnvironment::new();
    env.declare("mymap", CelTy::map(CelTy::Str, CelTy::Num));
    let ctx: Vec<(&str, Value)> = vec![("mymap", (map(&[("a", Value::Num(1.0))])).into())];
    assert!(
        support::run(&env, r#"mymap["missing"]"#, &ctx).is_err(),
        "Should error on missing map key"
    );
}

// ---- src/functions.rs ------------------------------------------------------------------------

#[test]
fn functions_size() {
    yes("size([1, 2, 3]) == 3");
    yes("size({'a': 1, 'b': 2, 'c': 3}) == 3");
    yes("[1, 2, 3].size() == 3");
}

#[test]
fn functions_has() {
    let mut env = CelEnvironment::new();
    env.declare("foo", CelTy::map(CelTy::Str, CelTy::Num));
    let ctx: Vec<(&str, Value)> = vec![("foo", (map(&[("bar", Value::Num(1.0))])).into())];
    for src in ["has(foo.bar) == true", "has(foo.baz) == false"] {
        assert_eq!(
            support::run(&env, src, &ctx),
            Ok(Value::Bool(true)),
            "{src}"
        );
    }
}

#[test]
fn functions_map() {
    yes("[1, 2, 3].map(x, x * 2) == [2, 4, 6]");
    yes("[1, 2, 3].map(y, y + 1) == [2, 3, 4]");
    yes("[1, 2, 3].map(y, y == 2, y + 1) == [3]");
    yes("[[1, 2], [2, 3]].map(x, x.map(x, x * 2)) == [[2, 4], [4, 6]]");
    yes(r#"{'John': 'smart'}.map(key, key) == ['John']"#);
}

#[test]
fn functions_filter() {
    yes("[1, 2, 3].filter(x, x > 2) == [3]");
}

#[test]
fn functions_all() {
    yes("[0, 1, 2].all(x, x >= 0)");
    yes("[0, 1, 2].all(x, x > 0) == false");
    yes("{0: 0, 1:1, 2:2}.all(x, x >= 0) == true");
}

#[test]
fn functions_exists() {
    yes("[0, 1, 2].exists(x, x > 0)");
    yes("[0, 1, 2].exists(x, x == 3) == false");
    yes("[0, 1, 2, 2].exists(x, x == 2)");
    yes("{0: 0, 1:1, 2:2}.exists(x, x > 0)");
}

#[test]
fn functions_exists_one() {
    yes("[0, 1, 2].exists_one(x, x > 0) == false");
    yes("[0, 1, 2].exists_one(x, x == 0)");
    yes("{0: 0, 1:1, 2:2}.exists_one(x, x == 2)");
}

#[test]
fn functions_starts_with() {
    yes("'foobar'.startsWith('foo') == true");
    yes("'foobar'.startsWith('bar') == false");
}

#[test]
fn functions_ends_with() {
    yes("'foobar'.endsWith('bar') == true");
    yes("'foobar'.endsWith('foo') == false");
}

#[test]
fn functions_duration() {
    yes("duration('1s') == duration('1000ms')");
    yes("duration('1m') == duration('60s')");
    yes("duration('1h') == duration('60m')");
    yes("duration('1m') > duration('1s')");
    yes("duration('1m') < duration('1h')");
    yes("duration('1h') - duration('1m') == duration('59m')");
    yes("duration('1h') + duration('1m') == duration('1h1m')");
    yes("duration('2h30m45s').getSeconds() == 9045");
    yes("duration('1s500ms').getMilliseconds() == 1500");
    yes("duration('90s').getSeconds() == 90");
}

#[test]
fn functions_contains() {
    yes("'foobar'.contains('bar') == true");
}

#[test]
fn functions_matches() {
    yes("'foobar'.matches('^[a-zA-Z]*$') == true");
    yes("{'1': 'abc', '2': 'def', '3': 'ghi'}.all(key, key.matches('^[a-zA-Z]*$')) == false");
}

#[test]
fn functions_matches_err() {
    assert_eq!(
        support::run_closed("'foobar'.matches('(foo') == true"),
        Err(ExecutionError::FunctionError {
            function: "matches".to_string(),
            message: "'(foo' not a valid regex:\nregex parse error:\n    (foo\n    ^\nerror: unclosed group"
                .to_string()
        })
    );
}

/// No value is coerced to a bool: every non-bool `||` operand is the checker's refusal.
#[test]
fn functions_no_bool_coercion() {
    for src in [
        "'' || false",
        "1 || false",
        "0.1|| false",
        "[] || false",
        "{} || false",
        "null || false",
    ] {
        assert!(
            matches!(
                refused_in(&CelEnvironment::new(), src),
                CelError::Check { .. }
            ),
            "`{src}`"
        );
    }
}

/// A number that names no key is `no such key`, wherever the map lives — built by the program,
/// returned by a comprehension, or read through a comprehension variable.
#[test]
fn a_fractional_key_is_no_such_key_wherever_the_map_lives() {
    for src in [
        "{1: 'a'}[1.5]",
        "[{1: 'a'}].map(x, x)[0][1.5]",
        "[{1: 'a'}].filter(x, true)[0][1.5]",
        "[{1: 'a'}].map(m, m[1.5])",
    ] {
        match support::run_closed(src) {
            Err(ExecutionError::NoSuchKey(k)) => assert_eq!(k.as_str(), "1.5", "{src}"),
            other => panic!("{src}: want NoSuchKey(\"1.5\"), got {other:?}"),
        }
    }
}

/// Values render as the error contract says: the text below was captured on the fork's value model
/// before `CelValue` replaced it, and must not move by a character.
#[test]
fn values_render_as_the_error_contract_says() {
    let message = |src: &str| -> String {
        let env = CelEnvironment::new();
        let p = typed_cel::fork::compile_any(&env, src).unwrap_or_else(|e| panic!("{src}: {e}"));
        match typed_cel::FastProgram::new(&p)
            .expect("lowers")
            .eval(&env.activation())
        {
            Err(CelError::Evaluation { message, .. }) => message,
            other => panic!("{src}: {other:?}"),
        }
    };
    for (src, want) in [
        (
            "[1, 2][5] == 1.0",
            "could not be evaluated: Index out of bounds: Float(5.0)",
        ),
        (
            "[1, 2][1.5] == 1.0",
            "could not be evaluated: Index out of bounds: Float(1.5)",
        ),
        (
            "[[1]][0][3] == 1.0",
            "could not be evaluated: Index out of bounds: Float(3.0)",
        ),
        (
            "[1][-1] == 1.0",
            "could not be evaluated: Index out of bounds: Float(-1.0)",
        ),
        (
            "{null: true}[null]",
            "could not be evaluated: Unable to use value 'Null' as a key",
        ),
        (
            "[1.0, 2.5]",
            "produced List([Float(1.0), Float(2.5)]) rather than a bool",
        ),
        ("'x'", "produced String(\"x\") rather than a bool"),
        ("b'ab'", "produced Bytes([97, 98]) rather than a bool"),
        (
            "duration('90s')",
            "produced Duration(TimeDelta { secs: 90, nanos: 0 }) rather than a bool",
        ),
        ("null", "produced Null rather than a bool"),
        (
            "[duration('1ns')]",
            "produced List([Duration(TimeDelta { secs: 0, nanos: 1 })]) rather than a bool",
        ),
        (
            "[[1], []]",
            "produced List([List([Float(1.0)]), List([])]) rather than a bool",
        ),
        (
            "['a', 'b']",
            "produced List([String(\"a\"), String(\"b\")]) rather than a bool",
        ),
        (
            "{'a': 1}",
            "produced Map(Map { map: {String(\"a\"): Float(1.0)} }) rather than a bool",
        ),
        (
            "{1: 'a'}",
            "produced Map(Map { map: {Num(1): String(\"a\")} }) rather than a bool",
        ),
        (
            "{true: [1]}",
            "produced Map(Map { map: {Bool(true): List([Float(1.0)])} }) rather than a bool",
        ),
        ("3.5", "produced Float(3.5) rather than a bool"),
        ("[b'x']", "produced List([Bytes([120])]) rather than a bool"),
        ("[null]", "produced List([Null]) rather than a bool"),
    ] {
        assert_eq!(message(src), want, "`{src}`");
    }
}

/// A map comes back in key order, whatever order it was built in — and a map holding keys of
/// every kind (which only a host or a binder can build; a map literal's keys share one type) orders
/// numbers, then bools, then strings.
#[test]
fn a_map_result_comes_back_in_key_order() {
    let result = |src: &str| {
        let p = typed_cel::fork::compile_any(&CelEnvironment::new(), src)
            .unwrap_or_else(|e| panic!("{src}: {e}"));
        let code = typed_cel::FastProgram::new(&p).expect("lowers");
        format!(
            "{:?}",
            typed_cel::fork::fast_value(&code, &CelEnvironment::new().runtime().activation())
        )
    };
    assert_eq!(
        result("{'b': 1, 'a': 2, 'c': 3}"),
        r#"Ok(Map(Map { map: {String("a"): Float(2.0), String("b"): Float(1.0), String("c"): Float(3.0)} }))"#
    );
    assert_eq!(
        result("{3: 'c', 1: 'a', 2: 'b'}"),
        r#"Ok(Map(Map { map: {Num(1): String("a"), Num(2): String("b"), Num(3): String("c")} }))"#
    );
    let mixed = typed_cel::CelMap::new([
        (typed_cel::CelMapKey::Str(CelKey::new("b")), Value::Num(1.0)),
        (typed_cel::CelMapKey::Str(CelKey::new("a")), Value::Num(2.0)),
        (typed_cel::CelMapKey::Bool(true), Value::Num(4.0)),
        (typed_cel::CelMapKey::Num(1), Value::Num(3.0)),
    ]);
    assert_eq!(
        format!("{:?}", Value::Map(mixed)),
        r#"Map(Map { map: {Num(1): Float(3.0), Bool(true): Float(4.0), String("a"): Float(2.0), String("b"): Float(1.0)} })"#
    );
}
