//! The dialect's REMOVALS, asserted from the outside.
//!
//! Every row in README.md's "Removed" table names one of these tests, and
//! `every_removal_row_has_a_rejection_test` checks that pairing. A removal that has no
//! test here is a claim about the language rather than a property of it — and the failure mode is
//! specific: the construct keeps working, nobody notices, and a policy written against it compiles
//! into a dialect that was supposed to have made it unwritable.
//!
//! The tests deliberately assert only that the construct FAILS, not exactly how. Some removals bite
//! at parse (`1u`, message literals, `[?k]`), others at evaluation (`timestamp()`,
//! `optional.of()`), and one bites at CHECK (`size()` over a string, which shares its evaluator arm
//! with lists and maps and can therefore only be refused by the signature table). Which one applies
//! is an implementation detail of where the construct was reachable from. What is NOT an
//! implementation detail — and is asserted — is that no spelling of a removed construct is
//! available to a policy.

use typed_cel::CompileOpts;
use std::rc::Rc;

use typed_cel::{CelEnvironment, CelTy, Record};

/// What the dialect does with an expression: a value, or a refusal.
///
/// Every refusal shape collapses to `Err` on purpose. Parse, check and run are phases of one
/// question — "can a policy write this?" — and a removal that moved from one phase to another is
/// still a removal. A program the checker admits runs on the backend.
fn eval(src: &str) -> Result<String, String> {
    let program = typed_cel::fork::compile_any(&CelEnvironment::new(), src)
        .map_err(|e| format!("refused: {e}"))?;
    let code = typed_cel::FastProgram::new(&program)
        .unwrap_or_else(|e| panic!("`{src}` checks but does not lower: {e}"));
    typed_cel::fork::fast_value(&code, &CelEnvironment::new().runtime().activation())
        .map(|v| format!("{v:?}"))
        .map_err(|e| format!("eval: {e}"))
}

/// Assert every spelling is refused, and say which one leaked.
fn all_refused(spellings: &[&str]) {
    let mut leaked = Vec::new();
    for src in spellings {
        if let Ok(value) = eval(src) {
            leaked.push(format!("  {src}  =>  {value}"));
        }
    }
    assert!(
        leaked.is_empty(),
        "these spellings still produce a value:\n{}",
        leaked.join("\n")
    );
}

/// `removed: protobuf`
///
/// Nothing in either environment produces a protobuf message, and the whole family — message
/// literals, enums, wrappers — arrives through one AST variant and one parser production. Deleting
/// the variant is what turns "message construction is rejected" from a runtime check into a
/// compile error in this crate.
#[test]
fn message_construction_is_gone() {
    all_refused(&[
        "TestAllTypes{single_int32: 1}",
        "TestAllTypes{}",
        "google.protobuf.Int32Value{value: 1}",
        ".cel.expr.conformance.proto3.TestAllTypes{single_int64: 17}",
        "google.protobuf.Duration{seconds: 123}",
    ]);

    // And the refusal happens at PARSE, so a policy carrying one never reaches an activation.
    let err = typed_cel::fork::parse("TestAllTypes{single_int32: 1}")
        .err()
        .expect("message construction parses today; it must not");
    let err = err.to_string();
    assert!(
        err.contains("typed-CEL dialect"),
        "the refusal must name the dialect so a policy author knows it is deliberate, got: {err}"
    );
}

/// `removed: dyn()`
///
/// `dyn()` exists to defeat type checking. One numeric type and a real checker make it
/// unnecessary, and keeping it would leave a documented hole in the checker the later passes build on.
#[test]
fn dyn_is_gone() {
    all_refused(&["dyn(1)", "dyn(1) == 1", "dyn([1, 2, 3])", "dyn('a')"]);
}

/// `removed: optional syntax`
///
/// `removed: optional values`. An optional READ (`x.?f`, `m[?k]`) is legal only as the operand of
/// `.orValue(d)`, `.hasValue()` or `has()` (`added: optional reads`); every form that would hold an
/// optional VALUE — a bare optional read, a comparison of one, the `optional.*` constructors and
/// the `value`/`or` accessors, `[?x]`, `{?k: v}` — is refused, never reinterpreted.
///
/// There is no flag to turn it back on, which is the point: a parser option is a thing a future
/// caller can set.
#[test]
fn optional_values_are_gone() {
    all_refused(&[
        "{'a': 1}[?'a']",
        "{'a': 1}.?a",
        "{'a': 1}.?a == 1",
        "{'a': 1}[?'a'] == 1",
        "{'a': 1}.?a.value() == 1",
        "{'a': 1}.?a.or({'a': 1}.?a).hasValue()",
        "optional.of(1)",
        "optional.none()",
        "optional.ofNonZeroValue(1)",
        "optional.of(1).value()",
        "optional.of(1).hasValue()",
        "optional.of(1).orValue(0)",
        "optional.none().orValue(0)",
        "optional.of(1).or(optional.of(2))",
        "[?'a']",
        "[?1]",
        "{?'a': 1}",
    ]);
}

/// `removed: timestamp` — and `diverges: durations without timestamps`.
///
/// A wall-clock read inside a sandbox decision is a bug: a revocation that fires because NTP
/// stepped is not a policy. Deleting the type is how that becomes unwritable rather than merely
/// discouraged.
///
/// The PAIR is the test. `timestamp` and `duration` share the chrono-backed conversion path, so
/// deleting one by deleting the shared path takes both — and duration is load-bearing for the
/// entire system environment, where every expression is a span comparison.
#[test]
fn timestamp_is_gone() {
    all_refused(&[
        "timestamp('2026-01-01T00:00:00Z')",
        "timestamp(0)",
        "timestamp('2026-01-01T00:00:00Z') > timestamp('2025-01-01T00:00:00Z')",
        "timestamp('2026-01-01T00:00:00Z').getFullYear()",
        "type(timestamp('2026-01-01T00:00:00Z'))",
    ]);

    // Durations survive, in every form the system environment needs.
    assert_eq!(
        eval("duration('30s') > duration('3s')"),
        Ok("Bool(true)".into())
    );
    assert_eq!(
        eval("duration('1h30m') == duration('90m')"),
        Ok("Bool(true)".into())
    );
    assert_eq!(
        eval("duration('5s') + duration('3s') == duration('8s')"),
        Ok("Bool(true)".into())
    );
    assert_eq!(
        eval("duration('5s') - duration('3s') == duration('2s')"),
        Ok("Bool(true)".into())
    );
    assert_eq!(
        eval("duration('500ms') < duration('1s')"),
        Ok("Bool(true)".into())
    );
    assert_eq!(eval("duration('90s').getSeconds()"), Ok("Int(90)".into()));
}

/// `removed: uint`
///
/// One numeric type. The `u` literal and the `uint` type are gone: a large integer written without
/// a `u` is the one number type, held exactly. The trap this closed — cel-rust's serde conversion
/// typing a positive JSON integer as `UInt`, which then picked a different ARITHMETIC — stays
/// closed because arithmetic and comparison are defined across every representation of a number.
#[test]
fn uint_is_gone() {
    all_refused(&[
        "1u",
        "1U",
        "0u",
        "uint(1)",
        "1u == 1",
        "uint(1) + uint(2)",
        "0xFFu",
        "type(1u)",
    ]);

    // The neighbours stay. (`int()` went with `removed: integer values` — there is no integer for
    // it to produce — and is refused by `type_conversion_functions_are_gone`.)
    assert_eq!(eval("1 + 1 == 2"), Ok("Bool(true)".into()));
}

/// `removed: size() on strings`
///
/// Refused by the signature table, which has no string overload, and gone from the evaluator: a
/// string has no `Sizer`, and the `size` overloads for strings and bytes are not registered.
///
/// `size()` returns BYTES, not code points: `size('πέντε')` is 10. A length predicate that means
/// something different on non-ASCII input is worse than no length predicate. The corpus rows where
/// that difference is OBSERVABLE are excluded; this test covers the rest of the overload, which is
/// invisible to the corpus because ASCII agrees.
#[test]
fn size_on_a_string_is_gone() {
    all_refused_at_check(&[
        "size('abc') > 0",
        "'abc'.size() > 0",
        "size('πέντε') > 0",
        "size(s) > 0",
        "s.size() > 0",
        "rec.name.size() > 0",
    ]);

    all_refused(&[
        "size('abc')",
        "'abc'.size()",
        "size(b'abc')",
        "b'abc'.size()",
    ]);

    // The overload stays for the containers.
    checks("size([1, 2, 3]) == 3");
    checks("size({'a': 1}) == 1");
    checks("size(l) == 3");
    checks("l.size() == 3");
    checks("m.size() == 1");

    // And the evaluator still answers for them.
    assert_eq!(eval("size([1, 2, 3])"), Ok("Int(3)".into()));
    assert_eq!(eval("size({'a': 1})"), Ok("Int(1)".into()));
}

/// An environment holding one value of each shape, for the removals that bite at CHECK.
fn checker_env() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.declare("s", CelTy::Str);
    env.declare("l", CelTy::list(CelTy::Num));
    env.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    env.declare(
        "rec",
        CelTy::Record(Rc::new(Record {
            fields: vec![("name".to_string(), CelTy::Str)],
            optional: Default::default(),
            index: None,
            origin: "rec".to_string(),
        })),
    );
    env
}

/// Assert every spelling is refused by the CHECKER, and say which one leaked.
fn all_refused_at_check(spellings: &[&str]) {
    let env = checker_env();
    let mut leaked = Vec::new();
    for src in spellings {
        if env.compile(*src, &CompileOpts::default()).is_ok() {
            leaked.push(format!("  {src}"));
        }
    }
    assert!(
        leaked.is_empty(),
        "these spellings still type-check:\n{}",
        leaked.join("\n")
    );
}

fn checks(src: &str) {
    if let Err(e) = checker_env().compile(src, &CompileOpts::default()) {
        panic!("expected `{src}` to check, got:\n{e}");
    }
}

/// `removed: extension libraries`
///
/// The five extension libraries cel-go and cel-java ship — `math`, `strings`, `encoders`,
/// `bindings`, `block` — account for 454 excluded corpus cases, which is more than any other
/// removal. Upstream shipped none of them, and this dialect adds none.
///
/// The row is tested rather than taken on trust because "we simply never implemented it" and "it
/// is not reachable" are different claims, and only the second one survives someone registering a
/// function later. Every spelling below is what the corpus itself uses, so the test tracks the
/// thing the exclusions are excluding rather than a paraphrase of it.
#[test]
fn extension_libraries_are_gone() {
    all_refused(&[
        // math
        "math.greatest(1, 2)",
        "math.least(1, 2)",
        "math.abs(-1)",
        "math.ceil(1.5)",
        "math.bitAnd(3, 2)",
        // strings
        "'hello'.charAt(1)",
        "'hello'.indexOf('l')",
        "'hello'.replace('l', 'L')",
        "'a,b'.split(',')",
        "['a', 'b'].join(',')",
        "'hello'.upperAscii()",
        "'  a  '.trim()",
        "'%d'.format([1])",
        // encoders
        "base64.encode(b'hello')",
        "base64.decode('aGVsbG8=')",
        // bindings
        "cel.bind(x, 1, x + 1)",
        // block — spelled as the corpus does, via the internal call the optimizer emits
        "cel.@block([1], 1)",
        "cel.index(0)",
    ]);
}

/// The rendering of the CHECKER's refusal of `src`, or a panic naming what compiled instead.
///
/// `err()` rather than `unwrap_err()` because a compiled program is not `Debug`, and the point of
/// these three tests is the MESSAGE: a removal whose diagnostic says "undeclared variable" tells a
/// reader they made a typo, which is the one reading that sends them looking for the name.
fn refusal(env: &CelEnvironment, src: &str) -> String {
    env.compile(src, &CompileOpts::default())
        .err()
        .unwrap_or_else(|| panic!("`{src}` compiles today; it must not"))
        .to_string()
}

/// `removed: type values`
///
/// The dialect has a STATIC checker, so a runtime type value has no job: every question
/// `type(x) == type(y)` answers is either already decided at build time or a comparison the
/// signature table refuses outright.
///
/// The two spellings reach two DIFFERENT diagnostics, and enumerating both is the whole point.
/// `type(x)` is a CALL, so it goes down the unknown-function path, where a table of removed names
/// is consulted. A denotation — `bool`, `list`, `null_type` — is a bare IDENTIFIER, so it goes
/// down the undeclared-VARIABLE path instead, which never reaches that table. Getting the call
/// right and leaving the denotation reporting "undeclared variable `bool`" is the half-done state
/// this pairing catches.
#[test]
fn type_values_are_gone() {
    let env = checker_env();

    let err = refusal(&env, "type(rec.name) == type(s)");
    assert!(err.contains("type values"), "{err}");
    assert!(
        err.contains("README.md"),
        "the refusal must cite the row a reader can act on: {err}"
    );

    for denotation in [
        "int",
        "string",
        "list",
        "map",
        "bool",
        "double",
        "bytes",
        "null_type",
        "type",
    ] {
        let err = refusal(&env, denotation);
        assert!(
            err.contains("type values"),
            "`{denotation}` reports a typo rather than a removal: {err}"
        );
        assert!(
            err.contains("README.md"),
            "`{denotation}` does not cite its README row: {err}"
        );
    }
}

/// `removed: type conversion functions`
///
/// One numeric type leaves nothing for `int()` to convert to, `bool('true')` is string-typed
/// truthiness that the checker exists to prevent, and `string()` on a bytes value is lossy in a
/// way the caller would not notice — invalid UTF-8 becomes U+FFFD rather than an error.
#[test]
fn type_conversion_functions_are_gone() {
    let env = checker_env();
    for (expr, named) in [
        ("bool('true')", "bool"),
        ("int('1')", "int"),
        ("string(42)", "string"),
        ("double(1)", "double"),
        ("double('1.5')", "double"),
        ("bytes('abc')", "bytes"),
    ] {
        let err = refusal(&env, expr);
        assert!(
            err.contains(named),
            "`{expr}` does not name `{named}`: {err}"
        );
        assert!(
            err.contains("removed: type conversion functions"),
            "`{expr}` does not cite its README row: {err}"
        );
    }
    // Gone from the evaluator as well: none of them is registered.
    all_refused(&[
        "string(42)",
        "string('a')",
        "string(b'a')",
        "string(duration('1s'))",
        "double(1)",
        "double('1.5')",
        "bytes('abc')",
        "bytes(b'abc')",
    ]);
}

/// `not implemented: backtick-quoted field selection`
///
/// A removal whose diagnostic does not name the working spelling reads as a bug, so the MESSAGE —
/// not merely the `Err` — is what this asserts.
///
/// The refusal comes from the CHECKER, and it has to: the parser keeps the backticks inside the
/// field name, so ``m.`content-type` `` is a select for a key that happens not to exist. Left
/// alone it fails at evaluation with `No such key`, which reads as missing DATA rather than as a
/// construct the dialect does not have.
#[test]
fn backtick_field_selection_is_gone() {
    let env = checker_env();
    for expr in ["m.`content-type` == 1", "has(m.`content-type`)"] {
        let err = refusal(&env, expr);
        assert!(
            err.contains("['content-type']"),
            "the refusal must name the working spelling: {err}"
        );
        assert!(
            err.contains("README.md"),
            "the refusal must cite the row a reader can act on: {err}"
        );
    }

    // The index form is the one spelling, and it keeps working.
    assert!(env
        .compile(
            "'content-type' in m && m['content-type'] == 1",
            &CompileOpts::default()
        )
        .is_ok());
}

/// `src` evaluates to `want` (its `Debug` text) on the backend.
fn gives(src: &str, want: &str) {
    assert_eq!(eval(src), Ok(want.to_string()), "`{src}`");
}

/// `diverges: one numeric type`
///
/// The checker has ONE numeric type (`double`). A VALUE of it is held exactly, in one of three
/// representations — an `i64`, a `u64` above `i64::MAX`, or an `f64` — and the engine builds the
/// canonical one (an integral double in range is an integer). Every comparison is by exact value
/// across representations, so a checked program that mixes a bound number and a literal answers
/// as the arithmetic says: `x + 1` with `x: double` bound to `2` is `3`, which equals `3.0`.
#[test]
fn one_numeric_type_many_representations() {
    // The checked program that used to type-check and then fail: a bound double beside a literal.
    let mut env = CelEnvironment::new();
    env.declare("x", CelTy::Num);
    let program = env
        .compile("x + 1 == 3.0", &CompileOpts::default())
        .expect("checks");
    let mut activation = env.activation();
    activation.bind("x", &serde_json::json!(2)).unwrap();
    assert_eq!(
        program.evaluate(&activation).map_err(|e| e.to_string()),
        Ok(true)
    );

    // An integral number is held as an integer, whichever way it was spelled.
    gives("1 + 2", "Int(3)");
    gives("1.5 + 1.5", "Int(3)");
    gives("-7", "Int(-7)");
    gives("size([1, 2])", "Int(2)");
    gives("duration('90s').getSeconds()", "Int(90)");
    gives("[1, 2][0]", "Int(1)");
    gives("0.5 + 1", "Float(1.5)");

    // Division is real division: no truncation, and no division-by-zero error — spec CEL's
    // doubles answer `+inf`, and so does this dialect's one number type.
    gives("7 / 2 == 3.5", "Bool(true)");
    gives("7 / 2", "Float(3.5)");
    gives("1 / 0", "Float(inf)");
    gives("-1 / 0", "Float(-inf)");

    // A literal beyond 2^53 is held exactly, not as its nearest double.
    gives("-(9007199254740993)", "Int(-9007199254740993)");
    gives("-(9007199254740993) == -9007199254740992.0", "Bool(false)");

    // `diverges: exact integers span int64 and uint64`: past `i64::MAX` an integer is still
    // exact, where spec CEL's `int` overflows. Both sides here are exactly 2^63.
    gives(
        "9223372036854775807 + 1 == 9223372036854775808.0",
        "Bool(true)",
    );
    gives("9223372036854775807 + 1", "UInt(9223372036854775808)");

    // A map key spelled as an integer is an integer key, and an integral double finds it.
    gives("{1: 'a'}[1.0]", "String(\"a\")");
    gives("{1.0: 'a'}[1]", "String(\"a\")");
}

/// `removed: integer division`
///
/// One number type, so `/` cannot mean two things by how its operands were spelled: it is real
/// division. An integer quotient is exact when it divides and a double when it does not, and a
/// zero divisor is IEEE's answer rather than an error.
#[test]
fn integer_division_is_gone() {
    gives("7 / 2 == 3.5", "Bool(true)");
    gives("-7 / 2 == -3.5", "Bool(true)");
    gives("6 / 3", "Int(2)");
    gives("1 / 0 > 1e308", "Bool(true)");
    gives("-1 / 0 < -1e308", "Bool(true)");
    gives("0 / 0 == 0 / 0", "Bool(false)");
}

/// A list index is a double. An integral one indexes; a fraction is refused with the evaluator's
/// index error rather than rounded, because rounding would make `l[0.5]` silently mean `l[0]`.
#[test]
fn index_by_an_integral_double() {
    gives("[10, 20, 30][1.0]", "Int(20)");
    gives("[10, 20, 30][size([1])]", "Int(20)");
    gives("[10, 20, 30][4 / 2]", "Int(30)");
}

#[test]
fn index_by_a_fraction_is_refused() {
    for src in [
        "[10, 20, 30][0.5]",
        "[10, 20, 30][1 / 2]",
        "[10, 20, 30][-1]",
    ] {
        let got = eval(src);
        let err = got
            .as_ref()
            .err()
            .unwrap_or_else(|| panic!("`{src}` must be refused, got {got:?}"));
        assert!(
            err.contains("Index out of bounds"),
            "`{src}` must fail with the index error, got {err}"
        );
    }
}

/// `removed: modulo`
///
/// No generated program uses `%` — neither the chokepoint programs nor the HTTP environment — and
/// with one number kind it could only mean a floating-point remainder, a second arithmetic nobody
/// asked for. So it is refused by the checker, and the backend has no lowering for it.
#[test]
fn modulo_is_on_doubles_or_gone() {
    let mut env = CelEnvironment::new();
    env.declare("x", CelTy::Num);
    let err = refusal(&env, "x % 2.0 == 0.0");
    assert!(
        err.contains("removed: modulo"),
        "the refusal must cite its README row: {err}"
    );

    // The checker is the only way onto the backend, which has no `%` to run.
    all_refused(&["5 % 2", "5.0 % 2.0", "5 % 2 == 1"]);
}

/// An environment for the `dyn` value rows: a list of numbers, and a body whose schema declared one
/// member `unknown`.
fn dyn_env() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.declare("x", CelTy::list(CelTy::Num));
    env.declare("xs", CelTy::list(CelTy::Num));
    env.declare(
        "body",
        Record::new("body", [("name", CelTy::Str), ("blob", CelTy::Dyn)]),
    );
    env
}

/// `removed: dyn values`
///
/// A program that type-checks holds no `dyn` value anywhere. A value of no static type is what
/// would force a typed backend to keep a boxed escape hatch, and no program this dialect targets
/// needs one. Each construct that used to MANUFACTURE a `dyn` — a heterogeneous list or map literal, a
/// conditional whose branches differ, reading a member the schema declared `unknown` — is refused
/// by `compile`, with a message naming the construct and this row.
#[test]
fn dyn_values_are_gone() {
    let env = dyn_env();
    for (src, construct) in [
        (r#"[1.0, "a"] == x"#, "heterogeneous list literal"),
        (
            r#"{"a": 1.0, "b": "x"}.a == 1.0"#,
            "heterogeneous map literal",
        ),
        (
            r#"xs.map(x, x > 1.0 ? x : "s") == []"#,
            "branches of `?:` have different types",
        ),
        ("body.blob == 1.0", "a value of type dyn"),
        ("body.blob == null", "a value of type dyn"),
        ("'k' in body.blob", "a value of type dyn"),
    ] {
        let err = refusal(&env, src);
        assert!(
            err.contains(construct),
            "`{src}` must be refused naming `{construct}`, got: {err}"
        );
        assert!(
            err.contains("removed: dyn values"),
            "`{src}`: the refusal must cite its README row, got: {err}"
        );
    }
}

/// A `map` macro's result is a list of whatever its step produced — never `list(dyn)`.
#[test]
fn a_map_macro_types_its_result() {
    let env = dyn_env();
    // `list(double)` compares with `x`, a `list(double)`; `list(dyn)` would be refused.
    env.compile("xs.map(x, x + 1.0) == x", &CompileOpts::default())
        .unwrap_or_else(|e| panic!("a map over list(double) types as list(double): {e}"));
    let err = refusal(&env, r#"xs.map(x, x + 1.0) == ["a"]"#);
    assert!(err.contains("list(double)"), "{err}");
}

/// Presence is the one question a derived `unknown` member still answers.
#[test]
fn has_on_an_unknown_member_still_checks() {
    let env = dyn_env();
    env.compile("has(body.blob)", &CompileOpts::default())
        .unwrap_or_else(|e| panic!("`has(body.blob)` must check: {e}"));
    env.compile(
        "has(body.blob) && body.name == 'a'",
        &CompileOpts::default(),
    )
    .unwrap_or_else(|e| panic!("`has(body.blob)` must check beside a use of body: {e}"));
}

/// Assert each spelling is refused by the CHECKER, citing `row`.
fn refused_citing(row: &str, spellings: &[&str]) {
    let env = checker_env();
    for src in spellings {
        let err = refusal(&env, src);
        assert!(
            err.contains(&format!("`{row}`")),
            "`{src}` must be refused citing `{row}`, got: {err}"
        );
    }
}

/// `removed: ordering beyond numbers and strings`
///
/// `<`, `<=`, `>`, `>=` order numbers, strings and durations, and nothing else. Spec CEL also
/// orders bools and bytes; no program this dialect targets asks whether `false < true`, and a byte-wise
/// order over bytes is one more comparison a typed backend would carry for nobody.
#[test]
fn ordering_beyond_numbers_and_strings_is_gone() {
    refused_citing(
        "removed: ordering beyond numbers and strings",
        &[
            "false < true",
            "true >= false",
            "b'a' < b'b'",
            "b'a' <= b'b'",
            "[1] < [2]",
            "{1: 'a'} > {2: 'b'}",
            "null < null",
        ],
    );
    // Gone from the evaluator as well: a bool, a byte string and `null` have no ordering there.
    all_refused(&[
        "false < true",
        "true >= false",
        "b'a' < b'b'",
        "null < null",
    ]);
    // What stays: numbers, strings and durations.
    checks("1 < 2 && 'a' <= 'b' && duration('1s') > duration('0s') && l[0] >= 1.0");
}

/// `removed: logic on non-bools`
///
/// `&&`, `||` and `!` take bools. Spec CEL's `false && 32` is `false` — the short circuit never
/// looks at the number — but a policy that writes a number where a truth value goes has a bug the
/// checker exists to report.
#[test]
fn logic_on_non_bools_is_gone() {
    refused_citing(
        "removed: logic on non-bools",
        &[
            "false && 32",
            "'horses' && false",
            "true || 32",
            "'horses' || true",
            "!0",
            "!s",
        ],
    );
    checks("true && !false || s == 'a'");
}

/// `removed: bytes concatenation`
///
/// `+` concatenates strings and lists and adds numbers and durations. Nothing a policy reads is
/// assembled from byte strings.
#[test]
fn bytes_concatenation_is_gone() {
    refused_citing(
        "removed: bytes concatenation",
        &["b'abc' + b'def' == b'abcdef'", "b'' + b'' == b''"],
    );
    all_refused(&["b'abc' + b'def'"]);
    checks("b'abc' == b'abc'");
}

/// `diverges: undeclared names are compile errors`
///
/// Spec CEL evaluates `x || true` to `true` with `x` unbound: the short circuit absorbs the error.
/// Here the checker refuses the name before anything runs.
#[test]
fn undeclared_names_are_compile_errors() {
    refused_citing(
        "diverges: undeclared names are compile errors",
        &[
            "x || true",
            "true || x",
            "f_unknown(17) || true",
            "a.as() || true",
        ],
    );
}

/// `diverges: equality is homogeneous`
#[test]
fn equality_is_homogeneous() {
    refused_citing(
        "diverges: equality is homogeneous",
        &["['one'] == [2.0, 3.0]", "s != 1.0", "s == true"],
    );
    checks("['one'] == ['two'] && s != 'a'");
}

/// `diverges: duration() takes a string`
#[test]
fn duration_takes_a_string() {
    refused_citing(
        "diverges: duration() takes a string",
        &["duration(duration('1s')) == duration('1s')"],
    );
    all_refused(&["duration(duration('1s'))"]);
    checks("duration('1s') == duration('1000ms')");
}

/// `diverges: nesting is bounded`
///
/// The default `CelLimits::max_depth` is 32 (`added: evaluation bounds`): 31 negations of a literal
/// nest 32 deep and compile; 33 do not.
#[test]
fn nesting_is_bounded() {
    let nested = |n: usize| format!("{}true", "!".repeat(n));
    checks(&nested(31));
    refused_citing("diverges: nesting is bounded", &[nested(33).as_str()]);
}
