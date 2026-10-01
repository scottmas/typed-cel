//! The backend's answers at the edges: operators, absorption, comprehension errors, `has`, keys,
//! scoping, and lazy reads — each PINNED, value and error alike.
//!
//! Every source here type-checks (`fork::compile_any`) and runs on the backend (`FastProgram::new`,
//! `fork::fast_value`); a source the checker refuses has no run to pin. The pins are the backend's
//! answers; they were the tree evaluator's too while it existed, and `tests/generated_golden.rs`
//! pins the generated programs' answers the same way.

#[path = "support/mod.rs"]
mod support;

use typed_cel::CompileOpts;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use support::gen::{same_error, same_outcome};
use support::record;
use typed_cel::fork;
use typed_cel::CelValue as Value;
use typed_cel::FastProgram;
use typed_cel::{CelEnvironment, CelError, CelKey, CelTy, CelValue, ExecutionError, LazyValue};

type Outcome = Result<Value, ExecutionError>;

fn env_of(vars: &[(&str, CelTy)]) -> CelEnvironment {
    let mut env = CelEnvironment::new();
    for (name, ty) in vars {
        env.declare(*name, ty.clone());
    }
    env
}

/// `src` on the backend over `binds`, whose variables `vars` declares.
/// Through the unchecked-presence door: this suite pins what the BACKEND answers, and many of its
/// programs read a missing key on purpose — the absorption tables, the error pins. The checker
/// refuses those reads (proven presence); every other check still applies.
fn run_in(src: &str, binds: &[(&str, Value)], vars: &[(&str, CelTy)]) -> Outcome {
    support::run_unchecked_presence(&env_of(vars), src, binds)
}

fn run(src: &str) -> Outcome {
    run_in(src, &[], &[])
}

/// `src` answers exactly `want`, as `Debug` renders the outcome.
fn pin(src: &str, want: &str) {
    assert_eq!(format!("{:?}", run(src)), want, "`{src}`");
}

fn assert_ok(src: &str, want: Value) {
    let got = run(src);
    assert!(
        matches!(&got, Ok(v) if support::gen::same_value(v, &want)),
        "`{src}`: want Ok({want:?}), got {got:?}"
    );
}

fn assert_err(src: &str, want: ExecutionError) {
    let got = run(src);
    assert!(
        matches!(&got, Err(e) if same_error(e, &want)),
        "`{src}`: want Err({want:?}), got {got:?}"
    );
}

fn is_no_such_key(src: &str) {
    let got = run(src);
    assert!(
        matches!(got, Err(ExecutionError::NoSuchKey(_))),
        "`{src}`: want a missing key, got {got:?}"
    );
}

#[test]
fn fast_arithmetic() {
    assert_ok("1 + 2 * 3", Value::Num(7.0));
}

#[test]
fn every_operator_answers_as_pinned() {
    let pins = [
        // Add
        ("1 + 2", "Ok(Int(3))"),
        ("1.5 + 2.25", "Ok(Float(3.75))"),
        ("'a' + 'b'", "Ok(String(\"ab\"))"),
        ("[1] + [2]", "Ok(List([Int(1), Int(2)]))"),
        ("1 + 1.0", "Ok(Int(2))"),
        ("9223372036854775807 + 1", "Ok(UInt(9223372036854775808))"),
        // Sub
        ("5 - 7", "Ok(Int(-2))"),
        ("5.5 - 0.5", "Ok(Int(5))"),
        (
            "-9223372036854775807 - 2",
            "Err(Overflow(\"sub\", Int(-9223372036854775807), Int(2)))",
        ),
        // Mul
        ("6 * 7", "Ok(Int(42))"),
        ("1.5 * 2.0", "Ok(Int(3))"),
        ("9223372036854775807 * 2", "Ok(UInt(18446744073709551614))"),
        (
            "9223372036854775807 * 3",
            "Err(Overflow(\"mul\", Int(9223372036854775807), Int(3)))",
        ),
        // Div
        ("7 / 2", "Ok(Float(3.5))"),
        ("7.0 / 2.0", "Ok(Float(3.5))"),
        ("5.0 / 0.0", "Ok(Float(inf))"),
        ("0.0 / 0.0", "Ok(Float(NaN))"),
        ("-5.0 / 0.0", "Ok(Float(-inf))"),
        ("1 / 0", "Ok(Float(inf))"),
        // Eq / Ne
        ("1 == 1", "Ok(Bool(true))"),
        ("1 == 1.0", "Ok(Bool(true))"),
        ("'a' == 'a'", "Ok(Bool(true))"),
        ("[1, 2] == [1, 2]", "Ok(Bool(true))"),
        ("{'a': 1} == {'a': 1}", "Ok(Bool(true))"),
        ("null == null", "Ok(Bool(true))"),
        ("1 != 2", "Ok(Bool(true))"),
        ("b'a' != b'a'", "Ok(Bool(false))"),
        ("[1] != [1, 2]", "Ok(Bool(true))"),
        // Lt / Le / Gt / Ge
        ("1 < 2", "Ok(Bool(true))"),
        ("2.0 <= 2.0", "Ok(Bool(true))"),
        ("'b' > 'a'", "Ok(Bool(true))"),
        ("1 < 2.5", "Ok(Bool(true))"),
        ("3 >= 3", "Ok(Bool(true))"),
        ("3 > 3", "Ok(Bool(false))"),
        // In
        ("2 in [1, 2]", "Ok(Bool(true))"),
        ("3 in [1, 2]", "Ok(Bool(false))"),
        ("'a' in {'a': 1}", "Ok(Bool(true))"),
        // Unary
        ("-1", "Ok(Int(-1))"),
        ("-1.5", "Ok(Float(-1.5))"),
        (
            "-(-9223372036854775807 - 1)",
            "Ok(UInt(9223372036854775808))",
        ),
        ("!true", "Ok(Bool(false))"),
        ("!false", "Ok(Bool(true))"),
    ];
    assert!(pins.len() >= 40, "{} sources", pins.len());
    for (src, want) in pins {
        pin(src, want);
    }
}

/// The checker refuses each of these (a plain type error, an undeclared name), so none reaches the
/// backend. The removals with a dialect row
/// of their own — logic on non-bools, bytes `+`, `%`, ordering and heterogeneous equality — are
/// pinned in `tests/dialect.rs`; these are plain type errors.
#[test]
fn a_type_error_never_reaches_the_backend() {
    for src in [
        "'a' - 'b'",
        "[1] - [1]",
        "'a' * 2",
        "-'a'",
        "{'a': 1} + 1",
        "null + 1",
        "1 in 1",
        "'a' in 'abc'",
        "size(1, 2)",
        "[1, 2]['a']",
        "1.all(x, true)",
        "missing",
        "1.missing()",
    ] {
        assert!(
            fork::compile_any(&CelEnvironment::new(), src).is_err(),
            "`{src}` must be refused by the checker"
        );
    }
}

#[test]
fn errors_are_pinned() {
    pin("{}.a", "Err(NoSuchKey(\"a\"))");
    pin("{'a': 1}.b", "Err(NoSuchKey(\"b\"))");
    pin("[1][5]", "Err(IndexOutOfBounds(Int(5)))");
    pin("[1][-1]", "Err(IndexOutOfBounds(Int(-1)))");
    pin("{null: true}", "Err(UnsupportedKeyType(Null))");
    assert_err("{}.a", ExecutionError::NoSuchKey(Arc::new("a".to_string())));
    assert_err(
        "{null: true}",
        ExecutionError::UnsupportedKeyType(Value::Null),
    );
}

/// `m` is `{'a': 1}`, so `m['x']` and `m['y']` are missing keys: a bool operand that is an
/// error, which is the only operand besides `true` and `false` a checked `&&`/`||` can have.
fn absorbing(src: &str) -> Outcome {
    let ctx: Vec<(&str, Value)> = vec![(
        "m",
        (Value::record([(CelKey::new("a"), Value::Num(1.0))])).into(),
    )];
    run_in(src, &ctx, &[("m", CelTy::map(CelTy::Str, CelTy::Num))])
}

fn no_such_key(key: &str) -> ExecutionError {
    ExecutionError::NoSuchKey(Arc::new(key.to_string()))
}

fn assert_absorbs(src: &str, want: Outcome) {
    let got = absorbing(src);
    assert!(
        same_outcome(&got, &want),
        "`{src}`: want {want:?}, got {got:?}"
    );
}

#[test]
fn or_absorption_table() {
    let t = || Ok(Value::Bool(true));
    let f = || Ok(Value::Bool(false));
    assert_absorbs("true || true", t());
    assert_absorbs("true || false", t());
    assert_absorbs("true || (m['y'] == 1.0)", t());
    assert_absorbs("false || true", t());
    assert_absorbs("false || false", f());
    assert_absorbs("false || (m['y'] == 1.0)", Err(no_such_key("y")));
    assert_absorbs("(m['x'] == 1.0) || true", t());
    assert_absorbs("(m['x'] == 1.0) || false", Err(no_such_key("x")));
    // When both sides fail, the RIGHT operand's error is the one reported.
    assert_absorbs("(m['x'] == 1.0) || (m['y'] == 1.0)", Err(no_such_key("y")));
}

#[test]
fn and_absorption_table() {
    let t = || Ok(Value::Bool(true));
    let f = || Ok(Value::Bool(false));
    assert_absorbs("true && true", t());
    assert_absorbs("true && false", f());
    assert_absorbs("true && (m['y'] == 1.0)", Err(no_such_key("y")));
    assert_absorbs("false && true", f());
    assert_absorbs("false && false", f());
    assert_absorbs("false && (m['y'] == 1.0)", f());
    assert_absorbs("(m['x'] == 1.0) && false", f());
    assert_absorbs("(m['x'] == 1.0) && true", Err(no_such_key("x")));
    assert_absorbs("(m['x'] == 1.0) && (m['y'] == 1.0)", Err(no_such_key("y")));
}

#[test]
fn comprehension_errors_are_absorbed_only_by_a_deciding_value() {
    // `{1: true, 3: false}[e]` is true at 1, a missing key at 2 and false at 3 — an error with a
    // deciding value on either side of it. (Division by zero was this test's error once; IEEE
    // division has none.)
    assert_ok(
        "[1, 2, 3].all(e, {1: true, 3: false}[e])",
        Value::Bool(false),
    );
    is_no_such_key("[2, 1].all(e, {1: true, 3: false}[e])");
    assert_ok(
        "[2, 1].exists(e, {1: true, 3: false}[e])",
        Value::Bool(true),
    );
    assert_err(
        "[1, 0].map(x, {1: 1}[x])",
        ExecutionError::NoSuchKey(Arc::new("0".to_string())),
    );
    // exists_one's step never absorbs.
    pin(
        "[0, 1].exists_one(x, {1: 1}[x] == 1)",
        "Err(NoSuchKey(\"0\"))",
    );
    pin(
        "[1, 2, 3].filter(x, {1: 1, 3: 3}[x] > 0)",
        "Err(NoSuchKey(\"2\"))",
    );
    pin("[1, 2].map(x, x > 1, x * 2)", "Ok(List([Int(4)]))");
    pin("[].all(x, {}.a == 1)", "Ok(Bool(true))");
    pin("[1, 2, 3].exists(e, e == 2)", "Ok(Bool(true))");
}

#[test]
fn a_nested_loop_error_unwinds_to_the_outer_step() {
    is_no_such_key("[[1, 0], [1]].all(xs, xs.all(x, {1: true}[x]))");
    assert_ok(
        "[[1, 0], [1]].exists(xs, xs.all(x, {1: true}[x]))",
        Value::Bool(true),
    );
}

#[test]
fn has_on_maps_and_non_maps() {
    assert_ok("has({'a': 1}.a)", Value::Bool(true));
    assert_ok("has({'a': 1}.b)", Value::Bool(false));
    pin(
        "has([1].a)",
        "Err(UnexpectedType { got: \"string\", want: \"double\" })",
    );
    pin("has(1.a)", "Err(NoSuchOverload)");
}

#[test]
fn duplicate_map_keys_keep_the_last() {
    pin("{'a': 1, 'a': 2}['a']", "Ok(Int(2))");
}

#[test]
fn comprehension_variables_shadow_and_restore() {
    let ctx: Vec<(&str, Value)> = vec![("x", (Value::Num(10.0)).into())];
    let got = run_in(
        "x + [1, 2].map(x, x * 2)[1] + x",
        &ctx,
        &[("x", CelTy::Num)],
    );
    assert!(matches!(got, Ok(Value::Int(24))), "{got:?}");
}

// ---- the public API, over lazy values ----

fn no_such(key: &str) -> CelError {
    CelError::NoSuchMember {
        key: key.to_string(),
    }
}

/// `r`: `a` is a number, `t` answers `NoSuchMember`. Counts every member resolution.
#[derive(Debug)]
struct CountingRecord {
    reads: Arc<AtomicUsize>,
}

impl LazyValue for CountingRecord {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        self.reads.fetch_add(1, Ordering::SeqCst);
        match name {
            "a" => Ok(CelValue::Num(1.0)),
            other => Err(no_such(other)),
        }
    }
}

/// `m`: keys `a`, `b`, numbers behind them. Counts member reads and `keys()` calls.
#[derive(Debug)]
struct CountingMap {
    keys: Vec<CelKey>,
    reads: Arc<AtomicUsize>,
    iterations: Arc<AtomicUsize>,
}

impl LazyValue for CountingMap {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        self.reads.fetch_add(1, Ordering::SeqCst);
        let ix = self
            .keys
            .iter()
            .position(|k| k.as_str() == name)
            .ok_or_else(|| no_such(name))?;
        Ok(CelValue::Num(ix as f64))
    }

    fn keys(&self) -> Option<Box<dyn Iterator<Item = &CelKey> + '_>> {
        self.iterations.fetch_add(1, Ordering::SeqCst);
        Some(Box::new(self.keys.iter()))
    }
}

fn lazy_env() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.declare("r", record("r", &[("a", CelTy::Num), ("t", CelTy::Str)]));
    env.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    env
}

/// What one evaluation observed: its answer (as comparable text) and the three counters.
#[derive(Debug, PartialEq)]
struct Observed {
    answer: (bool, Option<bool>, String),
    record_reads: usize,
    map_reads: usize,
    map_iterations: usize,
}

fn observe(
    env: &CelEnvironment,
    run: &dyn Fn(&typed_cel::CelActivation) -> Result<bool, CelError>,
) -> Observed {
    let record_reads = Arc::new(AtomicUsize::new(0));
    let map_reads = Arc::new(AtomicUsize::new(0));
    let map_iterations = Arc::new(AtomicUsize::new(0));
    let mut act = env.activation();
    act.bind_lazy(
        "r",
        CelValue::Lazy(Arc::new(CountingRecord {
            reads: Arc::clone(&record_reads),
        })),
    )
    .unwrap();
    act.bind_lazy(
        "m",
        CelValue::Lazy(Arc::new(CountingMap {
            keys: vec![CelKey::new("a"), CelKey::new("b")],
            reads: Arc::clone(&map_reads),
            iterations: Arc::clone(&map_iterations),
        })),
    )
    .unwrap();
    let out = run(&act);
    Observed {
        answer: (
            out.is_ok(),
            out.as_ref().ok().copied(),
            out.as_ref()
                .err()
                .map(|e| e.to_string())
                .unwrap_or_default(),
        ),
        record_reads: record_reads.load(Ordering::SeqCst),
        map_reads: map_reads.load(Ordering::SeqCst),
        map_iterations: map_iterations.load(Ordering::SeqCst),
    }
}

/// What `src` observes through the PUBLIC API (`CelProgram::evaluate`), on a fresh activation.
fn observe_one(src: &str) -> Observed {
    let env = lazy_env();
    let program = env
        .compile(src, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("{src}: {e}"));
    observe(&env, &|act| program.evaluate(act))
}

#[test]
fn lazy_reads_are_counted() {
    let e = observe_one("false && r.a == 1.0");
    assert_eq!(e.record_reads, 0);
    // The left errors through the lazy `NoSuchMember`, is captured, and the right is still read.
    let e = observe_one("r.t == 'x' || r.a == 1.0");
    assert_eq!(e.record_reads, 2);
    assert_eq!(e.answer.1, Some(true));
    // A field is read once per decision, however often the program names it.
    let e = observe_one("r.a + r.a > 0.0");
    assert_eq!(e.record_reads, 1);
    let e = observe_one("m.exists(k, k == 'b')");
    assert!(e.map_iterations > 0, "{e:?}");
    let e = observe_one("m.exists(k, m[k] > 0.0)");
    assert_eq!(e.answer, (true, Some(true), String::new()));
    let e = observe_one("m.all(k, m[k] >= 0.0) && r.a == 1.0");
    assert_eq!(e.answer, (true, Some(true), String::new()));
}

/// A field is read once per decision — but only a read that SUCCEEDED is kept. A failed read is
/// asked again where the program names the field again, and fails there again; a read the program
/// never reaches (a loop over nothing) is never made, so its failure cannot fail the decision.
#[test]
fn only_a_successful_read_is_reused() {
    // `r.t` is missing: each `||` absorbs its failure (`r.a == 1.0`, read once), and each asks.
    let e = observe_one("(r.t == 'x' || r.a == 1.0) && (r.t == 'y' || r.a == 1.0)");
    assert_eq!(e.answer, (true, Some(true), String::new()));
    assert_eq!(e.record_reads, 3);
    // A loop over nothing reads nothing in its body.
    let e = observe_one("m.filter(k, false).all(k, r.t == 'x')");
    assert_eq!(e.answer, (true, Some(true), String::new()));
    assert_eq!(e.record_reads, 0);
    // A present field in a loop body: read on the first element, reused after.
    let e = observe_one("m.all(k, r.a == 1.0)");
    assert_eq!(e.answer, (true, Some(true), String::new()));
    assert_eq!(e.record_reads, 1);
}

#[test]
fn lazy_answers_are_pinned() {
    let e = observe_one("r.a > 0.0");
    assert_eq!(e.answer, (true, Some(true), String::new()));
    let e = observe_one("r.t == 'x'");
    assert!(!e.answer.0);
    assert!(
        e.answer
            .2
            .contains("could not be evaluated: No such key: t"),
        "{}",
        e.answer.2
    );
    // `has()` on a lazy is an existence question in both, never the member's value.
    let e = observe_one("has(r.a)");
    assert_eq!(e.answer, (true, Some(true), String::new()));
}

// ---- fused string comparisons keep `&&`/`||` absorption --------------------------------------

/// Three string fields, each present with a value or absent, answered through `Facts`.
struct Three<'a> {
    fields: Vec<&'a str>,
    vals: [Option<&'a str>; 3],
}

impl typed_cel::Facts for Three<'_> {
    fn str(&self, f: typed_cel::FieldId) -> Option<&str> {
        let slot = ["a", "b", "c"]
            .iter()
            .position(|n| *n == self.fields[f.index()])
            .expect("a field of req");
        self.vals[slot]
    }
    fn bool(&self, _: typed_cel::FieldId) -> Option<bool> {
        None
    }
    fn num(&self, _: typed_cel::FieldId) -> Option<f64> {
        None
    }
    fn has(&self, _: typed_cel::FieldId) -> bool {
        true
    }
}

/// One operand's answer under CEL: its bool, or the field whose missing read it raises.
type Operand = Result<bool, &'static str>;

/// `&&` (`or == false`) / `||` (`or == true`) over two operands, as CEL defines it: a deciding
/// value absorbs an error on either side; two errors report the RIGHT one.
fn logic(or: bool, l: Operand, r: Operand) -> Operand {
    match (l, r) {
        (Ok(x), _) if x == or => Ok(or),
        (Ok(_), r) => r,
        (Err(_), Ok(y)) if y == or => Ok(or),
        (Err(e), Ok(_)) => Err(e),
        (Err(_), Err(e)) => Err(e),
    }
}

/// The message the backend raises for `field`'s missing read, from a program that reads only it
/// in value position (no fusion there).
fn missing_message(env: &CelEnvironment, field: &str) -> String {
    let p = env
        .compile(&format!("req.{field} == 'x'"), &CompileOpts::default())
        .expect("compiles");
    let fast = typed_cel::FastProgram::new(&p).expect("lowers");
    let fields: Vec<String> = fast
        .fields()
        .iter()
        .map(|f| f.segments().collect())
        .collect();
    let facts = Three {
        fields: fields.iter().map(String::as_str).collect(),
        vals: [None; 3],
    };
    let err = fast
        .decide(&facts, &mut typed_cel::FastScratch::default())
        .expect_err("a missing field raises");
    let text = err.to_string();
    text[text
        .find("could not be evaluated")
        .expect("an evaluation error")..]
        .to_string()
}

#[test]
fn fused_equality_keeps_and_absorption() {
    let env = env_of(&[(
        "req",
        record(
            "req",
            &[("a", CelTy::Str), ("b", CelTy::Str), ("c", CelTy::Str)],
        ),
    )]);
    let msg: std::collections::HashMap<&str, String> = ["a", "b", "c"]
        .into_iter()
        .map(|f| (f, missing_message(&env, f)))
        .collect();
    let mut fused_seen = std::collections::BTreeSet::new();
    let mut checked = 0;
    for ne in [false, true] {
        let op = if ne { "!=" } else { "==" };
        let ab = format!("req.a {op} req.b");
        let ck = format!("req.c {op} 'x'");
        for or in [false, true] {
            let join = if or { "||" } else { "&&" };
            for (src, ab_first) in [
                (format!("{ab} {join} {ck}"), true),
                (format!("{ck} {join} {ab}"), false),
            ] {
                let p = env
                    .compile(&src, &CompileOpts::default())
                    .expect("compiles");
                let fast = typed_cel::FastProgram::new(&p).expect("lowers");
                fused_seen.extend(
                    fast.op_names()
                        .into_iter()
                        .filter(|n| n.starts_with("CondEqF")),
                );
                let fields: Vec<String> = fast
                    .fields()
                    .iter()
                    .map(|f| f.segments().collect())
                    .collect();
                for a in [Some("x"), Some("y"), None] {
                    for c in [Some("x"), Some("z"), None] {
                        let b = Some("x");
                        let ab_v: Operand = match a {
                            None => Err("a"),
                            Some(a) => Ok((a == "x") != ne),
                        };
                        let ck_v: Operand = match c {
                            None => Err("c"),
                            Some(c) => Ok((c == "x") != ne),
                        };
                        let want = if ab_first {
                            logic(or, ab_v, ck_v)
                        } else {
                            logic(or, ck_v, ab_v)
                        };
                        let facts = Three {
                            fields: fields.iter().map(String::as_str).collect(),
                            vals: [a, b, c],
                        };
                        let got = fast.decide(&facts, &mut typed_cel::FastScratch::default());
                        match (&want, &got) {
                            (Ok(w), Ok(g)) => assert_eq!(w, g, "{src} with a={a:?} c={c:?}"),
                            (Err(field), Err(e)) => assert!(
                                e.to_string().ends_with(&msg[field]),
                                "{src} with a={a:?} c={c:?}: want `{field}`'s error ({}), got {e}",
                                msg[field]
                            ),
                            _ => panic!("{src} with a={a:?} c={c:?}: want {want:?}, got {got:?}"),
                        }
                        checked += 1;
                    }
                }
            }
        }
    }
    assert_eq!(checked, 72);
    assert_eq!(
        fused_seen.into_iter().collect::<Vec<_>>(),
        ["CondEqFF", "CondEqFK"],
        "the programs lower through the fused ops, so this table tests them"
    );
}

/// A string test against `b + c` never builds the concatenation (`StrOp2`). Held against the same
/// test over `[b + c][0]`, which builds it, for every triple of strings drawn from a set with
/// empty, overlapping and multi-byte members — and with roots left unbound, so a failing read
/// must fail at the same operand, in the same order.
#[test]
fn a_concatenation_tested_unbuilt_answers_as_built() {
    use typed_cel::FastProgram;
    const FORMS: &[(&str, &str)] = &[
        ("a.startsWith(b + c)", "a.startsWith([b + c][0])"),
        ("a.endsWith(b + c)", "a.endsWith([b + c][0])"),
        ("a == b + c", "a == [b + c][0]"),
        ("b + c == a", "[b + c][0] == a"),
        ("a != b + c", "a != [b + c][0]"),
        ("(b + c).startsWith(a)", "[b + c][0].startsWith(a)"),
        ("(b + c).endsWith(a)", "[b + c][0].endsWith(a)"),
    ];
    const STRS: &[&str] = &["", "a", "b", "ab", "ba", "é", "aé", "éa", "abé"];
    let mut env = CelEnvironment::new();
    for root in ["a", "b", "c"] {
        env.declare(root, CelTy::Str);
    }
    let lower = |src: &str| {
        let p = fork::compile_any_unchecked_presence(&env, src)
            .unwrap_or_else(|e| panic!("{src}: {e}"));
        FastProgram::new(&p).unwrap_or_else(|e| panic!("{src}: {e}"))
    };
    let answer = |p: &FastProgram, binds: &[(&str, &str)]| {
        let mut act = env.runtime().activation();
        for (name, v) in binds {
            act.bind_fact(name, Value::Str((*v).into()));
        }
        format!("{:?}", fork::fast_value(p, &act))
    };
    let (mut compared, mut mismatches) = (0, Vec::new());
    for (src, reference) in FORMS {
        let (got, want) = (lower(src), lower(reference));
        assert!(
            got.op_names().contains(&"StrOp2") && !got.op_names().contains(&"Arith"),
            "`{src}` still builds its concatenation: {:?}",
            got.op_names()
        );
        let mut cases: Vec<Vec<(&str, &str)>> = Vec::new();
        for a in STRS {
            for b in STRS {
                for c in STRS {
                    cases.push(vec![("a", a), ("b", b), ("c", c)]);
                }
            }
        }
        // Every subset of the roots unbound.
        for mask in 0..7u8 {
            let binds = [("a", "ab"), ("b", "a"), ("c", "b")];
            cases.push(
                binds
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| mask & (1 << i) != 0)
                    .map(|(_, b)| *b)
                    .collect(),
            );
        }
        for binds in &cases {
            compared += 1;
            let (g, w) = (answer(&got, binds), answer(&want, binds));
            if g != w {
                mismatches.push(format!("`{src}` over {binds:?}: {g} vs built {w}"));
            }
        }
    }
    assert!(
        mismatches.is_empty(),
        "{} of {compared} differ:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// A list or map literal of fields that is only searched or indexed by a constant is never built:
/// `x in [a, b]` is an `==` chain, `[a, b].exists(v, P)` runs `P` per element register, and
/// `{"k": v}["k"]` is `v`. Held against the same question over a collection that IS built
/// (`[…] + []`, a map inside a list), for every assignment of three strings to the roots and every
/// subset of them left unbound — so each element still runs, and fails, where it did.
#[test]
fn a_literal_collection_searched_unbuilt_answers_as_built() {
    use typed_cel::FastProgram;
    const FORMS: &[(&str, &str)] = &[
        ("x in [a, b, c]", "x in ([a, b, c] + [])"),
        (r#"x in [a, "q", c]"#, r#"x in ([a, "q", c] + [])"#),
        (
            "[a, b, c].exists(v, v == x)",
            "([a, b, c] + []).exists(v, v == x)",
        ),
        (
            "[a, b, c].all(v, v != x)",
            "([a, b, c] + []).all(v, v != x)",
        ),
        (
            "[a, b, c].exists_one(v, v == x)",
            "([a, b, c] + []).exists_one(v, v == x)",
        ),
        (
            r#"[a, b].exists(v, {"p": true, "q": false}[v])"#,
            r#"([a, b] + []).exists(v, {"p": true, "q": false}[v])"#,
        ),
        (
            r#"[a, b].all(v, {"p": true, "q": false}[v])"#,
            r#"([a, b] + []).all(v, {"p": true, "q": false}[v])"#,
        ),
        (
            r#"{"k": a, "j": b, "k": c}["k"] == x"#,
            r#"[{"k": a, "j": b, "k": c}][0]["k"] == x"#,
        ),
        (
            r#"{"k": a, "j": b}["j"] == x"#,
            r#"[{"k": a, "j": b}][0]["j"] == x"#,
        ),
    ];
    const STRS: &[&str] = &["", "p", "q"];
    let mut env = CelEnvironment::new();
    for root in ["a", "b", "c", "x"] {
        env.declare(root, CelTy::Str);
    }
    let lower = |src: &str| {
        let p = fork::compile_any_unchecked_presence(&env, src)
            .unwrap_or_else(|e| panic!("{src}: {e}"));
        FastProgram::new(&p).unwrap_or_else(|e| panic!("{src}: {e}"))
    };
    let answer = |p: &FastProgram, binds: &[(&str, &str)]| {
        let mut act = env.runtime().activation();
        for (name, v) in binds {
            act.bind_fact(name, Value::Str((*v).into()));
        }
        format!("{:?}", fork::fast_value(p, &act))
    };
    let mut cases: Vec<Vec<(&str, &str)>> = Vec::new();
    for a in STRS {
        for b in STRS {
            for c in STRS {
                for x in STRS {
                    cases.push(vec![("a", a), ("b", b), ("c", c), ("x", x)]);
                }
            }
        }
    }
    for mask in 0..15u8 {
        let binds = [("a", "p"), ("b", "q"), ("c", "p"), ("x", "p")];
        cases.push(
            binds
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, b)| *b)
                .collect(),
        );
    }
    let (mut compared, mut mismatches) = (0, Vec::new());
    for (src, reference) in FORMS {
        let (got, want) = (lower(src), lower(reference));
        assert!(
            !got.op_names()
                .iter()
                .any(|o| matches!(*o, "MakeList" | "MakeMap" | "In" | "IterInit")),
            "`{src}` still builds its collection: {:?}",
            got.op_names()
        );
        for binds in &cases {
            compared += 1;
            let (g, w) = (answer(&got, binds), answer(&want, binds));
            if g != w {
                mismatches.push(format!("`{src}` over {binds:?}: {g} vs built {w}"));
            }
        }
    }
    assert!(
        mismatches.is_empty(),
        "{} of {compared} differ:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// Membership in numbers known at compile time — `x in [..]`, `[..].exists(v, v == x)`, a chain of
/// `x == k` — is one `NumSet` lookup, and a known map's keys are a string matcher: each answers as
/// the same question over a collection the program builds and searches, for a needle that is
/// `-0.0` against a `0.0`, NaN (equal to nothing), a value no element has, or unbound.
#[test]
fn a_known_set_answers_as_searching_it() {
    use typed_cel::FastProgram;
    const FORMS: &[(&str, &str)] = &[
        (
            "x in [0.0, 1.0, 2.5, 1e300]",
            "x in ([0.0, 1.0, 2.5, 1e300] + [])",
        ),
        ("x in [-0.0, 7.0]", "x in ([-0.0, 7.0] + [])"),
        (
            "[0.0, 1.0, 2.5].exists(v, v == x)",
            "([0.0, 1.0, 2.5] + []).exists(v, v == x)",
        ),
        (
            "[0.0, 1.0, 2.5].exists(v, x == v)",
            "([0.0, 1.0, 2.5] + []).exists(v, x == v)",
        ),
        (
            "x == 0.0 || x == 1.0 || x == 2.5",
            "x == 0.0 || (x == 1.0 || (x == 2.5 || false))",
        ),
        (
            r#"{"a": 1.0, "b": 2.0}.exists(k, k == s)"#,
            r#"[{"a": 1.0, "b": 2.0}][0].exists(k, k == s)"#,
        ),
    ];
    let mut env = CelEnvironment::new();
    env.declare("x", CelTy::Num);
    env.declare("s", CelTy::Str);
    let lower = |src: &str| {
        let p = fork::compile_any_unchecked_presence(&env, src)
            .unwrap_or_else(|e| panic!("{src}: {e}"));
        FastProgram::new(&p).unwrap_or_else(|e| panic!("{src}: {e}"))
    };
    let answer = |p: &FastProgram, x: Option<f64>, s: Option<&str>| {
        let mut act = env.runtime().activation();
        if let Some(x) = x {
            act.bind_fact("x", Value::Num(x));
        }
        if let Some(s) = s {
            act.bind_fact("s", Value::Str(s.into()));
        }
        format!("{:?}", fork::fast_value(p, &act))
    };
    let xs = [
        Some(0.0),
        Some(-0.0),
        Some(1.0),
        Some(2.5),
        Some(7.0),
        Some(1e300),
        Some(f64::NAN),
        Some(3.0),
        None,
    ];
    let ss = [Some("a"), Some("b"), Some("c"), Some(""), None];
    let (mut compared, mut mismatches) = (0, Vec::new());
    for (src, reference) in FORMS {
        let (got, want) = (lower(src), lower(reference));
        assert!(
            got.op_names()
                .iter()
                .any(|o| matches!(*o, "NumIn" | "Match")),
            "`{src}` is not a set lookup: {:?}",
            got.op_names()
        );
        for x in xs {
            for s in ss {
                compared += 1;
                let (g, w) = (answer(&got, x, s), answer(&want, x, s));
                if g != w {
                    mismatches.push(format!("`{src}` x={x:?} s={s:?}: {g} vs searched {w}"));
                }
            }
        }
    }
    assert!(
        mismatches.is_empty(),
        "{} of {compared} differ:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// A member selected from a BOUND value — a record, a map, one with an optional member absent —
/// answers as pinned, in a loop and out of one. (A lazy view's member: `tests/lazy.rs`.)
#[test]
fn a_selected_member_answers_as_before() {
    let item = support::record_opt(
        "item",
        &[
            ("id", CelTy::Str),
            ("qty", CelTy::Num),
            ("note", CelTy::Str),
        ],
        &["note"],
    );
    let vars = [
        ("items", CelTy::list(item)),
        ("ms", CelTy::list(CelTy::map(CelTy::Str, CelTy::Num))),
    ];
    let rec = |id: &str, qty: f64, note: Option<&str>| {
        let mut f = vec![
            (CelKey::new("id"), Value::Str(id.into())),
            (CelKey::new("qty"), Value::Num(qty)),
        ];
        if let Some(n) = note {
            f.push((CelKey::new("note"), Value::Str(n.into())));
        }
        Value::record(f)
    };
    let items = Value::list([rec("a", 1.0, Some("x")), rec("b", 2.0, None)]);
    let ms = Value::list([
        Value::record([(CelKey::new("a"), Value::Num(2.0))]),
        Value::record([]),
    ]);
    let binds = [("items", items), ("ms", ms)];
    const PINNED: &[(&str, &str)] = &[
        ("items[0].qty > 0.0", "Ok(Bool(true))"),
        ("items[1].id == \"b\"", "Ok(Bool(true))"),
        ("items[1].note == \"x\"", "Err(NoSuchKey(\"note\"))"),
        ("items.exists(i, i.qty > 1.5)", "Ok(Bool(true))"),
        (
            "items.all(i, i.id != \"z\" && i.qty > 0.0)",
            "Ok(Bool(true))",
        ),
        ("items.exists(i, i.note == \"x\")", "Ok(Bool(true))"),
        ("items.all(i, i.note == \"x\")", "Err(NoSuchKey(\"note\"))"),
        ("ms[0].a > 1.0", "Ok(Bool(true))"),
        ("ms[1].a > 1.0", "Err(NoSuchKey(\"a\"))"),
        ("ms.exists(m, m.a > 1.0)", "Ok(Bool(true))"),
        ("ms.all(m, m.a > 1.0)", "Err(NoSuchKey(\"a\"))"),
        ("size(items.map(i, i.id)) == 2.0", "Ok(Bool(true))"),
    ];
    let mut wrong = Vec::new();
    for (src, want) in PINNED {
        // Unchecked presence: several rows read an absent member on purpose — what the backend
        // answers when a value breaks its type's promise (the checker refuses these programs).
        let got = format!(
            "{:?}",
            support::run_unchecked_presence(&env_of(&vars), src, &binds)
        );
        if got != *want {
            wrong.push(format!("        ({src:?}, {got:?}),"));
        }
    }
    assert!(wrong.is_empty(), "answers moved:\n{}", wrong.join("\n"));
}

/// Arithmetic answers as pinned: numbers (IEEE: a zero divisor is an infinity or NaN, never an
/// error), a constant on either side of the non-commutative operators, strings and durations,
/// in a loop and out of one.
#[test]
fn arithmetic_answers_as_before() {
    let vars = [
        ("n", CelTy::Num),
        ("z", CelTy::Num),
        ("s", CelTy::Str),
        ("d", CelTy::Duration),
        ("xs", CelTy::list(CelTy::Num)),
    ];
    let binds = [
        ("n", Value::Num(4.0)),
        ("z", Value::Num(0.0)),
        ("s", Value::Str("ab".into())),
        (
            "d",
            Value::Duration(typed_cel::CelDuration::from_millis(1500)),
        ),
        (
            "xs",
            Value::list([Value::Num(1.0), Value::Num(f64::NAN), Value::Num(-2.0)]),
        ),
    ];
    const PINNED: &[(&str, &str)] = &[
        ("n + 1.0 == 5.0", "Ok(Bool(true))"),
        ("n - 1.0 == 3.0", "Ok(Bool(true))"),
        ("1.0 - n == -3.0", "Ok(Bool(true))"),
        ("n * 2.5 == 10.0", "Ok(Bool(true))"),
        ("n / 8.0 == 0.5", "Ok(Bool(true))"),
        ("8.0 / n == 2.0", "Ok(Bool(true))"),
        ("1.0 / z > 1000000.0", "Ok(Bool(true))"),
        ("-1.0 / z < 0.0", "Ok(Bool(true))"),
        ("z / z == z / z", "Ok(Bool(false))"),
        ("n * n - n / 2.0 == 14.0", "Ok(Bool(true))"),
        ("s + \"c\" == \"abc\"", "Ok(Bool(true))"),
        ("\"x\" + s == \"xab\"", "Ok(Bool(true))"),
        ("d + duration(\"1s\") > duration(\"2s\")", "Ok(Bool(true))"),
        ("d - duration(\"1s\") < duration(\"1s\")", "Ok(Bool(true))"),
        ("xs.exists(x, x * 2.0 > 1.0)", "Ok(Bool(true))"),
        ("xs.all(x, 10.0 - x > 0.0)", "Err(NoSuchOverload)"),
        ("size(xs.map(x, x / 2.0)) == 3.0", "Ok(Bool(true))"),
        ("xs.map(x, x * 2.0)[0] == 2.0", "Ok(Bool(true))"),
        (
            "xs.filter(x, x + 1.0 > 0.0) == [1.0]",
            "Err(NoSuchOverload)",
        ),
    ];
    let mut wrong = Vec::new();
    for (src, want) in PINNED {
        let got = format!("{:?}", run_in(src, &binds, &vars));
        if got != *want {
            wrong.push(format!("        ({src:?}, {got:?}),"));
        }
    }
    assert!(wrong.is_empty(), "answers moved:\n{}", wrong.join("\n"));
}

/// A literal regex is compiled once and its error kept for where `matches` runs — never raised
/// by a loop that tests no element — and `in` over a bound list answers as pinned.
#[test]
fn a_literal_pattern_and_a_bound_list_search_answer_as_before() {
    let vars = [
        ("s", CelTy::Str),
        ("n", CelTy::Num),
        ("nan", CelTy::Num),
        ("ss", CelTy::list(CelTy::Str)),
        ("none", CelTy::list(CelTy::Str)),
        ("xs", CelTy::list(CelTy::Num)),
    ];
    let binds = [
        ("s", Value::Str("ab".into())),
        ("n", Value::Num(2.0)),
        ("nan", Value::Num(f64::NAN)),
        (
            "ss",
            Value::list([Value::Str("x".into()), Value::Str("ab".into())]),
        ),
        ("none", Value::list([])),
        (
            "xs",
            Value::list([Value::Num(1.0), Value::Num(f64::NAN), Value::Num(2.0)]),
        ),
    ];
    const PINNED: &[(&str, &str)] = &[
        ("s.matches(\"^a\")", "Ok(Bool(true))"),
        ("s.matches(\"(\")", "Err(FunctionError { function: \"matches\", message: \"'(' not a valid regex:\\nregex parse error:\\n    (\\n    ^\\nerror: unclosed group\" })"),
        ("ss.exists(x, x.matches(\"^a\"))", "Ok(Bool(true))"),
        ("ss.all(x, x.matches(\"^a\"))", "Ok(Bool(false))"),
        ("ss.exists(x, x.matches(\"(\"))", "Err(FunctionError { function: \"matches\", message: \"'(' not a valid regex:\\nregex parse error:\\n    (\\n    ^\\nerror: unclosed group\" })"),
        ("none.exists(x, x.matches(\"(\"))", "Ok(Bool(false))"),
        ("s in ss", "Ok(Bool(true))"),
        ("\"y\" in ss", "Ok(Bool(false))"),
        ("s in none", "Ok(Bool(false))"),
        ("n in xs", "Ok(Bool(true))"),
        ("3.0 in xs", "Ok(Bool(false))"),
        ("nan in xs", "Ok(Bool(false))"),
    ];
    let mut wrong = Vec::new();
    for (src, want) in PINNED {
        let got = format!("{:?}", run_in(src, &binds, &vars));
        if got != *want {
            wrong.push(format!("        ({src:?}, {got:?}),"));
        }
    }
    assert!(wrong.is_empty(), "answers moved:\n{}", wrong.join("\n"));
}

/// `req: {o?, p?, q?, r?: double, d: double, s?: {a?: {z?: double}}, m: map(string, double)}`.
fn guarded_env() -> CelEnvironment {
    let z = support::record_opt("req.s.a", &[("z", CelTy::Num)], &["z"]);
    let a = support::record_opt("req.s", &[("a", z)], &["a"]);
    env_of(&[(
        "req",
        support::record_opt(
            "req",
            &[
                ("o", CelTy::Num),
                ("p", CelTy::Num),
                ("q", CelTy::Num),
                ("r", CelTy::Num),
                ("d", CelTy::Num),
                ("s", a),
                ("m", CelTy::map(CelTy::Str, CelTy::Num)),
            ],
            &["o", "p", "q", "r", "s"],
        ),
    )])
}

fn lower_guarded(env: &CelEnvironment, src: &str) -> FastProgram {
    let p = fork::compile_any_unchecked_presence(env, src).unwrap_or_else(|e| panic!("{src}: {e}"));
    FastProgram::new(&p).unwrap_or_else(|e| panic!("{src}: {e}"))
}

const FOUR_GUARDED: &str =
    "req.?o.orValue(0.0) + req.?p.orValue(0.0) + req.?q.orValue(0.0) + req.?r.orValue(0.0) < 100.0";

const GUARDED_CHAIN: &str =
    "(has(req.s) && has(req.s.a) && has(req.s.a.z) ? req.s.a.z : 0.0) < 10.0";

/// `has(p) ? p : d` — the guard says exactly "p is present" — lowers to ONE host call that reads
/// `p` or answers "absent" (`ReadOr`), and a branch over the default (`BrSet`): no `Has`, no second
/// read, whoever wrote the guard — by hand, or `.orValue` (`added: optional reads`).
#[test]
fn a_guarded_read_lowers_to_one_read() {
    let env = guarded_env();
    for (src, n) in [
        ("(has(req.o) ? req.o : 0.0) < 10.0", 1),
        (GUARDED_CHAIN, 1),
        ("('k' in req.m ? req.m['k'] : 0.0) < 10.0", 1),
        ("(has(req.o) ? req.o : req.d) < 10.0", 1),
        (FOUR_GUARDED, 4),
    ] {
        let names = lower_guarded(&env, src).op_names();
        assert!(
            !names.contains(&"Has") && !names.contains(&"Jump") && !names.contains(&"Cond"),
            "`{src}` still guards and jumps: {names:?}"
        );
        assert_eq!(
            names.iter().filter(|o| **o == "BrSet").count(),
            n,
            "`{src}`: one branch per guarded read: {names:?}"
        );
        assert_eq!(
            names.iter().filter(|o| **o == "ReadOr").count(),
            n,
            "`{src}`: one read per guarded read: {names:?}"
        );
    }
}

/// A guard that does not say exactly "the value's own path is present" is not fused.
#[test]
fn a_guard_that_is_not_the_reads_own_path_is_not_fused() {
    let env = guarded_env();
    for src in [
        // Guards another field.
        "(has(req.p) ? req.o : 0.0) < 10.0",
        // A conjunct that is not a presence test.
        "(has(req.s.a) && req.s.a.z > 1.0 ? req.s.a.z : 0.0) < 10.0",
        // Inverted.
        "(!has(req.o) ? 0.0 : req.o) < 10.0",
        // A gap: `req.s.a` is not guarded, so a missing `a` is an error, not the default.
        "(has(req.s) && has(req.s.a.z) ? req.s.a.z : 0.0) < 10.0",
    ] {
        let names = lower_guarded(&env, src).op_names();
        assert!(
            names.contains(&"Has") && !names.contains(&"ReadOr"),
            "`{src}`: {names:?}"
        );
    }
}

/// The fused program answers exactly as the ternary it replaces — error text included — over
/// every combination of present and absent, and over a present value of the WRONG type, which
/// must stay an error and never read as the default.
#[test]
fn a_fused_read_answers_as_the_ternary() {
    let env = guarded_env();
    let num = |n: f64| Value::Num(n);
    let rec = |fields: Vec<(&str, Value)>| {
        Value::record(fields.into_iter().map(|(k, v)| (CelKey::new(k), v)))
    };
    let mut bindings: Vec<Value> = Vec::new();
    for mask in 0..16u32 {
        let mut fields = vec![("d", num(1.0)), ("m", rec(vec![]))];
        for (i, name) in ["o", "p", "q", "r"].into_iter().enumerate() {
            if mask & (1 << i) != 0 {
                fields.push((name, num(i as f64 + 1.0)));
            }
        }
        bindings.push(rec(fields));
    }
    // `o` present with the wrong type.
    bindings.push(rec(vec![
        ("o", Value::Str("three".into())),
        ("d", num(1.0)),
        ("m", rec(vec![])),
    ]));
    // The chain, at every depth, and mistyped at each step; and a map key present and absent.
    let base = || vec![("d", num(1.0))];
    let with = |extra: Vec<(&'static str, Value)>| {
        let mut f = base();
        f.extend(extra);
        rec(f)
    };
    for extra in [
        vec![("m", rec(vec![("k", num(2.0))]))],
        vec![("s", rec(vec![])), ("m", rec(vec![]))],
        vec![("s", rec(vec![("a", rec(vec![]))])), ("m", rec(vec![]))],
        vec![
            ("s", rec(vec![("a", rec(vec![("z", num(3.0))]))])),
            ("m", rec(vec![])),
        ],
        vec![("s", Value::Str("s".into())), ("m", rec(vec![]))],
        vec![("s", rec(vec![("a", num(1.0))])), ("m", rec(vec![]))],
        vec![
            (
                "s",
                rec(vec![("a", rec(vec![("z", Value::Str("z".into()))]))]),
            ),
            ("m", rec(vec![])),
        ],
        // `m` is required: missing, it is an error in both.
        vec![],
    ] {
        bindings.push(with(extra));
    }
    let mut compared = 0;
    for src in [
        FOUR_GUARDED,
        GUARDED_CHAIN,
        "('k' in req.m ? req.m['k'] : 0.0) < 10.0",
        "(has(req.o) ? req.o : req.d) < 10.0",
        "(has(req.o) ? req.o : 0.0) + (has(req.o) ? req.o : 0.0) < 10.0",
    ] {
        let p = fork::compile_any_unchecked_presence(&env, src).unwrap();
        let fused = FastProgram::new(&p).unwrap();
        let plain = fork::fast_program_unfused(&p).unwrap();
        assert!(
            plain.op_names().contains(&"Has") && !plain.op_names().contains(&"ReadOr"),
            "`{src}`: the unfused lowering fused: {:?}",
            plain.op_names()
        );
        for b in &bindings {
            let mut act = env.runtime().activation();
            act.bind_fact("req", b.clone());
            let (got, want) = (
                format!("{:?}", fork::fast_value(&fused, &act)),
                format!("{:?}", fork::fast_value(&plain, &act)),
            );
            assert_eq!(got, want, "`{src}` over {b:?}");
            compared += 1;
        }
    }
    assert_eq!(compared, 5 * 25);
}

/// A field as a `Facts` provider holds it: absent, a number, or a string where the schema says
/// number (mistyped).
#[derive(Clone, Copy, Debug)]
enum Fact {
    Absent,
    Num(f64),
    Str(&'static str),
}

/// `req.<name>` for each of `o, p, q, r, d`, answered by field id against one program's fields.
struct GuardFacts(Vec<Fact>);

impl GuardFacts {
    fn of(code: &FastProgram, by_name: &[(&str, Fact)]) -> GuardFacts {
        GuardFacts(
            code.fields()
                .iter()
                .map(|f| {
                    let names: Vec<&str> = f.segments().collect();
                    match names.as_slice() {
                        [n] => by_name
                            .iter()
                            .find(|(k, _)| k == n)
                            .map_or(Fact::Absent, |(_, v)| *v),
                        other => panic!("no fact for req.{}", other.join(".")),
                    }
                })
                .collect(),
        )
    }
}

impl typed_cel::Facts for GuardFacts {
    fn bool(&self, _: typed_cel::FieldId) -> Option<bool> {
        None
    }
    fn num(&self, f: typed_cel::FieldId) -> Option<f64> {
        match self.0[f.index()] {
            Fact::Num(n) => Some(n),
            _ => None,
        }
    }
    fn str(&self, f: typed_cel::FieldId) -> Option<&str> {
        match self.0[f.index()] {
            Fact::Str(s) => Some(s),
            _ => None,
        }
    }
    fn has(&self, f: typed_cel::FieldId) -> bool {
        !matches!(self.0[f.index()], Fact::Absent)
    }
}

/// Through a `Facts` provider, whose getters answer `None` both for ABSENT and for a value of the
/// wrong type: the fused read tells the two apart exactly as `has` then `Read` did — a mistyped
/// field is an error, never the default.
#[test]
fn a_fused_read_over_facts_answers_as_the_ternary() {
    let env = guarded_env();
    let mut cases: Vec<Vec<(&str, Fact)>> = Vec::new();
    for mask in 0..16u32 {
        let mut c = vec![("d", Fact::Num(1.0))];
        for (i, name) in ["o", "p", "q", "r"].into_iter().enumerate() {
            if mask & (1 << i) != 0 {
                c.push((name, Fact::Num(i as f64 + 1.0)));
            }
        }
        cases.push(c);
    }
    cases.push(vec![("o", Fact::Str("three")), ("d", Fact::Num(1.0))]);
    cases.push(vec![("d", Fact::Str("one"))]);
    let mut errors = 0;
    for src in [
        FOUR_GUARDED,
        "(has(req.o) ? req.o : req.d) < 10.0",
        "(has(req.o) ? req.o : 0.0) + (has(req.o) ? req.o : 0.0) < 10.0",
    ] {
        let p = fork::compile_any_unchecked_presence(&env, src).unwrap();
        let fused = FastProgram::new(&p).unwrap();
        let plain = fork::fast_program_unfused(&p).unwrap();
        for c in &cases {
            let mut s = typed_cel::FastScratch::default();
            let got = format!("{:?}", fused.decide(&GuardFacts::of(&fused, c), &mut s));
            let want = format!("{:?}", plain.decide(&GuardFacts::of(&plain, c), &mut s));
            assert_eq!(got, want, "`{src}` over {c:?}");
            errors += usize::from(want.starts_with("Err"));
        }
    }
    assert!(errors >= 3, "the mistyped cases must be errors: {errors}");
}
