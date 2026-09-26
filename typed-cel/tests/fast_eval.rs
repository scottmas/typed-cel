//! The fast backend against the evaluator: the same expression, the same context, the same answer.
//!
//! Most tests run one source through BOTH `Program::execute` (the absorbed evaluator, on the
//! parsed tree) and the fast backend (on the same source CHECKED, `fork::compile_any`, then
//! `FastProgram::new`), and require `same_outcome`. Where the exact answer is load-bearing it is
//! pinned too, so a backend and an evaluator that drifted together still fail. Every source here
//! type-checks: the fast backend runs checked programs only, so a source the checker refuses has no
//! run on it to compare.

#[path = "support/mod.rs"]
mod support;

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use support::gen::{same_error, same_outcome};
use support::record;
use typed_cel::fork::{self, objects::Value, Context, Program};
use typed_cel::{
    CelEnvironment, CelError, CelKey, CelTy, CelValue, ExecutionError, FastProgram, LazyValue, Vm,
};

type Outcome = Result<Value, ExecutionError>;

/// (evaluator, fast backend) for `src` on `ctx`, whose variables `vars` declares. Every source
/// here must type-check: the fast backend runs checked programs only.
fn both_in(src: &str, ctx: &Context, vars: &[(&str, CelTy)]) -> (Outcome, Outcome) {
    let p = Program::compile(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    let checked = fork::compile_any(&env_of(vars), src)
        .unwrap_or_else(|e| panic!("`{src}` must type-check: {e}"));
    let fast = FastProgram::new(&checked).unwrap_or_else(|e| panic!("`{src}` must lower: {e}"));
    (p.execute(ctx), fork::fast_value(&fast, ctx))
}

fn env_of(vars: &[(&str, CelTy)]) -> CelEnvironment {
    let mut env = CelEnvironment::new();
    for (name, ty) in vars {
        env.declare(*name, ty.clone());
    }
    env
}

/// `same_outcome` for `src`, returning the (agreed) outcome.
fn agree_in(src: &str, ctx: &Context, vars: &[(&str, CelTy)]) -> Outcome {
    let (eval, fast) = both_in(src, ctx, vars);
    assert!(
        same_outcome(&eval, &fast),
        "`{src}`: the fast backend disagrees with the evaluator\n  evaluator: {eval:?}\n  fast:      {fast:?}"
    );
    fast
}

fn agree(src: &str) -> Outcome {
    agree_in(src, &Context::default(), &[])
}

fn assert_ok(src: &str, want: Value) {
    let got = agree(src);
    assert!(
        matches!(&got, Ok(v) if support::gen::same_value(v, &want)),
        "`{src}`: want Ok({want:?}), got {got:?}"
    );
}

fn assert_err(src: &str, want: ExecutionError) {
    let got = agree(src);
    assert!(
        matches!(&got, Err(e) if same_error(e, &want)),
        "`{src}`: want Err({want:?}), got {got:?}"
    );
}

fn is_no_such_key(src: &str) {
    let got = agree(src);
    assert!(
        matches!(got, Err(ExecutionError::NoSuchKey(_))),
        "`{src}`: want a missing key, got {got:?}"
    );
}

#[test]
fn fast_arithmetic() {
    assert_ok("1 + 2 * 3", Value::Float(7.0));
}

#[test]
fn every_operator_matches_the_evaluator() {
    let sources = [
        // Add
        "1 + 2",
        "1.5 + 2.25",
        "'a' + 'b'",
        "[1] + [2]",
        "1 + 1.0",
        "9223372036854775807 + 1",
        // Sub
        "5 - 7",
        "5.5 - 0.5",
        "-9223372036854775807 - 2",
        // Mul
        "6 * 7",
        "1.5 * 2.0",
        "9223372036854775807 * 2",
        // Div
        "7 / 2",
        "7.0 / 2.0",
        "5.0 / 0.0",
        "0.0 / 0.0",
        "-5.0 / 0.0",
        "1 / 0",
        // Eq / Ne
        "1 == 1",
        "1 == 1.0",
        "'a' == 'a'",
        "[1, 2] == [1, 2]",
        "{'a': 1} == {'a': 1}",
        "null == null",
        "1 != 2",
        "b'a' != b'a'",
        "[1] != [1, 2]",
        // Lt / Le / Gt / Ge
        "1 < 2",
        "2.0 <= 2.0",
        "'b' > 'a'",
        "1 < 2.5",
        "3 >= 3",
        "3 > 3",
        // In
        "2 in [1, 2]",
        "3 in [1, 2]",
        "'a' in {'a': 1}",
        // Unary
        "-1",
        "-1.5",
        "-(-9223372036854775807 - 1)",
        "!true",
        "!false",
    ];
    assert!(sources.len() >= 40, "{} sources", sources.len());
    for src in sources {
        let _ = agree(src);
    }
}

/// The evaluator would answer each of these (`NoSuchOverload`, `UndeclaredReference`, …); the
/// checker refuses them first, so they never reach either backend. The removals with a dialect row
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
fn errors_are_the_evaluators_errors() {
    for src in ["{}.a", "{'a': 1}.b", "[1][5]", "[1][-1]", "{null: true}"] {
        let got = agree(src);
        assert!(got.is_err(), "`{src}` should fail, got {got:?}");
    }
    assert_err("{}.a", ExecutionError::NoSuchKey(Arc::new("a".to_string())));
    assert_err(
        "{null: true}",
        ExecutionError::UnsupportedKeyType(Value::Null),
    );
}

/// `m` is `{'a': 1}`, so `m['x']` and `m['y']` are missing keys: a bool operand that is an
/// error, which is the only operand besides `true` and `false` a checked `&&`/`||` can have.
fn absorbing(src: &str) -> Outcome {
    let mut ctx = Context::default();
    ctx.add_variable_from_value("m", HashMap::from([("a", 1i64)]));
    agree_in(src, &ctx, &[("m", CelTy::map(CelTy::Str, CelTy::Num))])
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
    let lefts = ["true", "false", "(m['x'] == 1.0)"];
    let rights = ["true", "false", "(m['y'] == 1.0)"];
    for l in lefts {
        for r in rights {
            let _ = absorbing(&format!("{l} || {r}"));
        }
    }
    assert_absorbs("(m['x'] == 1.0) || true", Ok(Value::Bool(true)));
    assert_absorbs("(m['x'] == 1.0) || false", Err(no_such_key("x")));
    // The RIGHT operand's error, because the evaluator `?`-propagates it.
    assert_absorbs("(m['x'] == 1.0) || (m['y'] == 1.0)", Err(no_such_key("y")));
}

#[test]
fn and_absorption_table() {
    let lefts = ["true", "false", "(m['x'] == 1.0)"];
    let rights = ["true", "false", "(m['y'] == 1.0)"];
    for l in lefts {
        for r in rights {
            let _ = absorbing(&format!("{l} && {r}"));
        }
    }
    assert_absorbs("(m['x'] == 1.0) && false", Ok(Value::Bool(false)));
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
    let got = agree("[0, 1].exists_one(x, {1: 1}[x] == 1)");
    assert!(got.is_err(), "exists_one's step never absorbs: {got:?}");
    for src in [
        "[1, 2, 3].filter(x, {1: 1, 3: 3}[x] > 0)",
        "[1, 2].map(x, x > 1, x * 2)",
        "[].all(x, {}.a == 1)",
        "[1, 2, 3].exists(e, e == 2)",
    ] {
        let _ = agree(src);
    }
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
fn has_follows_the_evaluator_on_maps_and_non_maps() {
    assert_ok("has({'a': 1}.a)", Value::Bool(true));
    assert_ok("has({'a': 1}.b)", Value::Bool(false));
    let _ = agree("has([1].a)");
    let _ = agree("has(1.a)");
}

#[test]
fn duplicate_map_keys_keep_the_last() {
    let _ = agree("{'a': 1, 'a': 2}['a']");
}

/// A fractional key into a map with NUMBER keys type-checks and is no key at all, and the evaluator
/// answers it differently by where the map lives: `NoSuchKey` from a borrowed one
/// (`Indexer::get`), `UnsupportedKeyType` from an owned one (`Indexer::steal`). The backend tracks
/// which it holds so it can answer the same.
#[test]
fn index_keeps_the_borrowed_and_owned_paths_apart() {
    // A root map takes only literal string keys (the demand rule), so the borrowed map here is a
    // comprehension variable.
    let borrowed = agree("[{1: 'a'}].map(m, m[1.5])");
    let owned = agree("{1: 'a'}[1.5]");
    let (Err(b), Err(o)) = (&borrowed, &owned) else {
        panic!("both should fail: {borrowed:?} / {owned:?}");
    };
    assert!(
        !same_error(b, o),
        "the borrowed (`get`) and owned (`steal`) paths answered alike ({b:?}) — this test no \
         longer tells them apart"
    );
}

/// A comprehension variable is BORROWED from the evaluator's child scope (context.rs:151-165), so
/// indexing one takes `Indexer::get`, even when the backend holds it as an owned copy.
#[test]
fn a_comprehension_variable_indexes_like_a_borrowed_one() {
    for src in [
        "[{1: 'a'}].map(m, m[1.5])",
        "[[{1: 'a'}]].map(m, m[0][1.5])",
        "[{1: 'a'}].exists(m, m[1.5] == 'a')",
        "[{'a': 1}].map(m, m['a'])",
    ] {
        let _ = agree(src);
    }
}

#[test]
fn comprehension_variables_shadow_and_restore() {
    let mut ctx = Context::default();
    ctx.add_variable_from_value("x", 10i64);
    let got = agree_in(
        "x + [1, 2].map(x, x * 2)[1] + x",
        &ctx,
        &[("x", CelTy::Num)],
    );
    assert!(matches!(got, Ok(Value::Float(24.0))), "{got:?}");
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

/// (evaluator, `Vm::eval`) observations for `src` through the PUBLIC API, each on a fresh activation.
fn observe_both(src: &str) -> (Observed, Observed) {
    let env = lazy_env();
    let program = env.compile(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    let bytecode = typed_cel::emit(&program).expect("emits");
    let eval = observe(&env, &|act| program.evaluate(act));
    let vm = observe(&env, &|act| Vm::new().eval(&bytecode, act));
    assert_eq!(eval, vm, "`{src}`: `Vm::eval` observed differently");
    (eval, vm)
}

#[test]
fn lazy_reads_match_the_evaluator() {
    let (e, _) = observe_both("false && r.a == 1.0");
    assert_eq!(e.record_reads, 0);
    // The left errors through the lazy `NoSuchMember`, is captured, and the right is still read.
    let (e, _) = observe_both("r.t == 'x' || r.a == 1.0");
    assert_eq!(e.record_reads, 2);
    assert_eq!(e.answer.1, Some(true));
    let (e, _) = observe_both("r.a + r.a > 0.0");
    assert_eq!(e.record_reads, 2);
    let (e, _) = observe_both("m.exists(k, k == 'b')");
    assert!(e.map_iterations > 0, "{e:?}");
    observe_both("m.exists(k, m[k] > 0.0)");
    observe_both("m.all(k, m[k] >= 0.0) && r.a == 1.0");
}

#[test]
fn vm_eval_answers_exactly_what_evaluate_answers() {
    let (e, _) = observe_both("r.a > 0.0");
    assert_eq!(e.answer, (true, Some(true), String::new()));
    let (e, _) = observe_both("r.t == 'x'");
    assert!(!e.answer.0);
    assert!(
        e.answer
            .2
            .contains("could not be evaluated: No such key: t"),
        "{}",
        e.answer.2
    );
    // `has()` on a lazy is an existence question in both, never the member's value.
    let (e, _) = observe_both("has(r.a)");
    assert_eq!(e.answer, (true, Some(true), String::new()));
}

/// The evaluator hands a comprehension's result back OWNED (`into_owned`, objects.rs:1215-1217), so
/// indexing it takes `Indexer::steal`. Inside the result expression the accumulator is a
/// comprehension variable — borrowed, `Indexer::get` — so the lowering marks the result's end with
/// `Op::Own`. Without it the backend answers `NoSuchOverload` where the evaluator answers
/// `UnsupportedKeyType(Float(1.5))`.
#[test]
fn a_comprehension_result_is_handed_back_owned() {
    for src in [
        "[{1: 'a'}].map(x, x)[0][1.5]",
        "[{1: 'a'}].filter(x, true)[0][1.5]",
        "[{'a': 1}].map(x, x)[0]['a']",
    ] {
        let _ = agree(src);
    }
}
