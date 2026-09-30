//! Exact numbers: the dialect has ONE numeric type, and a value of it is held exactly — an integer a
//! document, a literal, a binding or a host fact carries (up to `u64::MAX`) is never rounded to a
//! double on its way to a comparison. The bypass this closes: two account ids above 2^53 that
//! round to the same double compare EQUAL, and a policy on one admits the other.

#[path = "support/mod.rs"]
mod support;

use typed_cel::CompileOpts;
use std::sync::Arc;

use typed_cel::{
    emit, with_unfused_loops, CelEnvironment, CelNum, CelTy, Facts, FastProgram, FastScratch,
    FieldId, StreamedProgram, Vm,
};
use serde_json::{json, Value};
use support::events::to_events;
use support::record;

/// `2^53 + 1`, the first integer an `f64` cannot hold. It rounds to its neighbour `2^53`.
const ABOVE: i64 = 9007199254740993;
const NEIGHBOUR: i64 = 9007199254740992;

fn body_env(fields: &[(&str, CelTy)]) -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.declare("body", record("body", fields));
    env
}

/// `src` over `body`, bound from `doc`.
fn eval_body(fields: &[(&str, CelTy)], src: &str, doc: Value) -> Result<bool, String> {
    let env = body_env(fields);
    let program = env
        .compile(src, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("{src}: {e}"));
    let mut act = env.activation();
    act.bind("body", &doc).map_err(|e| e.to_string())?;
    program.evaluate(&act).map_err(|e| e.to_string())
}

/// `src` over no bindings at all — through the unchecked-presence door: some cases read a map
/// literal at a key it may lack, to pin how numbers name keys at run time.
fn eval(src: &str) -> Result<bool, String> {
    let env = CelEnvironment::new();
    let program = typed_cel::fork::compile_unchecked_presence(&env, src, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("{src}: {e}"));
    program
        .evaluate(&env.activation())
        .map_err(|e| e.to_string())
}

/// `src` over `body`, streamed from `text` one byte-fragment at a time; the run's final verdict.
fn streamed(fields: &[(&str, CelTy)], src: &str, text: &str) -> Result<bool, String> {
    let env = body_env(fields);
    let compiled = env
        .compile(src, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("{src}: {e}"));
    let code = Arc::new(emit(&compiled).expect("the program emits"));
    let p = StreamedProgram::new(
        Arc::new(Vm::new()),
        &env,
        &compiled,
        code,
        env.activation(),
        "body",
    )
    .expect("the program streams");
    let mut run = p.begin();
    for e in to_events(text, 1) {
        run.push(e.as_event());
    }
    run.finish().map_err(|e| e.to_string())
}

#[test]
fn an_id_above_2_53_does_not_match_its_neighbour_through_a_binding() {
    let f = [("account_id", CelTy::Num)];
    let src = format!("body.account_id == {ABOVE}");
    assert_eq!(
        eval_body(&f, &src, json!({"account_id": NEIGHBOUR})),
        Ok(false),
        "a different account must not match"
    );
    assert_eq!(eval_body(&f, &src, json!({"account_id": ABOVE})), Ok(true));
}

#[test]
fn an_id_above_2_53_does_not_match_its_neighbour_through_a_streamed_body() {
    let f = [("account_id", CelTy::Num)];
    let src = format!("body.account_id == {ABOVE}");
    assert_eq!(
        streamed(&f, &src, &format!(r#"{{"account_id":{NEIGHBOUR}}}"#)),
        Ok(false),
        "a different account must not match"
    );
    assert_eq!(
        streamed(&f, &src, &format!(r#"{{"account_id":{ABOVE}}}"#)),
        Ok(true)
    );
}

#[test]
fn u64_max_is_exact() {
    let f = [("n", CelTy::Num)];
    let src = "body.n == 18446744073709551615";
    let env = body_env(&f);
    env.compile(src, &CompileOpts::default())
        .expect("an integer literal up to u64::MAX is the one number type, held exactly");
    assert_eq!(eval_body(&f, src, json!({"n": u64::MAX})), Ok(true));
    assert_eq!(
        eval_body(&f, src, json!({"n": 18446744073709551614u64})),
        Ok(false)
    );
}

/// Every number field answers `n`; every other kind is absent.
struct Num(CelNum);

impl Facts for Num {
    fn bool(&self, _: FieldId) -> Option<bool> {
        None
    }
    fn num(&self, _: FieldId) -> Option<f64> {
        Some(self.0.as_f64())
    }
    fn number(&self, _: FieldId) -> Option<CelNum> {
        Some(self.0)
    }
    fn str(&self, _: FieldId) -> Option<&str> {
        None
    }
    fn has(&self, _: FieldId) -> bool {
        true
    }
}

/// A provider that only knows doubles: the `number` default reads `num`.
struct OnlyNum(f64);

impl Facts for OnlyNum {
    fn bool(&self, _: FieldId) -> Option<bool> {
        None
    }
    fn num(&self, _: FieldId) -> Option<f64> {
        Some(self.0)
    }
    fn str(&self, _: FieldId) -> Option<&str> {
        None
    }
    fn has(&self, _: FieldId) -> bool {
        true
    }
}

fn req_program(src: &str) -> FastProgram {
    let env = body_env(&[]);
    let mut env = env;
    env.declare(
        "req",
        record("req", &[("id", CelTy::Num), ("n", CelTy::Num)]),
    );
    let p = env
        .compile(src, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("{src}: {e}"));
    FastProgram::new(&p).expect("lowers")
}

fn decide(p: &FastProgram, facts: &dyn Facts) -> Result<bool, String> {
    p.decide(facts, &mut FastScratch::default())
        .map_err(|e| e.to_string())
}

#[test]
fn an_id_above_2_53_does_not_match_its_neighbour_through_a_host_fact() {
    let p = req_program(&format!("req.id == {ABOVE}"));
    assert_eq!(decide(&p, &Num(CelNum::Int(NEIGHBOUR))), Ok(false));
    assert_eq!(decide(&p, &Num(CelNum::Int(ABOVE))), Ok(true));
}

#[test]
fn a_facts_impl_with_only_num_still_works() {
    let p = req_program("req.n == 3");
    assert_eq!(decide(&p, &OnlyNum(3.0)), Ok(true));
    assert_eq!(decide(&p, &OnlyNum(3.5)), Ok(false));
}

// ---- literals and the general operators ----

#[test]
fn integer_literals_are_exact() {
    assert_eq!(eval("9007199254740993 == 9007199254740992"), Ok(false));
    assert_eq!(eval("9007199254740993 - 9007199254740992 == 1"), Ok(true));
    assert_eq!(
        eval("18446744073709551615 == 18446744073709551615"),
        Ok(true)
    );
    assert_eq!(
        eval("18446744073709551615 > 18446744073709551614"),
        Ok(true)
    );
    assert_eq!(
        eval("-9223372036854775808 < -9223372036854775807"),
        Ok(true)
    );
    assert_eq!(eval("0x10 == 16"), Ok(true));
    assert_eq!(eval("0xFFFFFFFFFFFFFFFF == 18446744073709551615"), Ok(true));
}

#[test]
fn one_numeric_type_still_mixes_freely() {
    let env = {
        let mut env = CelEnvironment::new();
        env.declare("x", CelTy::Num);
        env
    };
    for src in [
        "x + 1 == 3.0",
        "x + 0.5 == 2.5",
        "x * 1.5 == 3",
        "[1, 2.0, 3][1] == 2",
        "1 == 1.0",
        "{1: 'a'}[1.0] == 'a'",
        "{1.0: 'a'}[1] == 'a'",
        "x / 4 == 0.5",
        "2.0 in [1, 2, 3]",
        "x in [1.0, 2.0]",
    ] {
        let p = env
            .compile(src, &CompileOpts::default())
            .unwrap_or_else(|e| panic!("{src}: {e}"));
        let mut act = env.activation();
        act.bind("x", &json!(2)).unwrap();
        assert_eq!(
            p.evaluate(&act).map_err(|e| e.to_string()),
            Ok(true),
            "{src}"
        );
    }
    // A key that is not integral names no key: refused, never truncated to `1`.
    let err = eval("{1.5: 'a'}[1] == 'a'").expect_err("a fractional key is refused");
    assert!(err.contains("1.5"), "{err}");
}

#[test]
fn integer_overflow_is_an_error_not_a_rounding() {
    for src in [
        "18446744073709551615 + 1 == 0",
        "-9223372036854775808 - 1 < 0",
        "18446744073709551615 * 2 > 0",
        "-(18446744073709551615) < 0",
    ] {
        let err = eval(src).expect_err(src);
        assert!(err.contains("Overflow"), "{src}: {err}");
    }
    // Past `i64::MAX` but inside `u64` is exact, not an overflow.
    assert_eq!(
        eval("9223372036854775807 + 1 == 9223372036854775808"),
        Ok(true)
    );
    assert_eq!(
        eval("-(-9223372036854775808) == 9223372036854775808"),
        Ok(true)
    );
}

#[test]
fn division_keeps_its_meaning() {
    for src in [
        "7 / 2 == 3.5",
        "-7 / 2 == -3.5",
        "6 / 3 == 2",
        "1 / 0 > 1e308",
        "-1 / 0 < -1e308",
        "0 / 0 != 0 / 0",
        "1 / -(0.0) < -1e308",
        "-(0.0) == 0",
    ] {
        assert_eq!(eval(src), Ok(true), "{src}");
    }
}

#[test]
fn a_uint_literal_with_a_suffix_is_still_refused() {
    let env = CelEnvironment::new();
    // Refused (as `removed: uint` or, where the duration shorthand reads `1u` first, as an
    // unknown unit): the unsuffixed spelling is the one number type, the suffixed one is not.
    for src in ["1u == 1", "18446744073709551615u == 1", "0xFFu == 255"] {
        env.compile(src, &CompileOpts::default()).expect_err(src);
    }
    assert!(env
        .compile("18446744073709551615 == 1", &CompileOpts::default())
        .is_ok());
    // Past `u64::MAX` there is no exact integer to hold, so the literal is refused.
    let err = env
        .compile("18446744073709551616 == 1", &CompileOpts::default())
        .expect_err("past u64::MAX")
        .to_string();
    assert!(err.contains("invalid int literal"), "{err}");
}

#[test]
fn residuals_print_integers_exactly() {
    let mut env = CelEnvironment::new();
    env.declare("policy", record("policy", &[("id", CelTy::Num)]));
    env.declare("req", record("req", &[("id", CelTy::Num)]));
    let p = env
        .compile("policy.id == req.id", &CompileOpts::default())
        .unwrap();
    let mut known = env.activation();
    known
        .bind("policy", &json!({"id": 9007199254740993u64}))
        .unwrap();
    let residual = env
        .compile(
            p.source(),
            &CompileOpts {
                known: Some(&known),
                ..Default::default()
            },
        )
        .expect("specializes");
    assert!(
        residual.source().contains("9007199254740993"),
        "{}",
        residual.source()
    );
    let again = env
        .compile(residual.source(), &CompileOpts::default())
        .expect("the residual compiles");
    let mut act = env.activation();
    act.bind("req", &json!({"id": NEIGHBOUR})).unwrap();
    assert_eq!(again.evaluate(&act).map_err(|e| e.to_string()), Ok(false));
    act.bind("req", &json!({"id": ABOVE})).unwrap();
    assert_eq!(again.evaluate(&act).map_err(|e| e.to_string()), Ok(true));
}

// ---- the fast paths ----

#[test]
fn a_fused_field_compare_is_exact() {
    // Each element is compared against a field the loop caches: the fused `CondFR`.
    let lt = req_program(&format!("[{NEIGHBOUR}, 1].all(x, x < req.id)"));
    let gt = req_program(&format!("[{ABOVE}, {ABOVE}].all(x, x > req.id)"));
    for p in [&lt, &gt] {
        assert!(
            p.op_names().contains(&"CondFR"),
            "not the fused compare:\n{}",
            p.listing()
        );
    }
    for unfused in [false, true] {
        let run = |p: &FastProgram, n: i64| {
            let f = || decide(p, &Num(CelNum::Int(n)));
            if unfused {
                with_unfused_loops(f)
            } else {
                f()
            }
        };
        assert_eq!(run(&lt, ABOVE), Ok(true), "unfused={unfused}");
        assert_eq!(run(&lt, NEIGHBOUR), Ok(false), "unfused={unfused}");
        assert_eq!(run(&gt, NEIGHBOUR), Ok(true), "unfused={unfused}");
        assert_eq!(run(&gt, ABOVE), Ok(false), "unfused={unfused}");
    }
}

#[test]
fn a_scanned_loop_is_exact() {
    let mut env = CelEnvironment::new();
    env.declare("xs", CelTy::list(CelTy::Num));
    env.declare("rs", CelTy::list(record("r", &[("id", CelTy::Num)])));
    env.declare("req", record("req", &[("id", CelTy::Num)]));
    let cases: [(&str, serde_json::Value, bool); 8] = [
        (
            "xs.exists(x, x == 9007199254740993)",
            json!([NEIGHBOUR, 9007199254740994i64]),
            false,
        ),
        (
            "xs.exists(x, x == 9007199254740993)",
            json!([1, ABOVE]),
            true,
        ),
        (
            "xs.all(x, x > 9007199254740992)",
            json!([ABOVE, ABOVE]),
            true,
        ),
        (
            "xs.all(x, x > 9007199254740992)",
            json!([ABOVE, NEIGHBOUR]),
            false,
        ),
        // Against a field rather than a constant.
        ("xs.exists(x, x == req.id)", json!([NEIGHBOUR, 5]), false),
        ("xs.all(x, x < req.id)", json!([NEIGHBOUR, 5]), true),
        // A record member against a field.
        (
            "rs.exists(r, r.id == req.id)",
            json!([{"id": NEIGHBOUR}]),
            false,
        ),
        (
            "rs.exists(r, r.id == req.id)",
            json!([{"id": 1}, {"id": ABOVE}]),
            true,
        ),
    ];
    for (src, list, want) in cases {
        let p = env
            .compile(src, &CompileOpts::default())
            .unwrap_or_else(|e| panic!("{src}: {e}"));
        let fast = FastProgram::new(&p).expect("lowers");
        assert!(
            fast.scanned_loops() >= 1,
            "{src}: no scan\n{}",
            fast.listing()
        );
        let mut act = env.activation();
        let (xs, rs) = if src.starts_with("rs") {
            (json!([]), list.clone())
        } else {
            (list.clone(), json!([]))
        };
        act.bind("xs", &xs).unwrap();
        act.bind("rs", &rs).unwrap();
        act.bind("req", &json!({"id": ABOVE})).unwrap();
        let fused = fast.eval(&act).map_err(|e| e.to_string());
        let unfused = with_unfused_loops(|| fast.eval(&act).map_err(|e| e.to_string()));
        assert_eq!(fused, Ok(want), "{src} over {list}");
        assert_eq!(unfused, Ok(want), "{src} over {list}, unfused");
    }
}

#[test]
fn a_number_set_is_exact() {
    let p = req_program("req.id in [9007199254740993, 1, 2]");
    assert_eq!(decide(&p, &Num(CelNum::Int(NEIGHBOUR))), Ok(false));
    assert_eq!(decide(&p, &Num(CelNum::Int(ABOVE))), Ok(true));
    assert_eq!(decide(&p, &Num(CelNum::Float(1.0))), Ok(true));
    let chain =
        req_program("req.id == 1 || req.id == 2 || req.id == 9007199254740993 || req.id == 7");
    assert_eq!(decide(&chain, &Num(CelNum::Int(NEIGHBOUR))), Ok(false));
    assert_eq!(decide(&chain, &Num(CelNum::Int(ABOVE))), Ok(true));
    assert_eq!(decide(&chain, &Num(CelNum::UInt(7))), Ok(true));
    for src in [
        "-0.0 in [0]",
        "0 in [-0.0]",
        "!(0/0 in [0/0])",
        "18446744073709551615 in [18446744073709551615]",
    ] {
        assert_eq!(eval(src), Ok(true), "{src}");
    }
}
