//! CALL hosts: a host function declared with a signature only, whose implementation each RUN
//! supplies through a [`HostDispatch`]. The checker types a call to one; the fast backend routes it
//! to the run's dispatcher; the specializer never folds it, because the known activation has no
//! implementation to resolve it with; and a run with no dispatcher fails the call as an evaluation
//! error, never a panic.

use std::sync::Arc;

use typed_cel::{
    emit, CelEnvironment, CelError, CelKey, CelTy, CelValue, FactPoll, Facts, FastScratch, FieldId,
    HostDispatch, LazyValue, NoCallHosts, Record, Vm,
};

/// Counts calls by name and answers from a table.
#[derive(Default)]
struct Counting {
    calls: Vec<(String, Vec<CelValue>)>,
    answers: Vec<(&'static str, Option<CelValue>)>,
}

impl Counting {
    /// `None` answers an evaluation error.
    fn answering(answers: Vec<(&'static str, Option<CelValue>)>) -> Counting {
        Counting {
            calls: Vec::new(),
            answers,
        }
    }

    fn count(&self, name: &str) -> usize {
        self.calls.iter().filter(|(n, _)| n == name).count()
    }
}

impl HostDispatch for Counting {
    fn call(&mut self, name: &str, args: &[CelValue]) -> Result<CelValue, CelError> {
        self.calls.push((name.to_string(), args.to_vec()));
        match self.answers.iter().find(|(n, _)| *n == name) {
            Some((_, Some(v))) => Ok(v.clone()),
            _ => Err(CelError::unknown_host_function(name)),
        }
    }
}

fn req_ty() -> CelTy {
    Record::new("req", [("x", CelTy::Str)]).into()
}

fn env_with(decls: &[(&str, Vec<CelTy>, CelTy)]) -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.declare("req", req_ty());
    for (name, params, ret) in decls {
        env.declare_call_host(name, params, ret.clone())
            .unwrap_or_else(|e| panic!("{name}: {e}"));
    }
    env
}

fn req_act(env: &CelEnvironment) -> typed_cel::CelActivation {
    let mut act = env.runtime().activation();
    act.bind_fact(
        "req",
        CelValue::Record(vec![(CelKey::new("x"), CelValue::Str("abc".into()))]),
    );
    act
}

#[test]
fn a_call_host_reaches_the_dispatcher() {
    let env = env_with(&[("probe_len", vec![CelTy::Str, req_ty()], CelTy::Num)]);
    let p = env
        .compile_returning(r#"probe_len("abc", req) == 3.0"#, &CelTy::Bool)
        .expect("compiles");
    let bc = emit(&p).expect("emits");
    let mut d = Counting::answering(vec![("probe_len", Some(CelValue::Num(3.0)))]);
    let got = Vm::new()
        .eval_result_with(&bc, &req_act(&env), &mut d)
        .expect("evaluates");
    assert!(matches!(got, CelValue::Bool(true)), "{got:?}");
    assert_eq!(d.count("probe_len"), 1);
    assert!(matches!(&d.calls[0].1[0], CelValue::Str(s) if s == "abc"));
}

#[test]
fn an_unknown_call_host_is_an_evaluation_error() {
    let env = env_with(&[("x", vec![], CelTy::Bool)]);
    let p = env.compile("x()").expect("compiles");
    let bc = emit(&p).expect("emits");
    let mut d = Counting::default();
    let err = Vm::new()
        .eval_result_with(&bc, &req_act(&env), &mut d)
        .expect_err("the dispatcher refused it");
    assert!(matches!(err, CelError::Evaluation { .. }), "{err:?}");
    // With no dispatcher at all, the same: an error, not a panic.
    let err = Vm::new()
        .eval_result(&bc, &req_act(&env))
        .expect_err("no dispatcher answers a call host");
    assert!(matches!(err, CelError::Evaluation { .. }), "{err:?}");
    let mut none = NoCallHosts;
    assert!(Vm::new()
        .eval_result_with(&bc, &req_act(&env), &mut none)
        .is_err());
}

#[test]
fn a_call_host_is_never_folded() {
    let mut env = env_with(&[("probe_k", vec![CelTy::Str], CelTy::Str)]);
    env.declare("k", Record::new("k", [("r", CelTy::Str)]));
    let p = env.compile(r#"probe_k(k.r) == "x""#).expect("compiles");
    let mut known = env.activation();
    known
        .bind("k", &serde_json::json!({"r": "/a"}))
        .expect("binds");
    let residual = env.specialize(&p, &known).expect("specializes");
    let src = residual.source();
    assert!(src.contains("probe_k("), "{src}");
    assert!(src.contains("\"/a\""), "the known argument folded: {src}");
    // A zero-argument call is closed too, and stays.
    let env = env_with(&[("probe_z", vec![], CelTy::Bool)]);
    let p = env.compile("probe_z()").expect("compiles");
    let residual = env.specialize(&p, &env.activation()).expect("specializes");
    assert!(
        residual.source().contains("probe_z("),
        "{}",
        residual.source()
    );
}

#[test]
fn or_skips_the_right_side_after_true() {
    let env = env_with(&[
        ("probe_a", vec![req_ty()], CelTy::Bool),
        ("probe_b", vec![req_ty()], CelTy::Bool),
    ]);
    let bc = emit(
        &env.compile("probe_a(req) || probe_b(req)")
            .expect("compiles"),
    )
    .expect("emits");
    for (a, want_b) in [(true, 0), (false, 1)] {
        let mut d = Counting::answering(vec![
            ("probe_a", Some(CelValue::Bool(a))),
            ("probe_b", Some(CelValue::Bool(false))),
        ]);
        let got = Vm::new()
            .eval_result_with(&bc, &req_act(&env), &mut d)
            .expect("evaluates");
        assert!(matches!(got, CelValue::Bool(b) if b == a), "{got:?}");
        assert_eq!(d.count("probe_a"), 1);
        assert_eq!(d.count("probe_b"), want_b, "probe_a answered {a}");
    }
}

/// Pins the fork's `||`: an ERROR on the left still evaluates the right. A gate program that relies
/// on `||` to stop spending I/O must therefore never let a method answer `Err`.
#[test]
fn or_evaluates_the_right_side_after_an_error() {
    let env = env_with(&[
        ("probe_a", vec![req_ty()], CelTy::Bool),
        ("probe_b", vec![req_ty()], CelTy::Bool),
    ]);
    let bc = emit(
        &env.compile("probe_a(req) || probe_b(req)")
            .expect("compiles"),
    )
    .expect("emits");
    let mut d = Counting::answering(vec![
        ("probe_a", None),
        ("probe_b", Some(CelValue::Bool(true))),
    ]);
    let got = Vm::new().eval_result_with(&bc, &req_act(&env), &mut d);
    assert!(matches!(got, Ok(CelValue::Bool(true))), "{got:?}");
    assert_eq!(d.count("probe_b"), 1);
}

#[test]
fn a_call_host_and_a_closure_host_cannot_share_a_name() {
    let mut env = CelEnvironment::new();
    env.register_host(
        "shared",
        &[CelTy::Str],
        CelTy::Str,
        false,
        Arc::new(|a: &[CelValue]| Ok(a[0].clone())),
    )
    .expect("registers");
    let err = env
        .declare_call_host("shared", &[CelTy::Str], CelTy::Str)
        .err()
        .expect("refused");
    assert!(matches!(err, CelError::Registration { .. }), "{err:?}");

    let mut env = CelEnvironment::new();
    env.declare_call_host("other", &[], CelTy::Str)
        .expect("declares");
    let err = env
        .register_host(
            "other",
            &[],
            CelTy::Str,
            false,
            Arc::new(|_: &[CelValue]| Ok(CelValue::Str(String::new()))),
        )
        .err()
        .expect("refused");
    assert!(matches!(err, CelError::Registration { .. }), "{err:?}");
    // The dialect's own names are refused as they are for a closure host.
    let err = env
        .declare_call_host("size", &[CelTy::Str], CelTy::Num)
        .err()
        .expect("refused");
    assert!(matches!(err, CelError::Registration { .. }), "{err:?}");
}

/// A record a call host answers, read by member.
#[derive(Debug)]
struct Outcome {
    admits: bool,
    how: &'static str,
}

impl LazyValue for Outcome {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        match name {
            "admits" => Ok(CelValue::Bool(self.admits)),
            "how" => Ok(CelValue::Str(self.how.into())),
            _ => Err(CelError::NoSuchMember { key: name.into() }),
        }
    }
}

fn outcome_ty() -> CelTy {
    Record::new("outcome", [("admits", CelTy::Bool), ("how", CelTy::Str)]).into()
}

#[test]
fn a_call_host_answers_a_lazy_record() {
    let env = env_with(&[("rule", vec![], outcome_ty())]);
    let bc = emit(
        &env.compile_returning(
            r#"rule().admits ? (rule().how == "opaque" ? "allow:opaque" : "allow:route") : "refuse""#,
            &CelTy::Str,
        )
        .expect("compiles"),
    )
    .expect("emits");
    for (admits, how, want) in [
        (true, "opaque", "allow:opaque"),
        (true, "route", "allow:route"),
        (false, "", "refuse"),
    ] {
        let mut d = Counting::answering(vec![(
            "rule",
            Some(CelValue::Lazy(Arc::new(Outcome { admits, how }))),
        )]);
        let got = Vm::new()
            .eval_result_with(&bc, &req_act(&env), &mut d)
            .expect("evaluates");
        assert!(matches!(&got, CelValue::Str(s) if s == want), "{got:?}");
    }
    // An eager record serves the same members.
    let mut d = Counting::answering(vec![(
        "rule",
        Some(CelValue::Record(vec![
            (CelKey::new("admits"), CelValue::Bool(true)),
            (CelKey::new("how"), CelValue::Str("opaque".into())),
        ])),
    )]);
    let got = Vm::new().eval_result_with(&bc, &req_act(&env), &mut d);
    assert!(
        matches!(&got, Ok(CelValue::Str(s)) if s == "allow:opaque"),
        "{got:?}"
    );
}

/// No fields: every read is a call host's.
struct NoFacts;

impl Facts for NoFacts {
    fn bool(&self, _: FieldId) -> Option<bool> {
        None
    }
    fn num(&self, _: FieldId) -> Option<f64> {
        None
    }
    fn str(&self, _: FieldId) -> Option<&str> {
        None
    }
    fn has(&self, _: FieldId) -> bool {
        false
    }
    fn poll(&self, _: FieldId) -> FactPoll {
        FactPoll::Ready
    }
}

/// The production spelling: a tag over the caller's own facts, with the call hosts answered by a
/// dispatcher — and the program lists the call hosts it names.
#[test]
fn a_tag_decision_dispatches_call_hosts() {
    let env = env_with(&[("probe_a", vec![], CelTy::Bool)]);
    let p = env
        .compile_returning(r#"probe_a() ? "yes" : "no""#, &CelTy::Str)
        .expect("compiles");
    let bc = emit(&p).expect("emits");
    assert_eq!(bc.program().call_hosts(), vec!["probe_a"]);
    let tags = ["yes", "no"];
    for (a, want) in [(true, 0), (false, 1)] {
        let mut d = Counting::answering(vec![("probe_a", Some(CelValue::Bool(a)))]);
        let got = bc
            .program()
            .decide_tag_with(&NoFacts, &mut FastScratch::default(), &tags, &mut d)
            .expect("decides");
        assert_eq!(got, Some(want));
        assert_eq!(d.count("probe_a"), 1);
    }
    // A program that names none lists none.
    let plain = emit(
        &env.compile_returning(r#""yes""#, &CelTy::Str)
            .expect("compiles"),
    )
    .expect("emits");
    assert!(plain.program().call_hosts().is_empty());
}
