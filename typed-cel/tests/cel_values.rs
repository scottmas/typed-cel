//! `CelValue` beyond scalars — bytes, lists, records, null — bound straight into an activation, and
//! the prepared run-time half of an environment: `CelRuntime`, `bind_fact`, `Vm::eval_result`.
//!
//! Every value is checked on BOTH engines (the tree evaluator and the VM over `emit`), so a variant
//! that converts correctly for one and not the other fails here rather than in a caller.

use typed_cel::fork;
use typed_cel::{
    emit, CelActivation, CelBytecode, CelEnvironment, CelKey, CelProgram, CelRuntime, CelTy,
    CelValue, Record, Vm,
};

/// `Ok(true)` on the tree evaluator AND on the VM.
fn true_on_both(p: &CelProgram, act: &CelActivation) {
    assert_eq!(
        p.evaluate(act).map_err(|e| e.to_string()),
        Ok(true),
        "evaluator: `{}`",
        p.source()
    );
    let code = emit(p).expect("emits");
    assert_eq!(
        Vm::new().eval(&code, act).map_err(|e| e.to_string()),
        Ok(true),
        "vm: `{}`",
        p.source()
    );
}

/// Structural equality. `CelValue` has no `PartialEq` (it may hold a lazy view), so the test says
/// what "the same" means for the variants a result can take.
fn same(a: &CelValue, b: &CelValue) -> bool {
    use CelValue as V;
    match (a, b) {
        (V::Bool(x), V::Bool(y)) => x == y,
        (V::Num(x), V::Num(y)) => x.to_bits() == y.to_bits(),
        (V::Str(x), V::Str(y)) => x == y,
        (V::Duration(x), V::Duration(y)) => x == y,
        (V::Bytes(x), V::Bytes(y)) => x == y,
        (V::Null, V::Null) => true,
        (V::List(x), V::List(y)) => x.len() == y.len() && x.iter().zip(y).all(|(p, q)| same(p, q)),
        (V::Record(x), V::Record(y)) => {
            x.len() == y.len()
                && x.iter()
                    .zip(y)
                    .all(|((kp, vp), (kq, vq))| kp == kq && same(vp, vq))
        }
        _ => false,
    }
}

#[test]
fn a_bytes_value_binds_and_compares() {
    let mut env = CelEnvironment::new();
    env.declare("x", CelTy::Bytes);
    let p = env.compile(r#"x == b"/ws/\xff""#).expect("compiles");
    let mut act = env.runtime().activation();
    act.bind_fact("x", CelValue::Bytes(b"/ws/\xff".to_vec()));
    true_on_both(&p, &act);

    // And a different byte string is not equal — the comparison is on the bytes, not vacuous.
    let mut other = env.runtime().activation();
    other.bind_fact("x", CelValue::Bytes(b"/ws/\xfe".to_vec()));
    assert_eq!(p.evaluate(&other).map_err(|e| e.to_string()), Ok(false));
}

#[test]
fn a_record_value_is_selectable() {
    let mut env = CelEnvironment::new();
    env.declare(
        "r",
        Record::new(
            "r",
            [("a", CelTy::Str), ("n", CelTy::Num), ("b", CelTy::Bool)],
        ),
    );
    let p = env
        .compile(r#"r.a == "x" && r.n == 3 && r.b"#)
        .expect("compiles");
    let mut act = env.runtime().activation();
    act.bind_fact(
        "r",
        CelValue::Record(vec![
            ("a".into(), CelValue::Str("x".into())),
            ("n".into(), CelValue::Num(3.0)),
            ("b".into(), CelValue::Bool(true)),
        ]),
    );
    true_on_both(&p, &act);
}

#[test]
fn a_list_value_is_iterable() {
    let mut env = CelEnvironment::new();
    env.declare("l", CelTy::List(std::rc::Rc::new(CelTy::Str)));
    let mut act = env.runtime().activation();
    act.bind_fact(
        "l",
        CelValue::List(vec![CelValue::Str("a".into()), CelValue::Str("b".into())]),
    );
    for src in [r#"l.exists(s, s == "b")"#, "size(l) == 2"] {
        let p = env.compile(src).expect("compiles");
        true_on_both(&p, &act);
    }
}

#[test]
fn null_binds_as_null() {
    let mut env = CelEnvironment::new();
    env.declare("z", CelTy::Null);
    let p = env.compile("z == null").expect("compiles");
    let mut act = env.runtime().activation();
    act.bind_fact("z", CelValue::Null);
    true_on_both(&p, &act);
}

/// Bytecode for an expression of any result type, checked against an empty roster.
fn any_result(src: &str) -> CelBytecode {
    let p = fork::compile_any(&CelEnvironment::new(), src).unwrap_or_else(|e| panic!("{src}: {e}"));
    emit(&p).expect("emits")
}

#[test]
fn eval_result_returns_non_bool_values() {
    let act = CelEnvironment::new().runtime().activation();
    let cases: Vec<(&str, CelValue)> = vec![
        (r#""allow""#, CelValue::Str("allow".into())),
        (r#"b"ab""#, CelValue::Bytes(b"ab".to_vec())),
        (
            "[1, 2]",
            CelValue::List(vec![CelValue::Num(1.0), CelValue::Num(2.0)]),
        ),
        (
            r#"{"k": true}"#,
            CelValue::Record(vec![(CelKey::new("k"), CelValue::Bool(true))]),
        ),
        ("null", CelValue::Null),
    ];
    for (src, want) in cases {
        let got = Vm::new()
            .eval_result(&any_result(src), &act)
            .unwrap_or_else(|e| panic!("`{src}`: {e}"));
        assert!(same(&got, &want), "`{src}`: want {want:?}, got {got:?}");
    }
}

#[test]
fn eval_result_carries_an_evaluation_error() {
    let act = CelEnvironment::new().runtime().activation();
    let err = Vm::new()
        .eval_result(&any_result("{}.a"), &act)
        .expect_err("a missing key is an error, not a value");
    assert!(err.to_string().contains("could not be evaluated"), "{err}");
}

#[test]
fn bind_fact_does_not_consult_the_roster() {
    // A runtime from an environment that declares NOTHING still binds any name: the roster is
    // held at compile time, not at bind time.
    let runtime = CelEnvironment::new().runtime();
    let mut act = runtime.activation();
    act.bind_fact("anything", CelValue::Num(1.0));

    let mut declaring = CelEnvironment::new();
    declaring.declare("anything", CelTy::Num);
    let p = declaring.compile("anything == 1").expect("compiles");
    true_on_both(&p, &act);
}

#[test]
fn a_runtime_outlives_its_environment() {
    let (runtime, program) = {
        let mut env = CelEnvironment::new();
        env.declare("x", CelTy::Num);
        // `1.0`, not `1`: `Num + int literal` is an evaluation error in this dialect.
        let p = env.compile("x + 1.0 == 1000.0").expect("compiles");
        (env.runtime(), p)
        // `env` drops here.
    };
    let code = emit(&program).expect("emits");
    let (mut vm_hits, mut tree_hits) = (0, 0);
    for i in 0..1000 {
        let mut act = runtime.activation();
        act.bind_fact("x", CelValue::Num(i as f64));
        vm_hits += Vm::new().eval(&code, &act).expect("vm evaluates") as usize;
        tree_hits += program.evaluate(&act).expect("evaluator evaluates") as usize;
    }
    // Exactly x = 999: every activation read ITS OWN binding.
    assert_eq!((vm_hits, tree_hits), (1, 1));
}

#[test]
fn the_runtime_is_send_and_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<CelRuntime>();
    assert_send_sync::<CelBytecode>();
    assert_send_sync::<CelProgram>();
}
