//! Host functions: typed, pure functions an embedding ENVIRONMENT registers. The checker types a
//! call to one, the tree evaluator and the fast backend both dispatch it, and a specialization
//! folds it exactly when every argument is known. The dialect's own signature table never grows.

#[path = "support/mod.rs"]
mod support;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use support::gen::{host_roster, host_typed_json, Gen, SEEDS};
use typed_cel::{
    emit, CelActivation, CelEnvironment, CelError, CelKey, CelProgram, CelTy, CelValue, HostCall,
    LazyValue, Vm,
};

fn eval_err(message: &str) -> CelError {
    CelError::Evaluation {
        source: Arc::from("host"),
        message: message.to_string(),
    }
}

fn twice() -> HostCall {
    Arc::new(|a: &[CelValue]| match a {
        [CelValue::Num(n)] => Ok(CelValue::Num(n * 2.0)),
        _ => Err(eval_err("twice expects one number")),
    })
}

fn with_twice() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.register_host("twice", &[CelTy::Num], CelTy::Num, false, twice())
        .expect("`twice` is no dialect name");
    env
}

/// `Ok(true)` through `CelProgram::evaluate` (the tree evaluator, which needs the environment's
/// activation) AND through `Vm::eval` (the fast backend, on a prepared activation).
fn true_on_both(env: &CelEnvironment, p: &CelProgram, bind: &dyn Fn(&mut CelActivation)) {
    let mut tree = env.activation();
    bind(&mut tree);
    assert_eq!(
        p.evaluate(&tree).map_err(|e| e.to_string()),
        Ok(true),
        "evaluator: `{}`",
        p.source()
    );
    let mut prepared = env.runtime().activation();
    bind(&mut prepared);
    assert_eq!(
        Vm::new()
            .eval(&emit(p).expect("emits"), &prepared)
            .map_err(|e| e.to_string()),
        Ok(true),
        "vm: `{}`",
        p.source()
    );
}

#[test]
fn a_registered_host_function_type_checks_and_runs() {
    let mut env = with_twice();
    env.declare("x", CelTy::Num);
    let p = env.compile("twice(x) == 4.0").expect("compiles");
    true_on_both(&env, &p, &|act| {
        act.bind_fact("x", CelValue::Num(2.0));
    });
}

#[test]
fn a_member_host_function_runs_as_a_method() {
    let mut env = CelEnvironment::new();
    env.register_host(
        "shout",
        &[CelTy::Str],
        CelTy::Str,
        true,
        Arc::new(|a: &[CelValue]| match a {
            [CelValue::Str(s)] => Ok(CelValue::Str(format!("{}!", s.to_uppercase()))),
            _ => Err(eval_err("shout expects a string receiver")),
        }),
    )
    .expect("registers");
    env.declare("s", CelTy::Str);
    for src in [r#""a".shout() == "A!""#, r#"s.shout() == "AB!""#] {
        let p = env.compile(src).expect("compiles");
        true_on_both(&env, &p, &|act| {
            act.bind_fact("s", CelValue::Str("ab".into()));
        });
    }
}

#[test]
fn a_host_call_with_the_wrong_argument_type_is_a_check_error() {
    let err = with_twice()
        .compile("twice(\"a\") == 1.0")
        .expect_err("a string is not a double");
    let msg = err.to_string();
    assert!(matches!(err, CelError::Check { .. }), "{err:?}");
    assert!(
        msg.contains("twice") && msg.contains("(double) -> double"),
        "{msg}"
    );
}

#[test]
fn an_unknown_name_keeps_the_dialect_diagnostic() {
    let bare = CelEnvironment::new()
        .compile("nope(1.0) == 1.0")
        .expect_err("unknown")
        .to_string();
    assert!(
        bare.contains("this dialect registers no custom functions"),
        "{bare}"
    );
    assert!(!bare.contains("registered host functions"), "{bare}");

    let hosted = with_twice()
        .compile("nope(1.0) == 1.0")
        .expect_err("unknown")
        .to_string();
    assert!(
        hosted.contains("registered host functions: twice"),
        "{hosted}"
    );
}

#[test]
fn a_host_function_cannot_shadow_the_dialect() {
    let mut env = with_twice();
    for name in [
        "size",
        "startsWith",
        "int",
        "timestamp",
        "exists",
        "has",
        "_==_",
        "@in",
        "!_",
        "9lives",
        "",
        "a.b",
        "twice",
    ] {
        let got = env.register_host(name, &[CelTy::Num], CelTy::Num, false, twice());
        assert!(
            matches!(got, Err(CelError::Registration { .. })),
            "`{name}` must be refused: {:?}",
            got.map(|_| ())
        );
    }
}

#[test]
fn host_calls_fold_only_when_every_argument_is_known() {
    let count = Arc::new(AtomicUsize::new(0));
    let mut env = CelEnvironment::new();
    let c = Arc::clone(&count);
    env.register_host(
        "count_me",
        &[CelTy::Str],
        CelTy::Str,
        false,
        Arc::new(move |a: &[CelValue]| {
            c.fetch_add(1, Ordering::SeqCst);
            match a {
                [CelValue::Str(s)] => Ok(CelValue::Str(format!("{s}/"))),
                _ => Err(eval_err("count_me expects one string")),
            }
        }),
    )
    .expect("registers");
    env.declare("k", typed_cel::Record::new("k", [("r", CelTy::Str)]));
    env.declare("u", CelTy::Str);
    let p = env
        .compile_returning(
            r#"u.startsWith(count_me(k.r)) ? "hit" : count_me(u)"#,
            &CelTy::Str,
        )
        .expect("compiles");
    assert_eq!(count.load(Ordering::SeqCst), 0, "compiling calls nothing");
    let mut known = env.activation();
    known
        .bind("k", &serde_json::json!({"r": "/a"}))
        .expect("binds");
    let residual = env.specialize(&p, &known).expect("specializes");
    let src = residual.source();
    assert!(src.contains("\"/a/\""), "{src}");
    assert_eq!(src.matches("count_me(").count(), 1, "{src}");
    assert_eq!(
        count.load(Ordering::SeqCst),
        1,
        "the known-argument call folded once"
    );

    let code = emit(&residual).expect("emits");
    let run = |u: &str| {
        let mut act = env.runtime().activation();
        act.bind_fact("u", CelValue::Str(u.into()));
        match Vm::new().eval_result(&code, &act).expect("evaluates") {
            CelValue::Str(s) => s,
            other => panic!("{other:?}"),
        }
    };
    assert_eq!(run("/a/x"), "hit");
    assert_eq!(count.load(Ordering::SeqCst), 1);
    assert_eq!(run("/b"), "/b/");
    assert_eq!(count.load(Ordering::SeqCst), 2);
}

#[test]
fn a_host_error_is_an_evaluation_error_not_a_panic() {
    let mut env = CelEnvironment::new();
    env.register_host(
        "boom",
        &[CelTy::Num],
        CelTy::Num,
        false,
        Arc::new(|_: &[CelValue]| Err(eval_err("no"))),
    )
    .expect("registers");
    env.declare("x", CelTy::Num);
    let p = env.compile("boom(x) == 1.0").expect("compiles");
    let mut tree = env.activation();
    tree.bind_fact("x", CelValue::Num(1.0));
    let a = p.evaluate(&tree).expect_err("the evaluator reports it");
    let mut prepared = env.runtime().activation();
    prepared.bind_fact("x", CelValue::Num(1.0));
    let b = Vm::new()
        .eval_result(&emit(&p).expect("emits"), &prepared)
        .expect_err("the fast backend reports it");
    assert!(matches!(a, CelError::Evaluation { .. }), "{a:?}");
    // One error, worded identically by both engines.
    assert_eq!(a.to_string(), b.to_string());
    assert!(a.to_string().contains("boom"), "{a}");
}

/// A lazy record that counts nothing and serves one member.
#[derive(Debug)]
struct View;

impl LazyValue for View {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        match name {
            "a" => Ok(CelValue::Num(1.0)),
            _ => Err(CelError::NoSuchMember { key: name.into() }),
        }
    }
    fn keys(&self) -> Option<Box<dyn Iterator<Item = &CelKey> + '_>> {
        None
    }
}

#[test]
fn a_host_argument_with_no_cel_value_form_is_an_error() {
    // A list built by a comprehension converts, element by element.
    let mut env = CelEnvironment::new();
    env.register_host(
        "total",
        &[CelTy::list(CelTy::Num)],
        CelTy::Num,
        false,
        Arc::new(|a: &[CelValue]| match a {
            [CelValue::List(items)] => Ok(CelValue::Num(
                items
                    .iter()
                    .map(|v| match v {
                        CelValue::Num(n) => *n,
                        _ => f64::NAN,
                    })
                    .sum(),
            )),
            _ => Err(eval_err("total expects a list")),
        }),
    )
    .expect("registers");
    env.declare("xs", CelTy::list(CelTy::Num));
    let p = env
        .compile("total(xs.map(x, x * 2.0)) == 12.0")
        .expect("compiles");
    true_on_both(&env, &p, &|act| {
        act.bind_fact(
            "xs",
            CelValue::List(vec![
                CelValue::Num(1.0),
                CelValue::Num(2.0),
                CelValue::Num(3.0),
            ]),
        );
    });

    // A lazy argument arrives as the view it was bound with, not a copy.
    let view: Arc<dyn LazyValue> = Arc::new(View);
    let seen = Arc::new(AtomicUsize::new(0));
    let ty: CelTy = typed_cel::Record::new("v", [("a", CelTy::Num)]).into();
    let mut env = CelEnvironment::new();
    let (want, hits) = (Arc::clone(&view), Arc::clone(&seen));
    env.register_host(
        "same_view",
        std::slice::from_ref(&ty),
        CelTy::Bool,
        false,
        Arc::new(move |a: &[CelValue]| match a {
            [CelValue::Lazy(v)] => {
                hits.fetch_add(1, Ordering::SeqCst);
                Ok(CelValue::Bool(Arc::ptr_eq(v, &want)))
            }
            other => Err(eval_err(&format!("not a view: {other:?}"))),
        }),
    )
    .expect("registers");
    env.declare("v", ty);
    let p = env.compile("same_view(v)").expect("compiles");
    true_on_both(&env, &p, &|act| {
        act.bind_fact("v", CelValue::Lazy(Arc::clone(&view)));
    });
    assert_eq!(seen.load(Ordering::SeqCst), 2, "both engines called it");
}

#[test]
fn emit_is_deterministic_with_hosts() {
    let mut env = with_twice();
    env.declare("x", CelTy::Num);
    let p = env.compile("twice(twice(x)) == 8.0").expect("compiles");
    let (a, b) = (
        typed_cel::FastProgram::new(&p).expect("lowers"),
        typed_cel::FastProgram::new(&p).expect("lowers"),
    );
    assert_eq!(a.listing(), b.listing());
    assert!(a.listing().contains("Host"), "{}", a.listing());
}

/// Generated expressions over a roster with host functions, on both engines: the same verdict, or
/// the same error text, for every activation — a host call nested anywhere a value may be.
#[test]
fn generated_host_calls_agree_with_the_evaluator() {
    let env = host_roster();
    let mut compared = 0usize;
    let mut calls = 0usize;
    let mut mismatches = Vec::new();
    for seed in SEEDS {
        let mut g = Gen::new(seed ^ 0x4057);
        for index in 0..300 {
            let src = g.host_bool(4);
            calls += src.matches("twice(").count() + src.matches("tag(").count();
            let whence = format!("seed={seed:#x}, index={index}");
            let p = env
                .compile(&src)
                .unwrap_or_else(|e| panic!("{whence}: `{src}` does not compile:\n{e}"));
            let code = emit(&p).expect("emits");
            for _ in 0..3 {
                let json = host_typed_json(&mut g);
                let mut tree = env.activation();
                let mut prepared = env.activation();
                for (name, v) in &json {
                    tree.bind(name, v).expect("binds");
                    prepared.bind(name, v).expect("binds");
                }
                let a = p.evaluate(&tree).map_err(|e| e.to_string());
                let b = Vm::new().eval(&code, &prepared).map_err(|e| e.to_string());
                compared += 1;
                if a != b {
                    mismatches.push(format!(
                        "{whence}: {src}\n  with {json:?}\n  evaluate: {a:?}\n  vm:       {b:?}"
                    ));
                }
            }
        }
    }
    assert!(
        mismatches.is_empty(),
        "{} mismatch(es):\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
    assert!(calls >= 500, "only {calls} host calls were generated");
    assert!(compared >= 2000, "only {compared} comparisons");
}
