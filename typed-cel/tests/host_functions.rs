//! Host functions: typed, pure functions an embedding ENVIRONMENT registers. The checker types a
//! call to one, the tree evaluator and the fast backend both dispatch it, and a specialization
//! folds it exactly when every argument is known. The dialect's own signature table never grows.

#[path = "support/mod.rs"]
mod support;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use support::gen::{host_roster, host_typed_json, Gen, SEEDS};
use typed_cel::{
    emit, CelActivation, CelEnvironment, CelError, CelKey, CelNum, CelProgram, CelTy, CelValue,
    HostCall, LazyValue, Vm,
};

fn eval_err(message: &str) -> CelError {
    CelError::Evaluation {
        source: Arc::from("host"),
        message: message.to_string(),
    }
}

fn twice() -> HostCall {
    Arc::new(|a: &[CelValue]| match a {
        // A number arrives in whichever representation holds it (`twice(3)` is an integer).
        [a] => match a.num() {
            Some(n) => Ok(CelValue::from(CelNum::from_f64(n.as_f64() * 2.0))),
            None => Err(eval_err("twice expects one number")),
        },
        _ => Err(eval_err("twice expects one number")),
    })
}

fn with_twice() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.register_host("twice", &[CelTy::Num], CelTy::Num, false, twice())
        .expect("`twice` is no dialect name");
    env
}

/// `Ok(true)` on the backend, over an activation `bind` fills.
fn is_true(env: &CelEnvironment, p: &CelProgram, bind: &dyn Fn(&mut CelActivation)) {
    let mut act = env.runtime().activation();
    bind(&mut act);
    assert_eq!(
        p.evaluate(&act).map_err(|e| e.to_string()),
        Ok(true),
        "`{}`",
        p.source()
    );
}

#[test]
fn a_registered_host_function_type_checks_and_runs() {
    let mut env = with_twice();
    env.declare("x", CelTy::Num);
    let p = env.compile("twice(x) == 4.0").expect("compiles");
    is_true(&env, &p, &|act| {
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
            [CelValue::Str(s)] => Ok(CelValue::from(format!("{}!", s.to_uppercase()))),
            _ => Err(eval_err("shout expects a string receiver")),
        }),
    )
    .expect("registers");
    env.declare("s", CelTy::Str);
    for src in [r#""a".shout() == "A!""#, r#"s.shout() == "AB!""#] {
        let p = env.compile(src).expect("compiles");
        is_true(&env, &p, &|act| {
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
                [CelValue::Str(s)] => Ok(CelValue::from(format!("{s}/"))),
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
            CelValue::Str(s) => s.to_string(),
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
    let mut act = env.runtime().activation();
    act.bind_fact("x", CelValue::Num(1.0));
    let a = Vm::new()
        .eval_result(&emit(&p).expect("emits"), &act)
        .expect_err("the backend reports it");
    assert!(matches!(a, CelError::Evaluation { .. }), "{a:?}");
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
                    .map(|v| v.num().map_or(f64::NAN, CelNum::as_f64))
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
    is_true(&env, &p, &|act| {
        act.bind_fact(
            "xs",
            CelValue::list([CelValue::Num(1.0), CelValue::Num(2.0), CelValue::Num(3.0)]),
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
    is_true(&env, &p, &|act| {
        act.bind_fact("v", CelValue::Lazy(Arc::clone(&view)));
    });
    assert_eq!(seen.load(Ordering::SeqCst), 1, "the backend called it once");
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

/// Every name the retired evaluator's standard library declared (`Env::stdlib()`, captured before
/// it was deleted). A host function never takes one: each is a dialect built-in, and the refusal
/// must outlive the table it used to be read from.
const RETIRED_STDLIB: &[&str] = &[
    "contains",
    "duration",
    "endsWith",
    "getMilliseconds",
    "getSeconds",
    "matches",
    "size",
    "startsWith",
];

#[test]
fn register_host_refuses_every_name_the_retired_stdlib_declared() {
    for name in RETIRED_STDLIB {
        match CelEnvironment::new().register_host(name, &[CelTy::Str], CelTy::Bool, false, twice())
        {
            Err(CelError::Registration { .. }) => {}
            Err(other) => panic!("`{name}`: refused, but not as a registration: {other}"),
            Ok(_) => panic!("`{name}` registered as a host function"),
        }
    }
}
