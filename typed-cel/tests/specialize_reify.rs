//! `fork::reify` turns an evaluated value back into a literal expression, or refuses.
//!
//! The property every reifying test holds is "reify then evaluate is the identity": the expression
//! `reify` returns, run on the backend, produces the value it was given — same
//! variant, same bits. Where no CEL literal can spell a value (a non-finite double, an opaque host
//! value, a function value) the answer is `None`, never an approximation.

#[path = "support/mod.rs"]
mod support;

use std::sync::Arc;

use typed_cel::fork;
use typed_cel::fork::ast::{Expr, IdedExpr, LiteralValue};
use typed_cel::{CelError, CelKey, CelMap, CelMapKey as Key, CelValue as Value, LazyValue};

/// CEL's duration range in seconds (`src/duration.rs`'s `CEL_DURATION_MAX_SECS`, which is not
/// exported): ±10000 years.
const CEL_DURATION_MAX_SECS: i64 = 315_576_000_000;

/// `e` on the backend: rendered (`fork::unparse`), checked and run.
fn eval_expr(e: &IdedExpr) -> Value {
    let src = fork::unparse(e).unwrap_or_else(|err| panic!("{e:?} does not render: {err}"));
    eval_src(&src)
}

fn eval_src(src: &str) -> Value {
    support::run_closed(src).unwrap_or_else(|err| panic!("{src}: {err:?}"))
}

/// Bit-exact equality: `Value`'s `==` says `-0.0 == 0.0` and `NaN != NaN`, and neither is the
/// question here. Recurses through containers.
fn identical(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Num(x), Value::Num(y)) => x.to_bits() == y.to_bits(),
        (Value::List(x), Value::List(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| identical(p, q))
        }
        (Value::Map(x), Value::Map(y)) => {
            x.len() == y.len()
                && x.iter()
                    .zip(y.iter())
                    .all(|((k, v), (l, w))| k == l && identical(v, w))
        }
        _ => a == b,
    }
}

/// Reify `v`, evaluate the result, and require the value comes back identically.
fn round_trip(v: &Value) -> IdedExpr {
    let e = fork::reify(v).unwrap_or_else(|| panic!("{v:?} was refused"));
    let back = eval_expr(&e);
    assert!(
        identical(&back, v),
        "reify then evaluate is not the identity: {v:?} -> {e:?} -> {back:?}"
    );
    e
}

fn map(entries: Vec<(Key, Value)>) -> Value {
    Value::Map(CelMap::new(entries))
}

fn list(items: Vec<Value>) -> Value {
    Value::list(items)
}

fn s(x: &str) -> Value {
    Value::from(x)
}

#[test]
fn scalars_reify_to_themselves() {
    for v in [
        Value::Bool(true),
        Value::Bool(false),
        Value::Num(-3.0),
        Value::Num(i64::MIN as f64),
        Value::Num(9007199254740992.0),
        Value::Num(0.1),
        Value::Num(-0.0),
        Value::Num(1e300),
        s("a\"b\n"),
        Value::Bytes(vec![0, 255].into()),
        Value::Null,
    ] {
        let e = round_trip(&v);
        assert!(
            matches!(e.expr, Expr::Literal(_)),
            "a scalar reifies as a literal, got {e:?}"
        );
    }
}

/// Every number is a `Float`, even `7`, and reifies as a `Double` literal: there is no runtime
/// integer for an `Int` literal to stand for (`removed: integer values`).
#[test]
fn bound_number_reifies_as_double() {
    let e = round_trip(&Value::Num(7.0));
    assert!(
        matches!(e.expr, Expr::Literal(LiteralValue::Double(_))),
        "Float(7.0) must reify as a Double literal, got {e:?}"
    );
    assert_eq!(fork::unparse(&e).unwrap(), "7.0");
}

/// The parser refuses a non-finite double literal, so no residual can spell one. Not saturated,
/// not stringified: refused, so the fold keeps the expression that produced it.
#[test]
fn nonfinite_is_not_reified() {
    for f in [f64::INFINITY, f64::NEG_INFINITY, f64::NAN] {
        assert!(
            fork::reify(&Value::Num(f)).is_none(),
            "Float({f}) must be refused"
        );
        let l = list(vec![Value::Num(1.0), Value::Num(f)]);
        assert!(
            fork::reify(&l).is_none(),
            "a list holding Float({f}) must be refused"
        );
        let m = map(vec![(Key::Num(1), Value::Num(f))]);
        assert!(
            fork::reify(&m).is_none(),
            "a map holding Float({f}) must be refused"
        );
    }
}

#[test]
fn durations_reify_as_duration_calls() {
    for src in [
        "duration('90s')".to_string(),
        "duration('-1500ms')".to_string(),
        "duration('1ns')".to_string(),
        "duration('0s')".to_string(),
        "duration('-1ns')".to_string(),
        format!("duration('{CEL_DURATION_MAX_SECS}s')"),
        format!("duration('-{CEL_DURATION_MAX_SECS}s')"),
    ] {
        let v = eval_src(&src);
        assert!(matches!(v, Value::Duration(_)), "{src} evaluates to {v:?}");
        let e = round_trip(&v);
        let Expr::Call(c) = &e.expr else {
            panic!("{src}: a duration reifies as a call, got {e:?}");
        };
        assert_eq!(c.func_name, "duration", "{src}");
        assert!(c.target.is_none(), "{src}");
        assert!(
            matches!(
                c.args.as_slice(),
                [IdedExpr {
                    expr: Expr::Literal(LiteralValue::String(_)),
                    ..
                }]
            ),
            "{src}: one string argument, got {:?}",
            c.args
        );
    }
}

#[test]
fn containers_reify_recursively() {
    let str_key = |k: &str| Key::Str(CelKey::new(k));
    // Lists of maps of lists, nested — every container homogeneous, as a checked program's
    // values are, so the round trip runs through the checker.
    let leaf = |xs: Vec<f64>| {
        map(vec![(
            str_key("xs"),
            list(xs.into_iter().map(Value::Num).collect()),
        )])
    };
    let v = list(vec![
        map(vec![(
            str_key("a"),
            list(vec![leaf(vec![1.0, 2.5]), leaf(vec![])]),
        )]),
        map(vec![(str_key("a"), list(vec![]))]),
    ]);
    round_trip(&v);
    // Every key kind a map can have.
    round_trip(&map(vec![
        (Key::Num(-4), list(vec![])),
        (Key::Num(2), list(vec![Value::Num(1.0)])),
    ]));
    round_trip(&map(vec![
        (Key::Bool(true), s("t")),
        (Key::Bool(false), s("f")),
    ]));
    // A map whose keys differ in kind is no checked program's value, so it has no round trip; it
    // still reifies, keys sorted by kind.
    let mixed = map(vec![
        (str_key("xs"), list(vec![])),
        (Key::Num(-4), list(vec![])),
        (Key::Bool(true), list(vec![])),
    ]);
    let e = fork::reify(&mixed).expect("a mixed-key map reifies");
    assert_eq!(
        fork::unparse(&e).unwrap(),
        r#"{(-4.0): [], true: [], "xs": []}"#
    );
}

/// Built in any order, a map is held — and rendered — in key order, which is what makes a
/// residual's text deterministic.
#[test]
fn map_entries_are_sorted() {
    let keys: Vec<String> = (0..20).map(|i| format!("k{i:02}")).collect();
    let forward = map(keys
        .iter()
        .map(|k| (Key::Str(CelKey::new(k)), Value::Num(k.len() as f64)))
        .collect());
    let backward = map(keys
        .iter()
        .rev()
        .map(|k| (Key::Str(CelKey::new(k)), Value::Num(k.len() as f64)))
        .collect());
    let a = fork::unparse(&round_trip(&forward)).unwrap();
    let b = fork::unparse(&round_trip(&backward)).unwrap();
    assert_eq!(a, b, "the same map rendered two ways");

    let positions: Vec<usize> = keys
        .iter()
        .map(|k| {
            a.find(&format!("\"{k}\""))
                .unwrap_or_else(|| panic!("{k} in {a}"))
        })
        .collect();
    assert!(
        positions.windows(2).all(|w| w[0] < w[1]),
        "keys are not ascending in {a}"
    );
}

/// A lazy view: served on access, so it has no source form.
#[derive(Debug)]
struct View;

impl LazyValue for View {
    fn member(&self, name: &str) -> Result<Value, CelError> {
        Err(CelError::NoSuchMember {
            key: name.to_string(),
        })
    }
}

#[test]
fn a_lazy_view_is_refused() {
    let view = Value::Lazy(Arc::new(View));
    assert!(
        fork::reify(&view).is_none(),
        "a lazy view has no source form"
    );
    assert!(
        fork::reify(&list(vec![Value::Num(1.0), view.clone()])).is_none(),
        "a list holding a lazy view must be refused"
    );
    assert!(
        fork::reify(&map(vec![(Key::Num(1), view)])).is_none(),
        "a map holding a lazy view must be refused"
    );
}
