//! `fork::reify` turns an evaluated value back into a literal expression, or refuses.
//!
//! The property every reifying test holds is "reify then evaluate is the identity": the expression
//! `reify` returns, run by the crate's one evaluator, produces the value it was given — same
//! variant, same bits. Where no CEL literal can spell a value (a non-finite double, an opaque host
//! value, a function value) the answer is `None`, never an approximation.

use std::collections::HashMap;
use std::fmt::{Debug, Formatter, Result as FmtResult};
use std::sync::Arc;

use typed_cel::fork::ast::{Expr, IdedExpr, LiteralValue};
use typed_cel::fork::objects::{Key, Map, Opaque, Value};
use typed_cel::fork::parser::Parser;
use typed_cel::fork::{self, Context};

/// CEL's duration range in seconds (`src/duration.rs`'s `CEL_DURATION_MAX_SECS`, which is not
/// exported): ±10000 years.
const CEL_DURATION_MAX_SECS: i64 = 315_576_000_000;

fn eval_expr(e: &IdedExpr) -> Value {
    Value::resolve(e, &Context::default()).unwrap_or_else(|err| panic!("{e:?}: {err:?}"))
}

fn eval_src(src: &str) -> Value {
    let e = Parser::default()
        .parse(src)
        .unwrap_or_else(|err| panic!("{src}: {err}"));
    eval_expr(&e)
}

/// Bit-exact equality: `Value`'s `==` says `-0.0 == 0.0` and `NaN != NaN`, and neither is the
/// question here. Recurses through containers.
fn identical(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Float(x), Value::Float(y)) => x.to_bits() == y.to_bits(),
        (Value::List(x), Value::List(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| identical(p, q))
        }
        (Value::Map(x), Value::Map(y)) => {
            x.map.len() == y.map.len()
                && x.map
                    .iter()
                    .all(|(k, v)| y.map.get(k).is_some_and(|w| identical(v, w)))
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
    Value::Map(Map {
        map: Arc::new(entries.into_iter().collect::<HashMap<_, _>>()),
    })
}

fn list(items: Vec<Value>) -> Value {
    Value::List(Arc::new(items))
}

fn s(x: &str) -> Value {
    Value::String(Arc::new(x.to_string()))
}

#[test]
fn scalars_reify_to_themselves() {
    for v in [
        Value::Bool(true),
        Value::Bool(false),
        Value::Float(-3.0),
        Value::Float(i64::MIN as f64),
        Value::Float(9007199254740992.0),
        Value::Float(0.1),
        Value::Float(-0.0),
        Value::Float(1e300),
        s("a\"b\n"),
        Value::Bytes(Arc::new(vec![0, 255])),
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
    let e = round_trip(&Value::Float(7.0));
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
            fork::reify(&Value::Float(f)).is_none(),
            "Float({f}) must be refused"
        );
        let l = list(vec![Value::Float(1.0), Value::Float(f)]);
        assert!(
            fork::reify(&l).is_none(),
            "a list holding Float({f}) must be refused"
        );
        let m = map(vec![(Key::Num(1), Value::Float(f))]);
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
    let inner = map(vec![
        (
            Key::String(Arc::new("xs".into())),
            list(vec![Value::Float(1.0), Value::Float(2.5)]),
        ),
        (Key::Num(-4), list(vec![])),
        (Key::Bool(true), map(vec![])),
    ]);
    let v = list(vec![
        inner.clone(),
        map(vec![(
            Key::String(Arc::new("nested".into())),
            list(vec![inner, s("x"), Value::Null]),
        )]),
        list(vec![]),
    ]);
    round_trip(&v);
}

/// `Map` is a `HashMap`, so its iteration order is whatever the hasher says. Sorting the entries
/// is what makes a residual's text deterministic.
#[test]
fn map_entries_are_sorted() {
    let keys: Vec<String> = (0..20).map(|i| format!("k{i:02}")).collect();
    let forward = map(keys
        .iter()
        .map(|k| {
            (
                Key::String(Arc::new(k.clone())),
                Value::Float(k.len() as f64),
            )
        })
        .collect());
    let backward = map(keys
        .iter()
        .rev()
        .map(|k| {
            (
                Key::String(Arc::new(k.clone())),
                Value::Float(k.len() as f64),
            )
        })
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

#[derive(Eq, PartialEq)]
struct HostHandle(u64);

impl Debug for HostHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "HostHandle({})", self.0)
    }
}

impl Opaque for HostHandle {
    fn runtime_type_name(&self) -> &str {
        "test.HostHandle"
    }
}

#[test]
fn opaque_and_function_are_refused() {
    let opaque = Value::Opaque(Arc::new(HostHandle(7)));
    assert!(
        fork::reify(&opaque).is_none(),
        "an opaque value has no source form"
    );
    let function = Value::Function(Arc::new("size".into()), None);
    assert!(
        fork::reify(&function).is_none(),
        "a function value has no source form"
    );
    assert!(
        fork::reify(&list(vec![Value::Float(1.0), opaque])).is_none(),
        "a list holding an opaque value must be refused"
    );
    assert!(
        fork::reify(&map(vec![(Key::Num(1), function)])).is_none(),
        "a map holding a function value must be refused"
    );
}
