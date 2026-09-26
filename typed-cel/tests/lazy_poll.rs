//! A lazy value that can answer "not yet".
//!
//! `poll_member`/`poll_has` are how a value that is still arriving says a member is pending. The
//! evaluators that cannot wait (the tree walker, and `Vm::eval`) must treat a pending read as an
//! evaluation error that `&&`/`||` absorb exactly as they absorb any other. And `has(x.k)` / `k in
//! x` over a lazy are EXISTENCE questions answered through `poll_has`, never the member's value.
//!
//! Every verdict here is asked of both the tree walker and the VM, which must agree.

#[path = "support/mod.rs"]
mod support;

#[path = "support/scripted.rs"]
mod scripted;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use scripted::{Scripted, Slot};
use support::record_opt;
use typed_cel::{
    Access, CelActivation, CelEnvironment, CelError, CelKey, CelTy, CelValue, DemandHandle,
    LazyValue, Presence, Vm,
};

fn no_such(key: &str) -> CelError {
    CelError::NoSuchMember {
        key: key.to_string(),
    }
}

/// `tests/lazy.rs`'s record view: implements ONLY `member`, and counts every call.
#[derive(Debug)]
struct CountingRecord {
    field: f64,
    reads: Arc<AtomicUsize>,
}

impl LazyValue for CountingRecord {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        self.reads.fetch_add(1, Ordering::SeqCst);
        match name {
            "field" => Ok(CelValue::Num(self.field)),
            "boom" => Err(CelError::Bind {
                message: "boom failed".into(),
            }),
            other => Err(no_such(other)),
        }
    }
}

/// `tests/lazy.rs`'s map view: has `keys()`, counts member reads and key iterations.
#[derive(Debug)]
struct CountingMap {
    keys: Vec<CelKey>,
    reads: Arc<AtomicUsize>,
    iterations: Arc<AtomicUsize>,
}

impl LazyValue for CountingMap {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        self.reads.fetch_add(1, Ordering::SeqCst);
        if self.keys.iter().any(|k| k.as_str() == name) {
            Ok(CelValue::Num(1.0))
        } else {
            Err(no_such(name))
        }
    }

    fn keys(&self) -> Option<Box<dyn Iterator<Item = &CelKey> + '_>> {
        self.iterations.fetch_add(1, Ordering::SeqCst);
        Some(Box::new(self.keys.iter()))
    }
}

/// A map-typed lazy with NO `keys()`: `a` is present, everything else is not.
#[derive(Debug)]
struct Keyless;

impl LazyValue for Keyless {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        match name {
            "a" => Ok(CelValue::Num(1.0)),
            other => Err(no_such(other)),
        }
    }
}

/// Evaluate `src` with the tree walker and the VM, assert they agree, and return the walker's.
fn both(env: &CelEnvironment, act: &CelActivation, src: &str) -> Result<bool, CelError> {
    let program = env.compile(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    let walked = program.evaluate(act);
    let bytecode = typed_cel::emit(&program).expect("emits");
    let vm = Vm::new().eval(&bytecode, act);
    match (&walked, &vm) {
        (Ok(a), Ok(b)) => assert_eq!(a, b, "{src}: walker and VM disagree"),
        (Err(a), Err(b)) => assert_eq!(
            a.to_string(),
            b.to_string(),
            "{src}: walker and VM word the error differently"
        ),
        _ => panic!("{src}: walker {walked:?}, VM {vm:?}"),
    }
    walked
}

fn evaluation_message(r: Result<bool, CelError>) -> String {
    match r {
        Err(CelError::Evaluation { message, .. }) => message,
        other => panic!("expected an evaluation error, got {other:?}"),
    }
}

fn scripted_env() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.declare(
        "v",
        record_opt("v", &[("x", CelTy::Num), ("field", CelTy::Num)], &["field"]),
    );
    env.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    env
}

fn bind(env: &CelEnvironment, name: &str, value: Arc<dyn LazyValue>) -> CelActivation {
    let mut act = env.activation();
    act.bind_lazy(name, CelValue::Lazy(value)).unwrap();
    act
}

#[test]
fn poll_member_defaults_to_member() {
    let reads = Arc::new(AtomicUsize::new(0));
    let v = CountingRecord {
        field: 2.5,
        reads: Arc::clone(&reads),
    };
    match v.poll_member("field") {
        Ok(Access::Ready(CelValue::Num(n))) => assert_eq!(n, 2.5),
        other => panic!("expected Ready(Num), got {other:?}"),
    }
    assert_eq!(reads.load(Ordering::SeqCst), 1);
}

#[test]
fn poll_has_defaults_to_member() {
    let v = CountingRecord {
        field: 2.5,
        reads: Arc::new(AtomicUsize::new(0)),
    };
    assert_eq!(v.poll_has("field").unwrap(), Presence::Known(true));
    assert_eq!(v.poll_has("nope").unwrap(), Presence::Known(false));
    match v.poll_has("boom") {
        Err(CelError::Bind { message }) => assert_eq!(message, "boom failed"),
        other => panic!("a non-NoSuchMember error must propagate, got {other:?}"),
    }
}

#[test]
fn a_pending_member_is_an_evaluation_error() {
    let env = scripted_env();
    let s = Arc::new(Scripted::default());
    s.set("x", Slot::Pending(7));
    let act = bind(&env, "v", s.clone());

    let message = evaluation_message(both(&env, &act, "v.x == 1.0"));
    assert!(message.contains("not yet available"), "{message}");
    assert!(!message.contains("scripted: pending"), "{message}");
    assert!(s.reads("x") > 0, "the pending member was never polled");
}

#[test]
fn a_pending_member_is_absorbed_like_any_error() {
    let env = scripted_env();
    let s = Arc::new(Scripted::default());
    s.set("x", Slot::Pending(7));
    let act = bind(&env, "v", s);

    assert_eq!(both(&env, &act, "v.x == 1.0 && false").unwrap(), false);
    assert_eq!(both(&env, &act, "v.x == 1.0 || true").unwrap(), true);
    let message = evaluation_message(both(&env, &act, "false || v.x == 1.0"));
    assert!(message.contains("not yet available"), "{message}");
}

#[test]
fn has_on_a_lazy_is_an_existence_question() {
    let mut env = CelEnvironment::new();
    env.declare(
        "v",
        record_opt(
            "v",
            &[("field", CelTy::Num), ("note", CelTy::Str)],
            &["note"],
        ),
    );
    let act = bind(
        &env,
        "v",
        Arc::new(CountingRecord {
            field: 2.0,
            reads: Arc::new(AtomicUsize::new(0)),
        }),
    );

    assert_eq!(both(&env, &act, "has(v.field)").unwrap(), true);
    assert_eq!(both(&env, &act, "has(v.note)").unwrap(), false);
}

#[test]
fn in_on_a_keyless_lazy_asks_presence() {
    let mut env = CelEnvironment::new();
    env.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    let act = bind(&env, "m", Arc::new(Keyless));

    assert_eq!(both(&env, &act, r#""a" in m"#).unwrap(), true);
    assert_eq!(both(&env, &act, r#""b" in m"#).unwrap(), false);
}

#[test]
fn in_on_a_keyed_lazy_is_unchanged() {
    let mut env = CelEnvironment::new();
    env.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    let reads = Arc::new(AtomicUsize::new(0));
    let iterations = Arc::new(AtomicUsize::new(0));
    let act = bind(
        &env,
        "m",
        Arc::new(CountingMap {
            keys: vec![CelKey::new("k1"), CelKey::new("k2")],
            reads: Arc::clone(&reads),
            iterations: Arc::clone(&iterations),
        }),
    );

    assert_eq!(both(&env, &act, r#""k1" in m"#).unwrap(), true);
    assert_eq!(both(&env, &act, r#""k9" in m"#).unwrap(), false);
    // Answered from `keys()`, never by resolving a member.
    assert_eq!(reads.load(Ordering::SeqCst), 0);
    assert!(iterations.load(Ordering::SeqCst) > 0);
}

#[test]
fn has_and_in_on_a_pending_lazy_are_errors() {
    let env = scripted_env();
    let s = Arc::new(Scripted::default());
    s.set("field", Slot::Pending(3));
    s.set("a", Slot::Pending(4));
    let v = bind(&env, "v", s.clone());
    let m = bind(&env, "m", s);

    let message = evaluation_message(both(&env, &v, "has(v.field)"));
    assert!(message.contains("not yet available"), "{message}");
    let message = evaluation_message(both(&env, &m, r#""a" in m"#));
    assert!(message.contains("not yet available"), "{message}");
}

#[test]
fn a_demand_handle_round_trips_its_id() {
    assert_eq!(DemandHandle::new(42).id(), 42);
    assert_eq!(DemandHandle::new(42), DemandHandle::new(42));
}
