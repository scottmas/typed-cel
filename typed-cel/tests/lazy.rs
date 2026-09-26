//! The one extension point: a value that resolves on ACCESS.
//!
//! The property under test is not "it produces the right answer" — it is that producing the right
//! answer costs one `member` call per field an expression actually reads, and iterating a
//! container costs no allocation per key. That is what makes the cost of evaluating a policy
//! proportional to the POLICY rather than to the state behind it, and it is invisible to any test
//! that only checks the result.

#[path = "support/mod.rs"]
mod support;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use support::record;
use typed_cel::{CelEnvironment, CelError, CelKey, CelTy, CelValue, LazyValue};

fn no_such(key: &str) -> CelError {
    CelError::NoSuchMember {
        key: key.to_string(),
    }
}

/// A record-shaped view that counts every member resolution.
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
            other => Err(no_such(other)),
        }
    }
}

/// A map-shaped view whose entries are themselves views. Keys are stored, so iteration hands them
/// out by reference.
#[derive(Debug)]
struct CountingMap {
    keys: Vec<CelKey>,
    values: Vec<f64>,
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
        Ok(CelValue::Lazy(Arc::new(Entry {
            n: self.values[ix],
            reads: Arc::clone(&self.reads),
        })))
    }

    fn keys(&self) -> Option<Box<dyn Iterator<Item = &CelKey> + '_>> {
        self.iterations.fetch_add(1, Ordering::SeqCst);
        Some(Box::new(self.keys.iter()))
    }
}

#[derive(Debug)]
struct Entry {
    n: f64,
    reads: Arc<AtomicUsize>,
}

impl LazyValue for Entry {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        self.reads.fetch_add(1, Ordering::SeqCst);
        match name {
            "n" => Ok(CelValue::Num(self.n)),
            other => Err(no_such(other)),
        }
    }
}

#[test]
fn a_lazy_value_serves_a_select() {
    let reads = Arc::new(AtomicUsize::new(0));
    let mut env = CelEnvironment::new();
    env.declare("x", record("x", &[("field", CelTy::Num)]));
    let program = env.compile("x.field > 1.0").unwrap();

    let mut activation = env.activation();
    activation
        .bind_lazy(
            "x",
            CelValue::Lazy(Arc::new(CountingRecord {
                field: 2.0,
                reads: Arc::clone(&reads),
            })),
        )
        .unwrap();

    assert_eq!(program.evaluate(&activation).unwrap(), true);
    // ONE resolution for one field read. Nothing was materialized: a view that built a map would
    // have resolved every field it has, whether the expression named it or not.
    assert_eq!(reads.load(Ordering::SeqCst), 1);
}

#[test]
fn a_lazy_value_serves_a_comprehension() {
    let reads = Arc::new(AtomicUsize::new(0));
    let iterations = Arc::new(AtomicUsize::new(0));
    let mut env = CelEnvironment::new();
    env.declare(
        "m",
        CelTy::map(CelTy::Str, record("entry", &[("n", CelTy::Num)])),
    );
    let program = env.compile("m.exists(k, m[k].n > 0.0)").unwrap();

    let mut activation = env.activation();
    activation
        .bind_lazy(
            "m",
            CelValue::Lazy(Arc::new(CountingMap {
                keys: vec![CelKey::new("a"), CelKey::new("b"), CelKey::new("c")],
                values: vec![-1.0, -1.0, 5.0],
                reads: Arc::clone(&reads),
                iterations: Arc::clone(&iterations),
            })),
        )
        .unwrap();

    assert_eq!(program.evaluate(&activation).unwrap(), true);
    // The comprehension went through `keys()`, which is the seam that lets a wide root be iterated
    // at all — a view with no `keys` is not iterable and this expression would have errored.
    assert!(
        iterations.load(Ordering::SeqCst) > 0,
        "the comprehension did not iterate through `keys()`"
    );
}

#[test]
fn a_missing_member_reads_as_no_such_key_not_as_zero() {
    // The totality the language rests on: a typo must ERROR, not read as a zero value. A view that
    // answered `CelValue::Num(0.0)` for an unknown member would make `files["/typo"].closed.count
    // > 0` permanently false — a condition that never fires.
    let mut env = CelEnvironment::new();
    env.declare(
        "x",
        record("x", &[("field", CelTy::Num), ("absent", CelTy::Num)]),
    );
    let program = env.compile("x.absent > 1.0").unwrap();

    let mut activation = env.activation();
    activation
        .bind_lazy(
            "x",
            CelValue::Lazy(Arc::new(CountingRecord {
                field: 2.0,
                reads: Arc::new(AtomicUsize::new(0)),
            })),
        )
        .unwrap();

    let rendered = program.evaluate(&activation).unwrap_err().to_string();
    assert!(rendered.contains("absent"), "{rendered}");
}

#[test]
fn a_scalar_is_not_a_container() {
    // `as_iterable`/`as_container` are reported CONDITIONALLY on `keys()`. Claiming otherwise would
    // make a comprehension over a scalar silently iterate nothing — an `exists` that is always
    // false rather than an error.
    let mut env = CelEnvironment::new();
    env.declare(
        "m",
        CelTy::map(CelTy::Str, record("entry", &[("n", CelTy::Num)])),
    );
    let program = env.compile("m.exists(k, m[k].n > 0.0)").unwrap();

    let mut activation = env.activation();
    // A view with NO `keys` bound where the type says map.
    activation
        .bind_lazy(
            "m",
            CelValue::Lazy(Arc::new(CountingRecord {
                field: 1.0,
                reads: Arc::new(AtomicUsize::new(0)),
            })),
        )
        .unwrap();

    assert!(
        program.evaluate(&activation).is_err(),
        "iterating a non-container must error, not read as an empty comprehension"
    );
}

#[test]
fn a_lazy_binding_is_still_refused_for_an_undeclared_name() {
    let env = CelEnvironment::new();
    let mut activation = env.activation();
    let rendered = activation
        .bind_lazy("nowhere", CelValue::Duration(5))
        .err()
        .expect("an undeclared name must be refused")
        .to_string();
    assert!(rendered.contains("nowhere"), "{rendered}");
    assert!(rendered.contains("not declared"), "{rendered}");
}
