//! Running one corpus case against this crate, and deciding whether it agreed.

use typed_cel::fork;
// The dialect's value, beside the corpus's own `CelValue`.
use typed_cel::CelValue as Value;
use typed_cel::{CelKey, CelMap, CelMapKey, CelNum, FastProgram};

use super::case::{Binding, Case, CelValue, Expect};

/// What a case resolved to.
///
/// Every case is compiled through the checker a policy compiles through
/// (`CelEnvironment::compile`) with its bindings declared at their values' types, and runs only if
/// the checker admits it. A program the checker REFUSES never reaches an activation, so it has no
/// run-time outcome to compare — it is `Refused`, with the checker's message, and it is a red unless
/// an exclusion names the dialect row it cites.
#[derive(Clone, Debug, PartialEq)]
pub enum Outcome {
    /// The checker admitted it, and the backend agreed with the corpus.
    Pass,
    /// The case expects an evaluation ERROR and the checker refused the program first. Both
    /// refuse it, so this is agreement — reached statically. Never for a case that expects a
    /// value: that refusal is either a dialect row or a red.
    PassStatic(String),
    /// The checker refused it. The message is `CelError`'s rendering.
    Refused(String),
    /// The checker admitted it and the run disagreed, or the harness could not decide.
    Fail(String),
}

impl Outcome {
    /// Agreement with the corpus, at run time or statically.
    pub fn is_pass(&self) -> bool {
        matches!(self, Outcome::Pass | Outcome::PassStatic(_))
    }
}

/// Run one case: declare every binding at the type its VALUE has, compile the expression through
/// the checker a policy compiles through, and — when the checker admits it — run it on the backend,
/// the engine every policy runs on. What the checker adds is the dialect.
///
/// A non-`bool` expression is ADMITTED when the checker typed it and only the result kind stood
/// between it and a policy: `compile` insists on `bool` because a policy is a predicate, not
/// because the corpus's `1 + 2` is ill-typed. That includes a result such as `[]`, whose `dyn` is
/// an element type nothing pinned rather than a value: every construct that PRODUCES a `dyn`
/// value is refused by the checker where it is written, and a policy's result is `bool` anyway.
///
/// A PANIC, in the checker or the backend, is a `Fail` rather than an abort: the corpus
/// deliberately feeds values a careless implementation mishandles, and letting one escape would
/// take the other cases with it. Catching it here means ONE definition of the outcome, shared by
/// the report and the generated tests.
pub fn run(case: &Case) -> Outcome {
    if case.check_only {
        return Outcome::Fail("check_only: the harness runs what it checks".into());
    }
    if let Expect::Unsupported(what) = &case.expect {
        return Outcome::Fail(format!("harness cannot decide {what}"));
    }
    let mut env = typed_cel::CelEnvironment::new();
    for (name, binding) in &case.bindings {
        let Binding::Value(v) = binding else {
            return Outcome::Fail(format!("binding `{name}` is not a plain value"));
        };
        match type_of(v) {
            Some(ty) => {
                env.declare(name.clone(), ty);
            }
            None => return Outcome::Fail(format!("binding `{name}`: cannot type {v:?}")),
        }
    }
    // Compiled ONCE: `compile_any` is `compile` without the `bool` requirement, so admission is
    // exactly `compile` succeeding or refusing only with `NotBoolean` — and the program it admits is
    // the one that runs.
    let admitted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        fork::compile_any(&env, &case.expr).map_err(|e| e.to_string())
    }));
    match admitted {
        Ok(Ok(program)) => {
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                evaluate(case, &program)
            })) {
                Ok(Ok(())) => Outcome::Pass,
                Ok(Err(why)) => Outcome::Fail(why),
                Err(payload) => {
                    Outcome::Fail(format!("panicked in the backend: {}", panic_text(payload)))
                }
            }
        }
        Ok(Err(refusal)) if matches!(case.expect, Expect::EvalError) => {
            Outcome::PassStatic(refusal)
        }
        Ok(Err(refusal)) => Outcome::Refused(refusal),
        Err(_) => Outcome::Fail("panicked in the checker".into()),
    }
}

fn panic_text(payload: Box<dyn std::any::Any + Send>) -> String {
    payload
        .downcast_ref::<&str>()
        .map(|s| s.to_string())
        .or_else(|| payload.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "<non-string panic>".into())
}

/// Run an ADMITTED case on the backend and compare it with the corpus's expectation. Every checked
/// program lowers; a refusal is a defect of the backend and FAILS the case.
fn evaluate(case: &Case, program: &typed_cel::CelProgram) -> Result<(), String> {
    let code = FastProgram::new(program)
        .map_err(|e| format!("the backend refused a checked program: {e}"))?;

    let mut act = typed_cel::CelEnvironment::new().runtime().activation();
    for (name, binding) in &case.bindings {
        let Binding::Value(v) = binding else { continue };
        match to_runtime(v) {
            Some(value) => {
                act.bind_fact(name, value);
            }
            None => return Err(format!("binding `{name}`: cannot represent {v:?}")),
        }
    }

    match (&case.expect, fork::fast_value(&code, &act)) {
        (Expect::EvalError, Err(_)) => Ok(()),
        (Expect::EvalError, Ok(v)) => Err(format!("expected an eval error, got {v:?}")),

        (Expect::True, Ok(Value::Bool(true))) => Ok(()),
        (Expect::True, Ok(v)) => Err(format!("expected true, got {v:?}")),
        (Expect::True, Err(e)) => Err(format!("expected true, got error: {e}")),

        (Expect::Value(want), Ok(got)) if equal(want, &got) => Ok(()),
        (Expect::Value(want), Ok(got)) => Err(format!("expected {want:?}, got {got:?}")),
        (Expect::Value(want), Err(e)) => Err(format!("expected {want:?}, got error: {e}")),

        (Expect::Unsupported(_), _) => unreachable!("refused before the checker runs"),
    }
}

/// A corpus value as something a `Context` can hold. `None` for kinds the dialect has no runtime
/// representation of — those cases must be excluded, and if they are not they fail loudly.
pub fn to_runtime(v: &CelValue) -> Option<Value> {
    Some(match v {
        CelValue::Null => Value::Null,
        CelValue::Bool(b) => Value::Bool(*b),
        // One number type, held exactly: a bound integer is an integer (`Value::Int`), a bound
        // double a double — the same representations the dialect's own binders build.
        CelValue::Int(i) => Value::Int(*i),
        CelValue::Double(d) => Value::Num(*d),
        // A `uint64_value` BINDING is a number the dialect holds exactly (canonical: an `Int` when
        // it fits). What `removed: uint` still removes is the `u` literal and the `uint` TYPE, which
        // `names_uint` excludes by the expression's text.
        CelValue::Uint(u) => Value::from(*u),
        CelValue::String(s) => Value::Str(s.as_str().into()),
        CelValue::Bytes(b) => Value::Bytes(b.as_slice().into()),
        CelValue::List(items) => Value::List(
            items
                .iter()
                .map(to_runtime)
                .collect::<Option<Vec<_>>>()?
                .into(),
        ),
        CelValue::Map(entries) => {
            let mut map = Vec::new();
            for (k, val) in entries {
                map.push((key_of(&to_runtime(k)?)?, to_runtime(val)?));
            }
            Value::Map(CelMap::new(map))
        }
        CelValue::Object { .. } | CelValue::Enum { .. } | CelValue::Type(_) => return None,
        CelValue::Unsupported(_) => return None,
    })
}

/// The map key a runtime value names: a string, a bool, or an integral number.
fn key_of(v: &Value) -> Option<CelMapKey> {
    match v {
        Value::Str(s) => Some(CelMapKey::Str(CelKey::new(s))),
        Value::Bool(b) => Some(CelMapKey::Bool(*b)),
        v => v.num()?.integral_key().map(CelMapKey::Num),
    }
}

/// A corpus number as the dialect's one number: `int64_value`, `uint64_value` and `double_value`
/// are three spellings of it.
fn want_num(v: &CelValue) -> Option<CelNum> {
    match v {
        CelValue::Int(i) => Some(CelNum::Int(*i)),
        CelValue::Uint(u) => Some(CelNum::UInt(*u)),
        CelValue::Double(d) => Some(CelNum::Float(*d)),
        _ => None,
    }
}

/// Does the runtime value match what the corpus expects?
///
/// Numbers compare by exact VALUE: the dialect has one numeric type, so `int64_value: 3` and
/// `double_value: 3.0` expect the same number, and a representation (`Int(3)`, `Float(3.0)`) is not
/// a kind. What stays visible is every place the VALUE differs — an integer division that
/// truncates, an overflow the spec errors on. Everything else compares by kind and content.
fn equal(want: &CelValue, got: &Value) -> bool {
    if let (Some(w), Some(g)) = (want_num(want), got.num()) {
        // NaN is not equal to itself, but "the expression produced NaN" is exactly what several
        // fp_math cases assert, so it is compared structurally rather than by `==`.
        let nan = |n: CelNum| matches!(n, CelNum::Float(f) if f.is_nan());
        return w.eq_exact(g) || (nan(w) && nan(g));
    }
    match (want, got) {
        (CelValue::Null, Value::Null) => true,
        (CelValue::Bool(a), Value::Bool(b)) => a == b,
        (CelValue::String(a), Value::Str(b)) => a.as_str() == &**b,
        (CelValue::Bytes(a), Value::Bytes(b)) => a.as_slice() == &**b,
        (CelValue::List(a), Value::List(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(w, g)| equal(w, g))
        }
        (CelValue::Map(a), Value::Map(b)) => {
            if a.len() != b.len() {
                return false;
            }
            a.iter().all(|(k, v)| {
                to_runtime(k)
                    .and_then(|k| key_of(&k))
                    .and_then(|k| b.iter().find(|(got, _)| **got == k).map(|(_, g)| g.clone()))
                    .is_some_and(|got| equal(v, &got))
            })
        }
        _ => false,
    }
}

/// The type a bound corpus value has — the harness's stand-in for the `type_env` a checked
/// environment declares. A collection's members must share one type, exactly as a literal's must;
/// a mixed one is a `dyn` value, and every use of it is refused. `None` for kinds the dialect has
/// no type for.
pub fn type_of(v: &CelValue) -> Option<typed_cel::CelTy> {
    use typed_cel::CelTy;
    fn one(tys: impl Iterator<Item = Option<CelTy>>) -> Option<CelTy> {
        let mut out: Option<CelTy> = None;
        for t in tys {
            let t = t?;
            out = Some(match out {
                None => t,
                Some(prev) if prev == t => prev,
                Some(_) => CelTy::Dyn,
            });
        }
        // An empty value carries no element type; with no `type_env` to read one from, it is
        // `dyn`, and a use of it is refused.
        Some(out.unwrap_or(CelTy::Dyn))
    }
    Some(match v {
        CelValue::Null => CelTy::Null,
        CelValue::Bool(_) => CelTy::Bool,
        CelValue::Int(_) | CelValue::Uint(_) | CelValue::Double(_) => CelTy::Num,
        CelValue::String(_) => CelTy::Str,
        CelValue::Bytes(_) => CelTy::Bytes,
        CelValue::List(items) => CelTy::list(one(items.iter().map(type_of))?),
        CelValue::Map(entries) => CelTy::map(
            one(entries.iter().map(|(k, _)| type_of(k)))?,
            one(entries.iter().map(|(_, v)| type_of(v)))?,
        ),
        CelValue::Object { .. }
        | CelValue::Enum { .. }
        | CelValue::Type(_)
        | CelValue::Unsupported(_) => return None,
    })
}
