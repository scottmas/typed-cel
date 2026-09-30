//! Binding values, and what a non-`Ok(true)` outcome MEANS.
//!
//! Two properties live here and both are security properties.
//!
//! **Binding is SCHEMA-DIRECTED.** The declared type leads and the JSON is pulled to match, rather
//! than the JSON's shape choosing a type. Under the one-numeric-type rule that is total for every
//! JSON number, so a [`BindError`] means the declared type and the value disagree — which schema
//! validation upstream of the program should already have caught.
//!
//! **A non-`Ok(true)` outcome is the CALLER's to interpret.** [`CelProgram::evaluate`] returns
//! `Result<bool, CelError>` and says nothing about what should happen next, because "closed"
//! points a different way at every site: an assertion that cannot be evaluated must deny, a
//! revocation expression that cannot be evaluated must revoke, and a transition step that cannot
//! be evaluated must hold the permission it already has rather than advance. One enum here could
//! not have named the third, and a "false on error" convention would make one of them fail OPEN.

use std::sync::Arc;

use crate::bindings::Bindings;
use crate::bounds::{self, CelLimits};
use crate::check::TypeEnv;
use crate::ty::CelTy;
use crate::{CelKey, CelMap, CelMapKey, CelValue};

/// Why a value could not be bound as its declared type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BindError {
    pub path: String,
    pub message: String,
}

impl std::fmt::Display for BindError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "`{}`: {}", self.path, self.message)
    }
}

/// The values one evaluation reads.
///
/// Built from a [`CelEnvironment`](crate::CelEnvironment), so binding a name the environment did
/// not declare is refused at construction rather than silently ignored — an activation carrying a
/// variable no expression can name is a variable somebody expected to be checked.
pub struct CelActivation {
    types: TypeEnv,
    limits: CelLimits,
    roots: Bindings,
    elements: usize,
    /// Names bound with `bind` — materialized values a specialization may fold. `bind_lazy`
    /// removes a name: a view is read on access and cannot be written into a residual.
    known_roots: std::collections::BTreeSet<String>,
}

impl std::fmt::Debug for CelActivation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CelActivation")
            .field("declared", &self.types.roster())
            .finish_non_exhaustive()
    }
}

impl CelActivation {
    /// An activation over `types`. It holds values only: the backend dispatches a host call
    /// through its program, never through the activation.
    pub(crate) fn new(types: TypeEnv, limits: CelLimits) -> CelActivation {
        CelActivation {
            types,
            limits,
            roots: Bindings::default(),
            elements: 0,
            known_roots: std::collections::BTreeSet::new(),
        }
    }

    /// An activation with NO roster, for [`CelRuntime::activation`](crate::CelRuntime::activation):
    /// its program was checked against a roster when it compiled, and binding here goes through
    /// [`bind_fact`](CelActivation::bind_fact). An empty `TypeEnv` allocates nothing.
    pub(crate) fn prepared(limits: CelLimits) -> CelActivation {
        CelActivation::new(TypeEnv::default(), limits)
    }

    /// Bind a value WITHOUT a roster check or a type-directed conversion.
    ///
    /// For an activation whose program was checked against a roster at compile time, with a
    /// caller that packs exactly what that roster declares — the caller's own test holds it to
    /// that. Never use this to bind untrusted JSON: that is [`bind`](CelActivation::bind), whose
    /// input caps exist because an evaluation cannot be interrupted once it has started.
    pub fn bind_fact(&mut self, name: &str, value: crate::CelValue) -> &mut CelActivation {
        self.roots.set(name, value);
        // A fact is bound per evaluation, not a root a specialization folds.
        self.known_roots.remove(name);
        self
    }

    /// Bind `json` to `name`, as the type the environment declared for it.
    ///
    /// The input caps are checked HERE, because `execute` cannot be interrupted once it has
    /// started — capping at evaluation time is too late.
    pub fn bind(
        &mut self,
        name: &str,
        json: &serde_json::Value,
    ) -> Result<&mut CelActivation, crate::CelError> {
        let Some(ty) = self.types.get(name).cloned() else {
            return Err(crate::CelError::Bind {
                message: format!(
                    "`{name}` is not declared in this environment; declared: {}",
                    self.types.roster().join(", ")
                ),
            });
        };
        bounds::check_input(json, name, &self.limits, &mut self.elements).map_err(|e| {
            crate::CelError::Bind {
                message: e.to_string(),
            }
        })?;
        let value = bind_value(&ty, json, name).map_err(|e| crate::CelError::Bind {
            message: e.to_string(),
        })?;
        self.roots.set(name, value);
        self.known_roots.insert(name.to_string());
        Ok(self)
    }

    /// Bind a value that resolves ON ACCESS — the one extension point the library offers.
    ///
    /// This is the seam a poll loop uses. Serializing a sandbox's state to JSON per grant per tick
    /// allocates a map of the entire state for data almost no expression reads; a
    /// [`LazyValue`](crate::LazyValue) serves indexing straight off the state, so the cost of a
    /// policy is proportional to the POLICY rather than to the sandbox.
    ///
    /// Takes a [`CelValue`](crate::CelValue) rather than a bare `Arc<dyn LazyValue>` because the
    /// same roster mixes the two: `uptime` is a plain duration and `files` is a view, and two
    /// binding methods for one seam is a distinction the caller would have to re-derive at every
    /// site. The bounds are NOT checked here — a lazy value materializes nothing, so there is no
    /// element count to cap.
    pub fn bind_lazy(
        &mut self,
        name: &str,
        value: crate::CelValue,
    ) -> Result<&mut CelActivation, crate::CelError> {
        if self.types.get(name).is_none() {
            return Err(crate::CelError::Bind {
                message: format!(
                    "`{name}` is not declared in this environment; declared: {}",
                    self.types.roster().join(", ")
                ),
            });
        }
        self.roots.set(name, value);
        self.known_roots.remove(name);
        Ok(self)
    }

    pub(crate) fn roots(&self) -> &Bindings {
        &self.roots
    }

    /// The roots a specialization may fold: bound with `bind`, and not since rebound lazily.
    pub(crate) fn known_roots(&self) -> &std::collections::BTreeSet<String> {
        &self.known_roots
    }

    /// The values alone, for a run that may wait and move between threads. The roster has done
    /// its job — every name bound was checked against it — and it cannot come along: `CelTy`
    /// holds `Rc`, so a `TypeEnv` is not `Send`.
    pub fn into_bindings(self) -> CelBindings {
        CelBindings { roots: self.roots }
    }

    /// The bound values, with the roots named in `open` left to be filled per run by
    /// [`CelTemplate::instantiate`]. Each `open` name must be DECLARED and NOT already bound;
    /// checked here, while the roster still exists.
    pub fn into_template(self, open: &[&str]) -> Result<CelTemplate, crate::CelError> {
        let mut names: Vec<String> = Vec::with_capacity(open.len());
        for &name in open {
            if self.types.get(name).is_none() {
                return Err(crate::CelError::Bind {
                    message: format!(
                        "`{name}` is not declared in this environment; declared: {}",
                        self.types.roster().join(", ")
                    ),
                });
            }
            if self.roots.get(name).is_some() {
                return Err(crate::CelError::Bind {
                    message: format!("`{name}` is already bound, so it cannot be left open"),
                });
            }
            if names.iter().any(|n| n == name) {
                return Err(crate::CelError::Bind {
                    message: format!("`{name}` is named open twice"),
                });
            }
            names.push(name.to_string());
        }
        Ok(CelTemplate {
            roots: self.roots,
            open: names,
        })
    }
}

/// Bindings without the type roster: the values one run reads.
///
/// `Send`, so it can travel with a [`VmRun`] that waits across feeds and changes threads.
pub struct CelBindings {
    roots: Bindings,
}

impl std::fmt::Debug for CelBindings {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CelBindings")
            .field("bound", &self.roots.names().collect::<Vec<_>>())
            .finish()
    }
}

impl CelBindings {
    pub(crate) fn roots(&self) -> &Bindings {
        &self.roots
    }
}

/// Bindings with some roots left OPEN, filled per run. Built once and shared across threads.
pub struct CelTemplate {
    roots: Bindings,
    open: Vec<String>,
}

impl std::fmt::Debug for CelTemplate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CelTemplate")
            .field("bound", &self.roots.names().collect::<Vec<_>>())
            .field("open", &self.open)
            .finish()
    }
}

impl CelTemplate {
    /// Fresh bindings: every bound root cloned, every open root filled exactly once. A missing,
    /// repeated or extra name — one that is bound already, or not declared at all — is
    /// [`CelError::Bind`](crate::CelError::Bind).
    pub fn instantiate(
        &self,
        open: Vec<(&str, crate::CelValue)>,
    ) -> Result<CelBindings, crate::CelError> {
        // One `Arc` bump per bound root.
        let mut roots = self.roots.clone();
        let mut filled: Vec<&str> = Vec::with_capacity(open.len());
        for (name, value) in open {
            if !self.open.iter().any(|n| n == name) {
                return Err(crate::CelError::Bind {
                    message: format!(
                        "`{name}` is not an open root of this template; open: {}",
                        self.open.join(", ")
                    ),
                });
            }
            if filled.contains(&name) {
                return Err(crate::CelError::Bind {
                    message: format!("`{name}` is filled twice"),
                });
            }
            filled.push(name);
            roots.set(name, value);
        }
        if let Some(missing) = self.open.iter().find(|n| !filled.contains(&n.as_str())) {
            return Err(crate::CelError::Bind {
                message: format!("the open root `{missing}` was not filled"),
            });
        }
        Ok(CelBindings { roots })
    }
}

impl crate::CelProgram {
    /// `Ok(true)` / `Ok(false)` when the expression evaluated to a bool. Everything else — an
    /// evaluation error, or a non-bool result — is `Err`.
    ///
    /// The library does NOT say what an `Err` should cause. That is the caller's, and it differs
    /// per site: an HTTP assertion that cannot be evaluated must DENY, a `revoke_after` that
    /// cannot be evaluated must REVOKE, and a transition step that cannot be evaluated must hold
    /// the current permission rather than advance. One enum here could not have named the third,
    /// and a "false on error" convention would make one of them fail OPEN.
    ///
    /// Runs on the backend, lowered once and cached in the program (the same lowering [`emit`]
    /// shares). A residual's constant slots are the lowered program's constants; there is no scope
    /// to bind them in.
    ///
    /// [`emit`]: crate::emit
    pub fn evaluate(&self, activation: &CelActivation) -> Result<bool, crate::CelError> {
        self.lowered()?.eval(activation)
    }
}

/// Runs bytecode, on the fast backend. Construct with `Vm::new()`: the private field keeps `Vm { }`
/// unconstructible outside the crate, so `Vm` can gain state without touching a caller.
#[derive(Debug)]
pub struct Vm {
    _reserved: (),
}

impl Default for Vm {
    fn default() -> Vm {
        Vm::new()
    }
}

impl Vm {
    pub fn new() -> Vm {
        Vm { _reserved: () }
    }

    /// `Ok(true)` / `Ok(false)` when the bytecode evaluated to a bool; everything else is `Err` —
    /// the same contract, and the same error text, as [`CelProgram::evaluate`](crate::CelProgram::evaluate).
    pub fn eval(
        &self,
        bytecode: &crate::CelBytecode,
        activation: &CelActivation,
    ) -> Result<bool, crate::CelError> {
        bytecode.fast.eval(activation)
    }

    /// Run `bytecode` and return its value, whatever its type. [`eval`](crate::Vm::eval) is this
    /// plus "must be a bool". A value with no [`CelValue`](crate::CelValue) spelling is an `Err`,
    /// never a default.
    pub fn eval_result(
        &self,
        bytecode: &crate::CelBytecode,
        activation: &CelActivation,
    ) -> Result<crate::CelValue, crate::CelError> {
        bytecode.fast.eval_result(activation)
    }

    /// [`eval_result`](crate::Vm::eval_result), with `dispatch` answering every CALL host
    /// ([`CelEnvironment::declare_call_host`](crate::CelEnvironment::declare_call_host)). Runs to
    /// completion on the calling thread: it never suspends, so the dispatcher may borrow.
    pub fn eval_result_with(
        &self,
        bytecode: &crate::CelBytecode,
        activation: &CelActivation,
        dispatch: &mut dyn crate::HostDispatch,
    ) -> Result<crate::CelValue, crate::CelError> {
        bytecode.fast.eval_result_with(activation, dispatch)
    }
}

/// A run that can wait. Owns its bytecode and its state, so it outlives the call that started it
/// and moves between threads with whatever holds it.
///
/// It runs on the fast backend, as every run does. The state is the
/// backend's `(pc, registers, arena)`, holding nothing borrowed from a caller: what a register
/// borrowed from the bindings is copied into the run's own arena at the moment it pauses, and only
/// then.
pub struct VmRun {
    code: Arc<crate::CelBytecode>,
    /// `None` once the run has finished.
    state: Option<crate::fast::Paused>,
}

impl std::fmt::Debug for VmRun {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VmRun")
            .field("pc", &self.pc())
            .field("stack_depth", &self.stack_depth())
            .finish_non_exhaustive()
    }
}

/// What [`Vm::resume`](crate::Vm::resume) came back with.
#[derive(Debug)]
pub enum RunStep {
    /// The verdict — the same contract, and the same error text, as
    /// [`CelProgram::evaluate`](crate::CelProgram::evaluate).
    Done(Result<bool, crate::CelError>),
    /// A lazy read is not answerable yet. Resume once the value that handed out this handle has
    /// moved on; the run re-executes that read and nothing before it.
    Need(crate::DemandHandle),
}

impl VmRun {
    pub fn new(code: Arc<crate::CelBytecode>) -> VmRun {
        VmRun {
            code,
            state: Some(crate::fast::Paused::start()),
        }
    }

    /// The op the run executes next; `None` once finished.
    #[doc(hidden)]
    pub fn pc(&self) -> Option<usize> {
        self.state.as_ref().map(|s| s.pc())
    }

    /// How many registers hold a value; `None` once finished.
    #[doc(hidden)]
    pub fn stack_depth(&self) -> Option<usize> {
        self.state.as_ref().map(|s| s.live())
    }
}

impl crate::Vm {
    /// Run until the program finishes or reads a lazy member that is not available yet.
    ///
    /// `Need` returns control at once and holds nothing: the run keeps its state, and the next
    /// `resume` re-executes the pending read. A run resumed after it finished answers
    /// [`CelError::Bind`](crate::CelError::Bind), never a panic.
    pub fn resume(&self, run: &mut VmRun, bindings: &CelBindings) -> RunStep {
        let Some(owned) = run.state.take() else {
            return RunStep::Done(Err(crate::CelError::Bind {
                message: "this run already finished".into(),
            }));
        };
        match run
            .code
            .fast
            .resume::<dyn crate::Facts>(owned, &bindings.roots, None)
        {
            crate::fast::Resumed::Done(out) => RunStep::Done(out),
            crate::fast::Resumed::Need(handle, paused) => {
                run.state = Some(paused);
                RunStep::Need(handle)
            }
        }
    }
}

/// Bind `json` as `ty`. The TYPE leads.
fn bind_value(ty: &CelTy, json: &serde_json::Value, path: &str) -> Result<CelValue, BindError> {
    use serde_json::Value as J;
    let mismatch = || BindError {
        path: path.to_string(),
        message: format!("schema says {}, value is {}", ty.name(), shape(json)),
    };
    let str_key = |k: &str| CelMapKey::Str(CelKey::new(k));
    Ok(match (ty, json) {
        (CelTy::Bool, J::Bool(b)) => CelValue::Bool(*b),
        // ONE numeric type, and this is where an integer stays an integer: `i64`, then `u64`, then
        // a double (a fraction, an exponent — or an integer past `u64::MAX`, which serde_json has
        // already rounded). The integer arms come FIRST: `as_f64` answers for every integer too.
        (CelTy::Num, J::Number(n)) => number(n).ok_or_else(mismatch)?,
        (CelTy::Str, J::String(s)) => CelValue::Str(s.as_str().into()),
        (CelTy::Null, J::Null) => CelValue::Null,
        // A duration has no JSON witness of its own, so a fixture spells it the way `duration()`
        // does. The live system environment binds lazy views instead and never comes through here.
        (CelTy::Duration, J::String(s)) => CelValue::Duration(crate::CelDuration::of(
            crate::duration::parse_duration(s)
                .map(|(_, d)| d)
                .map_err(|e| BindError {
                    path: path.to_string(),
                    message: format!("not a duration: {e}"),
                })?,
        )),
        (CelTy::List(el), J::Array(items)) => {
            let mut out = Vec::with_capacity(items.len());
            for (i, item) in items.iter().enumerate() {
                out.push(bind_value(el, item, &format!("{path}[{i}]"))?);
            }
            CelValue::list(out)
        }
        (CelTy::Map(k, v) | CelTy::UnsafeMap(k, v), J::Object(entries)) => {
            if **k != CelTy::Str {
                return Err(mismatch());
            }
            let mut out = Vec::with_capacity(entries.len());
            for (key, value) in entries {
                out.push((
                    str_key(key),
                    bind_value(v, value, &format!("{path}.{key}"))?,
                ));
            }
            CelValue::Map(CelMap::new(out))
        }
        (CelTy::Record(r), J::Object(entries)) => {
            let mut out = Vec::with_capacity(entries.len());
            for (name, field_ty) in &r.fields {
                match entries.get(name) {
                    Some(v) => {
                        out.push((
                            str_key(name),
                            bind_value(field_ty, v, &format!("{path}.{name}"))?,
                        ));
                    }
                    // LET THE ABSENT CASE STAY ABSENT. The shape that reads naturally —
                    // `entries.get(name).unwrap_or(&J::Null)` — makes a missing field compare
                    // equal to an explicit null, and makes `body.a == body.b` true when NEITHER
                    // exists. Leaving the key out is what makes `NoSuchKey` fire, which the
                    // verdict then maps to a deny.
                    None if r.is_optional(name) => {}
                    None => {
                        return Err(BindError {
                            path: format!("{path}.{name}"),
                            message: "required by the schema, absent from the value".to_string(),
                        })
                    }
                }
            }
            // Keys the record did not declare are carried only where an index signature covers
            // them. Anything else is dropped: the checker will not let an expression name it, so
            // binding it would put unvalidated data one `dyn` away from an activation.
            if let Some((_, value_ty)) = &r.index {
                for (key, value) in entries {
                    if r.get(key).is_none() {
                        out.push((
                            str_key(key),
                            bind_value(value_ty, value, &format!("{path}.{key}"))?,
                        ));
                    }
                }
            }
            CelValue::Map(CelMap::new(out))
        }
        // `unknown`: the checker permits only `has()` on one (`removed: dyn values`), so the
        // value's own shape is the only thing available and it is enough for that.
        (CelTy::Dyn, v) => json_value(v),
        (CelTy::Unusable(why), _) => {
            return Err(BindError {
                path: path.to_string(),
                message: format!("{why}"),
            })
        }
        _ => return Err(mismatch()),
    })
}

/// A JSON number, exactly: an integer as an integer, anything else as its (canonical) double.
fn number(n: &serde_json::Number) -> Option<CelValue> {
    Some(match (n.as_i64(), n.as_u64()) {
        (Some(i), _) => CelValue::Int(i),
        (None, Some(u)) => CelValue::from(u),
        _ => CelValue::from(crate::CelNum::from_f64(n.as_f64()?)),
    })
}

/// A JSON value bound by its OWN shape. Reachable only under a `dyn`.
fn json_value(v: &serde_json::Value) -> CelValue {
    use serde_json::Value as J;
    match v {
        J::Null => CelValue::Null,
        J::Bool(b) => CelValue::Bool(*b),
        // Exact, as under a declared type: one numeric type holds under `dyn` too.
        J::Number(n) => number(n).unwrap_or(CelValue::Num(f64::NAN)),
        J::String(s) => CelValue::Str(s.as_str().into()),
        J::Array(items) => CelValue::list(items.iter().map(json_value)),
        J::Object(entries) => CelValue::Map(CelMap::new(
            entries
                .iter()
                .map(|(k, v)| (CelMapKey::Str(CelKey::new(k)), json_value(v))),
        )),
    }
}

fn shape(v: &serde_json::Value) -> &'static str {
    match v {
        serde_json::Value::Null => "null",
        serde_json::Value::Bool(_) => "a bool",
        serde_json::Value::Number(_) => "a number",
        serde_json::Value::String(_) => "a string",
        serde_json::Value::Array(_) => "a list",
        serde_json::Value::Object(_) => "an object",
    }
}

#[cfg(test)]
mod number_tests {
    use super::*;

    /// The `dyn` binding path holds an integer exactly, as a declared `double` does.
    #[test]
    fn dyn_json_binds_exactly() {
        let exact = |j: serde_json::Value| json_value(&j);
        assert_eq!(
            format!("{:?}", exact(serde_json::json!(9007199254740993u64))),
            "Int(9007199254740993)"
        );
        assert_eq!(
            format!("{:?}", exact(serde_json::json!(u64::MAX))),
            "UInt(18446744073709551615)"
        );
        assert_eq!(format!("{:?}", exact(serde_json::json!(2.5))), "Float(2.5)");
        assert_eq!(format!("{:?}", exact(serde_json::json!(2.0))), "Int(2)");
        assert_eq!(
            format!("{:?}", exact(serde_json::json!({"a": [7]}))),
            "Map(Map { map: {String(\"a\"): List([Int(7)])} })"
        );
    }
}
