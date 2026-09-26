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

use std::collections::HashMap;
use std::sync::Arc;

use crate::bounds::{self, CelLimits};
use crate::check::TypeEnv;
use crate::objects::{Key, Map, Value};
use crate::ty::CelTy;

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
    ctx: crate::Context<'static>,
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
    /// An activation over `types`, with every host function in `hosts` registered for the TREE
    /// evaluator — which is what `evaluate` and a specialization's fold run. The fast backend
    /// dispatches a host call through its program instead, so a prepared activation registers none.
    pub(crate) fn new(
        types: TypeEnv,
        functions: Arc<crate::env::Env>,
        hosts: &crate::hostfn::HostTable,
        limits: CelLimits,
    ) -> CelActivation {
        let mut ctx = crate::Context::with_env(functions);
        // A CALL host has no implementation here: the tree evaluator fails a call to one, and a
        // specialization therefore keeps it symbolic.
        for entry in hosts.entries.iter().filter(|e| e.closure().is_some()) {
            ctx.add_function(&entry.name, tree_host(entry.clone()));
        }
        CelActivation {
            types,
            limits,
            ctx,
            elements: 0,
            known_roots: std::collections::BTreeSet::new(),
        }
    }

    /// An activation with NO roster, for [`CelRuntime::activation`](crate::CelRuntime::activation):
    /// its program was checked against a roster when it compiled, and binding here goes through
    /// [`bind_fact`](CelActivation::bind_fact). An empty `TypeEnv` allocates nothing, and no host
    /// function is registered: this activation is for the fast backend, which calls one through
    /// its program. The tree evaluator needs [`CelEnvironment::activation`](crate::CelEnvironment::activation).
    pub(crate) fn prepared(functions: Arc<crate::env::Env>, limits: CelLimits) -> CelActivation {
        CelActivation::new(
            TypeEnv::default(),
            functions,
            &crate::hostfn::HostTable::default(),
            limits,
        )
    }

    /// Bind a value WITHOUT a roster check or a type-directed conversion.
    ///
    /// For an activation whose program was checked against a roster at compile time, with a
    /// caller that packs exactly what that roster declares — the caller's own test holds it to
    /// that. Never use this to bind untrusted JSON: that is [`bind`](CelActivation::bind), whose
    /// input caps exist because an evaluation cannot be interrupted once it has started.
    pub fn bind_fact(&mut self, name: &str, value: crate::CelValue) -> &mut CelActivation {
        self.ctx
            .add_variable_as_val(name.to_string(), value.into_val());
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
        self.ctx.add_variable_from_value(name.to_string(), value);
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
        self.ctx
            .add_variable_as_val(name.to_string(), value.into_val());
        self.known_roots.remove(name);
        Ok(self)
    }

    pub(crate) fn context(&self) -> &crate::Context<'static> {
        &self.ctx
    }

    /// The roots a specialization may fold: bound with `bind`, and not since rebound lazily.
    pub(crate) fn known_roots(&self) -> &std::collections::BTreeSet<String> {
        &self.known_roots
    }

    /// The values alone, for a run that may wait and move between threads. The roster has done
    /// its job — every name bound was checked against it — and it cannot come along: `CelTy`
    /// holds `Rc`, so a `TypeEnv` is not `Send`.
    pub fn into_bindings(self) -> CelBindings {
        CelBindings { ctx: self.ctx }
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
            if bound(&self.ctx).any(|(n, _)| n == name) {
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
            ctx: self.ctx,
            open: names,
        })
    }
}

/// A host function as the tree evaluator calls one: the receiver (for a member) and the arguments
/// as boundary values, the result back as an evaluator value. A lazy argument arrives as the view
/// it was bound with. Worded exactly as the fast backend words the same failures.
fn tree_host(entry: crate::hostfn::HostEntry) -> crate::magic::Function {
    Box::new(
        move |ftx: &mut crate::FunctionContext| -> crate::objects::ResolveResult {
            let mut args = Vec::with_capacity(entry.arity);
            for v in ftx.this.iter().chain(ftx.args.iter()) {
                let arg = crate::lazy::val_to_cel(v.as_ref()).ok_or_else(|| {
                    crate::hostfn::failure(&entry.name, "argument has no CelValue form")
                })?;
                args.push(arg);
            }
            let call = entry.closure().expect("only closures are registered");
            let out = call(&args).map_err(|e| crate::hostfn::failure(&entry.name, e))?;
            out.into_value().ok_or_else(|| {
                crate::hostfn::failure(&entry.name, "a host function returned a lazy value")
            })
        },
    )
}

/// Bindings without the type roster: the values one run reads.
///
/// `Send`, so it can travel with a [`VmRun`] that waits across feeds and changes threads.
pub struct CelBindings {
    ctx: crate::Context<'static>,
}

impl std::fmt::Debug for CelBindings {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CelBindings")
            .field(
                "bound",
                &bound(&self.ctx).map(|(n, _)| n).collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl CelBindings {
    pub(crate) fn context(&self) -> &crate::Context<'static> {
        &self.ctx
    }
}

/// Bindings with some roots left OPEN, filled per run. Built once and shared across threads.
pub struct CelTemplate {
    ctx: crate::Context<'static>,
    open: Vec<String>,
}

impl std::fmt::Debug for CelTemplate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CelTemplate")
            .field(
                "bound",
                &bound(&self.ctx).map(|(n, _)| n).collect::<Vec<_>>(),
            )
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
        // `Context` is the fork's and does not derive `Clone`; rebuild one value by value.
        let mut ctx = crate::Context::default();
        for (name, value) in bound(&self.ctx) {
            ctx.add_variable_as_val(name.to_string(), value.clone_as_boxed());
        }
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
            ctx.add_variable_as_val(name.to_string(), value.into_val());
        }
        if let Some(missing) = self.open.iter().find(|n| !filled.contains(&n.as_str())) {
            return Err(crate::CelError::Bind {
                message: format!("the open root `{missing}` was not filled"),
            });
        }
        Ok(CelBindings { ctx })
    }
}

/// The variables a root context holds. A `CelActivation`'s context is always a root.
fn bound<'c>(
    ctx: &'c crate::Context<'static>,
) -> impl Iterator<Item = (&'c str, &'c dyn crate::common::value::Val)> {
    let vars = match ctx {
        crate::Context::Root { variables, .. } => Some(variables),
        crate::Context::Child { .. } => None,
    };
    vars.into_iter()
        .flat_map(|v| v.iter().map(|(n, b)| (n.as_str(), b.as_ref())))
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
    /// `execute` returns `Result<Value, ExecutionError>` — two failure channels — and the `Ok` one
    /// still carries non-bool values, so everything that is not `Ok(Value::Bool(b))` becomes an
    /// `Err` here. Writing `Ok(v) => Ok(v != Value::Bool(false))` instead would be a silent
    /// allow-on-error at whichever call site reads `false` as safe.
    pub fn evaluate(&self, activation: &CelActivation) -> Result<bool, crate::CelError> {
        let slots = self.pool().slots();
        if slots.is_empty() {
            return verdict(
                self.source_arc(),
                self.program().execute(activation.context()),
            );
        }
        // A residual's constant slots, bound in a scope of their own over the caller's roots. No
        // declared name can be a slot's, so nothing the caller bound is shadowed.
        let mut scope = activation.context().new_inner_scope();
        for (name, value) in slots {
            scope.add_variable_from_value(name.to_string(), value.clone());
        }
        verdict(self.source_arc(), self.program().execute(&scope))
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
            .resume::<dyn crate::Facts>(owned, &bindings.ctx, None)
        {
            crate::fast::Resumed::Done(out) => RunStep::Done(out),
            crate::fast::Resumed::Need(handle, paused) => {
                run.state = Some(paused);
                RunStep::Need(handle)
            }
        }
    }
}

/// The mapping from an evaluation's outcome to a verdict for
/// [`CelProgram::evaluate`](crate::CelProgram::evaluate). The fast backend words it identically
/// (`fast::verdict`), and the differentials compare the text.
fn verdict(
    source: Arc<str>,
    out: Result<Value, crate::ExecutionError>,
) -> Result<bool, crate::CelError> {
    match out {
        Ok(Value::Bool(b)) => Ok(b),
        Ok(other) => Err(crate::CelError::Evaluation {
            source,
            message: format!("produced {other:?} rather than a bool"),
        }),
        Err(e) => Err(crate::CelError::Evaluation {
            source,
            message: format!("could not be evaluated: {e}"),
        }),
    }
}

/// Bind `json` as `ty`. The TYPE leads.
fn bind_value(ty: &CelTy, json: &serde_json::Value, path: &str) -> Result<Value, BindError> {
    use serde_json::Value as J;
    let mismatch = || BindError {
        path: path.to_string(),
        message: format!("schema says {}, value is {}", ty.name(), shape(json)),
    };
    Ok(match (ty, json) {
        (CelTy::Bool, J::Bool(b)) => Value::Bool(*b),
        // ONE numeric type, always a double. `removed: uint` deleted the trap where a
        // serde-converted positive integer arrived as `UInt` and picked the arithmetic; binding
        // through `Value::Float` is what makes sure that deletion reached the binder.
        (CelTy::Num, J::Number(n)) => Value::Float(n.as_f64().ok_or_else(mismatch)?),
        (CelTy::Str, J::String(s)) => Value::String(Arc::new(s.clone())),
        (CelTy::Null, J::Null) => Value::Null,
        // A duration has no JSON witness of its own, so a fixture spells it the way `duration()`
        // does. The live system environment binds `Val` views instead and never comes through here.
        (CelTy::Duration, J::String(s)) => Value::Duration(
            crate::duration::parse_duration(s)
                .map(|(_, d)| d)
                .map_err(|e| BindError {
                    path: path.to_string(),
                    message: format!("not a duration: {e}"),
                })?,
        ),
        (CelTy::List(el), J::Array(items)) => {
            let mut out = Vec::with_capacity(items.len());
            for (i, item) in items.iter().enumerate() {
                out.push(bind_value(el, item, &format!("{path}[{i}]"))?);
            }
            Value::List(Arc::new(out))
        }
        (CelTy::Map(k, v), J::Object(entries)) => {
            if **k != CelTy::Str {
                return Err(mismatch());
            }
            let mut out = HashMap::with_capacity(entries.len());
            for (key, value) in entries {
                out.insert(
                    Key::String(Arc::new(key.clone())),
                    bind_value(v, value, &format!("{path}.{key}"))?,
                );
            }
            Value::Map(Map { map: Arc::new(out) })
        }
        (CelTy::Record(r), J::Object(entries)) => {
            let mut out = HashMap::with_capacity(entries.len());
            for (name, field_ty) in &r.fields {
                match entries.get(name) {
                    Some(v) => {
                        out.insert(
                            Key::String(Arc::new(name.clone())),
                            bind_value(field_ty, v, &format!("{path}.{name}"))?,
                        );
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
                        out.insert(
                            Key::String(Arc::new(key.clone())),
                            bind_value(value_ty, value, &format!("{path}.{key}"))?,
                        );
                    }
                }
            }
            Value::Map(Map { map: Arc::new(out) })
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

/// A JSON value bound by its OWN shape. Reachable only under a `dyn`.
fn json_value(v: &serde_json::Value) -> Value {
    use serde_json::Value as J;
    match v {
        J::Null => Value::Null,
        J::Bool(b) => Value::Bool(*b),
        // Still a double: one numeric type holds under `dyn` too.
        J::Number(n) => Value::Float(n.as_f64().unwrap_or(f64::NAN)),
        J::String(s) => Value::String(Arc::new(s.clone())),
        J::Array(items) => Value::List(Arc::new(items.iter().map(json_value).collect())),
        J::Object(entries) => Value::Map(Map {
            map: Arc::new(
                entries
                    .iter()
                    .map(|(k, v)| (Key::String(Arc::new(k.clone())), json_value(v)))
                    .collect(),
            ),
        }),
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
mod tests {
    /// Two activations from one runtime — and two from one environment — read ONE function table.
    /// Rebuilding it per activation is a whole stdlib per evaluation, and nothing else notices.
    #[test]
    fn activations_share_one_function_table() {
        let env = crate::CelEnvironment::new();
        let runtime = env.runtime();
        let (a, b) = (runtime.activation(), runtime.activation());
        assert!(std::ptr::eq(a.ctx.env(), b.ctx.env()));

        let (c, d) = (env.activation(), env.activation());
        assert!(std::ptr::eq(c.ctx.env(), d.ctx.env()));
        assert!(std::ptr::eq(a.ctx.env(), c.ctx.env()));
    }
}
