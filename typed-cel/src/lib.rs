//! # CEL-Rust
//!
//! A parser and interpreter for the Common Expression Language (CEL) in Rust.
//!
//! ## Optional Features
//!
//! - `chrono`: Enables support for `duration` and `timestamp` types using the `chrono` crate.
//! - `regex`: Enables support for regular expressions.
//! - `json`: Enables conversion between CEL values and JSON.
//!
extern crate core;

use std::sync::Arc;
use thiserror::Error;

// The absorbed fork. PRIVATE — see the public-contract section below. `dead_code` is allowed
// across it because narrowing the surface made a lot of upstream API unreachable, and deleting it
// would make the fork point undiffable, which is the one thing `ATTRIBUTION.md` promises a reader
// it will not be.
#[allow(dead_code)]
mod common;
#[allow(dead_code)]
mod parser;

// The fork's own in-crate unit tests import these from the crate root. Crate-private rather than
// deleted: they are not contract, but removing them would edit absorbed source.
#[allow(unused_imports)]
pub(crate) use common::ast::IdedExpr;
use parser::{Expression, ExpressionReferences, Parser};

mod duration;

// ------------------------------------------------------------------------------------------
// Files authored for the dialect. Everything above this line is the absorbed fork, module layout unchanged
// so a reader can diff against the fork point (ATTRIBUTION.md).
// ------------------------------------------------------------------------------------------
mod activation;
mod bindings;
mod bounds;
mod check;
mod demand;
mod desugar;
mod emit;
mod event;
mod fast;
mod governed;
mod hostfn;
mod lazy;
mod prepared;
mod shape;
mod sigs;
mod specialize;
mod sync_facts;
mod ty;
mod unparse;
mod value;
pub use activation::{BindError, CelActivation, CelBindings, CelTemplate, RunStep, Vm, VmRun};
pub use bounds::CelLimits;
pub use check::{CheckError, TypeEnv};
pub use demand::{DemandSet, Segment};
pub use desugar::{desugar, DesugarError, SpanMap};
pub use emit::{emit, CelBytecode};
/// Deterministic run counters (ops, `slow` entries, field reads, store pushes, allocations), for
/// the crate's own cost-model tests. Only under the `profile` feature, which only the crate's own
/// test build turns on.
#[cfg(feature = "profile")]
#[doc(hidden)]
pub use fast::profile;
#[doc(hidden)]
pub use fast::{inline_ops, layout_sizes, with_literal_comprehensions, with_unfused_loops};
pub use fast::{FactPoll, Facts, FastProgram, FastScratch, FieldId, FieldPath};
pub use governed::{
    GovernedDoc, GovernedShape, RunLiveness, StreamedProgram, StreamedRun, GOVERNED_CELL_BYTES,
};
pub use hostfn::{HostCall, HostDispatch, NoCallHosts, TAG_OTHER};
pub use lazy::{Access, CelKey, DemandHandle, LazyValue, Presence};
pub use prepared::CelRuntime;
pub use shape::{Conjunct, Literal};
pub use sync_facts::{FactFn, SyncFacts};
pub use value::{CelDuration, CelMap, CelMapKey, CelValue};

/// The repository README's code blocks, compiled and run as doctests so its examples cannot rot.
#[cfg(doctest)]
#[doc = include_str!("../../README.md")]
pub struct RepositoryReadme;
pub use event::Event;
pub use ty::{CelTy, Record, Relax, Unusable};

#[derive(Error, Clone, Debug, PartialEq)]
#[non_exhaustive]
pub enum ExecutionError {
    #[error("Invalid argument type: {:?}", .target)]
    UnsupportedTargetType { target: CelValue },
    /// Indicates that the script attempted to use a value as a key in a map,
    /// but the type of the value was not supported as a key.
    #[error("Unable to use value '{0:?}' as a key")]
    UnsupportedKeyType(CelValue),
    #[error("Unexpected type: got '{got}', want '{want}'")]
    UnexpectedType { got: String, want: String },
    /// Indicates that the script attempted to reference a key on a type that
    /// was missing the requested key.
    #[error("No such key: {0}")]
    NoSuchKey(Arc<String>),
    /// Indicates that the script used an existing operator or function with
    /// values of one or more types for which no overload was declared.
    #[error("No such overload")]
    NoSuchOverload,
    /// Indicates that the script attempted to reference an undeclared variable
    /// method, or function.
    #[error("Undeclared reference to '{0}'")]
    UndeclaredReference(Arc<String>),
    /// Indicates that an unsupported binary operator was applied on two values
    /// where it's unsupported, for example list + map.
    #[error("Unsupported binary operator '{0}': {1:?}, {2:?}")]
    UnsupportedBinaryOperator(&'static str, CelValue, CelValue),
    /// Indicates that a function had an error during execution.
    #[error("Error executing function '{function}': {message}")]
    FunctionError { function: String, message: String },
    #[error("Overflow from binary operator '{0}': {1:?}, {2:?}")]
    Overflow(&'static str, CelValue, CelValue),
    #[error("Index out of bounds: {0:?}")]
    IndexOutOfBounds(CelValue),
    #[error("InternalError: {0:?}")]
    InternalError(String),
}

impl ExecutionError {
    pub fn no_such_key(name: &str) -> Self {
        ExecutionError::NoSuchKey(Arc::new(name.to_string()))
    }

    pub fn undeclared_reference(name: &str) -> Self {
        ExecutionError::UndeclaredReference(Arc::new(name.to_string()))
    }

    pub fn function_error<E: ToString>(function: &str, error: E) -> Self {
        ExecutionError::FunctionError {
            function: function.to_string(),
            message: error.to_string(),
        }
    }

    pub fn unsupported_target_type(target: CelValue) -> Self {
        ExecutionError::UnsupportedTargetType { target }
    }

    pub fn unsupported_key_type(value: CelValue) -> Self {
        ExecutionError::UnsupportedKeyType(value)
    }
}

// A parsed tree. Nothing outside the crate can name it — `CelEnvironment::compile` is the only way a
// caller gets a program.
pub(crate) use program::Program;

mod program {
    use super::{Expression, ExpressionReferences};

    #[derive(Debug)]
    pub struct Program {
        expression: Expression,
    }

    impl Program {
        /// A program running an already-built tree — a specialization's residual, which is assembled
        /// rather than parsed.
        pub(crate) fn from_expression(expression: Expression) -> Program {
            Program { expression }
        }

        /// Returns the variables and functions referenced by the CEL program
        ///
        /// # Example
        /// ```rust
        /// let expression = typed_cel::fork::parse("size(foo) > 0").unwrap();
        /// let references = expression.references();
        ///
        /// assert!(references.has_function("size"));
        /// assert!(references.has_variable("foo"));
        /// ```
        pub fn references(&self) -> ExpressionReferences<'_> {
            self.expression.references()
        }

        /// Returns the contained expression
        pub fn expression(&self) -> &Expression {
            &self.expression
        }
    }
}

// ------------------------------------------------------------------------------------------
// The absorbed data model and the compile pipeline's pieces, for THIS CRATE'S OWN harnesses only.
//
// The cel-spec conformance lane, the specializer's and the unparser's tests reach values, trees and
// the backend's boundary value through these doors: a corpus case answers a value of any type where
// the public contract answers a `bool`. They are not callers — they are the crate testing itself.
//
// Gated on `conformance`, which the self dev-dependency turns on for the whole test build and
// which nothing else enables. So a real consumer links a crate where the fork is entirely private,
// and `tests/purity.rs::the_fork_is_not_public` asserts the gate rather than just the absence.
#[cfg(feature = "conformance")]
#[doc(hidden)]
pub mod fork {

    pub use crate::specialize::{check_no_known_read, expression_of, reify, renumber};
    pub use crate::unparse::{unparse, UnparseError};

    /// Parse `src` — no desugaring, no check. For the tests that inspect a tree.
    pub fn parse(src: &str) -> Result<crate::IdedExpr, crate::parser::ParseErrors> {
        crate::parser::Parser::default().parse(src)
    }

    /// `CelEnvironment::compile` without the `bool` requirement, for the typed conformance lane,
    /// whose cases have results of every type.
    pub fn compile_any(
        env: &crate::CelEnvironment,
        expression: &str,
    ) -> Result<crate::CelProgram, crate::CelError> {
        env.compile_checked(expression).map(|(p, _)| p)
    }

    /// The backend's value over `activation`'s bound values.
    pub fn fast_value(
        p: &crate::FastProgram,
        activation: &crate::CelActivation,
    ) -> Result<crate::CelValue, crate::ExecutionError> {
        crate::fast::run_value(p, activation.roots())
    }

    /// `CelEnvironment::specialize`, also handing back each constant slot's name and type.
    pub fn specialize_slots(
        env: &crate::CelEnvironment,
        program: &crate::CelProgram,
        known: &crate::CelActivation,
    ) -> Result<(crate::CelProgram, Vec<(String, crate::CelTy)>), crate::CelError> {
        env.specialize_slots(program, known)
    }

    /// `CelEnvironment::specialize` with every fold lowering refused — for the test that pins a
    /// refusal as LOUD.
    pub fn specialize_with_lowering_refused(
        env: &crate::CelEnvironment,
        program: &crate::CelProgram,
        known: &crate::CelActivation,
    ) -> Result<crate::CelProgram, crate::CelError> {
        env.specialize_inner(program, known, true).map(|(p, _)| p)
    }

    pub mod ast {
        pub use crate::common::ast::{EntryExpr, Expr, IdedExpr, LiteralValue, SourceInfo};
    }

    pub mod parser {
        pub use crate::parser::Parser;
    }
}

// The public contract.
//
// The absorbed types stay internal — no `pub mod` and no `pub use` of a parser or value-model type
// here — so the fork's internals remain ours to change without breaking a caller. Enforced by
// `tests/purity.rs::the_fork_is_not_public`, because the claim is otherwise one nobody checks.
//
// The one extension point is `LazyValue`, and everything crossing it is a `CelValue` — a closed
// enum — so a caller that serves values on access still names no absorbed type.
// ------------------------------------------------------------------------------------------

/// A half-open byte range in the AUTHORED source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// The variables an expression may name and their field structure.
///
/// One environment serves many expressions — `compile` takes `&self` — because a policy compiles
/// dozens of assertions against one endpoint's schemas.
///
/// The crate is deliberately environment-AGNOSTIC: it knows about types, and it knows nothing
/// about what a `body` or a `listener` is. Rosters are built by the embedding application.
#[derive(Clone)]
pub struct CelEnvironment {
    env: TypeEnv,
    limits: CelLimits,
    /// The functions this environment registered ([`register_host`](CelEnvironment::register_host)).
    hosts: Arc<hostfn::HostTable>,
    /// The closed string sets it declared ([`declare_enum`](CelEnvironment::declare_enum)).
    enums: Arc<hostfn::EnumTable>,
}

impl std::fmt::Debug for CelEnvironment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CelEnvironment")
            .field("env", &self.env)
            .field("limits", &self.limits)
            .finish_non_exhaustive()
    }
}

impl Default for CelEnvironment {
    fn default() -> CelEnvironment {
        CelEnvironment::with_limits(CelLimits::default())
    }
}

impl CelEnvironment {
    pub fn new() -> CelEnvironment {
        CelEnvironment::default()
    }

    pub fn with_limits(limits: CelLimits) -> CelEnvironment {
        CelEnvironment {
            env: TypeEnv::new(),
            limits,
            hosts: Arc::new(hostfn::HostTable::default()),
            enums: Arc::new(hostfn::EnumTable::default()),
        }
    }

    /// Declare that the string field at `path` (a declared root, then member names) only ever
    /// holds one of `values` — at most 64, each once. It changes no meaning: the field is still a
    /// `string`. What it changes is how the fast backend compares it with a LISTED literal — by a
    /// tag, the value's index in `values`, which a [`Facts`] provider may answer directly
    /// ([`Facts::tag`]); any other string is [`TAG_OTHER`] and equals no listed value.
    pub fn declare_enum(
        &mut self,
        path: &[&str],
        values: &[&str],
    ) -> Result<&mut CelEnvironment, CelError> {
        let refuse = |message: String| {
            Err(CelError::Registration {
                name: path.join("."),
                message,
            })
        };
        let mut ty = match path.first().and_then(|root| self.env.get(root)) {
            Some(t) => t.clone(),
            None => return refuse("the root is not declared".into()),
        };
        for member in &path[1..] {
            let next = match &ty {
                CelTy::Record(r) => r.get(member).cloned(),
                _ => None,
            };
            match next {
                Some(t) => ty = t,
                None => return refuse(format!("no declared member `{member}`")),
            }
        }
        if ty != CelTy::Str {
            return refuse(format!("a closed set is of strings; this is {}", ty.name()));
        }
        if values.len() > hostfn::MAX_ENUM_VALUES {
            return refuse(format!(
                "{} values; a closed set lists at most {}",
                values.len(),
                hostfn::MAX_ENUM_VALUES
            ));
        }
        if let Some(v) = values
            .iter()
            .enumerate()
            .find_map(|(i, v)| values[..i].contains(v).then_some(v))
        {
            return refuse(format!("`{v}` is listed twice"));
        }
        if self.enums.at(path).is_some() {
            return refuse("already declared in this environment".into());
        }
        Arc::make_mut(&mut self.enums).entries.push((
            path.iter().map(|p| p.to_string()).collect(),
            values.iter().map(|v| Box::from(*v)).collect(),
        ));
        Ok(self)
    }

    /// Declare a HOST function: `name`, typed `params -> ret` for the checker, answered by `call`.
    /// `params` includes the receiver when `member` is true (`s.f(x)` is `[type of s, type of x]`).
    ///
    /// The function must be PURE (see [`HostCall`]): a specialization folds a call whose
    /// arguments are all known, and the fast backend may call it while lowering. A name the dialect
    /// owns — a built-in, a removal, a macro, an operator spelling — is refused, as is anything
    /// that is not an identifier and any second registration of one name.
    pub fn register_host(
        &mut self,
        name: &str,
        params: &[CelTy],
        ret: CelTy,
        member: bool,
        call: HostCall,
    ) -> Result<&mut CelEnvironment, CelError> {
        self.add_host(name, params, ret, member, hostfn::HostImpl::Closure(call))
    }

    /// Declare a CALL host: `name`, typed `() params -> ret` for the checker, with NO
    /// implementation here — each run supplies one through a [`HostDispatch`]
    /// ([`Vm::eval_result_with`], [`FastProgram::decide_tag_with`]). A call to one is never folded
    /// (the known activation cannot resolve it) and a run without a dispatcher fails it as an
    /// evaluation error. Refuses exactly the names [`register_host`](CelEnvironment::register_host)
    /// refuses, including one either kind already holds.
    pub fn declare_call_host(
        &mut self,
        name: &str,
        params: &[CelTy],
        ret: CelTy,
    ) -> Result<&mut CelEnvironment, CelError> {
        self.add_host(name, params, ret, false, hostfn::HostImpl::PerCall)
    }

    fn add_host(
        &mut self,
        name: &str,
        params: &[CelTy],
        ret: CelTy,
        member: bool,
        imp: hostfn::HostImpl,
    ) -> Result<&mut CelEnvironment, CelError> {
        let refuse = |message: &str| {
            Err(CelError::Registration {
                name: name.to_string(),
                message: message.to_string(),
            })
        };
        let ident = name
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
            && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
        if !ident || name.starts_with('_') {
            return refuse(
                "a host function's name is an identifier: a letter, then letters, digits or `_`",
            );
        }
        // Every name the retired evaluator's standard library declared is a dialect name too
        // (`tests/host_functions.rs::register_host_refuses_every_name_the_retired_stdlib_declared`).
        if check::is_dialect_name(name) {
            return refuse("the dialect owns this name; a host function never shadows it");
        }
        if self.env.host(name).is_some() {
            return refuse("already registered in this environment");
        }
        if member && params.is_empty() {
            return refuse("a member function's parameters start with its receiver");
        }
        self.env.declare_host(
            name,
            check::HostSig {
                params: params.to_vec(),
                ret,
                member,
            },
        );
        Arc::make_mut(&mut self.hosts)
            .entries
            .push(hostfn::HostEntry {
                name: name.to_string(),
                member,
                arity: params.len(),
                imp,
            });
        Ok(self)
    }

    /// Declare a top-level variable. The roster is a CLOSED enumeration built by one function in
    /// the caller — nothing rejects a variable named `credential`; it simply is not declared.
    pub fn declare(
        &mut self,
        name: impl Into<String>,
        ty: impl Into<CelTy>,
    ) -> &mut CelEnvironment {
        self.env.declare(name, ty.into());
        self
    }

    pub fn limits(&self) -> &CelLimits {
        &self.limits
    }

    pub fn types(&self) -> &TypeEnv {
        &self.env
    }

    /// An empty activation over this environment's roster. Binding a name it did not declare is
    /// refused rather than silently ignored.
    pub fn activation(&self) -> CelActivation {
        CelActivation::new(self.env.clone(), self.limits)
    }

    /// The run-time half of this environment: the limits, and no roster.
    /// Cheap to keep, `Send + Sync`, and independent of the environment once built.
    pub fn runtime(&self) -> CelRuntime {
        CelRuntime::new(self.limits)
    }

    /// Desugar, bound, parse, check. Every mistake a policy can make in an expression is found
    /// here, when a human is present to read the error.
    pub fn compile(&self, expression: &str) -> Result<CelProgram, CelError> {
        self.compile_as(expression, ResultKind::Bool)
            .map_err(|e| match e {
                // `compile`'s own error shape, unchanged for every caller.
                CelError::WrongResultType { source, actual, .. } => {
                    CelError::NotBoolean { source, actual }
                }
                other => other,
            })
    }

    /// Compile a program that must produce `expected`. [`compile`](CelEnvironment::compile) is
    /// this with `bool`. The type must be EXACTLY `expected` — `dyn` never qualifies — and only
    /// the [`ResultKind`]s are supported.
    pub fn compile_returning(
        &self,
        expression: &str,
        expected: &CelTy,
    ) -> Result<CelProgram, CelError> {
        let kind = ResultKind::of(expected).ok_or_else(|| CelError::WrongResultType {
            source: Arc::from(expression),
            expected: expected.name(),
            actual: "(unsupported result type)".into(),
        })?;
        self.compile_as(expression, kind)
    }

    /// Everything `compile` does, requiring `kind` of the result.
    pub(crate) fn compile_as(
        &self,
        expression: &str,
        kind: ResultKind,
    ) -> Result<CelProgram, CelError> {
        let (mut program, ty) = self.compile_checked(expression)?;
        // The result must BE the kind, not be compatible with one. `Dyn` lands here: uncertainty
        // must not become authorization, and must not become revocation either.
        if ty != kind.ty() {
            return Err(CelError::WrongResultType {
                source: program.authored.clone(),
                expected: kind.ty().name(),
                actual: ty.name(),
            });
        }
        program.result = kind;
        Ok(program)
    }

    /// [`compile`](CelEnvironment::compile) without the `bool` requirement: the checked program
    /// and its type.
    pub(crate) fn compile_checked(
        &self,
        expression: &str,
    ) -> Result<(CelProgram, CelTy), CelError> {
        let authored: Arc<str> = Arc::from(expression);
        let (desugared, spans) = desugar(expression).map_err(|e| CelError::Desugar {
            source: authored.clone(),
            at: e.at(),
            message: e.to_string(),
        })?;
        bounds::check_source(&desugared, &self.limits).map_err(|e| CelError::Bounds {
            source: authored.clone(),
            message: e.to_string(),
        })?;

        let (expr, info) = Parser::default()
            .parse_with_source_info(&desugared)
            .map_err(|e| CelError::Parse {
                source: authored.clone(),
                rendered: e.to_string(),
            })?;

        bounds::check_cost(&expr, &self.limits).map_err(|e| CelError::Bounds {
            source: authored.clone(),
            message: e.to_string(),
        })?;

        let (ty, demand, types) = check::Checker::new(&self.env, self.limits.max_depth)
            .run_typed(&expr)
            .map_err(|errors| {
                // Report the FIRST error through `Display`. A checker that cascades is a checker
                // whose output nobody reads, and the first one is the one the author actually
                // made — but CARRY the rest, so `CelError::all` can list them.
                let first = errors.first().expect("at least one error").clone();
                CelError::Check {
                    source: authored.clone(),
                    at: span_of(first.id, &info, &spans),
                    message: first.message,
                    available: first.available,
                    all: errors,
                }
            })?;

        // The tree that was checked is the tree that runs: `Parser::parse` is
        // `parse_with_source_info` without the source map, so a second parse would only rebuild
        // it — and the node kinds below are keyed by ITS ids.
        let program = Program::from_expression(expr);
        Ok((
            CelProgram {
                authored,
                demand,
                program,
                pool: specialize::ConstPool::default(),
                kinds: kinds_of(&types),
                // The harness's `compile_any` keeps whatever its type names; `compile_as`
                // overwrites it with the kind it required.
                result: ResultKind::of(&ty).unwrap_or(ResultKind::Bool),
                hosts: self.hosts.clone(),
                enums: self.enums.clone(),
                lowered: std::sync::OnceLock::new(),
            },
            ty,
        ))
    }
}

/// The node kinds the fast backend lowers by, from the checker's type of every node.
pub(crate) fn kinds_of(types: &std::collections::HashMap<u64, CelTy>) -> fast::Kinds {
    types
        .iter()
        .map(|(id, ty)| {
            let k = match ty {
                CelTy::Bool => fast::Kind::Bool,
                CelTy::Num => fast::Kind::Num,
                CelTy::Str => fast::Kind::Str,
                CelTy::Bytes => fast::Kind::Bytes,
                CelTy::Null => fast::Kind::Null,
                CelTy::Duration => fast::Kind::Duration,
                CelTy::List(_) => fast::Kind::List,
                CelTy::Map(..) => fast::Kind::Map,
                CelTy::Record(_) => fast::Kind::Record,
                CelTy::Dyn | CelTy::Unusable(_) => fast::Kind::Dyn,
            };
            (*id, k)
        })
        .collect()
}

impl CelEnvironment {
    /// Fold every root `known` bound with `bind` out of `program`.
    ///
    /// The residual reads only roots that were not bound, or were bound with `bind_lazy`, and
    /// agrees with `program` on every completion of them. It is built from the folded tree, not
    /// re-parsed: its `source()` is that tree rendered, and its `demand()` is what checking that
    /// tree harvests — exactly what the residual reads.
    pub fn specialize(
        &self,
        program: &CelProgram,
        known: &CelActivation,
    ) -> Result<CelProgram, CelError> {
        self.specialize_slots(program, known).map(|(p, _)| p)
    }

    /// [`specialize`](CelEnvironment::specialize), also handing back each constant slot's name and
    /// the type the residual was re-checked with.
    ///
    /// A known composite the residual still reads is not written out as a literal: it is held in
    /// the residual's constant pool and read as `$kN`, typed from the type the ORIGINAL was checked
    /// at for the node it replaces. A known scalar is still written out.
    pub(crate) fn specialize_slots(
        &self,
        program: &CelProgram,
        known: &CelActivation,
    ) -> Result<(CelProgram, Vec<(String, CelTy)>), CelError> {
        self.specialize_inner(program, known, false)
    }

    /// [`specialize_slots`](CelEnvironment::specialize_slots); `refuse_all` fails every lowering of
    /// a closed subtree (the test door `fork::specialize_with_lowering_refused`).
    pub(crate) fn specialize_inner(
        &self,
        program: &CelProgram,
        known: &CelActivation,
        refuse_all: bool,
    ) -> Result<(CelProgram, Vec<(String, CelTy)>), CelError> {
        let refuse = |message: String| CelError::Specialize {
            source: program.source_arc(),
            message,
        };
        // A slot's type exists only inside the `specialize` that made it (a `CelTy` is not
        // `Send`, and a program is), so a residual holding slots cannot be re-checked again.
        if !program.pool.is_empty() {
            return Err(refuse(
                "a residual that holds constant slots cannot be specialized again; specialize the \
                 original with every known root bound"
                    .to_string(),
            ));
        }
        let roots = known.known_roots();
        let original = program.program().expression();
        // The type of every node, from the checker and roster the original compiled against.
        let (_, _, types) = check::Checker::new(&self.env, self.limits.max_depth)
            .run_typed(original)
            .map_err(|errors| {
                let first = errors.first().map(|e| e.message.as_str()).unwrap_or("");
                refuse(format!("the original does not type-check: {first}"))
            })?;
        let kinds = kinds_of(&types);
        let (mut residual, slots, refused) = specialize::fold_typed(
            original,
            known.roots(),
            roots,
            self.limits,
            &types,
            specialize::Lowering {
                kinds: &kinds,
                hosts: &self.hosts,
                enums: &self.enums,
                refuse_all,
            },
        );
        // Every closed subtree of a checked tree lowers; one that does not is a defect of the
        // backend, never a reason to leave a known read in the residual.
        if let Some(first) = refused.first() {
            return Err(refuse(format!(
                "the backend could not lower a closed subtree ({} time(s)); first: {first}",
                refused.len()
            )));
        }
        specialize::renumber(&mut residual);
        specialize::check_no_known_read(&residual, roots).map_err(|path| {
            refuse(format!(
                "known root `{path}` is not fully reducible: the residual still reads it"
            ))
        })?;
        // Not skipped because the original passed: unrolling trades the estimate's assumed
        // iteration count for the real element count, so a residual can cost MORE.
        bounds::check_cost(&residual, &self.limits).map_err(|e| CelError::Bounds {
            source: program.source_arc(),
            message: format!("the specialized form {e}"),
        })?;
        // The residual's demand comes from checking IT, with the same checker and roster the
        // original compiled against, and each slot declared with its type: a folded branch's reads
        // are gone, and a superset would have a caller populate what nothing reads. The folded
        // roots are no longer in the tree, and a slot is not demand.
        let decls: Vec<(String, CelTy)> = slots
            .iter()
            .map(|s| (s.name.clone(), s.ty.clone()))
            .collect();
        // Re-checked against the ORIGINAL's result kind: a `string` program's residual is a
        // `string` program, never re-held to `compile`'s `bool`.
        let (demand, types) = specialize::recheck(
            &self.env,
            self.limits.max_depth,
            &residual,
            &decls,
            program.result.ty(),
        )
        .map_err(refuse)?;
        let pool = specialize::ConstPool::new(
            slots
                .into_iter()
                .map(|s| (Arc::from(s.name.as_str()), s.value))
                .collect(),
        );
        let rendered = unparse::unparse(&residual).map_err(|e| refuse(e.to_string()))?;
        let rendered = format!("{rendered}{}", pool.legend());
        Ok((
            CelProgram {
                authored: Arc::from(rendered),
                demand,
                program: Program::from_expression(residual),
                pool,
                kinds: kinds_of(&types),
                result: program.result,
                hosts: self.hosts.clone(),
                enums: self.enums.clone(),
                lowered: std::sync::OnceLock::new(),
            },
            decls,
        ))
    }
}

/// The authored span of the node with expression id `id`.
fn span_of(id: u64, info: &common::ast::SourceInfo, spans: &SpanMap) -> Option<Span> {
    let (start, stop) = info.offset_for(id)?;
    let start = spans.to_authored(start as usize);
    // The recorded range is INCLUSIVE and addresses the token that ANCHORS a node — the operator
    // for a call, the `.` for a select — not the node's full extent. So a diagnostic about
    // `body.no_such_field` carets the dot, and the MESSAGE has to name the field.
    let end = spans.to_authored(stop as usize) + 1;
    Some(Span {
        start,
        end: end.max(start + 1),
    })
}

/// One expression: desugared, bounded, parsed and checked, ready to evaluate.
///
/// Holds its AUTHORED source for diagnostics and its demand set for the runtime. `Send + Sync`,
/// because a compiled policy is shared across request-handling threads and across the poll loop.
#[derive(Debug)]
pub struct CelProgram {
    authored: Arc<str>,
    demand: DemandSet,
    program: Program,
    /// A residual's known composites, read by slot. Empty for a compiled program.
    pool: specialize::ConstPool,
    /// Every node's kind, from the checker, for the fast backend's lowering.
    kinds: fast::Kinds,
    /// The type the program is required to produce.
    result: ResultKind,
    /// The host functions of the environment it was compiled in, dispatched by index.
    hosts: Arc<hostfn::HostTable>,
    /// The closed string sets of that environment.
    enums: Arc<hostfn::EnumTable>,
    /// This program on the backend, lowered on first use and then shared by `evaluate`, `emit` and
    /// every clone of its bytecode. `Err` holds the lowering refusal's message (a backend defect).
    lowered: std::sync::OnceLock<Result<Arc<FastProgram>, Arc<str>>>,
}

impl CelProgram {
    /// The lowered program, built on first use.
    pub(crate) fn lowered(&self) -> Result<&Arc<FastProgram>, CelError> {
        let slot = self.lowered.get_or_init(|| {
            FastProgram::new(self).map(Arc::new).map_err(|e| match e {
                CelError::Emit { message, .. } => Arc::from(message),
                other => Arc::from(other.to_string()),
            })
        });
        slot.as_ref().map_err(|message| CelError::Emit {
            source: self.source_arc(),
            message: message.to_string(),
        })
    }
}

/// The type a program is required to produce ([`CelEnvironment::compile_returning`]). `Copy` and
/// `Send`, unlike [`CelTy`], so a compiled program carries it across threads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResultKind {
    Bool,
    Str,
    Num,
    Bytes,
}

impl ResultKind {
    /// The kind `ty` names, when it names one. `dyn` names none.
    pub fn of(ty: &CelTy) -> Option<ResultKind> {
        match ty {
            CelTy::Bool => Some(ResultKind::Bool),
            CelTy::Str => Some(ResultKind::Str),
            CelTy::Num => Some(ResultKind::Num),
            CelTy::Bytes => Some(ResultKind::Bytes),
            _ => None,
        }
    }

    pub(crate) fn ty(self) -> CelTy {
        match self {
            ResultKind::Bool => CelTy::Bool,
            ResultKind::Str => CelTy::Str,
            ResultKind::Num => CelTy::Num,
            ResultKind::Bytes => CelTy::Bytes,
        }
    }
}

impl CelProgram {
    /// The AUTHORED form, always — never the desugared one. A diagnostic quoting source the author
    /// did not write is a diagnostic about the wrong program.
    pub fn source(&self) -> &str {
        &self.authored
    }

    /// What this expression reads. See [`DemandSet`].
    pub fn demand(&self) -> &DemandSet {
        &self.demand
    }

    /// The type this program is required to produce.
    pub fn result_kind(&self) -> ResultKind {
        self.result
    }

    pub(crate) fn source_arc(&self) -> Arc<str> {
        self.authored.clone()
    }

    pub(crate) fn program(&self) -> &Program {
        &self.program
    }

    pub(crate) fn pool(&self) -> &specialize::ConstPool {
        &self.pool
    }

    pub(crate) fn kinds(&self) -> &fast::Kinds {
        &self.kinds
    }

    pub(crate) fn hosts(&self) -> &Arc<hostfn::HostTable> {
        &self.hosts
    }

    pub(crate) fn enums(&self) -> &hostfn::EnumTable {
        &self.enums
    }
}

/// Every way compiling or evaluating an expression can fail.
///
/// Structured parts rather than one formatted string: the policy compiler knows the endpoint, the
/// status code and the file position, and it assembles the final rendering. An error already
/// flattened into prose cannot be placed in a file.
#[derive(Debug)]
pub enum CelError {
    /// `1d`, `30x`. See [`DesugarError`].
    Desugar {
        source: Arc<str>,
        at: usize,
        message: String,
    },
    /// Outside [`CelLimits`].
    Bounds {
        source: Arc<str>,
        message: String,
    },
    /// A value could not be bound into an activation, or was bound to an undeclared name.
    Bind {
        message: String,
    },
    /// Did not parse. Carries the renderer's OWN output, which already has a caret — and the whole
    /// of it, because `ParseErrors` is a collection and the discarded ones are often the
    /// informative ones.
    Parse {
        source: Arc<str>,
        rendered: String,
    },
    /// Parsed but did not check.
    ///
    /// `message`/`available` are the FIRST error's, because a cascading diagnostic is one nobody
    /// reads and the first is the one the author actually made. `rest` carries the others so a
    /// policy compiler can list them all — a caller listing a file's problems wants every one, and
    /// dropping them at the boundary meant it could never have them.
    Check {
        source: Arc<str>,
        at: Option<Span>,
        message: String,
        available: Option<Vec<String>>,
        all: Vec<CheckError>,
    },
    NotBoolean {
        source: Arc<str>,
        actual: String,
    },
    /// [`CelEnvironment::compile_returning`]: the program's type is not the one required.
    WrongResultType {
        source: Arc<str>,
        expected: String,
        actual: String,
    },
    /// Evaluation failed. ALWAYS fail-closed at the call site.
    Evaluation {
        source: Arc<str>,
        message: String,
    },
    /// Parsed and checked, but has no bytecode ([`emit`]). Unreachable for a program
    /// [`CelEnvironment::compile`] produced; carried rather than panicked on.
    Emit {
        source: Arc<str>,
        message: String,
    },
    /// A specialization could not produce a residual: a known root is still read, or the residual
    /// does not type-check or has no rendering. `source` is the ORIGINAL program's authored text.
    Specialize {
        source: Arc<str>,
        message: String,
    },
    /// [`CelEnvironment::register_host`] refused a name.
    Registration {
        name: String,
        message: String,
    },
    /// A [`LazyValue`] was asked for a member it does not have. Becomes the same `no such key` a
    /// materialized map produces, so a typo behaves identically either way.
    NoSuchMember {
        key: String,
    },
}

impl CelError {
    /// A call to a CALL host that the run's dispatcher does not answer.
    pub fn unknown_host_function(name: &str) -> CelError {
        CelError::Evaluation {
            source: Arc::from(name),
            message: format!("`{name}` is not a host function this run answers"),
        }
    }

    /// The authored expression this is about, when there is one.
    pub fn source(&self) -> Option<&str> {
        match self {
            CelError::Bind { .. }
            | CelError::Registration { .. }
            // A lazy view has no idea which expression is reading it; the backend adds the
            // source when it wraps this into an `Evaluation`.
            | CelError::NoSuchMember { .. } => None,
            CelError::Desugar { source, .. }
            | CelError::Bounds { source, .. }
            | CelError::Parse { source, .. }
            | CelError::Check { source, .. }
            | CelError::NotBoolean { source, .. }
            | CelError::WrongResultType { source, .. }
            | CelError::Evaluation { source, .. }
            | CelError::Emit { source, .. }
            | CelError::Specialize { source, .. } => Some(source),
        }
    }

    /// The authored span, when the error has one.
    pub fn span(&self) -> Option<Span> {
        match self {
            CelError::Check { at, .. } => *at,
            CelError::Desugar { at, .. } => Some(Span {
                start: *at,
                end: at + 1,
            }),
            _ => None,
        }
    }

    /// Every error the checker found, first one first.
    ///
    /// `Display` renders only the first — that decision stands, because a cascade is a diagnostic
    /// nobody reads. This is for a caller that lists a policy file's problems, which wants all of
    /// them. Empty for every error that is not a check failure.
    pub fn all(&self) -> &[CheckError] {
        match self {
            CelError::Check { all, .. } => all,
            _ => &[],
        }
    }

    /// The "available: …" roster, when the error has one.
    pub fn available(&self) -> Option<&[String]> {
        match self {
            CelError::Check { available, .. } => available.as_deref(),
            _ => None,
        }
    }
}

impl std::fmt::Display for CelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CelError::Bind { message } => write!(f, "{message}"),
            CelError::Parse { rendered, .. } => write!(f, "{rendered}"),
            CelError::Bounds { message, .. } => write!(f, "{message}"),
            CelError::NotBoolean { source, actual } => write!(
                f,
                "{source}\n  an expression must evaluate to bool, this one is {actual}"
            ),
            CelError::WrongResultType {
                source,
                expected,
                actual,
            } => write!(
                f,
                "{source}\n  this program must evaluate to {expected}, this one is {actual}"
            ),
            CelError::Evaluation { source, message } => write!(f, "{source}\n  {message}"),
            CelError::Emit { source, message } => write!(f, "{source}\n  {message}"),
            CelError::Specialize { source, message } => write!(f, "{source}\n  {message}"),
            CelError::NoSuchMember { key } => write!(f, "no such key: {key}"),
            CelError::Registration { name, message } => {
                write!(f, "cannot register `{name}`: {message}")
            }
            CelError::Desugar {
                source,
                at,
                message,
            } => {
                write!(f, "{source}\n{}\n  {message}", caret(source, *at, at + 1))
            }
            CelError::Check {
                source,
                at,
                message,
                available,
                ..
            } => {
                writeln!(f, "{source}")?;
                if let Some(span) = at {
                    writeln!(f, "{}", caret(source, span.start, span.end))?;
                }
                write!(f, "  {message}")?;
                if let Some(roster) = available {
                    write!(f, "\n  available: {}", roster.join(", "))?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for CelError {}

/// A `^^^` run under `[start, end)` of a single-line expression.
fn caret(source: &str, start: usize, end: usize) -> String {
    let start = start.min(source.len());
    let end = end.clamp(start + 1, source.len().max(start + 1));
    let mut out = String::with_capacity(end);
    out.push_str(&" ".repeat(start));
    out.push_str(&"^".repeat(end - start));
    out
}

/// Every function the dialect declares, with its overloads rendered as `README.md` writes them.
///
/// Public so `tests/signatures.rs` can hold the document and the table to each other in both
/// directions; nothing in the crate's contract depends on it.
pub fn signature_table() -> Vec<(&'static str, Vec<String>)> {
    sigs::rendered()
}
