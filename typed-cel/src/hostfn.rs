//! What an embedding ENVIRONMENT declares beyond its variables' types: host functions — typed for
//! the checker, pure, and dispatched by the backend — and closed
//! string sets. The dialect itself stays closed — see README "There are
//! no custom functions": these belong to one environment, not to the language.
//!
//! A function is a closure over whatever table its environment built, so a matching engine an
//! embedder already has is exposed as a call rather than re-implemented in expressions. It must
//! be PURE — deterministic, no I/O, no global state, no panics (an `Err` is its only failure) —
//! because a specialization folds a call whose arguments are all known, and the fast backend
//! calls it once per element of a known list when it builds a matcher.
//!
//! This file names only the boundary values a call takes and returns.

use std::sync::Arc;

use crate::{CelError, CelValue};

/// A host function: its arguments (the receiver first, for a member) to its result.
pub type HostCall = Arc<dyn Fn(&[CelValue]) -> Result<CelValue, CelError> + Send + Sync>;

/// A CALL host's implementation, supplied per RUN rather than at environment build: the run's
/// dispatcher answers every call to a function declared with
/// [`CelEnvironment::declare_call_host`](crate::CelEnvironment::declare_call_host).
///
/// It exists for a function whose by-product has no [`CelValue`] form, or whose inputs are the
/// caller's own typed data: the dispatcher borrows them for one run and keeps whatever it computed
/// for the caller to read afterwards. Never folded, never called while lowering.
pub trait HostDispatch {
    /// A call to the CALL host `name`, with its evaluated arguments (the receiver first, for a
    /// member). An `Err` is an evaluation error of the run, never a panic.
    fn call(&mut self, name: &str, args: &[CelValue]) -> Result<CelValue, CelError>;
}

/// The dispatcher for a run that supplies none: every CALL host is an evaluation error.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoCallHosts;

impl HostDispatch for NoCallHosts {
    fn call(&mut self, name: &str, _: &[CelValue]) -> Result<CelValue, CelError> {
        Err(CelError::unknown_host_function(name))
    }
}

/// How a registered function is answered.
#[derive(Clone)]
pub(crate) enum HostImpl {
    /// A pure closure over a table fixed when the environment was built: folded when every
    /// argument is known, and callable while lowering.
    Closure(HostCall),
    /// Answered by the run's [`HostDispatch`]; unknown to the specializer, which keeps a call to
    /// one symbolic.
    PerCall,
}

/// One registered function.
#[derive(Clone)]
pub(crate) struct HostEntry {
    pub(crate) name: String,
    pub(crate) member: bool,
    /// Including the receiver, for a member.
    pub(crate) arity: usize,
    pub(crate) imp: HostImpl,
}

impl HostEntry {
    /// The closure, for a function that has one.
    pub(crate) fn closure(&self) -> Option<&HostCall> {
        match &self.imp {
            HostImpl::Closure(c) => Some(c),
            HostImpl::PerCall => None,
        }
    }
}

/// Every function one environment registered, in registration order. A program carries the table
/// it was compiled against, so a call is dispatched by index, never by name.
#[derive(Clone, Default)]
pub(crate) struct HostTable {
    pub(crate) entries: Vec<HostEntry>,
}

impl HostTable {
    /// The index of `name` when it is registered with this calling form.
    pub(crate) fn index_of(&self, name: &str, member: bool) -> Option<u16> {
        self.entries
            .iter()
            .position(|e| e.name == name && e.member == member)
            .and_then(|i| u16::try_from(i).ok())
    }
}

impl std::fmt::Debug for HostTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.entries.iter().map(|e| (&e.name, e.member, e.arity)))
            .finish()
    }
}

/// Why a host call produced no value, worded once for both engines: the error the function
/// returned, or an argument or result with no boundary form.
pub(crate) fn failure(name: &str, why: impl std::fmt::Display) -> crate::ExecutionError {
    crate::ExecutionError::function_error(name, why)
}

/// A string field's value set is CLOSED: the field holds one of these values, or — from a provider
/// that does not keep that promise — some other string, which is [`TAG_OTHER`]. A value's TAG is
/// its index in the list. Declaring one changes no meaning; the fast backend compares a tag
/// instead of string bytes where the literal compared against is in the list.
pub const TAG_OTHER: u8 = u8::MAX;

/// The most values one closed set may list: a tag test is one 64-bit mask.
pub(crate) const MAX_ENUM_VALUES: usize = 64;

/// Every closed string set an environment declared, by field path (root first).
#[derive(Clone, Debug, Default)]
pub(crate) struct EnumTable {
    pub(crate) entries: Vec<(Vec<String>, Arc<[Box<str>]>)>,
}

impl EnumTable {
    /// The values of the set declared at `path` (root first), when one is.
    pub(crate) fn at(&self, path: &[&str]) -> Option<&Arc<[Box<str>]>> {
        self.entries
            .iter()
            .find(|(p, _)| p.len() == path.len() && p.iter().zip(path).all(|(a, b)| a == b))
            .map(|(_, v)| v)
    }
}

/// `s`'s tag in `values`, or [`TAG_OTHER`].
#[inline]
pub(crate) fn tag_of(values: &[Box<str>], s: &str) -> u8 {
    values
        .iter()
        .position(|v| **v == *s)
        .map_or(TAG_OTHER, |i| i as u8)
}
