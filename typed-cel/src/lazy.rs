//! The one extension point the library offers: a value that resolves on ACCESS.
//!
//! It exists because a system expression is evaluated on every tick for the life of a sandbox, so
//! building a map of the whole state per evaluation makes the cost of a policy proportional to the
//! SANDBOX rather than to the POLICY. A caller that has the data already — in atomics, in a ring
//! buffer, behind a lock — serves indexing straight off it and allocates one small scalar per
//! field an expression actually reads.
//!
//! It is deliberately the ONLY one. Everything that crosses this boundary is a [`CelValue`] — a
//! closed enum — so a caller writes against the one value and nothing else.

use std::sync::Arc;

use crate::value::CelValue;
use crate::ExecutionError;

/// A value that resolves its members on ACCESS rather than being materialized.
///
/// `'static` is not optional and is not a style choice: a [`CelValue`] holds a view as an
/// `Arc<dyn LazyValue>`, and a program's result may outlive the call that produced it. An
/// implementor therefore OWNS its state — typically an `Arc` of it — rather than borrowing one.
pub trait LazyValue: Send + Sync + std::fmt::Debug + 'static {
    /// `x.field` and `x["key"]` — the same call, because CEL does not distinguish them.
    ///
    /// A name this value does not have must be [`CelError::NoSuchMember`], NOT a zero value: a
    /// typo that reads as "never happened" is a condition that is permanently false, and for a
    /// revocation expression that is a grant that never revokes.
    fn member(&self, name: &str) -> Result<CelValue, crate::CelError>;

    /// [`member`](LazyValue::member), for a value that may still be arriving.
    ///
    /// `Pending` names the demand the read waits on. Settled answers never change: once a read is
    /// `Ready`, every later read of the same member is `Ready` with the same value. The default is
    /// never pending.
    fn poll_member(&self, name: &str) -> Result<Access, crate::CelError> {
        self.member(name).map(Access::Ready)
    }

    /// `has(x.name)` / `name in x` — an existence question, which may be decidable before (or
    /// without) the member's value.
    ///
    /// The default derives it from [`member`](LazyValue::member): [`CelError::NoSuchMember`] is
    /// `false`, a value is `true`, and any other error propagates.
    ///
    /// [`CelError::NoSuchMember`]: crate::CelError::NoSuchMember
    fn poll_has(&self, name: &str) -> Result<Presence, crate::CelError> {
        match self.member(name) {
            Ok(_) => Ok(Presence::Known(true)),
            Err(crate::CelError::NoSuchMember { .. }) => Ok(Presence::Known(false)),
            Err(e) => Err(e),
        }
    }

    /// The keys a comprehension iterates, for a value that is map-shaped. `None` means "not
    /// iterable", and a comprehension over it is an evaluation error.
    ///
    /// Keys are handed out BY REFERENCE. A comprehension reads each key where it lies, so a
    /// signature returning owned `String`s would allocate per key per tick and quietly undo the
    /// flat-cost guarantee this trait exists for — which is why the item is [`CelKey`], a key the
    /// implementor already stores, rather than a `&str` this module would have to wrap.
    fn keys(&self) -> Option<Box<dyn Iterator<Item = &CelKey> + '_>> {
        None
    }
}

/// Which demanded value a suspended read is waiting for.
///
/// Opaque to the backend; meaningful only to the value that handed it out.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DemandHandle(u32);

impl DemandHandle {
    pub fn new(id: u32) -> DemandHandle {
        DemandHandle(id)
    }

    pub fn id(self) -> u32 {
        self.0
    }
}

/// A member read that may not be answerable YET.
#[derive(Clone, Debug)]
pub enum Access {
    Ready(CelValue),
    Pending(DemandHandle),
}

/// The answer to an existence question that may not be answerable YET.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Presence {
    Known(bool),
    Pending(DemandHandle),
}

/// A map key a [`LazyValue`] stores so it can hand it out by reference.
///
/// Opaque on purpose: a shared string, so building the key once when the state is created costs
/// nothing per read, and a map's keys and a lazy value's keys are the same thing.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CelKey(Arc<str>);

impl CelKey {
    pub fn new(key: &str) -> CelKey {
        CelKey(key.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for CelKey {
    fn from(s: &str) -> CelKey {
        CelKey::new(s)
    }
}

impl From<String> for CelKey {
    fn from(s: String) -> CelKey {
        CelKey(s.into())
    }
}

impl std::fmt::Display for CelKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The one place a member lookup's error becomes a run's.
pub(crate) fn member_error(name: &str, e: crate::CelError) -> ExecutionError {
    match e {
        // The same `no such key` a real map produces, so a typo behaves identically whether the
        // value was materialized or resolved on access.
        crate::CelError::NoSuchMember { .. } => ExecutionError::no_such_key(name),
        other => ExecutionError::FunctionError {
            function: name.to_string(),
            message: other.to_string(),
        },
    }
}

/// The one place a pending read becomes a run's error. A run that cannot wait treats "not yet"
/// as any other failed read, so `&&`/`||` absorb it exactly as they absorb any
/// other error.
pub(crate) fn pending_error(name: &str, h: DemandHandle) -> ExecutionError {
    ExecutionError::FunctionError {
        function: name.to_string(),
        message: format!("value not yet available (demand {})", h.id()),
    }
}

/// `has(x.name)` / `name in x` over a lazy — an existence question, never the member's value.
/// A run that cannot wait reads "not yet" as an error.
pub(crate) fn presence(v: &dyn LazyValue, name: &str) -> Result<bool, ExecutionError> {
    match poll_presence(v, name)? {
        Presence::Known(b) => Ok(b),
        Presence::Pending(h) => Err(pending_error(name, h)),
    }
}

/// [`presence`] for a run that can wait: `Pending` is handed back rather than turned into an
/// error. Keys first when the value has them, so a keyed value answers from its keys and resolves
/// no member; presence (`poll_has`) otherwise, which is what makes `in` work on a keyless value.
pub(crate) fn poll_presence(v: &dyn LazyValue, name: &str) -> Result<Presence, ExecutionError> {
    if let Some(mut keys) = v.keys() {
        return Ok(Presence::Known(keys.any(|k| k.as_str() == name)));
    }
    v.poll_has(name).map_err(|e| member_error(name, e))
}

/// `x.name` / `x["name"]`: the member, or `Pending` for a value still arriving.
pub(crate) fn poll_read(v: &dyn LazyValue, name: &str) -> Result<Access, ExecutionError> {
    v.poll_member(name).map_err(|e| member_error(name, e))
}

/// [`poll_read`] for a run that cannot wait: "not yet" is an error.
pub(crate) fn read(v: &dyn LazyValue, name: &str) -> Result<CelValue, ExecutionError> {
    match poll_read(v, name)? {
        Access::Ready(v) => Ok(v),
        Access::Pending(h) => Err(pending_error(name, h)),
    }
}
