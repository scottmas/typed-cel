//! The one extension point the library offers: a value that resolves on ACCESS.
//!
//! It exists because a system expression is evaluated on every tick for the life of a sandbox, so
//! building a map of the whole state per evaluation makes the cost of a policy proportional to the
//! SANDBOX rather than to the POLICY. A caller that has the data already — in atomics, in a ring
//! buffer, behind a lock — serves indexing straight off it and allocates one small scalar per
//! field an expression actually reads.
//!
//! It is deliberately the ONLY one. The absorbed evaluator's own `Val` trait would serve the same
//! purpose and is strictly more capable, but it is the fork's, and a caller written against it is
//! a caller the fork cannot be re-based under. Everything that crosses this boundary is a
//! [`CelValue`] — a closed enum — so no absorbed type appears in a signature a caller writes.

use std::borrow::Cow;
use std::sync::Arc;

use crate::common::traits::{Container, Indexer, Iterable};
use crate::common::types::{CelDouble, CelString, Type};
use crate::common::value::Val;
use crate::ExecutionError;

/// A value that resolves its members on ACCESS rather than being materialized.
///
/// `'static` is not optional and is not a style choice: the evaluator's value trait is
/// `Any + Debug + Send + Sync`, and `Any` implies `'static`. An implementor therefore OWNS its
/// state — typically an `Arc` of it — rather than borrowing one.
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
    /// Keys are handed out BY REFERENCE. The evaluator's iterator yields borrowed values, so a
    /// signature returning owned `String`s would allocate per key per tick and quietly undo the
    /// flat-cost guarantee this trait exists for — which is why the item is [`CelKey`], a key the
    /// implementor already stores, rather than a `&str` this module would have to wrap.
    fn keys(&self) -> Option<Box<dyn Iterator<Item = &CelKey> + '_>> {
        None
    }
}

/// Which demanded value a suspended read is waiting for.
///
/// Opaque to the evaluator; meaningful only to the value that handed it out.
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
/// Opaque on purpose: it wraps the evaluator's string representation, so building the key once
/// when the state is created costs nothing per read.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct CelKey(CelString);

impl CelKey {
    pub fn new(key: &str) -> CelKey {
        CelKey(CelString::from(key))
    }

    pub fn as_str(&self) -> &str {
        self.0.inner()
    }
}

impl From<&str> for CelKey {
    fn from(s: &str) -> CelKey {
        CelKey::new(s)
    }
}

impl From<String> for CelKey {
    fn from(s: String) -> CelKey {
        CelKey(CelString::from(s))
    }
}

impl std::fmt::Display for CelKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// What a [`LazyValue`] may return, and what a caller may bind.
///
/// A closed enum, so the fork's `Value` never crosses the boundary. Numbers are `f64` because the
/// dialect has ONE numeric type; a duration is milliseconds because `chrono` is the fork's
/// business and a caller that had to name `chrono::Duration` would be depending on an absorbed
/// implementation detail.
#[derive(Clone, Debug)]
pub enum CelValue {
    Bool(bool),
    Num(f64),
    Str(String),
    /// Milliseconds.
    Duration(i64),
    /// A byte string, which need not be UTF-8.
    Bytes(Vec<u8>),
    List(Vec<CelValue>),
    /// A record: field name → value. Bound as the evaluator's string-keyed map, so the order is
    /// not observable to an expression; a value read BACK (`Vm::eval_result`) lists its fields in
    /// key order.
    Record(Vec<(CelKey, CelValue)>),
    Null,
    Lazy(Arc<dyn LazyValue>),
}

impl CelValue {
    /// Into the evaluator's value, directly: a list or a record converts element by element, so a
    /// lazy view inside one stays a view rather than being materialized.
    pub(crate) fn into_val(self) -> Box<dyn Val> {
        use crate::common::types::{CelBool, CelBytes, CelDuration, CelList, CelMap, CelNull};
        match self {
            CelValue::Bool(b) => Box::new(CelBool::from(b)),
            CelValue::Num(n) => Box::new(CelDouble::from(n)),
            CelValue::Str(s) => Box::new(CelString::from(s)),
            CelValue::Duration(ms) => {
                Box::new(CelDuration::from(chrono::Duration::milliseconds(ms)))
            }
            CelValue::Bytes(b) => Box::new(CelBytes::from(b)),
            CelValue::List(items) => Box::new(CelList::from(
                items
                    .into_iter()
                    .map(CelValue::into_val)
                    .collect::<Vec<_>>(),
            )),
            CelValue::Record(fields) => Box::new(CelMap::from(
                fields
                    .into_iter()
                    .map(|(k, v)| (crate::common::types::CelMapKey::String(k.0), v.into_val()))
                    .collect::<std::collections::HashMap<_, _>>(),
            )),
            CelValue::Null => Box::new(CelNull),
            CelValue::Lazy(v) => Box::new(LazyAdapter(v)),
        }
    }

    /// Into the evaluator's boundary value. `None` for a lazy view, which has no boundary form.
    pub(crate) fn into_value(self) -> Option<crate::objects::Value> {
        use crate::objects::{Key, Map, Value as V};
        Some(match self {
            CelValue::Bool(b) => V::Bool(b),
            CelValue::Num(n) => V::Float(n),
            CelValue::Str(s) => V::String(Arc::new(s)),
            CelValue::Duration(ms) => V::Duration(chrono::Duration::milliseconds(ms)),
            CelValue::Bytes(b) => V::Bytes(Arc::new(b)),
            CelValue::Null => V::Null,
            CelValue::List(items) => V::List(Arc::new(
                items
                    .into_iter()
                    .map(CelValue::into_value)
                    .collect::<Option<_>>()?,
            )),
            CelValue::Record(fields) => {
                let mut map = std::collections::HashMap::with_capacity(fields.len());
                for (k, v) in fields {
                    map.insert(
                        Key::String(Arc::new(k.0.inner().to_string())),
                        v.into_value()?,
                    );
                }
                V::Map(Map { map: Arc::new(map) })
            }
            CelValue::Lazy(_) => return None,
        })
    }

    /// From the evaluator's boundary value. `None` for a value with no `CelValue` spelling (an
    /// opaque, a function, a map with a non-string key); the caller turns that into an error,
    /// never into a default.
    pub(crate) fn from_value(v: &crate::objects::Value) -> Option<CelValue> {
        use crate::objects::{Key, Value as V};
        Some(match v {
            V::Bool(b) => CelValue::Bool(*b),
            V::Float(f) => CelValue::Num(*f),
            V::String(s) => CelValue::Str(s.to_string()),
            V::Bytes(b) => CelValue::Bytes(b.to_vec()),
            V::Null => CelValue::Null,
            V::Duration(d) => CelValue::Duration(d.num_milliseconds()),
            V::List(items) => CelValue::List(
                items
                    .iter()
                    .map(CelValue::from_value)
                    .collect::<Option<_>>()?,
            ),
            V::Map(m) => {
                let mut fields = m
                    .map
                    .iter()
                    .map(|(k, v)| match k {
                        Key::String(s) => Some((CelKey::new(s), CelValue::from_value(v)?)),
                        Key::Num(_) | Key::Bool(_) => None,
                    })
                    .collect::<Option<Vec<_>>>()?;
                // The map is hashed; key order makes the answer deterministic.
                fields.sort_by(|a, b| a.0.cmp(&b.0));
                CelValue::Record(fields)
            }
            V::Function(..) | V::Opaque(_) => return None,
        })
    }
}

/// An evaluator value as a boundary value, for a host function's argument: a lazy view is the
/// view itself, anything else converts through the boundary value. `None` for a value with no
/// `CelValue` spelling.
pub(crate) fn val_to_cel(v: &dyn Val) -> Option<CelValue> {
    if let Some(lazy) = v.downcast_ref::<LazyAdapter>() {
        return Some(CelValue::Lazy(Arc::clone(&lazy.0)));
    }
    let value = crate::objects::Value::try_from(v).ok()?;
    CelValue::from_value(&value)
}

/// The bridge. A `LazyValue` on one side, the fork's `Val` on the other, and nothing of the fork
/// visible through the trait.
#[derive(Clone, Debug)]
pub(crate) struct LazyAdapter(pub(crate) Arc<dyn LazyValue>);

/// Every view reports one opaque type. `Type::new_struct` does not exist; the opaque constructor
/// is what a non-map, non-list custom value uses.
fn lazy_type() -> &'static Type {
    static TY: std::sync::OnceLock<Type> = std::sync::OnceLock::new();
    TY.get_or_init(|| Type::new_opaque_type("cel.lazy"))
}

impl Val for LazyAdapter {
    fn get_type(&self) -> &Type {
        lazy_type()
    }
    fn clone_as_boxed(&self) -> Box<dyn Val> {
        Box::new(self.clone())
    }
    fn as_indexer(&self) -> Option<&dyn Indexer> {
        Some(self)
    }
    fn into_indexer(self: Box<Self>) -> Option<Box<dyn Indexer>> {
        Some(self)
    }
    fn as_iterable(&self) -> Option<&dyn Iterable> {
        // Reported conditionally: a value with no keys is not a container, and claiming otherwise
        // makes a comprehension over a scalar silently iterate nothing instead of erroring.
        self.0.keys().is_some().then_some(self)
    }
    fn as_container(&self) -> Option<&dyn Container> {
        self.0.keys().is_some().then_some(self)
    }
    fn equals(&self, _: &dyn Val) -> bool {
        false
    }
}

/// The one place a member lookup's error becomes the evaluator's.
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

/// The one place a pending read becomes the evaluator's error. An evaluator that cannot wait
/// treats "not yet" as any other failed read, so `&&`/`||` absorb it exactly as they absorb any
/// other error.
pub(crate) fn pending_error(name: &str, h: DemandHandle) -> ExecutionError {
    ExecutionError::FunctionError {
        function: name.to_string(),
        message: format!("value not yet available (demand {})", h.id()),
    }
}

impl LazyAdapter {
    /// `has(x.name)` / `name in x` over a lazy — an existence question, never the member's value.
    ///
    /// Keys first when the value has them, so a keyed value answers from its keys and resolves no
    /// member; presence (`poll_has`) otherwise, which is what makes `in` work on a keyless value.
    pub(crate) fn presence(&self, name: &str) -> Result<bool, ExecutionError> {
        match self.poll_presence(name)? {
            Presence::Known(b) => Ok(b),
            Presence::Pending(h) => Err(pending_error(name, h)),
        }
    }

    /// [`presence`](LazyAdapter::presence) for an evaluator that can wait: `Pending` is handed
    /// back rather than turned into an error. The same keys-first order, so both answer alike.
    pub(crate) fn poll_presence(&self, name: &str) -> Result<Presence, ExecutionError> {
        if let Some(mut keys) = self.0.keys() {
            return Ok(Presence::Known(keys.any(|k| k.as_str() == name)));
        }
        self.0.poll_has(name).map_err(|e| member_error(name, e))
    }

    /// `x.name` / `x["name"]` for an evaluator that can wait — [`Indexer::get`] without turning
    /// `Pending` into an error.
    pub(crate) fn poll_read(&self, name: &str) -> Result<Access, ExecutionError> {
        self.0.poll_member(name).map_err(|e| member_error(name, e))
    }
}

impl Indexer for LazyAdapter {
    fn get<'a>(&'a self, idx: &dyn Val) -> Result<Cow<'a, dyn Val>, ExecutionError> {
        let name = idx
            .downcast_ref::<CelString>()
            .map(CelString::inner)
            .ok_or(ExecutionError::NoSuchOverload)?;
        match self.poll_read(name)? {
            Access::Ready(v) => Ok(Cow::Owned(v.into_val())),
            Access::Pending(h) => Err(pending_error(name, h)),
        }
    }

    fn steal(self: Box<Self>, idx: &dyn Val) -> Result<Box<dyn Val>, ExecutionError> {
        Ok(self.get(idx)?.into_owned())
    }
}

impl Container for LazyAdapter {
    fn contains(&self, value: &dyn Val) -> Result<bool, ExecutionError> {
        let name = value
            .downcast_ref::<CelString>()
            .map(CelString::inner)
            .ok_or(ExecutionError::NoSuchOverload)?;
        Ok(self
            .0
            .keys()
            .map(|mut ks| ks.any(|k| k.as_str() == name))
            .unwrap_or(false))
    }
}

impl Iterable for LazyAdapter {
    fn iter<'a>(&'a self) -> Box<dyn crate::common::traits::Iterator<'a> + 'a> {
        match self.0.keys() {
            Some(keys) => Box::new(KeyIter { keys }),
            // Unreachable through `as_iterable`, which reports `None` for a value with no keys.
            None => Box::new(KeyIter {
                keys: Box::new(std::iter::empty()),
            }),
        }
    }
}

struct KeyIter<'a> {
    keys: Box<dyn Iterator<Item = &'a CelKey> + 'a>,
}

impl<'a> crate::common::traits::Iterator<'a> for KeyIter<'a> {
    fn next(&mut self) -> Option<&'a dyn Val> {
        // BORROWED, straight out of the implementor's own storage — a comprehension over a wide
        // root allocates nothing per key.
        self.keys.next().map(|k| &k.0 as &dyn Val)
    }
}
