//! The one value. What a caller binds, what a lazy value or a host function returns, what a
//! program's result is, and what a constant holds.

use std::fmt;
use std::sync::Arc;

use crate::lazy::{CelKey, LazyValue};

/// A CEL value. Cheap to clone: every composite and every string is shared.
#[derive(Clone)]
pub enum CelValue {
    Bool(bool),
    /// The dialect's one number kind.
    Num(f64),
    Str(Arc<str>),
    Duration(CelDuration),
    /// A byte string, which need not be UTF-8.
    Bytes(Arc<[u8]>),
    List(Arc<[CelValue]>),
    /// A record or a map: `body.user_id` and `m["k"]` both read one of these.
    Map(CelMap),
    Null,
    /// Served on access ([`LazyValue`]).
    Lazy(Arc<dyn LazyValue>),
}

/// A span of time, at the precision `duration()` parses (nanoseconds). Opaque so a caller never
/// names the parser's crate; a unit is always explicit at the call site.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CelDuration(chrono::TimeDelta);

impl CelDuration {
    pub fn from_millis(ms: i64) -> CelDuration {
        CelDuration(chrono::TimeDelta::milliseconds(ms))
    }

    pub fn from_nanos(ns: i64) -> CelDuration {
        CelDuration(chrono::TimeDelta::nanoseconds(ns))
    }

    pub fn as_millis(self) -> i64 {
        self.0.num_milliseconds()
    }

    /// `None` past ±292 years, which `i64` nanoseconds cannot hold.
    pub fn as_nanos(self) -> Option<i64> {
        self.0.num_nanoseconds()
    }

    pub(crate) fn delta(self) -> chrono::TimeDelta {
        self.0
    }

    pub(crate) fn of(d: chrono::TimeDelta) -> CelDuration {
        CelDuration(d)
    }
}

impl fmt::Debug for CelDuration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// A map key. A string is a [`CelKey`] so a [`LazyValue`]'s keys and a map's keys are the same
/// thing, handed out by reference. A number key is integral: `1` and `1.0` are one key, and a
/// number that is not integral names no key.
///
/// Ordered `Num < Bool < Str`, so every string key sits at the end of a [`CelMap`].
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CelMapKey {
    Num(i64),
    Bool(bool),
    Str(CelKey),
}

impl fmt::Debug for CelMapKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CelMapKey::Num(n) => write!(f, "Num({n:?})"),
            CelMapKey::Bool(b) => write!(f, "Bool({b:?})"),
            CelMapKey::Str(k) => write!(f, "String({:?})", k.as_str()),
        }
    }
}

impl CelMapKey {
    /// The key as the value a comprehension over the map binds.
    pub(crate) fn to_value(&self) -> CelValue {
        match self {
            CelMapKey::Num(n) => CelValue::Num(*n as f64),
            CelMapKey::Bool(b) => CelValue::Bool(*b),
            CelMapKey::Str(k) => CelValue::Str(k.as_str().into()),
        }
    }
}

/// Entries sorted by key, each key once. Lookup is a binary search; iteration is in key order,
/// which makes a comprehension over a map deterministic.
#[derive(Clone)]
pub struct CelMap(Arc<[(CelMapKey, CelValue)]>);

impl CelMap {
    /// From entries in any order; a LATER duplicate key wins (a map literal's rule).
    pub fn new(entries: impl IntoIterator<Item = (CelMapKey, CelValue)>) -> CelMap {
        let mut v: Vec<(CelMapKey, CelValue)> = entries.into_iter().collect();
        // A stable sort keeps equal keys in their order, so the last of each run is the latest.
        v.sort_by(|a, b| a.0.cmp(&b.0));
        let mut out: Vec<(CelMapKey, CelValue)> = Vec::with_capacity(v.len());
        for e in v {
            match out.last_mut() {
                Some(last) if last.0 == e.0 => *last = e,
                _ => out.push(e),
            }
        }
        CelMap(out.into())
    }

    /// The value under the string key `key`.
    pub fn get(&self, key: &str) -> Option<&CelValue> {
        let strs = self
            .0
            .partition_point(|(k, _)| !matches!(k, CelMapKey::Str(_)));
        let band = &self.0[strs..];
        band.binary_search_by(|(k, _)| match k {
            CelMapKey::Str(s) => s.as_str().cmp(key),
            _ => std::cmp::Ordering::Less,
        })
        .ok()
        .map(|i| &band[i].1)
    }

    pub(crate) fn get_key(&self, key: &CelMapKey) -> Option<&CelValue> {
        self.0
            .binary_search_by(|(k, _)| k.cmp(key))
            .ok()
            .map(|i| &self.0[i].1)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&CelMapKey, &CelValue)> {
        self.0.iter().map(|(k, v)| (k, v))
    }

    pub(crate) fn entries(&self) -> &[(CelMapKey, CelValue)] {
        &self.0
    }
}

impl CelValue {
    /// A record from string-keyed fields.
    pub fn record(fields: impl IntoIterator<Item = (CelKey, CelValue)>) -> CelValue {
        CelValue::Map(CelMap::new(
            fields.into_iter().map(|(k, v)| (CelMapKey::Str(k), v)),
        ))
    }

    pub fn list(items: impl IntoIterator<Item = CelValue>) -> CelValue {
        CelValue::List(items.into_iter().collect())
    }
}

impl From<bool> for CelValue {
    fn from(b: bool) -> CelValue {
        CelValue::Bool(b)
    }
}

impl From<f64> for CelValue {
    fn from(n: f64) -> CelValue {
        CelValue::Num(n)
    }
}

impl From<&str> for CelValue {
    fn from(s: &str) -> CelValue {
        CelValue::Str(s.into())
    }
}

impl From<String> for CelValue {
    fn from(s: String) -> CelValue {
        CelValue::Str(s.into())
    }
}

/// The key an integral double names; `None` for a double that names no key.
pub(crate) fn integral_key(f: f64) -> Option<i64> {
    (f.fract() == 0.0 && f >= i64::MIN as f64 && f < i64::MAX as f64).then_some(f as i64)
}

/// `Debug` is part of the error contract: error messages embed values with `{:?}`
/// (`Index out of bounds: Float(5.0)`), and `tests/generated_golden.rs` and
/// `tests/backend_edges.rs` pin that text.
impl fmt::Debug for CelValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CelValue::Bool(b) => write!(f, "Bool({b:?})"),
            CelValue::Num(n) => write!(f, "Float({n:?})"),
            CelValue::Str(s) => write!(f, "String({:?})", &**s),
            CelValue::Duration(d) => write!(f, "Duration({d:?})"),
            CelValue::Bytes(b) => write!(f, "Bytes({:?})", &**b),
            CelValue::List(l) => write!(f, "List({:?})", &**l),
            CelValue::Map(m) => {
                f.write_str("Map(Map { map: {")?;
                for (i, (k, v)) in m.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{k:?}: {v:?}")?;
                }
                f.write_str("} })")
            }
            CelValue::Null => f.write_str("Null"),
            CelValue::Lazy(v) => write!(f, "Lazy({v:?})"),
        }
    }
}

/// Structural equality: a `NaN` is not equal to itself, and a lazy view equals only itself.
impl PartialEq for CelValue {
    fn eq(&self, other: &CelValue) -> bool {
        match (self, other) {
            (CelValue::Bool(a), CelValue::Bool(b)) => a == b,
            (CelValue::Num(a), CelValue::Num(b)) => a == b,
            (CelValue::Str(a), CelValue::Str(b)) => a == b,
            (CelValue::Duration(a), CelValue::Duration(b)) => a == b,
            (CelValue::Bytes(a), CelValue::Bytes(b)) => a == b,
            (CelValue::List(a), CelValue::List(b)) => a == b,
            (CelValue::Map(a), CelValue::Map(b)) => a.entries() == b.entries(),
            (CelValue::Null, CelValue::Null) => true,
            (CelValue::Lazy(a), CelValue::Lazy(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }
}
