//! The fast backend's values: unboxed scalars in registers, composites borrowed.
//!
//! A [`Reg`] holds a scalar by value and a string, a byte string or a composite by REFERENCE — into
//! the host's data, into the program's constant pool, or into the run's [`Store`] for a value the
//! program built. There is no `Arc` and no per-read allocation: a read of a string field is a
//! `&str` copied into a register.
//!
//! Every function here states one rule of the dialect — a comparison, an index, a key — and the
//! error each failure is. The error TEXT is part of the contract (callers render it);
//! `tests/backend_edges.rs` and `tests/generated_golden.rs` pin it.

use std::sync::Arc;

use crate::lazy::{self, LazyValue};
use crate::num::CelNum;
use crate::value::integral_key;
use crate::ExecutionError;
use crate::{CelKey, CelMap, CelMapKey, CelValue};

/// One register.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Reg<'a> {
    Unset,
    Bool(bool),
    /// A number held as a double. `Num`, `Int` and `UInt` are three representations of the
    /// dialect's one number type ([`CelNum`]); read any of them with [`Reg::num`].
    Num(f64),
    Int(i64),
    UInt(u64),
    Null,
    Dur(chrono::Duration),
    Str(&'a str),
    Bytes(&'a [u8]),
    /// A composite or a lazy view someone else OWNS: a bound root or one of its members, a
    /// constant, or an owned value the run keeps in its `Store`. Never a scalar: `of_cel` unboxes
    /// those.
    Val(&'a CelValue),
    /// A list the program built.
    List(&'a [Reg<'a>]),
    /// A map the program built: keys are `Str`, integral numbers or `Bool`, each at most once.
    Map(&'a [(Reg<'a>, Reg<'a>)]),
    /// A caught error, by index into the run's error list.
    Err(u32),
}

impl Reg<'_> {
    /// The number this register holds, in whichever representation; `None` for a non-number.
    #[inline(always)]
    pub(crate) fn num(&self) -> Option<CelNum> {
        match *self {
            Reg::Int(i) => Some(CelNum::Int(i)),
            Reg::Num(f) => Some(CelNum::Float(f)),
            Reg::UInt(u) => Some(CelNum::UInt(u)),
            _ => None,
        }
    }
}

impl From<CelNum> for Reg<'_> {
    #[inline(always)]
    fn from(n: CelNum) -> Self {
        match n {
            CelNum::Int(i) => Reg::Int(i),
            CelNum::UInt(u) => Reg::UInt(u),
            CelNum::Float(f) => Reg::Num(f),
        }
    }
}

/// What a run builds and hands out references into: strings, lists, maps, and the values a lazy
/// read or a host function produced. Append-only for the life of one run; held only to be
/// dropped when the run ends.
#[allow(dead_code)]
pub(crate) enum Keep<'a> {
    Owned(Box<CelValue>),
    Str(Box<str>),
    Bytes(Box<[u8]>),
    Regs(Box<[Reg<'a>]>),
    Pairs(Box<[(Reg<'a>, Reg<'a>)]>),
    /// A list a loop built in place (`Append`), kept as the vector it grew in: never pushed to
    /// again once here, so its buffer does not move.
    Built(Vec<Reg<'a>>),
}

/// The run's arena.
#[derive(Default)]
#[repr(transparent)]
pub(crate) struct Store<'a> {
    pub(crate) items: Vec<Keep<'a>>,
}

impl<'a> Store<'a> {
    /// The vector, as the arena it is.
    pub(crate) fn wrap<'v>(items: &'v mut Vec<Keep<'a>>) -> &'v mut Store<'a> {
        // SAFETY: `Store` is `repr(transparent)` over exactly this vector.
        unsafe { &mut *(items as *mut Vec<Keep<'a>> as *mut Store<'a>) }
    }

    // SAFETY (all six): each value is moved into its own heap allocation (a `Box`), and the
    // reference handed out points into that allocation, which does not move when `items`
    // reallocates. `items` is only ever cleared by the run that owns this store, after its last
    // use of any reference it handed out (`fast::run`); no reference escapes a run, because
    // a run returns only owned values. A PAUSED run keeps its store, and the references into it,
    // together (`fast::Paused`).
    pub(crate) fn value(&mut self, v: CelValue) -> &'a CelValue {
        #[cfg(feature = "profile")]
        super::profile::store();
        let b = Box::new(v);
        let p: *const CelValue = &*b;
        self.items.push(Keep::Owned(b));
        unsafe { &*p }
    }

    pub(crate) fn str(&mut self, s: String) -> &'a str {
        #[cfg(feature = "profile")]
        super::profile::store();
        let b = s.into_boxed_str();
        let p: *const str = &*b;
        self.items.push(Keep::Str(b));
        unsafe { &*p }
    }

    pub(crate) fn bytes(&mut self, b: Vec<u8>) -> &'a [u8] {
        #[cfg(feature = "profile")]
        super::profile::store();
        let b = b.into_boxed_slice();
        let p: *const [u8] = &*b;
        self.items.push(Keep::Bytes(b));
        unsafe { &*p }
    }

    pub(crate) fn regs(&mut self, r: Vec<Reg<'a>>) -> &'a [Reg<'a>] {
        #[cfg(feature = "profile")]
        super::profile::store();
        let b = r.into_boxed_slice();
        let p: *const [Reg<'a>] = &*b;
        self.items.push(Keep::Regs(b));
        unsafe { &*p }
    }

    /// A loop's built list, kept without a copy or a shrink.
    pub(crate) fn built(&mut self, r: Vec<Reg<'a>>) -> &'a [Reg<'a>] {
        #[cfg(feature = "profile")]
        super::profile::store();
        let p: *const [Reg<'a>] = r.as_slice();
        self.items.push(Keep::Built(r));
        unsafe { &*p }
    }

    pub(crate) fn pairs(&mut self, r: Vec<(Reg<'a>, Reg<'a>)>) -> &'a [(Reg<'a>, Reg<'a>)] {
        #[cfg(feature = "profile")]
        super::profile::store();
        let b = r.into_boxed_slice();
        let p: *const [(Reg<'a>, Reg<'a>)] = &*b;
        self.items.push(Keep::Pairs(b));
        unsafe { &*p }
    }
}

/// A borrowed value as a register: scalars unboxed, composites and lazy views by reference.
pub(crate) fn of_cel(v: &CelValue) -> Reg<'_> {
    match v {
        CelValue::Bool(b) => Reg::Bool(*b),
        CelValue::Num(n) => Reg::Num(*n),
        CelValue::Int(i) => Reg::Int(*i),
        CelValue::UInt(u) => Reg::UInt(*u),
        CelValue::Str(s) => Reg::Str(s),
        CelValue::Bytes(b) => Reg::Bytes(b),
        CelValue::Duration(d) => Reg::Dur(d.delta()),
        CelValue::Null => Reg::Null,
        CelValue::List(_) | CelValue::Map(_) | CelValue::Lazy(_) => Reg::Val(v),
    }
}

/// A value the run produced (a lazy member, a host's result), as a register; a composite is kept
/// in the store.
pub(crate) fn of_owned<'a>(v: CelValue, st: &mut Store<'a>) -> Reg<'a> {
    match v {
        CelValue::Bool(b) => Reg::Bool(b),
        CelValue::Num(n) => Reg::Num(n),
        CelValue::Int(i) => Reg::Int(i),
        CelValue::UInt(u) => Reg::UInt(u),
        CelValue::Null => Reg::Null,
        CelValue::Duration(d) => Reg::Dur(d.delta()),
        other => of_cel(st.value(other)),
    }
}

/// The value a register holds.
pub(crate) fn to_cel(r: Reg<'_>, errs: &[ExecutionError]) -> Result<CelValue, ExecutionError> {
    Ok(match r {
        Reg::Unset => CelValue::Null,
        Reg::Bool(b) => CelValue::Bool(b),
        Reg::Num(n) => CelValue::Num(n),
        Reg::Int(i) => CelValue::Int(i),
        Reg::UInt(u) => CelValue::UInt(u),
        Reg::Null => CelValue::Null,
        Reg::Dur(d) => CelValue::Duration(crate::CelDuration::of(d)),
        Reg::Str(s) => CelValue::Str(s.into()),
        Reg::Bytes(b) => CelValue::Bytes(b.into()),
        Reg::Val(v) => v.clone(),
        Reg::List(items) => CelValue::List(
            items
                .iter()
                .map(|r| to_cel(*r, errs))
                .collect::<Result<_, _>>()?,
        ),
        Reg::Map(pairs) => {
            let mut m = Vec::with_capacity(pairs.len());
            for (k, v) in pairs {
                let key = match k {
                    Reg::Str(s) => CelMapKey::Str(CelKey::new(s)),
                    Reg::Bool(b) => CelMapKey::Bool(*b),
                    // `check_key` admitted only an integral number in `i64` range.
                    k => match k.num().and_then(integral_key) {
                        Some(n) => CelMapKey::Num(n),
                        None => return Err(unsupported_key(*k)),
                    },
                };
                m.push((key, to_cel(*v, errs)?));
            }
            CelValue::Map(CelMap::new(m))
        }
        Reg::Err(i) => return Err(errs[i as usize].clone()),
    })
}

// ---- lists and maps, whichever side built them ----

/// A list's length and elements, over a list the program built or a bound one.
pub(crate) enum ListView<'a> {
    Regs(&'a [Reg<'a>]),
    Vals(&'a [CelValue]),
}

impl<'a> ListView<'a> {
    pub(crate) fn of(r: Reg<'a>) -> Option<ListView<'a>> {
        match r {
            Reg::List(l) => Some(ListView::Regs(l)),
            Reg::Val(CelValue::List(l)) => Some(ListView::Vals(l)),
            _ => None,
        }
    }

    pub(crate) fn len(&self) -> usize {
        match self {
            ListView::Regs(l) => l.len(),
            ListView::Vals(l) => l.len(),
        }
    }

    pub(crate) fn get(&self, i: usize) -> Reg<'a> {
        match self {
            ListView::Regs(l) => l[i],
            ListView::Vals(l) => of_cel(&l[i]),
        }
    }
}

/// A map key, borrowed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum KeyRef<'k> {
    Num(i64),
    Bool(bool),
    Str(&'k str),
}

/// A register as a map key, or `None` for a value that names no key.
pub(crate) fn key_ref(k: Reg<'_>) -> Option<KeyRef<'_>> {
    match k {
        Reg::Str(s) => Some(KeyRef::Str(s)),
        Reg::Bool(b) => Some(KeyRef::Bool(b)),
        k => k.num().and_then(integral_key).map(KeyRef::Num),
    }
}

/// A map key as the register a comprehension over the map binds.
pub(crate) fn key_reg(k: &CelMapKey) -> Reg<'_> {
    match k {
        CelMapKey::Bool(b) => Reg::Bool(*b),
        CelMapKey::Num(n) => Reg::Int(*n),
        CelMapKey::Str(s) => Reg::Str(s.as_str()),
    }
}

/// A map, over one the program built or a bound one.
pub(crate) enum MapView<'a> {
    Pairs(&'a [(Reg<'a>, Reg<'a>)]),
    Vals(&'a CelMap),
}

impl<'a> MapView<'a> {
    pub(crate) fn of(r: Reg<'a>) -> Option<MapView<'a>> {
        match r {
            Reg::Map(m) => Some(MapView::Pairs(m)),
            Reg::Val(CelValue::Map(m)) => Some(MapView::Vals(m)),
            _ => None,
        }
    }

    pub(crate) fn len(&self) -> usize {
        match self {
            MapView::Pairs(m) => m.len(),
            MapView::Vals(m) => m.len(),
        }
    }

    pub(crate) fn get(&self, k: KeyRef<'_>) -> Option<Reg<'a>> {
        match self {
            MapView::Pairs(m) => m
                .iter()
                .find(|(key, _)| key_ref(*key) == Some(k))
                .map(|(_, v)| *v),
            MapView::Vals(m) => match k {
                KeyRef::Str(s) => m.get(s),
                KeyRef::Num(n) => m.get_key(&CelMapKey::Num(n)),
                KeyRef::Bool(b) => m.get_key(&CelMapKey::Bool(b)),
            }
            .map(of_cel),
        }
    }

    /// Every entry, in the map's own iteration order.
    pub(crate) fn for_each(&self, mut f: impl FnMut(Reg<'a>, Reg<'a>) -> bool) -> bool {
        match self {
            MapView::Pairs(m) => m.iter().all(|(k, v)| f(*k, *v)),
            MapView::Vals(m) => m.iter().all(|(k, v)| f(key_reg(k), of_cel(v))),
        }
    }
}

/// The lazy view a register holds.
pub(crate) fn lazy_of(r: Reg<'_>) -> Option<&dyn LazyValue> {
    match r {
        Reg::Val(CelValue::Lazy(l)) => Some(l.as_ref()),
        _ => None,
    }
}

// ---- the operators ----

/// `a.equals(b)`, the absorbed model's equality, for every pair a checked program can compare.
pub(crate) fn equals(a: Reg<'_>, b: Reg<'_>) -> bool {
    match (a, b) {
        (Reg::Int(x), Reg::Int(y)) => x == y,
        (Reg::Num(x), Reg::Num(y)) => x == y,
        (
            Reg::Int(..) | Reg::UInt(..) | Reg::Num(..),
            Reg::Int(..) | Reg::UInt(..) | Reg::Num(..),
        ) => a.num().zip(b.num()).is_some_and(|(x, y)| x.eq_exact(y)),
        (Reg::Bool(x), Reg::Bool(y)) => x == y,
        (Reg::Str(x), Reg::Str(y)) => x == y,
        (Reg::Bytes(x), Reg::Bytes(y)) => x == y,
        (Reg::Null, Reg::Null) => true,
        (Reg::Dur(x), Reg::Dur(y)) => x == y,
        (
            Reg::List(..) | Reg::Val(..) | Reg::Map(..),
            Reg::List(..) | Reg::Val(..) | Reg::Map(..),
        ) => {
            if let (Some(x), Some(y)) = (ListView::of(a), ListView::of(b)) {
                return x.len() == y.len() && (0..x.len()).all(|i| equals(x.get(i), y.get(i)));
            }
            if let (Some(x), Some(y)) = (MapView::of(a), MapView::of(b)) {
                return x.len() == y.len()
                    && x.for_each(|k, v| {
                        key_ref(k)
                            .and_then(|k| y.get(k))
                            .is_some_and(|w| equals(v, w))
                    });
            }
            // A lazy view equals nothing, itself included.
            false
        }
        _ => false,
    }
}

/// `in`: a lazy container first, then any container.
pub(crate) fn contains(needle: Reg<'_>, hay: Reg<'_>) -> Result<bool, ExecutionError> {
    if let Some(lazy) = lazy_of(hay) {
        let Reg::Str(name) = needle else {
            return Err(ExecutionError::NoSuchOverload);
        };
        return lazy::presence(lazy, name);
    }
    // A bound list searched for a string or a number: compared where they lie, no register made.
    match (hay, needle) {
        (Reg::Val(CelValue::List(l)), Reg::Str(n)) => {
            return Ok(l.iter().any(|v| match v {
                CelValue::Str(s) => s.as_ref() == n,
                other => equals(of_cel(other), needle),
            }))
        }
        (Reg::Val(CelValue::List(l)), Reg::Int(n)) => {
            return Ok(l.iter().any(|v| match v {
                CelValue::Int(x) => *x == n,
                other => equals(of_cel(other), needle),
            }))
        }
        (Reg::Val(CelValue::List(l)), Reg::Num(..) | Reg::UInt(..)) => {
            let n = needle.num().expect("a number");
            return Ok(l.iter().any(|v| match v.num() {
                Some(x) => x.eq_exact(n),
                None => equals(of_cel(v), needle),
            }));
        }
        _ => {}
    }
    if let Some(l) = ListView::of(hay) {
        return Ok((0..l.len()).any(|i| equals(l.get(i), needle)));
    }
    if let Some(m) = MapView::of(hay) {
        return match needle {
            Reg::Str(_) | Reg::Bool(_) => Ok(m.get(key_ref(needle).expect("a key")).is_some()),
            Reg::Num(_) | Reg::Int(_) | Reg::UInt(_) => {
                Ok(key_ref(needle).is_some_and(|k| m.get(k).is_some()))
            }
            // Any other needle is no key.
            other => Err(unsupported_key(other)),
        };
    }
    Err(ExecutionError::NoSuchOverload)
}

/// The error a value that is no map key converts to.
pub(crate) fn unsupported_key(k: Reg<'_>) -> ExecutionError {
    ExecutionError::UnsupportedKeyType(to_cel(k, &[]).unwrap_or(CelValue::Null))
}

/// `x.name` (not a presence test): a map's missing member is `no such key`, a lazy view answers
/// through `LazyValue`, and a list refuses a string index.
pub(crate) fn select<'a>(
    obj: Reg<'a>,
    key: &'a CelKey,
    st: &mut Store<'a>,
) -> Result<Reg<'a>, ExecutionError> {
    let name = key.as_str();
    match obj {
        Reg::Map(m) => MapView::Pairs(m)
            .get(KeyRef::Str(name))
            .ok_or_else(|| ExecutionError::no_such_key(name)),
        Reg::Val(CelValue::Map(m)) => m
            .get(name)
            .map(of_cel)
            .ok_or_else(|| ExecutionError::no_such_key(name)),
        Reg::Val(CelValue::Lazy(l)) => Ok(of_owned(lazy::read(l.as_ref(), name)?, st)),
        // A bound list's index refuses a string; a list the program built has no member at all.
        Reg::Val(CelValue::List(_)) => Err(string_index()),
        _ => Err(ExecutionError::NoSuchOverload),
    }
}

/// A list indexed by a string.
fn string_index() -> ExecutionError {
    ExecutionError::UnexpectedType {
        got: "string".into(),
        want: "double".into(),
    }
}

/// `has(x.name)`: presence of the member.
pub(crate) fn has(obj: Reg<'_>, key: &CelKey) -> Result<bool, ExecutionError> {
    let name = key.as_str();
    // A list reads the member through its index, and refuses a string one; the checker admits
    // `has(list.f)`.
    if ListView::of(obj).is_some() {
        return Err(string_index());
    }
    match obj {
        Reg::Map(m) => Ok(MapView::Pairs(m).get(KeyRef::Str(name)).is_some()),
        Reg::Val(CelValue::Map(m)) => Ok(m.get(name).is_some()),
        Reg::Val(CelValue::Lazy(l)) => lazy::presence(l.as_ref(), name),
        _ => Err(ExecutionError::NoSuchOverload),
    }
}

/// `a[b]`: a list by an integral in-range number, else `IndexOutOfBounds`; a map by a key of its
/// key type, else `NoSuchKey` — including a number that names no key (`1.5`) — wherever the map
/// lives.
pub(crate) fn index<'a>(
    a: Reg<'a>,
    b: Reg<'a>,
    st: &mut Store<'a>,
) -> Result<Reg<'a>, ExecutionError> {
    if let Some(l) = ListView::of(a) {
        let Some(n) = b.num() else {
            return Err(match b {
                Reg::Str(_) => string_index(),
                _ => ExecutionError::NoSuchOverload,
            });
        };
        return match integral_key(n) {
            Some(i) if i >= 0 && (i as u64) < l.len() as u64 => Ok(l.get(i as usize)),
            _ => Err(ExecutionError::IndexOutOfBounds(n.into())),
        };
    }
    if let Some(m) = MapView::of(a) {
        let name = |k: Reg<'_>| match k {
            Reg::Str(s) => s.to_string(),
            Reg::Bool(b) => b.to_string(),
            k => k.num().map(|n| n.to_string()).unwrap_or_default(),
        };
        let key = match b {
            Reg::Str(_) | Reg::Bool(_) => key_ref(b).expect("a key"),
            Reg::Num(_) | Reg::Int(_) | Reg::UInt(_) => match key_ref(b) {
                Some(k) => k,
                // a number that names no key is not in the map — the one answer, wherever
                // the map lives.
                None => return Err(ExecutionError::NoSuchKey(Arc::new(name(b)))),
            },
            // Unreachable from a checked program (`_[_]` is `(map(K, V), K) -> V`).
            _ => return Err(ExecutionError::NoSuchOverload),
        };
        return match m.get(key) {
            Some(r) => Ok(r),
            None => Err(ExecutionError::NoSuchKey(Arc::new(name(b)))),
        };
    }
    match (lazy_of(a), b) {
        (Some(lazy), Reg::Str(name)) => Ok(of_owned(lazy::read(lazy, name)?, st)),
        _ => Err(ExecutionError::NoSuchOverload),
    }
}

/// The size of a list or map.
pub(crate) fn size(a: Reg<'_>) -> Result<CelNum, ExecutionError> {
    if let Some(l) = ListView::of(a) {
        return Ok(CelNum::Int(l.len() as i64));
    }
    if let Some(m) = MapView::of(a) {
        return Ok(CelNum::Int(m.len() as i64));
    }
    // A lazy view has no size.
    Err(ExecutionError::NoSuchOverload)
}

/// A map literal's key, checked before its value runs.
pub(crate) fn check_key(k: Reg<'_>) -> Result<(), ExecutionError> {
    match k {
        Reg::Str(_) | Reg::Bool(_) => Ok(()),
        k if k.num().and_then(integral_key).is_some() => Ok(()),
        other => Err(unsupported_key(other)),
    }
}

/// The ordering behind `<`, `<=`, `>`, `>=`. Numbers, strings and durations,
/// and nothing else (`removed: ordering beyond numbers and strings`).
pub(crate) fn compare(a: Reg<'_>, b: Reg<'_>) -> Result<std::cmp::Ordering, ExecutionError> {
    match (a, b) {
        (Reg::Int(x), Reg::Int(y)) => Ok(x.cmp(&y)),
        (Reg::Num(x), Reg::Num(y)) => x.partial_cmp(&y).ok_or(ExecutionError::NoSuchOverload),
        (
            Reg::Int(..) | Reg::UInt(..) | Reg::Num(..),
            Reg::Int(..) | Reg::UInt(..) | Reg::Num(..),
        ) => a
            .num()
            .zip(b.num())
            .and_then(|(x, y)| x.cmp_exact(y))
            .ok_or(ExecutionError::NoSuchOverload),
        (Reg::Str(x), Reg::Str(y)) => Ok(x.cmp(y)),
        (Reg::Dur(x), Reg::Dur(y)) => Ok(x.cmp(&y)),
        _ => Err(ExecutionError::NoSuchOverload),
    }
}

/// The elements of a list, whichever side built it, into a fresh vector.
pub(crate) fn elements<'a>(r: Reg<'a>) -> Option<Vec<Reg<'a>>> {
    let l = ListView::of(r)?;
    Some((0..l.len()).map(|i| l.get(i)).collect())
}

/// `CelMapKey` for a key the program built, to build a constant map at compile time.
pub(crate) fn map_key(k: &CelValue) -> Option<CelMapKey> {
    match k {
        CelValue::Str(s) => Some(CelMapKey::Str(CelKey::new(s))),
        CelValue::Bool(b) => Some(CelMapKey::Bool(*b)),
        k => k.num().and_then(integral_key).map(CelMapKey::Num),
    }
}
