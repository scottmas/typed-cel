//! The fast backend's values: unboxed scalars in registers, composites borrowed.
//!
//! A [`Reg`] holds a scalar by value and a string, a byte string or a composite by REFERENCE — into
//! the host's data, into the program's constant pool, or into the run's [`Store`] for a value the
//! program built. There is no `Arc` and no per-read allocation: a read of a string field is a
//! `&str` copied into a register.
//!
//! Every function here mirrors one trait method of the absorbed value model (`common::types`) —
//! the same comparison, the same error constructor — because the evaluator is the specification
//! the backend is held to, error text included.

use std::sync::Arc;

use crate::common::types::map::{AsKeyRef, KeyRef};
use crate::common::types::{
    CelBool, CelBytes, CelDouble, CelDuration, CelList, CelMap, CelMapKey, CelNull, CelString,
};
use crate::common::value::Val;
use crate::lazy::{pending_error, Access, LazyAdapter};
use crate::objects::{integral_key, Key, Map, Value};
use crate::ExecutionError;

/// One register.
///
/// The `bool` on a composite is whether the evaluator would hold that value OWNED at this point
/// (`Cow::Owned`) rather than borrowed. It is observable in exactly one place: indexing a map with
/// a key that is no key (a fractional number) is `NoSuchKey` on a borrowed map (`Indexer::get`)
/// and `UnsupportedKeyType` on an owned one (`Indexer::steal`).
#[derive(Clone, Copy, Debug)]
pub(crate) enum Reg<'a> {
    Unset,
    Bool(bool),
    Num(f64),
    Null,
    Dur(chrono::Duration),
    Str(&'a str),
    Bytes(&'a [u8]),
    /// A value of the absorbed model: a host or constant list or map, a lazy view, an opaque.
    Dyn(&'a dyn Val, bool),
    /// A list the program built.
    List(&'a [Reg<'a>], bool),
    /// A map the program built: keys are `Str`, integral `Num` or `Bool`, each at most once.
    Map(&'a [(Reg<'a>, Reg<'a>)], bool),
    /// A caught error, by index into the run's error list.
    Err(u32),
}

impl<'a> Reg<'a> {
    /// The same value, as the evaluator holds a variable it reads back: borrowed.
    #[inline]
    pub(crate) fn borrowed(self) -> Reg<'a> {
        match self {
            Reg::Dyn(v, _) => Reg::Dyn(v, false),
            Reg::List(l, _) => Reg::List(l, false),
            Reg::Map(m, _) => Reg::Map(m, false),
            other => other,
        }
    }

    pub(crate) fn owned(self) -> Reg<'a> {
        match self {
            Reg::Dyn(v, _) => Reg::Dyn(v, true),
            Reg::List(l, _) => Reg::List(l, true),
            Reg::Map(m, _) => Reg::Map(m, true),
            other => other,
        }
    }
}

/// What a run builds and hands out references into: strings, lists, maps, and values of the
/// absorbed model a lazy read produced. Append-only for the life of one run; held only to be
/// dropped when the run ends.
#[allow(dead_code)]
pub(crate) enum Keep<'a> {
    Val(Box<dyn Val>),
    Str(Box<str>),
    Bytes(Box<[u8]>),
    Regs(Box<[Reg<'a>]>),
    Pairs(Box<[(Reg<'a>, Reg<'a>)]>),
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

    // SAFETY (all five): each value is moved into its own heap allocation (a `Box`), and the
    // reference handed out points into that allocation, which does not move when `items`
    // reallocates. `items` is only ever cleared by the run that owns this store, after its last
    // use of any reference it handed out (`fast::run`); no reference escapes a run, because
    // a run returns only owned values. A PAUSED run keeps its store, and the references into it,
    // together (`fast::Paused`).
    pub(crate) fn val(&mut self, v: Box<dyn Val>) -> &'a dyn Val {
        let p: *const dyn Val = &*v;
        self.items.push(Keep::Val(v));
        unsafe { &*p }
    }

    pub(crate) fn str(&mut self, s: String) -> &'a str {
        let b = s.into_boxed_str();
        let p: *const str = &*b;
        self.items.push(Keep::Str(b));
        unsafe { &*p }
    }

    pub(crate) fn bytes(&mut self, b: Vec<u8>) -> &'a [u8] {
        let b = b.into_boxed_slice();
        let p: *const [u8] = &*b;
        self.items.push(Keep::Bytes(b));
        unsafe { &*p }
    }

    pub(crate) fn regs(&mut self, r: Vec<Reg<'a>>) -> &'a [Reg<'a>] {
        let b = r.into_boxed_slice();
        let p: *const [Reg<'a>] = &*b;
        self.items.push(Keep::Regs(b));
        unsafe { &*p }
    }

    pub(crate) fn pairs(&mut self, r: Vec<(Reg<'a>, Reg<'a>)>) -> &'a [(Reg<'a>, Reg<'a>)] {
        let b = r.into_boxed_slice();
        let p: *const [(Reg<'a>, Reg<'a>)] = &*b;
        self.items.push(Keep::Pairs(b));
        unsafe { &*p }
    }
}

/// A value of the absorbed model, as a register. Scalars are unboxed; everything else stays a
/// reference.
pub(crate) fn of_val(v: &dyn Val, owned: bool) -> Reg<'_> {
    if let Some(b) = v.downcast_ref::<CelBool>() {
        Reg::Bool(*b.inner())
    } else if let Some(n) = v.downcast_ref::<CelDouble>() {
        Reg::Num(*n.inner())
    } else if let Some(s) = v.downcast_ref::<CelString>() {
        Reg::Str(s.inner())
    } else if let Some(b) = v.downcast_ref::<CelBytes>() {
        Reg::Bytes(b.inner())
    } else if v.downcast_ref::<CelNull>().is_some() {
        Reg::Null
    } else if let Some(d) = v.downcast_ref::<CelDuration>() {
        Reg::Dur(*d.inner())
    } else {
        Reg::Dyn(v, owned)
    }
}

/// A `Cow` the absorbed model produced, as a register; an owned one is kept in the store.
pub(crate) fn of_cow<'a>(
    v: std::borrow::Cow<'a, dyn Val>,
    owned: bool,
    st: &mut Store<'a>,
) -> Reg<'a> {
    match v {
        std::borrow::Cow::Borrowed(v) => of_val(v, owned),
        std::borrow::Cow::Owned(b) => {
            // A scalar needs no keeping unless it borrows (a string, bytes).
            if let Some(n) = b.downcast_ref::<CelDouble>() {
                return Reg::Num(*n.inner());
            }
            if let Some(x) = b.downcast_ref::<CelBool>() {
                return Reg::Bool(*x.inner());
            }
            of_val(st.val(b), true)
        }
    }
}

/// The boundary value, exactly as `Value::resolve` would convert the same value.
pub(crate) fn to_value(r: Reg<'_>, errs: &[ExecutionError]) -> Result<Value, ExecutionError> {
    Ok(match r {
        Reg::Unset => Value::Null,
        Reg::Bool(b) => Value::Bool(b),
        Reg::Num(n) => Value::Float(n),
        Reg::Null => Value::Null,
        Reg::Dur(d) => Value::Duration(d),
        Reg::Str(s) => Value::String(Arc::new(s.to_string())),
        Reg::Bytes(b) => Value::Bytes(Arc::new(b.to_vec())),
        Reg::Dyn(v, _) => Value::try_from(v)?,
        Reg::List(items, _) => Value::List(Arc::new(
            items
                .iter()
                .map(|r| to_value(*r, errs))
                .collect::<Result<_, _>>()?,
        )),
        Reg::Map(pairs, _) => {
            let mut m = std::collections::HashMap::with_capacity(pairs.len());
            for (k, v) in pairs {
                let key = match k {
                    Reg::Str(s) => Key::String(Arc::new(s.to_string())),
                    Reg::Num(n) => Key::Num(*n as i64),
                    Reg::Bool(b) => Key::Bool(*b),
                    _ => return Err(ExecutionError::InternalError("a map key".into())),
                };
                m.insert(key, to_value(*v, errs)?);
            }
            Value::Map(Map { map: Arc::new(m) })
        }
        Reg::Err(i) => return Err(errs[i as usize].clone()),
    })
}

/// A register as a value of the absorbed model, for the rare path that hands one to it.
pub(crate) fn to_val(r: Reg<'_>, errs: &[ExecutionError]) -> Result<Box<dyn Val>, ExecutionError> {
    Box::<dyn Val>::try_from(to_value(r, errs)?)
}

// ---- lists and maps, whichever side built them ----

/// A list's length and elements, over a list the program built or one of the absorbed model's.
pub(crate) enum ListView<'a> {
    Regs(&'a [Reg<'a>]),
    Vals(&'a [Box<dyn Val>]),
}

impl<'a> ListView<'a> {
    pub(crate) fn of(r: Reg<'a>) -> Option<ListView<'a>> {
        match r {
            Reg::List(l, _) => Some(ListView::Regs(l)),
            Reg::Dyn(v, _) => v
                .downcast_ref::<CelList>()
                .map(|l| ListView::Vals(l.inner())),
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
            ListView::Vals(l) => of_val(l[i].as_ref(), false),
        }
    }
}

/// A map key as the absorbed model's `KeyRef`, or `None` for a value that names no key.
pub(crate) fn key_ref<'k>(k: Reg<'k>) -> Option<KeyRef<'k>> {
    match k {
        Reg::Str(s) => Some(KeyRef::String(s)),
        Reg::Num(n) => integral_key(n).map(KeyRef::Num),
        Reg::Bool(b) => Some(KeyRef::Bool(b)),
        _ => None,
    }
}

fn key_reg(k: &CelMapKey) -> Reg<'_> {
    match k {
        CelMapKey::Bool(b) => Reg::Bool(*b.inner()),
        CelMapKey::Num(n) => Reg::Num(*n.inner()),
        CelMapKey::String(s) => Reg::Str(s.inner()),
    }
}

/// A map, over one the program built or one of the absorbed model's.
pub(crate) enum MapView<'a> {
    Pairs(&'a [(Reg<'a>, Reg<'a>)]),
    Vals(&'a std::collections::HashMap<CelMapKey, Box<dyn Val>>),
}

impl<'a> MapView<'a> {
    pub(crate) fn of(r: Reg<'a>) -> Option<MapView<'a>> {
        match r {
            Reg::Map(m, _) => Some(MapView::Pairs(m)),
            Reg::Dyn(v, _) => v.downcast_ref::<CelMap>().map(|m| MapView::Vals(m.inner())),
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
            MapView::Vals(m) => m
                .get(&k as &dyn AsKeyRef)
                .map(|v| of_val(v.as_ref(), false)),
        }
    }

    /// Every entry, in the map's own iteration order.
    pub(crate) fn for_each(&self, mut f: impl FnMut(Reg<'a>, Reg<'a>) -> bool) -> bool {
        match self {
            MapView::Pairs(m) => m.iter().all(|(k, v)| f(*k, *v)),
            MapView::Vals(m) => m
                .iter()
                .all(|(k, v)| f(key_reg(k), of_val(v.as_ref(), false))),
        }
    }
}

// ---- the operators ----

/// `a.equals(b)`, the absorbed model's equality, for every pair a checked program can compare.
pub(crate) fn equals(a: Reg<'_>, b: Reg<'_>) -> bool {
    match (a, b) {
        (Reg::Num(x), Reg::Num(y)) => x == y,
        (Reg::Bool(x), Reg::Bool(y)) => x == y,
        (Reg::Str(x), Reg::Str(y)) => x == y,
        (Reg::Bytes(x), Reg::Bytes(y)) => x == y,
        (Reg::Null, Reg::Null) => true,
        (Reg::Dur(x), Reg::Dur(y)) => x == y,
        (
            Reg::List(..) | Reg::Dyn(..) | Reg::Map(..),
            Reg::List(..) | Reg::Dyn(..) | Reg::Map(..),
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
            match (a, b) {
                (Reg::Dyn(x, _), Reg::Dyn(y, _)) => x.equals(y),
                _ => false,
            }
        }
        _ => false,
    }
}

/// `in` — `objects.rs`'s `operators::IN` arm: a lazy container first, then any container.
pub(crate) fn contains(needle: Reg<'_>, hay: Reg<'_>) -> Result<bool, ExecutionError> {
    if let Reg::Dyn(v, _) = hay {
        if let Some(lazy) = v.downcast_ref::<LazyAdapter>() {
            let Reg::Str(name) = needle else {
                return Err(ExecutionError::NoSuchOverload);
            };
            return lazy.presence(name);
        }
    }
    if let Some(l) = ListView::of(hay) {
        return Ok((0..l.len()).any(|i| equals(l.get(i), needle)));
    }
    if let Some(m) = MapView::of(hay) {
        return match needle {
            Reg::Str(_) | Reg::Bool(_) => Ok(m.get(key_ref(needle).expect("a key")).is_some()),
            Reg::Num(n) => Ok(integral_key(n).is_some_and(|k| m.get(KeyRef::Num(k)).is_some())),
            // `Container::contains` converts any other key and fails the conversion.
            other => Err(unsupported_key(other)),
        };
    }
    match hay {
        Reg::Dyn(v, _) => match v.as_container() {
            Some(c) => c.contains(to_val(needle, &[])?.as_ref()),
            None => Err(ExecutionError::NoSuchOverload),
        },
        _ => Err(ExecutionError::NoSuchOverload),
    }
}

/// The error a value that is no map key converts to.
pub(crate) fn unsupported_key(k: Reg<'_>) -> ExecutionError {
    ExecutionError::UnsupportedKeyType(to_value(k, &[]).unwrap_or(Value::Null))
}

/// `x.name` (not a presence test): `objects.rs`'s `Expr::Select` arm.
pub(crate) fn select<'a>(
    obj: Reg<'a>,
    key: &'a CelString,
    st: &mut Store<'a>,
) -> Result<Reg<'a>, ExecutionError> {
    match obj {
        Reg::Map(m, _) => MapView::Pairs(m)
            .get(KeyRef::String(key.inner()))
            .map(Reg::owned)
            .ok_or_else(|| ExecutionError::no_such_key(key.inner())),
        Reg::Dyn(v, _) => {
            let is_map = v.downcast_ref::<CelMap>().is_some();
            let got = match v.as_indexer() {
                Some(ix) => ix.get(key)?,
                None if is_map => return Err(ExecutionError::no_such_key(key.inner())),
                None => return Err(ExecutionError::NoSuchOverload),
            };
            Ok(of_cow(got, true, st).owned())
        }
        _ => Err(ExecutionError::NoSuchOverload),
    }
}

/// `has(x.name)`: `objects.rs`'s `Expr::Select` arm with `test` set.
pub(crate) fn has(obj: Reg<'_>, key: &CelString) -> Result<bool, ExecutionError> {
    // The fork's non-map arm reads the member through the indexer: a list's indexer refuses a
    // string index, and the checker admits `has(list.f)`.
    if ListView::of(obj).is_some() {
        return Err(ExecutionError::UnexpectedType {
            got: "string".into(),
            want: "double".into(),
        });
    }
    match obj {
        Reg::Map(m, _) => Ok(MapView::Pairs(m).get(KeyRef::String(key.inner())).is_some()),
        Reg::Dyn(v, _) => {
            if let Some(lazy) = v.downcast_ref::<LazyAdapter>() {
                return lazy.presence(key.inner());
            }
            if let Some(m) = v.downcast_ref::<CelMap>() {
                return Ok(m.inner().contains_key(key as &dyn AsKeyRef));
            }
            // The fork's non-map arm returns the member itself; a checked program never gets here.
            Err(ExecutionError::NoSuchOverload)
        }
        _ => Err(ExecutionError::NoSuchOverload),
    }
}

/// `a[b]`: `objects.rs`'s `operators::INDEX` arm — `Indexer::get` on a borrowed container,
/// `Indexer::steal` on an owned one.
pub(crate) fn index<'a>(
    a: Reg<'a>,
    b: Reg<'a>,
    st: &mut Store<'a>,
    errs: &[ExecutionError],
) -> Result<Reg<'a>, ExecutionError> {
    if let Some(l) = ListView::of(a) {
        let owned = matches!(a, Reg::List(_, true) | Reg::Dyn(_, true));
        let Reg::Num(f) = b else {
            return Err(match b {
                Reg::Str(_) => ExecutionError::UnexpectedType {
                    got: "string".into(),
                    want: "double".into(),
                },
                _ => ExecutionError::NoSuchOverload,
            });
        };
        return if f.fract() == 0.0 && f >= 0.0 && f < l.len() as f64 {
            let r = l.get(f as usize);
            Ok(if owned { r.owned() } else { r })
        } else {
            Err(ExecutionError::IndexOutOfBounds(f.into()))
        };
    }
    if let Some(m) = MapView::of(a) {
        let owned = matches!(a, Reg::Map(_, true) | Reg::Dyn(_, true));
        let name = |k: Reg<'_>| match k {
            Reg::Str(s) => s.to_string(),
            Reg::Num(n) => n.to_string(),
            Reg::Bool(b) => b.to_string(),
            _ => String::new(),
        };
        let key = match b {
            Reg::Str(_) | Reg::Bool(_) => key_ref(b).expect("a key"),
            Reg::Num(n) => match integral_key(n) {
                Some(k) => KeyRef::Num(k),
                // `get` reports the number it could not find; `steal` fails converting it.
                None if owned => return Err(unsupported_key(b)),
                None => return Err(ExecutionError::NoSuchKey(Arc::new(n.to_string()))),
            },
            _ if owned => return Err(unsupported_key(b)),
            _ => return Err(ExecutionError::NoSuchOverload),
        };
        return match m.get(key) {
            Some(r) => Ok(if owned { r.owned() } else { r }),
            None => Err(ExecutionError::NoSuchKey(Arc::new(name(b)))),
        };
    }
    match a {
        Reg::Dyn(v, owned) => {
            if let Some(lazy) = v.downcast_ref::<LazyAdapter>() {
                let Reg::Str(name) = b else {
                    return Err(ExecutionError::NoSuchOverload);
                };
                return match lazy.poll_read(name)? {
                    Access::Ready(v) => Ok(of_val(st.val(v.into_val()), true)),
                    Access::Pending(h) => Err(pending_error(name, h)),
                };
            }
            let idx = to_val(b, errs)?;
            if owned {
                let got = v
                    .clone_as_boxed()
                    .into_indexer()
                    .ok_or(ExecutionError::NoSuchOverload)?
                    .steal(idx.as_ref())?;
                Ok(of_val(st.val(got), true))
            } else {
                let got = v
                    .as_indexer()
                    .ok_or(ExecutionError::NoSuchOverload)?
                    .get(idx.as_ref())?;
                Ok(of_cow(got, false, st))
            }
        }
        _ => Err(ExecutionError::NoSuchOverload),
    }
}

/// The size of a list or map.
pub(crate) fn size(a: Reg<'_>) -> Result<f64, ExecutionError> {
    if let Some(l) = ListView::of(a) {
        return Ok(l.len() as f64);
    }
    if let Some(m) = MapView::of(a) {
        return Ok(m.len() as f64);
    }
    match a {
        Reg::Dyn(v, _) => match v.as_sizer() {
            Some(s) => Ok(*s.size().inner()),
            None => Err(ExecutionError::NoSuchOverload),
        },
        _ => Err(ExecutionError::NoSuchOverload),
    }
}

/// A map literal's key, converted before its value runs: `TryFrom<Box<dyn Val>> for CelMapKey`.
pub(crate) fn check_key(k: Reg<'_>) -> Result<(), ExecutionError> {
    match k {
        Reg::Str(_) | Reg::Bool(_) => Ok(()),
        Reg::Num(n) if integral_key(n).is_some() => Ok(()),
        other => Err(unsupported_key(other)),
    }
}

/// The ordering behind `<`, `<=`, `>`, `>=`: `Comparer::compare`. Numbers, strings and durations,
/// and nothing else (`removed: ordering beyond numbers and strings`).
pub(crate) fn compare(a: Reg<'_>, b: Reg<'_>) -> Result<std::cmp::Ordering, ExecutionError> {
    match (a, b) {
        (Reg::Num(x), Reg::Num(y)) => x.partial_cmp(&y).ok_or(ExecutionError::NoSuchOverload),
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
pub(crate) fn map_key(k: &Value) -> Option<CelMapKey> {
    match k {
        Value::String(s) => Some(CelMapKey::String(CelString::from(s.as_str()))),
        Value::Float(f) => integral_key(*f).map(|_| CelMapKey::Num(CelDouble::from(*f))),
        Value::Bool(b) => Some(CelMapKey::Bool(CelBool::from(*b))),
        _ => None,
    }
}
