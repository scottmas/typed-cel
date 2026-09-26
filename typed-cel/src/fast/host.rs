//! Where a run's roots come from: a [`Facts`] implementation reading the caller's own data by
//! field, or the values a [`CelActivation`] bound.
//!
//! [`CelActivation`]: crate::CelActivation

use std::sync::Arc;

use crate::bindings::Bindings;
use crate::lazy::{self, member_error, pending_error, Access, DemandHandle, Presence};
use crate::{CelKey, CelValue, ExecutionError};

use super::reg::{of_cel, Reg, Store};

/// A field path a program reads, by index into [`FastProgram::fields`](super::FastProgram::fields).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FieldId(pub(crate) u32);

impl FieldId {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// The id of `fields()[i]`. For harnesses that resolve a program's fields themselves.
    #[doc(hidden)]
    pub fn from_index(i: usize) -> FieldId {
        FieldId(i as u32)
    }
}

/// One step of a field path: `.name`, or `["name"]` — the same member either way.
#[derive(Clone, Debug)]
pub(crate) struct Step {
    pub(crate) name: CelKey,
}

/// A root and the members below it: `req.path_text` is root `req`, segments `["path_text"]`.
#[derive(Clone, Debug)]
pub struct FieldPath {
    pub(crate) root: String,
    pub(crate) steps: Vec<Step>,
}

impl FieldPath {
    pub fn root(&self) -> &str {
        &self.root
    }

    pub fn segments(&self) -> impl Iterator<Item = &str> {
        self.steps.iter().map(|s| s.name.as_str())
    }

    /// Does this path spell `root.a.b` for `names == [root, a, b]`?
    pub fn is(&self, names: &[&str]) -> bool {
        names.first() == Some(&self.root.as_str())
            && names.len() == self.steps.len() + 1
            && self
                .steps
                .iter()
                .zip(&names[1..])
                .all(|(s, n)| s.name.as_str() == *n)
    }

    /// The error a missing path is: an undeclared root, or no such key at the leaf.
    pub(crate) fn missing(&self) -> ExecutionError {
        match self.steps.last() {
            None => ExecutionError::UndeclaredReference(Arc::new(self.root.clone())),
            Some(s) => ExecutionError::no_such_key(s.name.as_str()),
        }
    }
}

/// The caller's data, read by field. Implemented by a request type directly, so a decision reads
/// its inputs where they already are rather than packing them into values first.
///
/// `None` is "absent": `no such key` at the leaf. Every method answers for the
/// field's DECLARED type; a program is only ever handed to a `Facts` whose fields have the types
/// its environment declared.
pub trait Facts {
    fn bool(&self, f: FieldId) -> Option<bool>;
    fn num(&self, f: FieldId) -> Option<f64>;
    fn str(&self, f: FieldId) -> Option<&str>;
    fn bytes(&self, f: FieldId) -> Option<&[u8]> {
        let _ = f;
        None
    }
    /// A field declared as a closed string set (`CelEnvironment::declare_enum`), by TAG: the
    /// value's index in the declared list, or [`TAG_OTHER`](crate::TAG_OTHER) for a string outside
    /// it. `None` (the default) has the backend look up [`str`](Facts::str) instead — so a
    /// provider answers a tag only where it has one for free, and must agree with `str` when it
    /// does.
    fn tag(&self, f: FieldId) -> Option<u8> {
        let _ = f;
        None
    }
    /// A duration field, in milliseconds — [`CelValue::Duration`](crate::CelValue::Duration)'s
    /// unit.
    fn duration_ms(&self, f: FieldId) -> Option<i64> {
        let _ = f;
        None
    }
    /// `has(x.f)`: is the member `f` names present?
    fn has(&self, f: FieldId) -> bool;

    /// Can field `f` be read YET? Asked before every read, for a provider whose data is still
    /// arriving; a provider that holds all of it keeps the default, which is always
    /// [`FactPoll::Ready`] and costs nothing.
    fn poll(&self, f: FieldId) -> FactPoll {
        let _ = f;
        FactPoll::Ready
    }

    /// [`poll`](Facts::poll) for `has(x.f)`: presence can be known before the member's value is.
    fn poll_has(&self, f: FieldId) -> FactPoll {
        let _ = f;
        FactPoll::Ready
    }
}

/// Whether a field can be read yet. `at` numbers the members below the field's root from 0, so
/// the error names the member it failed at, as a walk through views would.
#[derive(Debug)]
pub enum FactPoll {
    /// Read it now.
    Ready,
    /// Member `at` is not answerable yet: a run that can wait pauses, and re-reads it when resumed.
    Pending { at: usize, handle: DemandHandle },
    /// Reading member `at` fails with `error` — exactly as a [`LazyValue`](crate::LazyValue)
    /// failing the same read ([`CelError::NoSuchMember`](crate::CelError::NoSuchMember) is
    /// `no such key`).
    Failed { at: usize, error: crate::CelError },
}

/// What a read wants, from the field's declared type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Want {
    Bool,
    Num,
    Str,
    Bytes,
    Dur,
    Any,
}

/// Why a read produced no value.
pub(crate) enum Miss {
    /// It failed. Boxed so a read's result stays small: the error is the cold path.
    Err(Box<ExecutionError>),
    /// It is not answerable yet. Only a host that [waits](Host::waits) answers this.
    Need(DemandHandle),
}

impl From<ExecutionError> for Miss {
    #[cold]
    fn from(e: ExecutionError) -> Miss {
        Miss::Err(Box::new(e))
    }
}

/// The backend's view of a run's roots.
pub(crate) trait Host<'a> {
    fn read(&self, f: u32, want: Want, st: &mut Store<'a>) -> Result<Reg<'a>, Miss>;
    /// A closed-set string field's tag against `values`: read as a string and looked up, unless
    /// the host answers the tag itself.
    #[inline]
    fn tag(&self, f: u32, values: &[Box<str>], st: &mut Store<'a>) -> Result<u8, Miss> {
        match self.read(f, Want::Str, st)? {
            Reg::Str(s) => Ok(crate::hostfn::tag_of(values, s)),
            _ => Ok(crate::hostfn::TAG_OTHER),
        }
    }
    fn has(&self, f: u32, st: &mut Store<'a>) -> Result<bool, Miss>;
    /// Does a read that is not answerable yet PAUSE the run (`Miss::Need`)? Only a run that can
    /// wait says yes; every other run reads "not yet" as an error.
    fn waits(&self) -> bool {
        false
    }
    /// A call to a CALL host: answered by the run's dispatcher, when it has one.
    fn call_host(
        &self,
        name: &str,
        _args: &[crate::CelValue],
    ) -> Result<crate::CelValue, crate::CelError> {
        Err(crate::CelError::unknown_host_function(name))
    }
}

/// A host whose CALL hosts a [`HostDispatch`](crate::hostfn::HostDispatch) answers; every root read is
/// `inner`'s. The dispatcher is borrowed mutably for the run, so it sits in a cell: a run is one
/// thread and a call op never re-enters it.
pub(crate) struct Dispatching<'c, 'd, H> {
    pub(crate) inner: H,
    pub(crate) dispatch: &'c std::cell::RefCell<&'d mut dyn crate::hostfn::HostDispatch>,
}

impl<'a, H: Host<'a>> Host<'a> for Dispatching<'_, '_, H> {
    #[inline(always)]
    fn read(&self, f: u32, want: Want, st: &mut Store<'a>) -> Result<Reg<'a>, Miss> {
        self.inner.read(f, want, st)
    }
    #[inline(always)]
    fn tag(&self, f: u32, values: &[Box<str>], st: &mut Store<'a>) -> Result<u8, Miss> {
        self.inner.tag(f, values, st)
    }
    #[inline(always)]
    fn has(&self, f: u32, st: &mut Store<'a>) -> Result<bool, Miss> {
        self.inner.has(f, st)
    }
    fn waits(&self) -> bool {
        self.inner.waits()
    }
    fn call_host(
        &self,
        name: &str,
        args: &[crate::CelValue],
    ) -> Result<crate::CelValue, crate::CelError> {
        match self.dispatch.try_borrow_mut() {
            Ok(mut d) => d.call(name, args),
            Err(_) => Err(crate::CelError::Evaluation {
                source: std::sync::Arc::from(name),
                message: "a call host re-entered its own run".into(),
            }),
        }
    }
}

/// A [`Facts`] as a host. Only scalar fields: a composite root has no `Facts` spelling yet.
pub(crate) struct FactsHost<'a, F: ?Sized> {
    pub(crate) facts: &'a F,
    pub(crate) fields: &'a [FieldPath],
    /// Pause on [`FactPoll::Pending`] rather than failing.
    pub(crate) wait: bool,
}

impl<'a, F: Facts + ?Sized> FactsHost<'a, F> {
    /// A read of a number, bytes or duration field; `Any` is a composite, which `Facts` does not
    /// serve.
    #[inline(always)]
    fn read_rest(&self, f: u32, want: Want) -> Result<Option<Reg<'a>>, Miss> {
        let id = FieldId(f);
        Ok(match want {
            Want::Num => self.facts.num(id).map(Reg::Num),
            Want::Bytes => self.facts.bytes(id).map(Reg::Bytes),
            Want::Dur => self
                .facts
                .duration_ms(id)
                .map(|ms| Reg::Dur(chrono::Duration::milliseconds(ms))),
            Want::Str | Want::Bool => unreachable!("read answers the common kinds itself"),
            Want::Any => {
                return Err(Miss::from(ExecutionError::InternalError(format!(
                    "`{}` is not a scalar, and a Facts provider serves scalars only",
                    self.fields[f as usize].root
                ))))
            }
        })
    }
}

impl<F: ?Sized> FactsHost<'_, F> {
    /// A poll that was not `Ready`, as the miss a walk through views would produce.
    #[cold]
    #[inline(never)]
    fn miss(&self, f: u32, p: FactPoll) -> Miss {
        let path = &self.fields[f as usize];
        let name = |at: usize| {
            path.steps
                .get(at)
                .map_or(path.root.as_str(), |s| s.name.as_str())
        };
        match p {
            FactPoll::Ready => ExecutionError::InternalError("a ready poll".into()).into(),
            FactPoll::Pending { handle, .. } if self.wait => Miss::Need(handle),
            FactPoll::Pending { at, handle } => pending_error(name(at), handle).into(),
            FactPoll::Failed { at, error } => member_error(name(at), error).into(),
        }
    }
}

impl<'a, F: Facts + ?Sized> Host<'a> for FactsHost<'a, F> {
    #[inline(always)]
    fn read(&self, f: u32, want: Want, _: &mut Store<'a>) -> Result<Reg<'a>, Miss> {
        let id = FieldId(f);
        match self.facts.poll(id) {
            FactPoll::Ready => {}
            p => return Err(self.miss(f, p)),
        }
        // Compare-and-branch on the common kinds before the table: each read's kind is fixed, so
        // these branches predict perfectly where a jump table on `want` costs an indirect jump.
        let got = if want == Want::Str {
            self.facts.str(id).map(Reg::Str)
        } else if want == Want::Bool {
            self.facts.bool(id).map(Reg::Bool)
        } else {
            self.read_rest(f, want)?
        };
        got.ok_or_else(|| Miss::from(self.fields[f as usize].missing()))
    }

    #[inline(always)]
    fn tag(&self, f: u32, values: &[Box<str>], _: &mut Store<'a>) -> Result<u8, Miss> {
        let id = FieldId(f);
        match self.facts.poll(id) {
            FactPoll::Ready => {}
            p => return Err(self.miss(f, p)),
        }
        if let Some(t) = self.facts.tag(id) {
            return Ok(t);
        }
        match self.facts.str(id) {
            Some(s) => Ok(crate::hostfn::tag_of(values, s)),
            None => Err(Miss::from(self.fields[f as usize].missing())),
        }
    }
    #[inline(always)]
    fn has(&self, f: u32, _: &mut Store<'a>) -> Result<bool, Miss> {
        let id = FieldId(f);
        match self.facts.poll_has(id) {
            FactPoll::Ready => Ok(self.facts.has(id)),
            p => Err(self.miss(f, p)),
        }
    }

    fn waits(&self) -> bool {
        self.wait
    }
}

/// Bound values as a host: each path is walked member by member, one read per step, so a lazy
/// value serves exactly the reads the program makes.
pub(crate) struct RootsHost<'a> {
    pub(crate) roots: &'a Bindings,
    pub(crate) fields: &'a [FieldPath],
    /// Pause on a lazy member that is not answerable yet, rather than failing on it.
    pub(crate) wait: bool,
}

impl<'a> RootsHost<'a> {
    /// The value at `steps` below `root`. A member a lazy view hands back is kept in the store for
    /// the run.
    fn walk(
        &self,
        path: &'a FieldPath,
        steps: &'a [Step],
        st: &mut Store<'a>,
    ) -> Result<&'a CelValue, Miss> {
        let mut cur: &'a CelValue = self
            .roots
            .get(&path.root)
            .ok_or_else(|| ExecutionError::UndeclaredReference(Arc::new(path.root.clone())))?;
        for step in steps {
            let name = step.name.as_str();
            cur = match cur {
                CelValue::Map(m) => m
                    .get(name)
                    .ok_or_else(|| ExecutionError::no_such_key(name))?,
                CelValue::Lazy(l) => match lazy::poll_read(l.as_ref(), name)? {
                    Access::Ready(v) => st.value(v),
                    Access::Pending(h) if self.wait => return Err(Miss::Need(h)),
                    Access::Pending(h) => return Err(pending_error(name, h).into()),
                },
                // A list's index refuses a string.
                CelValue::List(_) => {
                    return Err(ExecutionError::UnexpectedType {
                        got: "string".into(),
                        want: "double".into(),
                    }
                    .into())
                }
                _ => return Err(ExecutionError::NoSuchOverload.into()),
            };
        }
        Ok(cur)
    }
}

impl<'a> Host<'a> for RootsHost<'a> {
    fn read(&self, f: u32, _: Want, st: &mut Store<'a>) -> Result<Reg<'a>, Miss> {
        let path = &self.fields[f as usize];
        Ok(of_cel(self.walk(path, &path.steps, st)?))
    }

    fn has(&self, f: u32, st: &mut Store<'a>) -> Result<bool, Miss> {
        let path = &self.fields[f as usize];
        let (last, prefix) = path
            .steps
            .split_last()
            .expect("a presence path has a member");
        let name = last.name.as_str();
        match self.walk(path, prefix, st)? {
            CelValue::Lazy(l) if self.wait => match lazy::poll_presence(l.as_ref(), name)? {
                Presence::Known(b) => Ok(b),
                Presence::Pending(h) => Err(Miss::Need(h)),
            },
            CelValue::Lazy(l) => Ok(lazy::presence(l.as_ref(), name)?),
            CelValue::Map(m) => Ok(m.get(name).is_some()),
            _ => Err(ExecutionError::NoSuchOverload.into()),
        }
    }

    fn waits(&self) -> bool {
        self.wait
    }
}

/// A run's roots from two places: the fields `mine` marks from a [`Facts`] provider, every other
/// from a context of bound values. A streamed run reads its document this way and the rest of its
/// roots from its bindings.
pub(crate) struct SplitHost<'a, F: ?Sized> {
    pub(crate) facts: FactsHost<'a, F>,
    pub(crate) ctx: RootsHost<'a>,
    pub(crate) mine: &'a [bool],
}

impl<'a, F: Facts + ?Sized> Host<'a> for SplitHost<'a, F> {
    fn read(&self, f: u32, want: Want, st: &mut Store<'a>) -> Result<Reg<'a>, Miss> {
        if self.mine[f as usize] {
            self.facts.read(f, want, st)
        } else {
            self.ctx.read(f, want, st)
        }
    }

    fn tag(&self, f: u32, values: &[Box<str>], st: &mut Store<'a>) -> Result<u8, Miss> {
        if self.mine[f as usize] {
            self.facts.tag(f, values, st)
        } else {
            self.ctx.tag(f, values, st)
        }
    }

    fn has(&self, f: u32, st: &mut Store<'a>) -> Result<bool, Miss> {
        if self.mine[f as usize] {
            self.facts.has(f, st)
        } else {
            self.ctx.has(f, st)
        }
    }

    fn waits(&self) -> bool {
        self.facts.wait && self.ctx.wait
    }
}
