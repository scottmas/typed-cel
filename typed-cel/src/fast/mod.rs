//! The fast typed backend: a register machine over unboxed values, reading host data by field.
//!
//! A checked program has concrete types and one number kind, so its values need no box: a
//! [`Reg`](reg::Reg) holds a bool or a double by value and a string by reference into the host's
//! data, the constant pool, or the run's arena. Every name resolves at lowering (`lower.rs`) — a
//! root to a [`FieldId`], a comprehension variable to a register, a function to an op — and a
//! known list's `exists` or `in` becomes one matcher built once (`matcher.rs`).
//!
//! The tree evaluator is the specification. Every op mirrors one arm of `objects.rs::resolve_val`,
//! error text included; a failing op jumps to the handler its lowering named, and `&&`/`||` absorb
//! exactly as the evaluator does. There is NO fallback: a program the checker admitted either
//! lowers here or `FastProgram::new` refuses it, and the gates count how many ran.
//!
//! This file names only the absorbed value model, the lazy seam and `fast`'s own modules — never
//! the parser or the checker.

mod host;
mod lower;
mod matcher;
mod reg;

use std::collections::HashMap;
use std::sync::Arc;

use crate::common::types::{CelList, CelMap, CelMapKey, CelString};
use crate::common::value::Val;
use crate::context::Context;
use crate::objects::Value;
use crate::ExecutionError;

use crate::lazy::{Access, DemandHandle, LazyAdapter, Presence};

use host::{CtxHost, Dispatching, FactsHost, Host, Miss, SplitHost, Want};
pub use host::{FactPoll, Facts, FieldId, FieldPath};
use matcher::StrMatcher;
use reg::{Keep, Reg, Store};

/// A register.
pub(crate) type R = u16;
/// An op's index.
pub(crate) type Pc = u32;

/// The static kind of a checked node — the part of its `CelTy` the backend lowers by.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Bool,
    Num,
    Str,
    Bytes,
    Null,
    Duration,
    List,
    Map,
    Record,
    Dyn,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Cmp {
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Arith {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StrOp {
    StartsWith,
    EndsWith,
    Contains,
}

/// Which accumulator settles a comprehension step and clears a pending error.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Absorb {
    Never,
    OnFalse,
    OnTrue,
}

/// One op. Every `err` is where a failure jumps; every other `Pc` is a jump target.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Op {
    Const {
        dst: R,
        k: u32,
    },
    /// A constant that is an error (`duration("x")`): raise it.
    Raise {
        k: u32,
        err: Pc,
    },
    Read {
        dst: R,
        f: u32,
        want: Want,
        err: Pc,
    },
    Has {
        dst: R,
        f: u32,
        err: Pc,
    },
    /// Read a comprehension variable — borrowed, as the evaluator reads a variable.
    Local {
        dst: R,
        src: R,
    },
    Own {
        r: R,
    },
    Select {
        dst: R,
        obj: R,
        key: u32,
        err: Pc,
    },
    HasOf {
        dst: R,
        obj: R,
        key: u32,
        err: Pc,
    },
    Index {
        dst: R,
        a: R,
        b: R,
        err: Pc,
    },
    Not {
        dst: R,
        a: R,
        err: Pc,
    },
    Neg {
        dst: R,
        a: R,
        err: Pc,
    },
    Eq {
        dst: R,
        a: R,
        b: R,
    },
    Ne {
        dst: R,
        a: R,
        b: R,
    },
    Cmp {
        dst: R,
        a: R,
        b: R,
        op: Cmp,
        err: Pc,
    },
    Arith {
        dst: R,
        a: R,
        b: R,
        op: Arith,
        err: Pc,
    },
    In {
        dst: R,
        a: R,
        b: R,
        err: Pc,
    },
    /// `a` equals one of a set of strings or begins with one of a set of prefixes.
    Match {
        dst: R,
        a: R,
        m: u32,
        err: Pc,
    },
    StrOp {
        dst: R,
        a: R,
        b: R,
        op: StrOp,
        err: Pc,
    },
    /// `a.matches(b)`; `re` is a pattern compiled at lowering, `u32::MAX` when `b` is computed.
    Matches {
        dst: R,
        a: R,
        b: R,
        re: u32,
        err: Pc,
    },
    Size {
        dst: R,
        a: R,
        err: Pc,
    },
    Duration {
        dst: R,
        a: R,
        err: Pc,
    },
    DurPart {
        dst: R,
        a: R,
        millis: bool,
        err: Pc,
    },
    MakeList {
        dst: R,
        start: R,
        n: u16,
    },
    CheckKey {
        r: R,
        err: Pc,
    },
    MakeMap {
        dst: R,
        start: R,
        n: u16,
    },
    Jump {
        to: Pc,
    },
    BrTrue {
        r: R,
        to: Pc,
    },
    BrFalse {
        r: R,
        to: Pc,
    },
    /// `try_bool(r)?`: `true` falls through, `false` jumps to `else_` (inverted: the other way
    /// round), anything else fails.
    Cond {
        r: R,
        invert: bool,
        else_: Pc,
        err: Pc,
    },
    /// `Read` of a bool field, then `Cond` on it.
    CondRead {
        f: u32,
        invert: bool,
        else_: Pc,
        err: Pc,
    },
    /// `EqK`, then `Cond` on it: `a == k` (`ne`: `!=`) falls through, else jumps.
    CondEqK {
        a: R,
        k: u32,
        ne: bool,
        else_: Pc,
    },
    /// `Match`, then `Cond` on it.
    CondMatch {
        a: R,
        m: u32,
        invert: bool,
        else_: Pc,
        err: Pc,
    },
    /// A caught left operand of `&&`/`||` whose right operand passed the result on: raise its
    /// error. A bool (the left passed it on too) does nothing.
    RaiseIfErr {
        r: R,
        err: Pc,
    },
    /// `a == k` / `a != k` against a scalar constant.
    EqK {
        dst: R,
        a: R,
        k: u32,
        ne: bool,
    },
    /// Take the error in flight into `dst`.
    Catch {
        dst: R,
    },
    /// `a || b` / `a && b` once `a` did not decide it and `b` is in `dst` (`objects.rs`,
    /// `LOGICAL_OR`/`LOGICAL_AND`): an erroring `a` is absorbed by a deciding `b`, and raised
    /// otherwise.
    Absorb {
        dst: R,
        a: R,
        or: bool,
        err: Pc,
    },
    /// `@not_strictly_false(a)`: `a`'s bool, or `true` for anything else.
    Nsf {
        dst: R,
        a: R,
    },
    IterInit {
        slot: u16,
        src: R,
        err: Pc,
    },
    IterNext {
        slot: u16,
        dst: R,
        exit: Pc,
    },
    BrPending {
        r: R,
        to: Pc,
    },
    Clear {
        r: R,
    },
    Step {
        accu: R,
        step: R,
        pend: R,
        absorb: Absorb,
    },
    CatchPending {
        pend: R,
    },
    RaisePending {
        pend: R,
        err: Pc,
    },
    /// Is closed-set field `f`'s tag one of `mask`'s bits (`ne`: is it NOT)? `set` is the field's
    /// value list in `Code::enum_sets`. A tag outside the list (`TAG_OTHER`) is in no mask.
    TagIn {
        dst: R,
        f: u32,
        set: u16,
        mask: u64,
        ne: bool,
        err: Pc,
    },
    /// `TagIn`, then `Cond` on it: jump to `else_` when the tag's membership equals `invert`.
    CondTagIn {
        f: u32,
        set: u16,
        mask: u64,
        invert: bool,
        else_: Pc,
        err: Pc,
    },
    /// Call host function `h` on the `n` registers from `start` (the receiver first, for a
    /// member): `hostfn::HostTable`'s entry, as the evaluator's registry calls it.
    Host {
        dst: R,
        start: R,
        n: u16,
        h: u16,
        err: Pc,
    },
    Ret {
        r: R,
    },
    /// `Const` into a register, then `Ret` of it.
    RetK {
        k: u32,
    },
    Fail,
}

impl Op {
    /// The variant's name, by an exhaustive match — a new op does not compile until it is named
    /// here, and `tests/vm_differential.rs::the_generators_reach_every_op` compares what the
    /// generators lower to against these names.
    pub(crate) fn name(&self) -> &'static str {
        use Op::*;
        match self {
            Const { .. } => "Const",
            Raise { .. } => "Raise",
            Read { .. } => "Read",
            Has { .. } => "Has",
            Local { .. } => "Local",
            Own { .. } => "Own",
            Select { .. } => "Select",
            HasOf { .. } => "HasOf",
            Index { .. } => "Index",
            Not { .. } => "Not",
            Neg { .. } => "Neg",
            Eq { .. } => "Eq",
            Ne { .. } => "Ne",
            Cmp { .. } => "Cmp",
            Arith { .. } => "Arith",
            In { .. } => "In",
            Match { .. } => "Match",
            StrOp { .. } => "StrOp",
            Matches { .. } => "Matches",
            Size { .. } => "Size",
            Duration { .. } => "Duration",
            DurPart { .. } => "DurPart",
            MakeList { .. } => "MakeList",
            CheckKey { .. } => "CheckKey",
            MakeMap { .. } => "MakeMap",
            Jump { .. } => "Jump",
            BrTrue { .. } => "BrTrue",
            BrFalse { .. } => "BrFalse",
            Cond { .. } => "Cond",
            CondRead { .. } => "CondRead",
            CondEqK { .. } => "CondEqK",
            CondMatch { .. } => "CondMatch",
            RaiseIfErr { .. } => "RaiseIfErr",
            EqK { .. } => "EqK",
            Catch { .. } => "Catch",
            Absorb { .. } => "Absorb",
            Nsf { .. } => "Nsf",
            IterInit { .. } => "IterInit",
            IterNext { .. } => "IterNext",
            BrPending { .. } => "BrPending",
            Clear { .. } => "Clear",
            Step { .. } => "Step",
            CatchPending { .. } => "CatchPending",
            RaisePending { .. } => "RaisePending",
            Host { .. } => "Host",
            TagIn { .. } => "TagIn",
            CondTagIn { .. } => "CondTagIn",
            Ret { .. } => "Ret",
            RetK { .. } => "RetK",
            Fail => "Fail",
        }
    }

    fn retarget(&mut self, at: &impl Fn(Pc) -> Pc) {
        use Op::*;
        match self {
            Raise { err, .. }
            | Read { err, .. }
            | Has { err, .. }
            | Select { err, .. }
            | HasOf { err, .. }
            | Index { err, .. }
            | Not { err, .. }
            | Neg { err, .. }
            | Cmp { err, .. }
            | Arith { err, .. }
            | In { err, .. }
            | Match { err, .. }
            | StrOp { err, .. }
            | Matches { err, .. }
            | Size { err, .. }
            | Duration { err, .. }
            | DurPart { err, .. }
            | CheckKey { err, .. }
            | Absorb { err, .. }
            | RaiseIfErr { err, .. }
            | IterInit { err, .. }
            | RaisePending { err, .. }
            | Host { err, .. }
            | TagIn { err, .. } => *err = at(*err),
            Jump { to } | BrTrue { to, .. } | BrFalse { to, .. } | BrPending { to, .. } => {
                *to = at(*to)
            }
            Cond { else_, err, .. }
            | CondRead { else_, err, .. }
            | CondMatch { else_, err, .. }
            | CondTagIn { else_, err, .. } => {
                *else_ = at(*else_);
                *err = at(*err);
            }
            CondEqK { else_, .. } => *else_ = at(*else_),
            IterNext { exit, .. } => *exit = at(*exit),
            Const { .. }
            | Local { .. }
            | Own { .. }
            | Eq { .. }
            | Ne { .. }
            | EqK { .. }
            | MakeList { .. }
            | MakeMap { .. }
            | Catch { .. }
            | Nsf { .. }
            | Clear { .. }
            | Step { .. }
            | CatchPending { .. }
            | Ret { .. }
            | RetK { .. }
            | Fail => {}
        }
    }
}

/// A constant.
#[derive(Debug)]
pub(crate) enum CVal {
    Bool(bool),
    Num(f64),
    Null,
    Dur(chrono::Duration),
    Str(Box<str>),
    Bytes(Box<[u8]>),
    /// A list or map, and whether the evaluator holds it owned (a literal) or borrowed (a slot).
    Dyn(Box<dyn Val>, bool),
    Err(ExecutionError),
}

impl CVal {
    /// A constant `EqK` can compare against.
    pub(crate) fn is_scalar(&self) -> bool {
        matches!(
            self,
            CVal::Bool(_)
                | CVal::Num(_)
                | CVal::Null
                | CVal::Dur(_)
                | CVal::Str(_)
                | CVal::Bytes(_)
        )
    }

    /// The constant as a register, for folding at lowering.
    pub(crate) fn reg_of(&self) -> Reg<'_> {
        self.reg()
    }

    #[inline]
    fn reg(&self) -> Reg<'_> {
        match self {
            CVal::Bool(b) => Reg::Bool(*b),
            CVal::Num(n) => Reg::Num(*n),
            CVal::Null => Reg::Null,
            CVal::Dur(d) => Reg::Dur(*d),
            CVal::Str(s) => Reg::Str(s),
            CVal::Bytes(b) => Reg::Bytes(b),
            CVal::Dyn(v, owned) => Reg::Dyn(v.as_ref(), *owned),
            CVal::Err(_) => Reg::Unset,
        }
    }
}

/// A lowered program.
#[derive(Debug, Default)]
pub(crate) struct Code {
    pub(crate) ops: Vec<Op>,
    pub(crate) consts: Vec<CVal>,
    /// Member names a computed select reads.
    pub(crate) names: Vec<CelString>,
    pub(crate) fields: Vec<FieldPath>,
    pub(crate) matchers: Vec<StrMatcher>,
    pub(crate) regexes: Vec<Result<regex::Regex, ExecutionError>>,
    pub(crate) nregs: usize,
    pub(crate) nloops: usize,
    /// The host functions a `Host` op calls, by index.
    pub(crate) hosts: Arc<crate::hostfn::HostTable>,
    /// The closed-set value lists a tag op looks a string up in, by index.
    pub(crate) enum_sets: Vec<Arc<[Box<str>]>>,
    /// Every constant as a register, built once by [`Code::seal`].
    kregs: Vec<Reg<'static>>,
}

impl Code {
    /// Materialize the constants as registers, so loading one is a copy.
    pub(crate) fn seal(&mut self) {
        self.kregs = self
            .consts
            .iter()
            // SAFETY: every register borrows from a constant's own heap allocation (a `Box`), which
            // `consts` owns, never mutates and never moves out of; `kregs` is only read through a
            // `&'a Code`, narrowing each register to `'a` before it is used.
            .map(|c| unsafe { std::mem::transmute::<Reg<'_>, Reg<'static>>(c.reg()) })
            .collect();
    }

    #[inline]
    fn konst<'a>(&'a self, k: u32) -> Reg<'a> {
        self.kregs[k as usize]
    }
}

/// A program on the fast backend. Built once from a [`CelProgram`](crate::CelProgram) — compiled
/// or specialized — and shared across threads.
#[derive(Debug)]
pub struct FastProgram {
    code: Code,
    source: Arc<str>,
}

impl FastProgram {
    /// Lower `p`. Every program `CelEnvironment::compile` or `specialize` produced lowers; a
    /// refusal is a defect of this backend, never a fallback.
    pub fn new(p: &crate::CelProgram) -> Result<FastProgram, crate::CelError> {
        let code = lower::lower(
            p.program().expression(),
            p.kinds(),
            p.pool().slots(),
            p.hosts(),
            p.enums(),
        )
        .map_err(|message| crate::CelError::Emit {
            source: p.source_arc(),
            message: format!("the fast backend cannot lower this program: {message}"),
        })?;
        Ok(FastProgram {
            code,
            source: p.source_arc(),
        })
    }

    /// The program's source, as [`CelProgram::source`](crate::CelProgram::source) has it.
    pub fn source(&self) -> &str {
        &self.source
    }

    /// Every field path the program reads, indexed by [`FieldId`]. A [`Facts`] implementation
    /// resolves these once and answers by index.
    pub fn fields(&self) -> &[FieldPath] {
        &self.code.fields
    }

    /// The [`FieldId`] of `root.a.b`, when the program reads it.
    pub fn field(&self, names: &[&str]) -> Option<FieldId> {
        self.code
            .fields
            .iter()
            .position(|p| p.is(names))
            .map(|i| FieldId(i as u32))
    }

    /// How many matchers lowering built. For the tests that must not be vacuous about them.
    #[doc(hidden)]
    pub fn matcher_count(&self) -> usize {
        self.code.matchers.len()
    }

    /// Whether any matcher searches a sorted set.
    #[doc(hidden)]
    pub fn has_sorted_matcher(&self) -> bool {
        self.code.matchers.iter().any(StrMatcher::is_sorted)
    }

    /// The lowered ops, one per line, for a reader chasing what a program runs.
    #[doc(hidden)]
    pub fn listing(&self) -> String {
        self.code
            .ops
            .iter()
            .enumerate()
            .map(|(i, op)| format!("{i:4}  {op:?}\n"))
            .collect()
    }

    /// The name of every op the program lowered to, in order.
    #[doc(hidden)]
    pub fn op_names(&self) -> Vec<&'static str> {
        self.code.ops.iter().map(Op::name).collect()
    }

    /// How many ops the program lowered to.
    #[doc(hidden)]
    pub fn op_count(&self) -> usize {
        self.code.ops.len()
    }

    /// The verdict over `activation`'s values — the contract, and the error text, of
    /// [`CelProgram::evaluate`](crate::CelProgram::evaluate).
    pub fn eval(&self, activation: &crate::CelActivation) -> Result<bool, crate::CelError> {
        let host = CtxHost {
            ctx: activation.context(),
            fields: &self.code.fields,
            wait: false,
        };
        let mut scratch = FastScratch::default();
        verdict(&self.source, run(&self.code, &host, &mut scratch, as_bool))
    }

    /// The value over `activation`'s values, whatever its type — [`Vm::eval_result`]'s contract.
    ///
    /// [`Vm::eval_result`]: crate::Vm::eval_result
    pub fn eval_result(
        &self,
        activation: &crate::CelActivation,
    ) -> Result<crate::CelValue, crate::CelError> {
        let v = self.eval_value(activation.context());
        match v {
            Ok(v) => crate::CelValue::from_value(&v).ok_or_else(|| crate::CelError::Evaluation {
                source: self.source.clone(),
                message: format!("produced {v:?}, which has no CelValue form"),
            }),
            Err(e) => Err(crate::CelError::Evaluation {
                source: self.source.clone(),
                message: format!("could not be evaluated: {e}"),
            }),
        }
    }

    /// [`eval_result`](FastProgram::eval_result), with `dispatch` answering every CALL host.
    pub fn eval_result_with(
        &self,
        activation: &crate::CelActivation,
        dispatch: &mut dyn crate::hostfn::HostDispatch,
    ) -> Result<crate::CelValue, crate::CelError> {
        let cell = std::cell::RefCell::new(dispatch);
        let host = Dispatching {
            inner: CtxHost {
                ctx: activation.context(),
                fields: &self.code.fields,
                wait: false,
            },
            dispatch: &cell,
        };
        let mut scratch = FastScratch::default();
        let v = run(&self.code, &host, &mut scratch, |r, errs| {
            reg::to_value(r, errs)
        })
        .and_then(|v| v);
        self.result_value(v)
    }

    fn result_value(
        &self,
        v: Result<Value, ExecutionError>,
    ) -> Result<crate::CelValue, crate::CelError> {
        match v {
            Ok(v) => crate::CelValue::from_value(&v).ok_or_else(|| crate::CelError::Evaluation {
                source: self.source.clone(),
                message: format!("produced {v:?}, which has no CelValue form"),
            }),
            Err(e) => Err(crate::CelError::Evaluation {
                source: self.source.clone(),
                message: format!("could not be evaluated: {e}"),
            }),
        }
    }

    /// The name of every CALL host the program calls, in op order, each once.
    pub fn call_hosts(&self) -> Vec<&str> {
        let mut out: Vec<&str> = Vec::new();
        for op in &self.code.ops {
            if let Op::Host { h, .. } = op {
                let e = &self.code.hosts.entries[*h as usize];
                if e.closure().is_none() && !out.contains(&e.name.as_str()) {
                    out.push(&e.name);
                }
            }
        }
        out
    }

    /// The boundary value over an evaluator context, as `Program::execute` returns it.
    pub(crate) fn eval_value(&self, ctx: &Context) -> Result<Value, ExecutionError> {
        let host = CtxHost {
            ctx,
            fields: &self.code.fields,
            wait: false,
        };
        let mut scratch = FastScratch::default();
        run(&self.code, &host, &mut scratch, |r, errs| {
            reg::to_value(r, errs)
        })
        .and_then(|v| v)
    }

    /// The verdict over the caller's own data. `scratch` is reused from call to call, so a
    /// decision allocates nothing once it has been warmed.
    pub fn decide<F: Facts + ?Sized>(
        &self,
        facts: &F,
        scratch: &mut FastScratch,
    ) -> Result<bool, crate::CelError> {
        let host = FactsHost {
            facts,
            fields: &self.code.fields,
            wait: false,
        };
        verdict(&self.source, run(&self.code, &host, scratch, as_bool))
    }

    /// The TAG a string program produced over the caller's own data: its index in `tags`, or
    /// `None` for a string that is not one of them — never a default. A result that is not a
    /// string, and an evaluation error, are `Err`. Like [`decide`](FastProgram::decide), a warmed
    /// `scratch` makes this allocate nothing: the tag is compared where the run left it.
    pub fn decide_tag<F: Facts + ?Sized>(
        &self,
        facts: &F,
        scratch: &mut FastScratch,
        tags: &[&str],
    ) -> Result<Option<usize>, crate::CelError> {
        let host = FactsHost {
            facts,
            fields: &self.code.fields,
            wait: false,
        };
        self.tag_on(&host, scratch, tags)
    }

    /// [`decide_tag`](FastProgram::decide_tag), with `dispatch` answering every CALL host.
    pub fn decide_tag_with<F: Facts + ?Sized>(
        &self,
        facts: &F,
        scratch: &mut FastScratch,
        tags: &[&str],
        dispatch: &mut dyn crate::hostfn::HostDispatch,
    ) -> Result<Option<usize>, crate::CelError> {
        let cell = std::cell::RefCell::new(dispatch);
        let host = Dispatching {
            inner: FactsHost {
                facts,
                fields: &self.code.fields,
                wait: false,
            },
            dispatch: &cell,
        };
        self.tag_on(&host, scratch, tags)
    }

    /// The number a `double` program produced over the caller's own data, with `dispatch`
    /// answering every CALL host. Any other result, and an evaluation error, are `Err`.
    pub fn decide_number_with<F: Facts + ?Sized>(
        &self,
        facts: &F,
        scratch: &mut FastScratch,
        dispatch: &mut dyn crate::hostfn::HostDispatch,
    ) -> Result<f64, crate::CelError> {
        let cell = std::cell::RefCell::new(dispatch);
        let host = Dispatching {
            inner: FactsHost {
                facts,
                fields: &self.code.fields,
                wait: false,
            },
            dispatch: &cell,
        };
        let out = run(&self.code, &host, scratch, |r, errs| match r {
            Reg::Num(n) => Ok(n),
            other => Err(reg::to_value(other, errs).unwrap_or(Value::Null)),
        });
        match out {
            Ok(Ok(n)) => Ok(n),
            Ok(Err(other)) => Err(crate::CelError::Evaluation {
                source: self.source.clone(),
                message: format!("produced {other:?} rather than a double"),
            }),
            Err(e) => Err(crate::CelError::Evaluation {
                source: self.source.clone(),
                message: format!("could not be evaluated: {e}"),
            }),
        }
    }

    fn tag_on<'a, H: Host<'a>>(
        &'a self,
        host: &H,
        scratch: &mut FastScratch,
        tags: &[&str],
    ) -> Result<Option<usize>, crate::CelError> {
        let out = run(&self.code, host, scratch, |r, errs| match r {
            Reg::Str(s) => Ok(tags.iter().position(|t| *t == s)),
            other => Err(reg::to_value(other, errs).unwrap_or(Value::Null)),
        });
        match out {
            Ok(Ok(tag)) => Ok(tag),
            Ok(Err(other)) => Err(crate::CelError::Evaluation {
                source: self.source.clone(),
                message: format!("produced {other:?} rather than a string"),
            }),
            Err(e) => Err(crate::CelError::Evaluation {
                source: self.source.clone(),
                message: format!("could not be evaluated: {e}"),
            }),
        }
    }
}

/// A run's result as a verdict, converting only what is not a bool.
#[inline]
fn as_bool(r: Reg<'_>, errs: &[ExecutionError]) -> Result<bool, Value> {
    match r {
        Reg::Bool(b) => Ok(b),
        other => Err(reg::to_value(other, errs).unwrap_or(Value::Null)),
    }
}

/// `activation.rs::verdict`, for a run that already knows whether it produced a bool.
#[inline]
fn verdict(
    source: &Arc<str>,
    out: Result<Result<bool, Value>, ExecutionError>,
) -> Result<bool, crate::CelError> {
    match out {
        Ok(Ok(b)) => Ok(b),
        Ok(Err(other)) => Err(crate::CelError::Evaluation {
            source: source.clone(),
            message: format!("produced {other:?} rather than a bool"),
        }),
        Err(e) => Err(crate::CelError::Evaluation {
            source: source.clone(),
            message: format!("could not be evaluated: {e}"),
        }),
    }
}

/// A comprehension's iteration, over whatever built its range.
enum Iter<'a> {
    Idle,
    Regs(&'a [Reg<'a>], usize),
    Pairs(&'a [(Reg<'a>, Reg<'a>)], usize),
    Vals(&'a [Box<dyn Val>], usize),
    Keys(std::collections::hash_map::Keys<'a, CelMapKey, Box<dyn Val>>),
    Other(Box<dyn crate::common::traits::Iterator<'a> + 'a>),
}

/// A run's working memory, kept between runs so a warmed decision allocates nothing.
///
/// Empty between runs: every reference a run puts in it is gone when the run returns.
#[derive(Default)]
pub struct FastScratch {
    regs: Vec<Reg<'static>>,
    store: Store<'static>,
    errs: Vec<ExecutionError>,
    iters: Vec<Iter<'static>>,
}

impl std::fmt::Debug for FastScratch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FastScratch").finish_non_exhaustive()
    }
}

/// `v`, re-lifetimed for one run. Anything a previous run left in it — only a run that panicked
/// leaves anything — is leaked rather than dropped, because it may refer to data that is gone.
///
/// # Safety
///
/// `T` and `U` must be the same type up to lifetimes, so layout and drop glue agree. The caller
/// empties the vector again before the lifetime it chose ends.
unsafe fn relife<T, U>(v: &mut Vec<T>) -> &mut Vec<U> {
    if !v.is_empty() {
        std::mem::forget(std::mem::take(v));
    }
    &mut *(v as *mut Vec<T> as *mut Vec<U>)
}

/// Run `code` against `host`, turning the result into an owned value with `out` before anything
/// the run built is released.
fn run<'a, H: Host<'a>, T>(
    code: &'a Code,
    host: &H,
    scratch: &mut FastScratch,
    out: impl FnOnce(Reg<'a>, &[ExecutionError]) -> T,
) -> Result<T, ExecutionError> {
    // SAFETY: each vector holds `X<'static>` between runs and `X<'a>` during this one, and each is
    // emptied below, before `'a` can end: nothing the run referenced outlives it.
    let (regs, items, iters) = unsafe {
        (
            relife::<Reg<'static>, Reg<'a>>(&mut scratch.regs),
            relife::<Keep<'static>, Keep<'a>>(&mut scratch.store.items),
            relife::<Iter<'static>, Iter<'a>>(&mut scratch.iters),
        )
    };
    let store: &mut Store<'a> = Store::wrap(items);
    let errs = &mut scratch.errs;
    errs.clear();
    regs.resize(code.nregs, Reg::Unset);
    if code.nloops > 0 {
        iters.resize_with(code.nloops, || Iter::Idle);
    }
    let result = match exec(code, host, regs, store, iters, errs, 0, None) {
        Exit::Ret(r) => Ok(out(r, errs)),
        Exit::Fail(e) => Err(e),
        // Only a host that waits pauses, and this run's does not.
        Exit::Need { .. } => Err(ExecutionError::InternalError(
            "a run that cannot wait paused".into(),
        )),
    };
    regs.clear();
    iters.clear();
    store.items.clear();
    result
}

/// How a run left `exec`.
enum Exit<'a> {
    Ret(Reg<'a>),
    Fail(ExecutionError),
    /// A read is not answerable yet. `pc` is the op that asked: resuming re-executes it, and
    /// nothing before it. Only a host that waits produces this.
    Need {
        handle: DemandHandle,
        pc: usize,
        inflight: Option<ExecutionError>,
    },
}

#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn exec<'a, H: Host<'a>>(
    code: &'a Code,
    host: &H,
    regs: &mut [Reg<'a>],
    st: &mut Store<'a>,
    iters: &mut [Iter<'a>],
    errs: &mut Vec<ExecutionError>,
    start: usize,
    inflight: Option<ExecutionError>,
) -> Exit<'a> {
    let ops = &code.ops[..];
    let mut pc = start;
    let mut inflight = inflight;
    // The op that asked for a value not answerable yet is `pc - 1`: `pc` has already moved past
    // it, and a pause puts it back, so the resumed run executes the same read again.
    macro_rules! need {
        ($h:expr) => {
            return Exit::Need {
                handle: $h,
                pc: pc - 1,
                inflight,
            }
        };
    }
    // The ops a decision runs most, inline; everything else through `slow`, which keeps this loop
    // small enough to hold its state in registers.
    loop {
        let op = ops[pc];
        pc += 1;
        match op {
            Op::Const { dst, k } => regs[dst as usize] = code.konst(k),
            Op::Jump { to } => pc = to as usize,
            Op::BrTrue { r, to } => {
                if matches!(regs[r as usize], Reg::Bool(true)) {
                    pc = to as usize;
                }
            }
            Op::BrFalse { r, to } => {
                if matches!(regs[r as usize], Reg::Bool(false)) {
                    pc = to as usize;
                }
            }
            Op::Local { dst, src } => regs[dst as usize] = regs[src as usize].borrowed(),
            Op::Read { dst, f, want, err } => match host.read(f, want, st) {
                Ok(v) => regs[dst as usize] = v,
                Err(Miss::Err(e)) => {
                    inflight = Some(e);
                    pc = err as usize;
                }
                Err(Miss::Need(h)) => need!(h),
            },
            Op::CondRead {
                f,
                invert,
                else_,
                err,
            } => match host.read(f, Want::Bool, st) {
                Ok(Reg::Bool(b)) => {
                    if b == invert {
                        pc = else_ as usize;
                    }
                }
                Ok(_) => {
                    inflight = Some(ExecutionError::NoSuchOverload);
                    pc = err as usize;
                }
                Err(Miss::Err(e)) => {
                    inflight = Some(e);
                    pc = err as usize;
                }
                Err(Miss::Need(h)) => need!(h),
            },
            Op::EqK { dst, a, k, ne } => {
                regs[dst as usize] = Reg::Bool(eq_k(regs[a as usize], code.konst(k)) != ne)
            }
            Op::CondEqK { a, k, ne, else_ } => {
                if eq_k(regs[a as usize], code.konst(k)) == ne {
                    pc = else_ as usize;
                }
            }
            Op::CondMatch {
                a,
                m,
                invert,
                else_,
                err,
            } => match regs[a as usize] {
                Reg::Str(s) => {
                    if code.matchers[m as usize].matches(s) == invert {
                        pc = else_ as usize;
                    }
                }
                _ => {
                    inflight = Some(ExecutionError::NoSuchOverload);
                    pc = err as usize;
                }
            },
            Op::Cond {
                r,
                invert,
                else_,
                err,
            } => match regs[r as usize] {
                Reg::Bool(b) => {
                    if b == invert {
                        pc = else_ as usize;
                    }
                }
                _ => {
                    inflight = Some(ExecutionError::NoSuchOverload);
                    pc = err as usize;
                }
            },
            Op::CondTagIn {
                f,
                set,
                mask,
                invert,
                else_,
                err,
            } => match host.tag(f, &code.enum_sets[set as usize], st) {
                Ok(t) => {
                    if in_mask(t, mask) == invert {
                        pc = else_ as usize;
                    }
                }
                Err(Miss::Err(e)) => {
                    inflight = Some(e);
                    pc = err as usize;
                }
                Err(Miss::Need(h)) => need!(h),
            },
            Op::RaiseIfErr { r, .. } if matches!(regs[r as usize], Reg::Bool(_)) => {}
            Op::Ret { r } => return Exit::Ret(regs[r as usize]),
            Op::RetK { k } => return Exit::Ret(code.konst(k)),
            _ => match slow(
                op,
                code,
                host,
                regs,
                st,
                iters,
                errs,
                &mut inflight,
                &mut pc,
            ) {
                Flow::Next => {}
                Flow::Ret(r) => return Exit::Ret(r),
                Flow::Fail(e) => return Exit::Fail(e),
                Flow::Need(h) => need!(h),
            },
        }
    }
}

/// What one op did.
enum Flow<'a> {
    Next,
    Ret(Reg<'a>),
    Fail(ExecutionError),
    /// Not answerable yet: the op did nothing, and `pc` is where `exec` left it.
    Need(DemandHandle),
}

/// Every op the hot loop does not handle inline: the rarer, larger ones.
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn slow<'a, H: Host<'a>>(
    op: Op,
    code: &'a Code,
    host: &H,
    regs: &mut [Reg<'a>],
    st: &mut Store<'a>,
    iters: &mut [Iter<'a>],
    errs: &mut Vec<ExecutionError>,
    inflight: &mut Option<ExecutionError>,
    pc: &mut usize,
) -> Flow<'a> {
    macro_rules! fail {
        ($e:expr, $to:expr) => {{
            *inflight = Some($e);
            *pc = $to as usize;
            return Flow::Next;
        }};
    }
    macro_rules! tryr {
        ($e:expr, $to:expr) => {
            match $e {
                Ok(v) => v,
                Err(e) => fail!(e, $to),
            }
        };
    }
    // A host read: a failure goes to the handler, "not yet" pauses the run.
    macro_rules! tryh {
        ($e:expr, $to:expr) => {
            match $e {
                Ok(v) => v,
                Err(Miss::Err(e)) => fail!(e, $to),
                Err(Miss::Need(h)) => return Flow::Need(h),
            }
        };
    }
    // A lazy operand in a run that waits is POLLED, as a host read is: the op answers from the
    // poll, or pauses the run before it has touched anything.
    let waits = host.waits();
    match op {
        Op::Const { dst, k } => regs[dst as usize] = code.konst(k),
        Op::Raise { k, err } => match &code.consts[k as usize] {
            CVal::Err(e) => fail!(e.clone(), err),
            _ => fail!(ExecutionError::InternalError("not an error".into()), err),
        },
        Op::Read { dst, f, want, err } => {
            regs[dst as usize] = tryh!(host.read(f, want, st), err);
        }
        Op::Has { dst, f, err } => regs[dst as usize] = Reg::Bool(tryh!(host.has(f, st), err)),
        Op::Local { dst, src } => regs[dst as usize] = regs[src as usize].borrowed(),
        Op::Own { r } => regs[r as usize] = regs[r as usize].owned(),
        Op::Select { dst, obj, key, err } => {
            let name = &code.names[key as usize];
            if let Some(lazy) = lazy_of(waits, regs[obj as usize]) {
                // `reg::select` on a lazy: `Indexer::get`, an owned answer, held owned.
                regs[dst as usize] = match tryr!(lazy.poll_read(name.inner()), err) {
                    Access::Ready(v) => {
                        reg::of_cow(std::borrow::Cow::Owned(v.into_val()), true, st).owned()
                    }
                    Access::Pending(h) => return Flow::Need(h),
                };
                return Flow::Next;
            }
            let v = reg::select(regs[obj as usize], name, st);
            regs[dst as usize] = tryr!(v, err);
        }
        Op::HasOf { dst, obj, key, err } => {
            let name = &code.names[key as usize];
            if let Some(lazy) = lazy_of(waits, regs[obj as usize]) {
                regs[dst as usize] = match tryr!(lazy.poll_presence(name.inner()), err) {
                    Presence::Known(b) => Reg::Bool(b),
                    Presence::Pending(h) => return Flow::Need(h),
                };
                return Flow::Next;
            }
            let v = reg::has(regs[obj as usize], name);
            regs[dst as usize] = Reg::Bool(tryr!(v, err));
        }
        Op::Index { dst, a, b, err } => {
            if let (Some(lazy), Reg::Str(name)) =
                (lazy_of(waits, regs[a as usize]), regs[b as usize])
            {
                regs[dst as usize] = match tryr!(lazy.poll_read(name), err) {
                    Access::Ready(v) => reg::of_val(st.val(v.into_val()), true),
                    Access::Pending(h) => return Flow::Need(h),
                };
                return Flow::Next;
            }
            let v = reg::index(regs[a as usize], regs[b as usize], st, errs);
            regs[dst as usize] = tryr!(v, err);
        }
        Op::Not { dst, a, err } => match regs[a as usize] {
            Reg::Bool(b) => regs[dst as usize] = Reg::Bool(!b),
            _ => fail!(ExecutionError::NoSuchOverload, err),
        },
        Op::Neg { dst, a, err } => match regs[a as usize] {
            Reg::Num(n) => regs[dst as usize] = Reg::Num(-n),
            _ => fail!(ExecutionError::NoSuchOverload, err),
        },
        Op::Eq { dst, a, b } => {
            regs[dst as usize] = Reg::Bool(reg::equals(regs[a as usize], regs[b as usize]))
        }
        Op::Ne { dst, a, b } => {
            regs[dst as usize] = Reg::Bool(!reg::equals(regs[a as usize], regs[b as usize]))
        }
        Op::Cmp { dst, a, b, op, err } => {
            use std::cmp::Ordering::*;
            let o = tryr!(reg::compare(regs[a as usize], regs[b as usize]), err);
            regs[dst as usize] = Reg::Bool(match op {
                Cmp::Lt => o == Less,
                Cmp::Le => o != Greater,
                Cmp::Gt => o == Greater,
                Cmp::Ge => o != Less,
            });
        }
        Op::Arith { dst, a, b, op, err } => {
            let v = arith(op, regs[a as usize], regs[b as usize], st, errs);
            regs[dst as usize] = tryr!(v, err);
        }
        Op::In { dst, a, b, err } => {
            if let (Reg::Str(name), Some(lazy)) =
                (regs[a as usize], lazy_of(waits, regs[b as usize]))
            {
                regs[dst as usize] = match tryr!(lazy.poll_presence(name), err) {
                    Presence::Known(b) => Reg::Bool(b),
                    Presence::Pending(h) => return Flow::Need(h),
                };
                return Flow::Next;
            }
            let v = reg::contains(regs[a as usize], regs[b as usize]);
            regs[dst as usize] = Reg::Bool(tryr!(v, err));
        }
        Op::Match { dst, a, m, err } => match regs[a as usize] {
            Reg::Str(s) => regs[dst as usize] = Reg::Bool(code.matchers[m as usize].matches(s)),
            _ => fail!(ExecutionError::NoSuchOverload, err),
        },
        Op::StrOp { dst, a, b, op, err } => match (regs[a as usize], regs[b as usize]) {
            (Reg::Str(s), Reg::Str(t)) => {
                regs[dst as usize] = Reg::Bool(match op {
                    StrOp::StartsWith => s.starts_with(t),
                    StrOp::EndsWith => s.ends_with(t),
                    StrOp::Contains => s.contains(t),
                })
            }
            (x, y) => {
                let bad = if matches!(x, Reg::Str(_)) { y } else { x };
                fail!(
                    ExecutionError::UnexpectedType {
                        got: type_name(bad).to_string(),
                        want: "string".to_string(),
                    },
                    err
                )
            }
        },
        Op::Matches { dst, a, b, re, err } => {
            let (Reg::Str(s), Reg::Str(p)) = (regs[a as usize], regs[b as usize]) else {
                fail!(ExecutionError::NoSuchOverload, err)
            };
            let hit = if re == u32::MAX {
                match regex::Regex::new(p) {
                    Ok(r) => r.is_match(s),
                    Err(e) => fail!(
                        ExecutionError::FunctionError {
                            function: "matches".to_string(),
                            message: format!("'{p}' not a valid regex:\n{e}"),
                        },
                        err
                    ),
                }
            } else {
                match &code.regexes[re as usize] {
                    Ok(r) => r.is_match(s),
                    Err(e) => fail!(e.clone(), err),
                }
            };
            regs[dst as usize] = Reg::Bool(hit);
        }
        Op::Size { dst, a, err } => {
            regs[dst as usize] = Reg::Num(tryr!(reg::size(regs[a as usize]), err));
        }
        Op::Duration { dst, a, err } => match regs[a as usize] {
            Reg::Str(s) => match crate::duration::parse_duration(s) {
                Ok((_, d)) => regs[dst as usize] = Reg::Dur(d),
                Err(e) => fail!(
                    ExecutionError::function_error("duration", e.to_string()),
                    err
                ),
            },
            Reg::Dur(d) => regs[dst as usize] = Reg::Dur(d),
            _ => fail!(ExecutionError::NoSuchOverload, err),
        },
        Op::DurPart {
            dst,
            a,
            millis,
            err,
        } => match regs[a as usize] {
            Reg::Dur(d) => {
                regs[dst as usize] = Reg::Num(if millis {
                    d.num_milliseconds() as f64
                } else {
                    d.num_seconds() as f64
                })
            }
            _ => fail!(ExecutionError::NoSuchOverload, err),
        },
        Op::MakeList { dst, start, n } => {
            let items = regs[start as usize..start as usize + n as usize].to_vec();
            regs[dst as usize] = Reg::List(st.regs(items), true);
        }
        Op::CheckKey { r, err } => tryr!(reg::check_key(regs[r as usize]), err),
        Op::MakeMap { dst, start, n } => {
            let mut pairs: Vec<(Reg<'a>, Reg<'a>)> = Vec::with_capacity(n as usize);
            for i in 0..n as usize {
                let k = regs[start as usize + 2 * i];
                let v = regs[start as usize + 2 * i + 1];
                // A repeated key keeps the LAST value, as `HashMap::insert` does.
                match pairs
                    .iter_mut()
                    .find(|(q, _)| reg::key_ref(*q) == reg::key_ref(k))
                {
                    Some(slot) => slot.1 = v,
                    None => pairs.push((k, v)),
                }
            }
            regs[dst as usize] = Reg::Map(st.pairs(pairs), true);
        }
        Op::Jump { to } => *pc = to as usize,
        Op::BrTrue { r, to } => {
            if matches!(regs[r as usize], Reg::Bool(true)) {
                *pc = to as usize;
            }
        }
        Op::BrFalse { r, to } => {
            if matches!(regs[r as usize], Reg::Bool(false)) {
                *pc = to as usize;
            }
        }
        Op::Cond {
            r,
            invert,
            else_,
            err,
        } => match regs[r as usize] {
            Reg::Bool(b) => {
                if b == invert {
                    *pc = else_ as usize;
                }
            }
            _ => fail!(ExecutionError::NoSuchOverload, err),
        },
        Op::EqK { dst, a, k, ne } => {
            regs[dst as usize] = Reg::Bool(eq_k(regs[a as usize], code.konst(k)) != ne)
        }
        Op::CondRead {
            f,
            invert,
            else_,
            err,
        } => match tryh!(host.read(f, Want::Bool, st), err) {
            Reg::Bool(b) => {
                if b == invert {
                    *pc = else_ as usize;
                }
            }
            _ => fail!(ExecutionError::NoSuchOverload, err),
        },
        Op::RaiseIfErr { r, err } => match regs[r as usize] {
            Reg::Bool(_) => {}
            Reg::Err(i) => fail!(errs[i as usize].clone(), err),
            _ => fail!(ExecutionError::NoSuchOverload, err),
        },
        Op::CondEqK { a, k, ne, else_ } => {
            if eq_k(regs[a as usize], code.konst(k)) == ne {
                *pc = else_ as usize;
            }
        }
        Op::CondMatch {
            a,
            m,
            invert,
            else_,
            err,
        } => match regs[a as usize] {
            Reg::Str(s) => {
                if code.matchers[m as usize].matches(s) == invert {
                    *pc = else_ as usize;
                }
            }
            _ => fail!(ExecutionError::NoSuchOverload, err),
        },
        Op::Catch { dst } => {
            errs.push(inflight.take().expect("an error in flight"));
            regs[dst as usize] = Reg::Err((errs.len() - 1) as u32);
        }
        Op::Absorb { dst, a, or, err } => {
            let v = match (regs[a as usize], regs[dst as usize]) {
                // The left operand passed it on (`false` for `||`, `true` for `&&`): the right
                // one is the answer.
                (Reg::Bool(l), Reg::Bool(_)) if l != or => return Flow::Next,
                (Reg::Bool(l), _) if l != or => ExecutionError::NoSuchOverload,
                // An erroring left is absorbed by a deciding right.
                (_, Reg::Bool(r)) if r == or => return Flow::Next,
                (Reg::Err(i), _) => errs[i as usize].clone(),
                _ => ExecutionError::NoSuchOverload,
            };
            fail!(v, err)
        }
        Op::Nsf { dst, a } => {
            regs[dst as usize] = Reg::Bool(match regs[a as usize] {
                Reg::Bool(b) => b,
                _ => true,
            })
        }
        Op::IterInit { slot, src, err } => {
            let it = match regs[src as usize] {
                Reg::List(l, _) => Iter::Regs(l, 0),
                Reg::Map(m, _) => Iter::Pairs(m, 0),
                Reg::Dyn(v, _) => {
                    if let Some(l) = v.downcast_ref::<CelList>() {
                        Iter::Vals(l.inner(), 0)
                    } else if let Some(m) = v.downcast_ref::<CelMap>() {
                        Iter::Keys(m.inner().keys())
                    } else {
                        match v.as_iterable() {
                            Some(it) => Iter::Other(it.iter()),
                            None => fail!(ExecutionError::NoSuchOverload, err),
                        }
                    }
                }
                _ => fail!(ExecutionError::NoSuchOverload, err),
            };
            iters[slot as usize] = it;
        }
        Op::IterNext { slot, dst, exit } => {
            let next = match &mut iters[slot as usize] {
                Iter::Idle => None,
                Iter::Regs(l, i) => l.get(*i).map(|r| {
                    *i += 1;
                    *r
                }),
                Iter::Pairs(m, i) => m.get(*i).map(|(k, _)| {
                    *i += 1;
                    *k
                }),
                Iter::Vals(l, i) => l.get(*i).map(|v| {
                    *i += 1;
                    reg::of_val(v.as_ref(), false)
                }),
                Iter::Keys(ks) => ks.next().map(|k| reg::of_val(k.inner(), false)),
                Iter::Other(it) => it.next().map(|v| reg::of_val(v, false)),
            };
            match next {
                Some(r) => regs[dst as usize] = r,
                None => {
                    iters[slot as usize] = Iter::Idle;
                    *pc = exit as usize;
                }
            }
        }
        Op::BrPending { r, to } => {
            if matches!(regs[r as usize], Reg::Err(_)) {
                *pc = to as usize;
            }
        }
        Op::Clear { r } => regs[r as usize] = Reg::Unset,
        Op::Step {
            accu,
            step,
            pend,
            absorb,
        } => {
            let s = regs[step as usize];
            let absorbs = match (absorb, s) {
                (Absorb::OnFalse, Reg::Bool(false)) | (Absorb::OnTrue, Reg::Bool(true)) => true,
                _ => false,
            };
            if absorbs {
                regs[pend as usize] = Reg::Unset;
            }
            regs[accu as usize] = s;
        }
        Op::CatchPending { pend } => {
            let e = inflight.take().expect("an error in flight");
            // The FIRST error is the one reported.
            if !matches!(regs[pend as usize], Reg::Err(_)) {
                errs.push(e);
                regs[pend as usize] = Reg::Err((errs.len() - 1) as u32);
            }
        }
        Op::RaisePending { pend, err } => {
            if let Reg::Err(i) = regs[pend as usize] {
                fail!(errs[i as usize].clone(), err);
            }
        }
        Op::TagIn {
            dst,
            f,
            set,
            mask,
            ne,
            err,
        } => {
            let t = tryh!(host.tag(f, &code.enum_sets[set as usize], st), err);
            regs[dst as usize] = Reg::Bool(in_mask(t, mask) != ne);
        }
        Op::CondTagIn {
            f,
            set,
            mask,
            invert,
            else_,
            err,
        } => {
            let t = tryh!(host.tag(f, &code.enum_sets[set as usize], st), err);
            if in_mask(t, mask) == invert {
                *pc = else_ as usize;
            }
        }
        Op::Host {
            dst,
            start,
            n,
            h,
            err,
        } => {
            let entry = &code.hosts.entries[h as usize];
            let mut args = Vec::with_capacity(n as usize);
            for i in 0..n as usize {
                match host_arg(regs[start as usize + i], errs) {
                    Some(v) => args.push(v),
                    None => fail!(
                        crate::hostfn::failure(&entry.name, "argument has no CelValue form"),
                        err
                    ),
                }
            }
            let out = match &entry.imp {
                crate::hostfn::HostImpl::Closure(call) => call(&args),
                crate::hostfn::HostImpl::PerCall => host.call_host(&entry.name, &args),
            };
            let out = tryr!(out.map_err(|e| crate::hostfn::failure(&entry.name, e)), err);
            regs[dst as usize] = match out {
                crate::CelValue::Bool(b) => Reg::Bool(b),
                crate::CelValue::Num(x) => Reg::Num(x),
                crate::CelValue::Null => Reg::Null,
                crate::CelValue::Str(x) => Reg::Str(st.str(x)),
                crate::CelValue::Bytes(x) => Reg::Bytes(st.bytes(x)),
                crate::CelValue::Duration(ms) => Reg::Dur(chrono::Duration::milliseconds(ms)),
                // A CALL host's record, read by member.
                lazy @ crate::CelValue::Lazy(_)
                    if matches!(entry.imp, crate::hostfn::HostImpl::PerCall) =>
                {
                    reg::of_val(st.val(lazy.into_val()), true)
                }
                crate::CelValue::Lazy(_) => fail!(
                    crate::hostfn::failure(&entry.name, "a host function returned a lazy value"),
                    err
                ),
                // A composite, owned, as the evaluator holds a function's result.
                composite => reg::of_val(st.val(composite.into_val()), true),
            };
        }
        Op::Ret { r } => return Flow::Ret(regs[r as usize]),
        Op::RetK { k } => return Flow::Ret(code.konst(k)),
        Op::Fail => return Flow::Fail(inflight.take().expect("an error in flight")),
    }
    Flow::Next
}

/// The lazy a register holds, for a run that waits; `None` otherwise, so the op takes its usual
/// path — which is also the evaluator's, "not yet" read as an error.
fn lazy_of<'a>(waits: bool, r: Reg<'a>) -> Option<&'a LazyAdapter> {
    match r {
        Reg::Dyn(v, _) if waits => v.downcast_ref::<LazyAdapter>(),
        _ => None,
    }
}

/// Is tag `t` one of `mask`'s bits? `TAG_OTHER` (and any tag past the mask) is in none.
#[inline(always)]
fn in_mask(t: u8, mask: u64) -> bool {
    t < 64 && mask >> t & 1 == 1
}

/// A register as a host function's argument: a lazy view is the view itself, a string is copied
/// out, anything else converts through the boundary value. `None` for a value with no `CelValue`
/// spelling.
fn host_arg(r: Reg<'_>, errs: &[ExecutionError]) -> Option<crate::CelValue> {
    match r {
        Reg::Bool(b) => Some(crate::CelValue::Bool(b)),
        Reg::Num(x) => Some(crate::CelValue::Num(x)),
        Reg::Str(x) => Some(crate::CelValue::Str(x.to_string())),
        Reg::Null => Some(crate::CelValue::Null),
        Reg::Dyn(v, _) if v.downcast_ref::<LazyAdapter>().is_some() => {
            let lazy = v.downcast_ref::<LazyAdapter>()?;
            Some(crate::CelValue::Lazy(Arc::clone(&lazy.0)))
        }
        other => crate::CelValue::from_value(&reg::to_value(other, errs).ok()?),
    }
}

/// `a == k` for a scalar constant `k`, with the string case — a tag, an enum value — inline.
#[inline(always)]
fn eq_k(a: Reg<'_>, k: Reg<'_>) -> bool {
    match (a, k) {
        (Reg::Str(x), Reg::Str(y)) => x == y,
        (Reg::Bool(x), Reg::Bool(y)) => x == y,
        (Reg::Num(x), Reg::Num(y)) => x == y,
        _ => reg::equals(a, k),
    }
}

/// `+ - * /`: the absorbed model's `Adder`, `Subtractor`, `Multiplier`, `Divider`.
fn arith<'a>(
    op: Arith,
    a: Reg<'a>,
    b: Reg<'a>,
    st: &mut Store<'a>,
    errs: &[ExecutionError],
) -> Result<Reg<'a>, ExecutionError> {
    let unsupported = |name: &'static str| {
        ExecutionError::UnsupportedBinaryOperator(
            name,
            reg::to_value(a, errs).unwrap_or(Value::Null),
            reg::to_value(b, errs).unwrap_or(Value::Null),
        )
    };
    Ok(match (op, a, b) {
        (Arith::Add, Reg::Num(x), Reg::Num(y)) => Reg::Num(x + y),
        (Arith::Sub, Reg::Num(x), Reg::Num(y)) => Reg::Num(x - y),
        (Arith::Mul, Reg::Num(x), Reg::Num(y)) => Reg::Num(x * y),
        (Arith::Div, Reg::Num(x), Reg::Num(y)) => Reg::Num(x / y),
        (Arith::Add, Reg::Str(x), Reg::Str(y)) => {
            let mut s = String::with_capacity(x.len() + y.len());
            s.push_str(x);
            s.push_str(y);
            Reg::Str(st.str(s))
        }
        (Arith::Add, Reg::Dur(x), Reg::Dur(y)) => Reg::Dur(
            x.checked_add(&y)
                .filter(crate::duration::in_cel_range)
                .ok_or(ExecutionError::Overflow("add", Value::Null, Value::Null))?,
        ),
        (Arith::Sub, Reg::Dur(x), Reg::Dur(y)) => Reg::Dur(
            x.checked_sub(&y)
                .filter(crate::duration::in_cel_range)
                .ok_or(ExecutionError::Overflow("sub", Value::Null, Value::Null))?,
        ),
        (Arith::Add, _, _) => match (reg::elements(a), reg::elements(b)) {
            (Some(mut x), Some(y)) => {
                x.extend(y);
                Reg::List(st.regs(x), true)
            }
            _ => return Err(unsupported("add")),
        },
        (Arith::Sub, ..) => return Err(unsupported("sub")),
        (Arith::Mul, ..) => return Err(unsupported("mul")),
        (Arith::Div, ..) => return Err(unsupported("div")),
    })
}

fn type_name(r: Reg<'_>) -> &'static str {
    match r {
        Reg::Bool(_) => "bool",
        Reg::Num(_) => "double",
        Reg::Str(_) => "string",
        Reg::Bytes(_) => "bytes",
        Reg::Null => "null_type",
        Reg::Dur(_) => "google.protobuf.Duration",
        Reg::List(..) => "list",
        Reg::Map(..) => "map",
        _ => "dyn",
    }
}

// ---- a run that waits ----

/// A run that can pause: `(pc, registers, arena)` and the rest of what `exec` holds, OWNED, so it
/// outlives the call that paused it and moves between threads with whatever holds it.
///
/// Every reference a paused run keeps points into its own `store` or into the constant pool of the
/// program it runs — never into the host's data, which is copied in at the pause (`rehome`), and
/// only at a pause: the path that never pauses copies nothing. So a `Paused` is only ever resumed
/// on the program that paused it, and whatever holds one holds that program too (`VmRun`,
/// `StreamedRun`).
pub(crate) struct Paused {
    pc: usize,
    regs: Vec<Reg<'static>>,
    store: Store<'static>,
    iters: Vec<Held<'static>>,
    errs: Vec<ExecutionError>,
    inflight: Option<ExecutionError>,
}

impl std::fmt::Debug for Paused {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Paused")
            .field("pc", &self.pc)
            .field("live", &self.live())
            .finish_non_exhaustive()
    }
}

/// A comprehension's iteration, as a paused run holds it: over its own copy of what was left, or
/// over a list in the program's constant pool.
enum Held<'a> {
    Idle,
    Regs(&'a [Reg<'a>], usize),
    Vals(&'a [Box<dyn Val>], usize),
}

impl Paused {
    /// A run that has not started.
    pub(crate) fn start() -> Paused {
        Paused {
            pc: 0,
            regs: Vec::new(),
            store: Store::default(),
            iters: Vec::new(),
            errs: Vec::new(),
            inflight: None,
        }
    }

    /// The op this run executes next.
    pub(crate) fn pc(&self) -> usize {
        self.pc
    }

    /// How many registers hold a value.
    pub(crate) fn live(&self) -> usize {
        self.regs
            .iter()
            .filter(|r| !matches!(r, Reg::Unset))
            .count()
    }
}

/// What [`FastProgram::resume`] came back with.
pub(crate) enum Resumed {
    /// The verdict, worded as [`CelProgram::evaluate`](crate::CelProgram::evaluate) words it.
    Done(Result<bool, crate::CelError>),
    /// A read is not answerable yet; the run is held here until it is.
    Need(DemandHandle, Paused),
}

impl Code {
    /// Is `v` one of this program's constants (so a paused run may keep pointing at it)?
    fn holds(&self, v: &dyn Val) -> bool {
        self.consts.iter().any(|c| match c {
            CVal::Dyn(b, _) => std::ptr::addr_eq(&**b as *const dyn Val, v as *const dyn Val),
            _ => false,
        })
    }

    /// Is `l` the elements of one of this program's constant lists?
    fn holds_list(&self, l: &[Box<dyn Val>]) -> bool {
        self.consts.iter().any(|c| match c {
            CVal::Dyn(b, _) => b
                .downcast_ref::<CelList>()
                .is_some_and(|x| std::ptr::eq(x.inner().as_ptr(), l.as_ptr())),
            _ => false,
        })
    }
}

/// `r`, pointing only into `out` and `code`: whatever it borrows from anywhere else — the host's
/// data, the store of the call that is ending — is copied into `out`.
fn rehome<'a>(r: Reg<'a>, code: &'a Code, out: &mut Store<'a>) -> Reg<'a> {
    match r {
        Reg::Str(s) => Reg::Str(out.str(s.to_string())),
        Reg::Bytes(b) => Reg::Bytes(out.bytes(b.to_vec())),
        Reg::Dyn(v, _) if code.holds(v) => r,
        Reg::Dyn(v, owned) => Reg::Dyn(out.val(v.clone_as_boxed()), owned),
        Reg::List(l, owned) => {
            let items = l.iter().map(|x| rehome(*x, code, out)).collect();
            Reg::List(out.regs(items), owned)
        }
        Reg::Map(m, owned) => {
            let pairs = m
                .iter()
                .map(|(k, v)| (rehome(*k, code, out), rehome(*v, code, out)))
                .collect();
            Reg::Map(out.pairs(pairs), owned)
        }
        Reg::Unset | Reg::Bool(_) | Reg::Num(_) | Reg::Null | Reg::Dur(_) | Reg::Err(_) => r,
    }
}

/// An iteration in flight, as a paused run holds it: what is left of it, in `out`.
fn hold<'a>(it: Iter<'a>, code: &'a Code, out: &mut Store<'a>) -> Held<'a> {
    let rest: Vec<Reg<'a>> = match it {
        Iter::Idle => return Held::Idle,
        Iter::Vals(l, i) if code.holds_list(l) => return Held::Vals(l, i),
        Iter::Regs(l, i) => l[i..].to_vec(),
        Iter::Pairs(m, i) => m[i..].iter().map(|(k, _)| *k).collect(),
        Iter::Vals(l, i) => l[i..]
            .iter()
            .map(|v| reg::of_val(v.as_ref(), false))
            .collect(),
        Iter::Keys(ks) => ks.map(|k| reg::of_val(k.inner(), false)).collect(),
        Iter::Other(mut it) => {
            let mut rest = Vec::new();
            while let Some(v) = it.next() {
                rest.push(reg::of_val(v, false));
            }
            rest
        }
    };
    let rest = rest.into_iter().map(|r| rehome(r, code, out)).collect();
    Held::Regs(out.regs(rest), 0)
}

impl<'a> Held<'a> {
    fn resume(self) -> Iter<'a> {
        match self {
            Held::Idle => Iter::Idle,
            Held::Regs(l, i) => Iter::Regs(l, i),
            Held::Vals(l, i) => Iter::Vals(l, i),
        }
    }
}

impl FastProgram {
    /// Run `p` on until it finishes or a read is not answerable yet. The roots are `ctx`'s,
    /// except the fields `facts` marks, which its provider answers.
    ///
    /// A pause leaves `pc` on the read that asked, so the next resume executes that read again and
    /// nothing before it.
    pub(crate) fn resume<F: Facts + ?Sized>(
        &self,
        p: Paused,
        ctx: &Context,
        facts: Option<(&F, &[bool])>,
    ) -> Resumed {
        let ctx = CtxHost {
            ctx,
            fields: &self.code.fields,
            wait: true,
        };
        match facts {
            Some((facts, mine)) => self.resume_on(
                p,
                &SplitHost {
                    facts: FactsHost {
                        facts,
                        fields: &self.code.fields,
                        wait: true,
                    },
                    ctx,
                    mine,
                },
            ),
            None => self.resume_on(p, &ctx),
        }
    }

    fn resume_on<'a, H: Host<'a>>(&'a self, p: Paused, host: &H) -> Resumed {
        let code = &self.code;
        let Paused {
            pc,
            regs,
            store,
            iters,
            mut errs,
            inflight,
        } = p;
        // `Reg` and `Store` are covariant: what lives for the paused run lives for this call.
        let mut regs: Vec<Reg<'a>> = regs;
        let mut store: Store<'a> = store;
        regs.resize(code.nregs, Reg::Unset);
        let mut iters: Vec<Iter<'a>> = iters.into_iter().map(Held::resume).collect();
        iters.resize_with(code.nloops, || Iter::Idle);
        let exit = exec(
            code, host, &mut regs, &mut store, &mut iters, &mut errs, pc, inflight,
        );
        match exit {
            Exit::Ret(r) => Resumed::Done(verdict(&self.source, Ok(as_bool(r, &errs)))),
            Exit::Fail(e) => Resumed::Done(verdict(&self.source, Err(e))),
            Exit::Need {
                handle,
                pc,
                inflight,
            } => {
                let mut fresh: Store<'a> = Store::default();
                let regs: Vec<Reg<'a>> =
                    regs.iter().map(|r| rehome(*r, code, &mut fresh)).collect();
                let iters: Vec<Held<'a>> = iters
                    .into_iter()
                    .map(|it| hold(it, code, &mut fresh))
                    .collect();
                // Nothing refers to the call's store any more: every register and iteration now
                // points into `fresh` or into `code`.
                drop(store);
                // SAFETY: every reference in `regs` and `iters` points into `fresh`'s boxes, which
                // move with it and are dropped with it, or into `self.code`'s constants, which
                // outlive the `Paused` because whatever holds one holds this program (see
                // `Paused`). The types differ only in lifetimes.
                let paused = unsafe {
                    Paused {
                        pc,
                        regs: std::mem::transmute::<Vec<Reg<'a>>, Vec<Reg<'static>>>(regs),
                        store: std::mem::transmute::<Store<'a>, Store<'static>>(fresh),
                        iters: std::mem::transmute::<Vec<Held<'a>>, Vec<Held<'static>>>(iters),
                        errs,
                        inflight,
                    }
                };
                Resumed::Need(handle, paused)
            }
        }
    }

    /// Per field: does the program read its VALUE (not only whether it is present)?
    pub(crate) fn value_reads(&self) -> Vec<bool> {
        let mut out = vec![false; self.code.fields.len()];
        for op in &self.code.ops {
            if let Op::Read { f, .. }
            | Op::CondRead { f, .. }
            | Op::TagIn { f, .. }
            | Op::CondTagIn { f, .. } = op
            {
                out[*f as usize] = true;
            }
        }
        out
    }
}

/// The node kinds of a checked program, by expression id.
pub(crate) type Kinds = HashMap<u64, Kind>;

/// The fast backend's run over an evaluator context: the boundary value, as `Program::execute`
/// returns it. For the crate's own harnesses.
#[cfg(feature = "conformance")]
pub(crate) fn run_value(p: &FastProgram, ctx: &Context) -> Result<Value, ExecutionError> {
    p.eval_value(ctx)
}
