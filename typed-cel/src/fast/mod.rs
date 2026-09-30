//! The engine: a register machine over unboxed values, reading host data by field.
//!
//! A CHECKED program is lowered once (`lower.rs`) and run by `exec`. There is no other engine and no
//! fallback: a program the checker admitted lowers, or `FastProgram::new` refuses it as a defect.
//!
//! The semantics, which every op and every lowering follows:
//! - Evaluation order is left to right; a member call's arguments run before its target.
//! - `a || b`, `a && b`: an error on the left is caught and the right side still runs; an absorbing
//!   value (`true` for `||`, `false` for `&&`) on EITHER side decides; otherwise an error propagates,
//!   and when both sides failed it is the RIGHT side's.
//! - `c ? a : b` runs only the chosen branch; an error in `c` propagates.
//! - A comprehension keeps its FIRST pending step error; an absorbing accumulator clears it.
//! - A map literal checks each key before its value runs; a later duplicate key wins.
//! - Indexing: a list by an integral in-range number, else `IndexOutOfBounds`; a map by a key of its
//!   key type, else `NoSuchKey` — including a number that names no key (`1.5`).
//! - Numbers are IEEE doubles: `1 / 0` is `+inf`, there is no integer overflow and no `%`.
//! Error TEXT is part of the contract (callers render it); `tests/backend_edges.rs` and
//! `tests/generated_golden.rs` pin it.
//!
//! This file names only the absorbed value model, the lazy seam and `fast`'s own modules — never
//! the parser or the checker.

mod host;
mod lower;
#[doc(hidden)]
pub use lower::with_literal_comprehensions;
pub use scan::with_unfused_loops;
mod matcher;
#[cfg(feature = "profile")]
pub mod profile;
mod reg;
mod scan;

use std::collections::HashMap;
use std::sync::Arc;

use crate::bindings::Bindings;
use crate::num::{CelNum, NumOp};
use crate::CelValue;
use crate::ExecutionError;
use crate::{CelKey, CelMapKey};

use crate::lazy::{self, Access, DemandHandle, LazyValue, Presence};

use host::{Dispatching, FactsHost, Host, Miss, RootsHost, SplitHost, Want};
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

impl Arith {
    /// Over two doubles: IEEE, so a zero divisor is an infinity or a NaN, never an error; the
    /// result canonical, so `1.5 + 1.5` is the integer `3`.
    #[inline(always)]
    pub(crate) fn float(self, x: f64, y: f64) -> Reg<'static> {
        Reg::from(CelNum::from_f64(match self {
            Arith::Add => x + y,
            Arith::Sub => x - y,
            Arith::Mul => x * y,
            Arith::Div => x / y,
        }))
    }

    /// Over two `i64`s, as [`Arith::num`] answers, where that is cheap: `None` sends it there (a
    /// result past `i64`, which is a `u64` or an overflow). A quotient is real division: exact
    /// when it divides, else a double, and a zero divisor IEEE's infinity or NaN.
    #[inline(always)]
    pub(crate) fn int(self, x: i64, y: i64) -> Option<Reg<'static>> {
        match self {
            Arith::Add => x.checked_add(y).map(Reg::Int),
            Arith::Sub => x.checked_sub(y).map(Reg::Int),
            Arith::Mul => x.checked_mul(y).map(Reg::Int),
            Arith::Div if y == 0 => Some(Reg::Num(x as f64 / 0.0)),
            Arith::Div => match x.checked_rem(y) {
                Some(0) => x.checked_div(y).map(Reg::Int),
                Some(_) => Some(Reg::Num(x as f64 / y as f64)),
                // `i64::MIN / -1` is `2^63`, a `u64`.
                None => None,
            },
        }
    }

    /// Over any two numbers, exactly (`crate::num::arith`); overflow is an error naming both.
    pub(crate) fn num(self, x: CelNum, y: CelNum) -> Result<CelNum, ExecutionError> {
        let op = match self {
            Arith::Add => NumOp::Add,
            Arith::Sub => NumOp::Sub,
            Arith::Mul => NumOp::Mul,
            Arith::Div => NumOp::Div,
        };
        crate::num::arith(op, x, y)
            .map_err(|_| ExecutionError::Overflow(op.name(), x.into(), y.into()))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StrOp {
    StartsWith,
    EndsWith,
    Contains,
}

/// What [`Op::CondFR`] asks of its register `a` and its field's value `v`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FieldTest {
    /// `a == v`, or `a != v` when `ne`: never fails.
    Eq { ne: bool },
    /// `a <op> v`: an unordered pair fails as `Cmp` does.
    Cmp(Cmp),
    /// `v.op(a)`: the field is the receiver (`req.path.startsWith(r)`).
    FieldRecv(StrOp),
    /// `a.op(v)`: the register is the receiver (`s.startsWith(req.p)`).
    RegRecv(StrOp),
}

/// What [`Op::StrOp2`] asks of `a` and the concatenation `b + c`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Concat {
    /// `a.startsWith(b + c)`
    Prefix,
    /// `a.endsWith(b + c)`
    Suffix,
    /// `a == b + c`
    Eq,
    /// `a != b + c`
    Ne,
    /// `(b + c).startsWith(a)`
    StartsWith,
    /// `(b + c).endsWith(a)`
    EndsWith,
}

impl Concat {
    /// The answer, from the pieces. Every slice is at a boundary a `starts_with` / `ends_with`
    /// just matched, so it is a char boundary.
    fn test(self, a: &str, b: &str, c: &str) -> bool {
        match self {
            Concat::Prefix => a.starts_with(b) && a[b.len()..].starts_with(c),
            Concat::Suffix => a.ends_with(c) && a[..a.len() - c.len()].ends_with(b),
            Concat::Eq => a.len() == b.len() + c.len() && a.starts_with(b) && a.ends_with(c),
            Concat::Ne => !Concat::Eq.test(a, b, c),
            Concat::StartsWith if a.len() <= b.len() => b.starts_with(a),
            Concat::StartsWith => a.starts_with(b) && c.starts_with(&a[b.len()..]),
            Concat::EndsWith if a.len() <= c.len() => c.ends_with(a),
            Concat::EndsWith => a.ends_with(c) && b.ends_with(&a[..a.len() - c.len()]),
        }
    }
}

impl Cmp {
    /// The operator with its operands swapped: `a < b` is `b > a`.
    pub(crate) fn flip(self) -> Cmp {
        match self {
            Cmp::Lt => Cmp::Gt,
            Cmp::Le => Cmp::Ge,
            Cmp::Gt => Cmp::Lt,
            Cmp::Ge => Cmp::Le,
        }
    }

    /// Does the operator hold for operands in order `o`?
    #[inline(always)]
    fn holds(self, o: std::cmp::Ordering) -> bool {
        use std::cmp::Ordering::*;
        match self {
            Cmp::Lt => o == Less,
            Cmp::Le => o != Greater,
            Cmp::Gt => o == Greater,
            Cmp::Ge => o != Less,
        }
    }
}

impl StrOp {
    #[inline(always)]
    fn test(self, s: &str, t: &str) -> bool {
        match self {
            StrOp::StartsWith => s.starts_with(t),
            StrOp::EndsWith => s.ends_with(t),
            StrOp::Contains => s.contains(t),
        }
    }
}

/// Which accumulator settles a comprehension step and clears a pending error.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Absorb {
    Never,
    OnFalse,
    OnTrue,
}

impl Absorb {
    /// Does a step answering `s` settle the accumulator (and so clear a pending error)?
    #[inline(always)]
    fn absorbs(self, s: Reg<'_>) -> bool {
        matches!(
            (self, s),
            (Absorb::OnFalse, Reg::Bool(false)) | (Absorb::OnTrue, Reg::Bool(true))
        )
    }
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
    /// Read a comprehension variable.
    Local {
        dst: R,
        src: R,
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
    /// `a[b]` where `b` is the key loop slot `slot` over map `a` stands on — the only computed key
    /// the checker admits (`m.all(k, m[k] > 0.0)`) — so the entry is the iteration's current one:
    /// no lookup. A lazy map, or anything unexpected, is `Index` in `slow`.
    IndexIter {
        dst: R,
        a: R,
        b: R,
        slot: u16,
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
    /// `a op k` — or `k op a` when `rev` — for a constant `k`: `Arith` without loading `k` into a
    /// register first.
    ArithK {
        dst: R,
        a: R,
        k: u32,
        op: Arith,
        rev: bool,
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
    /// A string test against a two-piece concatenation `b + c`, which is never built (`Concat`).
    StrOp2 {
        dst: R,
        a: R,
        b: R,
        c: R,
        op: Concat,
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
    /// `a.matches(p)` for a literal pattern `p` compiled into `regexes[re]`, as a branch: jump to
    /// `else_` when the answer is `invert`. A non-string, or the pattern's compile error, fails
    /// to `err` as `Matches` does.
    CondMatches {
        a: R,
        re: u32,
        invert: bool,
        else_: Pc,
        err: Pc,
    },
    /// `f.op(b + k)` — `StrOp2` with a string field `f` (through its cache register, unless
    /// `cache` is [`NO_CACHE`]) as the tested operand, a register `b` and a string constant `k`
    /// as the pieces — and a branch on it: jump to `else_` when the answer is `invert`.
    CondStrOp2F {
        f: u32,
        cache: R,
        b: R,
        k: u32,
        op: Concat,
        invert: bool,
        else_: Pc,
        err: Pc,
    },
    /// `field(a) == field(b)` for two string fields, in a branch: jumps to `else_` when the
    /// equality is `ne` (so `ne` folds `!=` and the branch's sense together). A read that fails
    /// jumps to `err` with its error in flight; `a` is read first, as the unfused reads were.
    CondEqFF {
        a: u32,
        b: u32,
        ne: bool,
        else_: Pc,
        err: Pc,
    },
    /// `field(a) == k` for a string field and a scalar constant, in a branch, likewise.
    CondEqFK {
        a: u32,
        k: u32,
        ne: bool,
        else_: Pc,
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
    /// `a || b` / `a && b` once `a` did not decide it and `b` is in `dst`: an erroring `a` is
    /// absorbed by a deciding `b`, and raised otherwise.
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
    /// Start iterating `src` in slot `slot`, and reset `clear` (the loop's pending error) unless
    /// it is [`NO_REG`].
    IterInit {
        slot: u16,
        src: R,
        clear: R,
        err: Pc,
    },
    /// The next element of slot `slot` into `dst` — and `clear` reset, unless it is [`NO_REG`]:
    /// a per-element pending error (`logic_chain`'s) folded into the fetch — or, past the last,
    /// to `exit`: unless `pend` (not [`NO_REG`]) holds the loop's pending error, which is raised
    /// to `err` instead (`RaisePending`, folded into the fetch that ends the loop).
    IterNext {
        slot: u16,
        dst: R,
        clear: R,
        pend: R,
        exit: Pc,
        err: Pc,
    },
    /// `IterNext`, having first passed over every element the loop's body would pass over — its
    /// region, `scans[scan]` — so the element it fetches is the first it cannot vouch for
    /// (`src/fast/scan.rs`). Lowering emits it for a predicate loop with `scan: SCAN_WANTED`, and
    /// `scan::fuse` gives it its region or makes it an `IterNext`.
    IterScan {
        slot: u16,
        dst: R,
        clear: R,
        pend: R,
        exit: Pc,
        err: Pc,
        scan: u16,
    },
    BrPending {
        r: R,
        to: Pc,
    },
    Clear {
        r: R,
    },
    /// `regs[r] += 1`: an `exists_one` loop's count, a number from its `Const 0`.
    Inc {
        r: R,
    },
    /// A field (through its cache register, unless `cache` is [`NO_CACHE`]) compared with a
    /// constant, as a branch: jump to `else_` when `field op k` is `invert`. A failed read, or
    /// operands `reg::compare` does not order (a NaN among them), fail to `err`, as `Cmp` does.
    CondCmpFK {
        f: u32,
        cache: R,
        want: Want,
        k: u32,
        op: Cmp,
        invert: bool,
        else_: Pc,
        err: Pc,
    },
    /// Register `a` tested against a field (through its cache register, unless `cache` is
    /// [`NO_CACHE`]), as a branch: jump to `else_` when the test is `invert`. A failed read, or a
    /// test the unfused ops would refuse, fails to `err` with their error.
    CondFR {
        a: R,
        f: u32,
        cache: R,
        want: Want,
        test: FieldTest,
        invert: bool,
        else_: Pc,
        err: Pc,
    },
    /// `a op k` for a constant `k`, as a branch: `CondEqK`'s ordering twin. Operands
    /// `reg::compare` does not order fail to `err`, as `Cmp` does.
    CondCmpK {
        a: R,
        k: u32,
        op: Cmp,
        invert: bool,
        else_: Pc,
        err: Pc,
    },
    /// `Read`, of a field the program reads more than once: the first read fills `cache`, which
    /// every later one copies. A field's value cannot change during a run; a failed read fills
    /// nothing, so reading the field again fails again, where and as it did.
    ReadCached {
        dst: R,
        f: u32,
        cache: R,
        want: Want,
        err: Pc,
    },
    /// Start the list a `map` / `filter` loop builds in slot `slot`, sized for `hint`'s length
    /// when it is a list or map.
    ListNew {
        slot: u16,
        hint: R,
    },
    /// Push `regs[src]` onto slot `slot`'s list, in place.
    Append {
        slot: u16,
        src: R,
    },
    /// The built list, moved into the store as it is: `regs[dst]`.
    ListFreeze {
        slot: u16,
        dst: R,
    },
    /// `regs[a]` is a number in `numsets[set]` — `==` against each, so anything else is not.
    NumIn {
        dst: R,
        a: R,
        set: u32,
    },
    /// Jump when `regs[r]` holds a value: a loop-invariant comprehension already computed.
    BrSet {
        r: R,
        to: Pc,
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
    /// member): `hostfn::HostTable`'s entry.
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
    /// here, and `tests/backend_generated.rs::the_generators_reach_every_op` compares what the
    /// generators lower to against these names.
    pub(crate) fn name(&self) -> &'static str {
        use Op::*;
        match self {
            Const { .. } => "Const",
            Raise { .. } => "Raise",
            Read { .. } => "Read",
            Has { .. } => "Has",
            Local { .. } => "Local",
            Select { .. } => "Select",
            HasOf { .. } => "HasOf",
            Index { .. } => "Index",
            Not { .. } => "Not",
            Neg { .. } => "Neg",
            Eq { .. } => "Eq",
            Ne { .. } => "Ne",
            Cmp { .. } => "Cmp",
            ArithK { .. } => "ArithK",
            Arith { .. } => "Arith",
            In { .. } => "In",
            Match { .. } => "Match",
            StrOp { .. } => "StrOp",
            StrOp2 { .. } => "StrOp2",
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
            CondEqFF { .. } => "CondEqFF",
            CondEqFK { .. } => "CondEqFK",
            EqK { .. } => "EqK",
            Catch { .. } => "Catch",
            Absorb { .. } => "Absorb",
            Nsf { .. } => "Nsf",
            IterInit { .. } => "IterInit",
            IterNext { .. } => "IterNext",
            IterScan { .. } => "IterScan",
            IndexIter { .. } => "IndexIter",
            BrPending { .. } => "BrPending",
            Clear { .. } => "Clear",
            Inc { .. } => "Inc",
            BrSet { .. } => "BrSet",
            NumIn { .. } => "NumIn",
            ListNew { .. } => "ListNew",
            Append { .. } => "Append",
            ListFreeze { .. } => "ListFreeze",
            ReadCached { .. } => "ReadCached",
            CondCmpFK { .. } => "CondCmpFK",
            CondFR { .. } => "CondFR",
            CondMatches { .. } => "CondMatches",
            CondStrOp2F { .. } => "CondStrOp2F",
            CondCmpK { .. } => "CondCmpK",
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

    /// Every single register the op names — the bases of `MakeList`'s, `MakeMap`'s and `Host`'s
    /// ranges excepted, which only `slow` reads, bounds-checked — and its iterator slot. A
    /// `cache`, `clear` or `pend` that is [`NO_REG`] names none: `exec` tests for it before
    /// reading one.
    fn operands(&self, reg: &mut impl FnMut(R), slot: &mut impl FnMut(u16)) {
        use Op::*;
        let mut opt = |r: R| {
            if r != NO_REG {
                reg(r)
            }
        };
        match *self {
            Const { dst, .. }
            | Read { dst, .. }
            | Has { dst, .. }
            | Catch { dst }
            | MakeList { dst, .. }
            | MakeMap { dst, .. }
            | Host { dst, .. }
            | TagIn { dst, .. } => opt(dst),
            Local { dst, src: a }
            | Select { dst, obj: a, .. }
            | HasOf { dst, obj: a, .. }
            | Not { dst, a, .. }
            | Neg { dst, a, .. }
            | ArithK { dst, a, .. }
            | Match { dst, a, .. }
            | Size { dst, a, .. }
            | Duration { dst, a, .. }
            | DurPart { dst, a, .. }
            | EqK { dst, a, .. }
            | Absorb { dst, a, .. }
            | Nsf { dst, a }
            | NumIn { dst, a, .. } => {
                opt(dst);
                opt(a);
            }
            Index { dst, a, b, .. }
            | Eq { dst, a, b }
            | Ne { dst, a, b }
            | Cmp { dst, a, b, .. }
            | Arith { dst, a, b, .. }
            | In { dst, a, b, .. }
            | StrOp { dst, a, b, .. }
            | Matches { dst, a, b, .. } => {
                opt(dst);
                opt(a);
                opt(b);
            }
            IndexIter {
                dst, a, b, slot: s, ..
            } => {
                opt(dst);
                opt(a);
                opt(b);
                slot(s);
            }
            StrOp2 { dst, a, b, c, .. } => {
                opt(dst);
                opt(a);
                opt(b);
                opt(c);
            }
            CheckKey { r, .. }
            | BrTrue { r, .. }
            | BrFalse { r, .. }
            | Cond { r, .. }
            | BrPending { r, .. }
            | Clear { r }
            | Inc { r }
            | BrSet { r, .. }
            | Ret { r } => opt(r),
            CondEqK { a, .. }
            | CondMatch { a, .. }
            | CondMatches { a, .. }
            | CondCmpK { a, .. } => opt(a),
            CondStrOp2F { cache, b, .. } => {
                opt(cache);
                opt(b);
            }
            CondCmpFK { cache, .. } => opt(cache),
            CondFR { a, cache, .. } => {
                opt(a);
                opt(cache);
            }
            ReadCached { dst, cache, .. } => {
                opt(dst);
                opt(cache);
            }
            IterInit {
                slot: s,
                src,
                clear,
                ..
            } => {
                opt(src);
                opt(clear);
                slot(s);
            }
            IterNext {
                slot: s,
                dst,
                clear,
                pend,
                ..
            }
            | IterScan {
                slot: s,
                dst,
                clear,
                pend,
                ..
            } => {
                opt(dst);
                opt(clear);
                opt(pend);
                slot(s);
            }
            ListNew { slot: s, hint } => {
                opt(hint);
                slot(s);
            }
            Append { slot: s, src: r } | ListFreeze { slot: s, dst: r } => {
                opt(r);
                slot(s);
            }
            Step {
                accu, step, pend, ..
            } => {
                opt(accu);
                opt(step);
                opt(pend);
            }
            CatchPending { pend } | RaisePending { pend, .. } => opt(pend),
            Raise { .. }
            | Jump { .. }
            | CondRead { .. }
            | CondEqFF { .. }
            | CondEqFK { .. }
            | CondTagIn { .. }
            | RetK { .. }
            | Fail => {}
        }
    }

    fn retarget(&mut self, at: &impl Fn(Pc) -> Pc) {
        use Op::*;
        match self {
            Raise { err, .. }
            | Read { err, .. }
            | ReadCached { err, .. }
            | Has { err, .. }
            | Select { err, .. }
            | HasOf { err, .. }
            | Index { err, .. }
            | Not { err, .. }
            | Neg { err, .. }
            | Cmp { err, .. }
            | Arith { err, .. }
            | ArithK { err, .. }
            | In { err, .. }
            | Match { err, .. }
            | StrOp { err, .. }
            | StrOp2 { err, .. }
            | Matches { err, .. }
            | Size { err, .. }
            | Duration { err, .. }
            | DurPart { err, .. }
            | CheckKey { err, .. }
            | Absorb { err, .. }
            | IterInit { err, .. }
            | IndexIter { err, .. }
            | RaisePending { err, .. }
            | Host { err, .. }
            | TagIn { err, .. } => *err = at(*err),
            Jump { to }
            | BrTrue { to, .. }
            | BrFalse { to, .. }
            | BrPending { to, .. }
            | BrSet { to, .. } => *to = at(*to),
            Cond { else_, err, .. }
            | CondRead { else_, err, .. }
            | CondMatch { else_, err, .. }
            | CondEqFF { else_, err, .. }
            | CondEqFK { else_, err, .. }
            | CondTagIn { else_, err, .. }
            | CondCmpFK { else_, err, .. }
            | CondFR { else_, err, .. }
            | CondMatches { else_, err, .. }
            | CondStrOp2F { else_, err, .. }
            | CondCmpK { else_, err, .. } => {
                *else_ = at(*else_);
                *err = at(*err);
            }
            CondEqK { else_, .. } => *else_ = at(*else_),
            IterNext { exit, err, .. } | IterScan { exit, err, .. } => {
                *exit = at(*exit);
                *err = at(*err);
            }
            Const { .. }
            | Local { .. }
            | Eq { .. }
            | Ne { .. }
            | EqK { .. }
            | MakeList { .. }
            | MakeMap { .. }
            | Catch { .. }
            | Nsf { .. }
            | Clear { .. }
            | Inc { .. }
            | NumIn { .. }
            | ListNew { .. }
            | Append { .. }
            | ListFreeze { .. }
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
    Num(CelNum),
    Null,
    Dur(chrono::Duration),
    Str(Box<str>),
    Bytes(Box<[u8]>),
    /// A list or map: a literal, or a residual's constant slot.
    Val(CelValue),
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
            CVal::Num(n) => Reg::from(*n),
            CVal::Null => Reg::Null,
            CVal::Dur(d) => Reg::Dur(*d),
            CVal::Str(s) => Reg::Str(s),
            CVal::Bytes(b) => Reg::Bytes(b),
            CVal::Val(v) => Reg::Val(v),
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
    pub(crate) names: Vec<CelKey>,
    pub(crate) fields: Vec<FieldPath>,
    pub(crate) matchers: Vec<StrMatcher>,
    pub(crate) numsets: Vec<matcher::NumSet>,
    /// The ops that ran while lowering folded a call over constants (`Lower::fold_call`): the
    /// backend computed those constants, so its coverage counts them.
    pub(crate) folded: Vec<&'static str>,
    pub(crate) regexes: Vec<Result<regex::Regex, ExecutionError>>,
    pub(crate) nregs: usize,
    pub(crate) nloops: usize,
    /// The host functions a `Host` op calls, by index.
    pub(crate) hosts: Arc<crate::hostfn::HostTable>,
    /// The closed-set value lists a tag op looks a string up in, by index.
    pub(crate) enum_sets: Vec<Arc<[Box<str>]>>,
    /// The regions a scanned `IterNext` passes elements over by (`IterNext::scan`), by index.
    pub(crate) scans: Vec<scan::ScanBody>,
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

    #[inline(always)]
    fn konst<'a>(&'a self, k: u32) -> Reg<'a> {
        *self.kref(k)
    }

    /// Constant `k`, in place: what a comparison reads, rather than a copy of it.
    #[inline(always)]
    fn kref<'a>(&'a self, k: u32) -> &'a Reg<'a> {
        debug_assert!((k as usize) < self.kregs.len());
        // SAFETY: `Code::verify` (run by `lower::finish` on every `Code` there is) checked every
        // constant index an op carries against `kregs`.
        unsafe { self.kregs.get_unchecked(k as usize) }
    }

    /// The invariants `exec` fetches ops, constants, registers and iterators under without a
    /// bounds check: every jump target is an op, every constant index is a constant, every
    /// register an op names is a register and every loop slot a slot, and the last op never falls
    /// through past the end.
    pub(crate) fn verify(&self) -> Result<(), String> {
        let n = self.ops.len() as u64;
        let bad = std::cell::Cell::new(None);
        for (pc, op) in self.ops.iter().enumerate() {
            let mut o = *op;
            o.retarget(&|t| {
                if u64::from(t) >= n {
                    bad.set(Some(format!(
                        "op {pc} ({}) jumps to {t}, past {n} ops",
                        op.name()
                    )));
                }
                t
            });
            let k = match *op {
                Op::Const { k, .. }
                | Op::Raise { k, .. }
                | Op::CondEqK { k, .. }
                | Op::CondEqFK { k, .. }
                | Op::CondCmpFK { k, .. }
                | Op::CondCmpK { k, .. }
                | Op::ArithK { k, .. }
                | Op::CondStrOp2F { k, .. }
                | Op::EqK { k, .. }
                | Op::RetK { k } => Some(k),
                _ => None,
            };
            op.operands(
                &mut |r| {
                    if r as usize >= self.nregs {
                        bad.set(Some(format!(
                            "op {pc} ({}) names register {r}, past {} registers",
                            op.name(),
                            self.nregs
                        )));
                    }
                },
                &mut |s| {
                    if s as usize >= self.nloops {
                        bad.set(Some(format!(
                            "op {pc} ({}) names loop slot {s}, past {} slots",
                            op.name(),
                            self.nloops
                        )));
                    }
                },
            );
            if let Some(k) = k {
                if k as usize >= self.kregs.len() {
                    bad.set(Some(format!(
                        "op {pc} ({}) names constant {k}, past {} constants",
                        op.name(),
                        self.kregs.len()
                    )));
                }
            }
        }
        for (pc, op) in self.ops.iter().enumerate() {
            if let Op::IterScan { scan, .. } = op {
                if *scan as usize >= self.scans.len() {
                    bad.set(Some(format!(
                        "op {pc} (IterScan) names scan body {scan}, past {} bodies",
                        self.scans.len()
                    )));
                }
            }
        }
        for (b, body) in self.scans.iter().enumerate() {
            // The element is value 0; each `Member`/`Entry` step defines the next.
            let mut defined = 1;
            for (s, step) in body.steps.iter().enumerate() {
                let (vals, cache) = step.operands();
                if let Some(r) = cache {
                    if r as usize >= self.nregs {
                        bad.set(Some(format!(
                            "scan body {b} step {s} names register {r}, past {} registers",
                            self.nregs
                        )));
                    }
                }
                for v in vals {
                    if *v as usize >= defined {
                        bad.set(Some(format!(
                            "scan body {b} step {s} names value {v}, not yet defined"
                        )));
                    }
                }
                if step.defines() {
                    defined += 1;
                }
                let (re, m) = step.tables();
                if re.is_some_and(|re| re as usize >= self.regexes.len())
                    || m.is_some_and(|m| m as usize >= self.matchers.len())
                {
                    bad.set(Some(format!(
                        "scan body {b} step {s} names a regex or matcher past the tables"
                    )));
                }
                if let Some(key) = step.name() {
                    if key as usize >= self.names.len() {
                        bad.set(Some(format!(
                            "scan body {b} step {s} names member {key}, past {} names",
                            self.names.len()
                        )));
                    }
                }
                if let Some(k) = step.konst() {
                    if k as usize >= self.kregs.len() {
                        bad.set(Some(format!(
                            "scan body {b} step {s} names constant {k}, past {} constants",
                            self.kregs.len()
                        )));
                    }
                }
                if let scan::Go::Step(t) = step.go() {
                    if t as usize <= s || t as usize >= body.steps.len() {
                        bad.set(Some(format!(
                            "scan body {b} step {s} jumps back, or past its steps, to step {t}"
                        )));
                    }
                }
            }
        }
        match self.ops.last() {
            Some(Op::Jump { .. } | Op::Ret { .. } | Op::RetK { .. } | Op::Fail) => {}
            last => bad.set(Some(format!(
                "the last op ({last:?}) can fall through past the end"
            ))),
        }
        match bad.into_inner() {
            Some(e) => Err(e),
            None => Ok(()),
        }
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

    /// One node of a CHECKED tree, lowered on its own — what the partial evaluator runs to fold a
    /// closed subtree. `kinds` is the checker's kind for every node of the tree `e` belongs to; every
    /// unbound identifier in `e` is read from the context it runs over. `Err` is a lowering refusal:
    /// a defect of this backend, which the caller reports rather than works around.
    pub(crate) fn lower_node(
        e: &crate::common::ast::IdedExpr,
        kinds: &Kinds,
        hosts: &Arc<crate::hostfn::HostTable>,
        enums: &crate::hostfn::EnumTable,
    ) -> Result<FastProgram, String> {
        Ok(FastProgram {
            code: lower::lower(e, kinds, &[], hosts, enums)?,
            source: Arc::from(""),
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
            .map(|(i, op)| {
                let mut line = format!("{i:4}  {op:?}\n");
                if let Op::IterScan { scan, .. } = op {
                    let steps = match self.code.scans.get(*scan as usize) {
                        Some(b) => &b.steps[..],
                        None => &[],
                    };
                    for (s, step) in steps.iter().enumerate() {
                        line.push_str(&format!("        step {s}: {step:?}\n"));
                    }
                }
                line
            })
            .collect()
    }

    /// How many of the program's loops scan: pass over the elements their body would pass over
    /// inside their `IterNext`.
    #[doc(hidden)]
    pub fn scanned_loops(&self) -> usize {
        self.code
            .ops
            .iter()
            .filter(|op| matches!(op, Op::IterScan { .. }))
            .count()
    }

    /// The name of every op the program lowered to, in order.
    #[doc(hidden)]
    pub fn op_names(&self) -> Vec<&'static str> {
        self.code.ops.iter().map(Op::name).collect()
    }

    /// The ops that ran at lowering to fold calls over constants into this program's constants.
    #[doc(hidden)]
    pub fn folded_op_names(&self) -> &[&'static str] {
        &self.code.folded
    }

    /// How many ops the program lowered to.
    #[doc(hidden)]
    pub fn op_count(&self) -> usize {
        self.code.ops.len()
    }

    /// The verdict over `activation`'s values — the contract, and the error text, of
    /// [`CelProgram::evaluate`](crate::CelProgram::evaluate).
    pub fn eval(&self, activation: &crate::CelActivation) -> Result<bool, crate::CelError> {
        let host = RootsHost {
            roots: activation.roots(),
            fields: &self.code.fields,
            wait: false,
        };
        verdict(
            &self.source,
            with_eval_scratch(|scratch| run(&self.code, &host, scratch, as_bool)),
        )
    }

    /// The value over `activation`'s values, whatever its type — [`Vm::eval_result`]'s contract.
    ///
    /// [`Vm::eval_result`]: crate::Vm::eval_result
    pub fn eval_result(
        &self,
        activation: &crate::CelActivation,
    ) -> Result<crate::CelValue, crate::CelError> {
        self.result_value(self.eval_value(activation.roots()))
    }

    /// [`eval_result`](FastProgram::eval_result), with `dispatch` answering every CALL host.
    pub fn eval_result_with(
        &self,
        activation: &crate::CelActivation,
        dispatch: &mut dyn crate::hostfn::HostDispatch,
    ) -> Result<crate::CelValue, crate::CelError> {
        let cell = std::cell::RefCell::new(dispatch);
        let host = Dispatching {
            inner: RootsHost {
                roots: activation.roots(),
                fields: &self.code.fields,
                wait: false,
            },
            dispatch: &cell,
        };
        let v = with_eval_scratch(|scratch| run(&self.code, &host, scratch, reg::to_cel))
            .and_then(|v| v);
        self.result_value(v)
    }

    fn result_value(
        &self,
        v: Result<CelValue, ExecutionError>,
    ) -> Result<crate::CelValue, crate::CelError> {
        match v {
            Ok(v) => Ok(v),
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

    /// The boundary value over a context of bound values.
    pub(crate) fn eval_value(&self, roots: &Bindings) -> Result<CelValue, ExecutionError> {
        let host = RootsHost {
            roots,
            fields: &self.code.fields,
            wait: false,
        };
        with_eval_scratch(|scratch| run(&self.code, &host, scratch, reg::to_cel)).and_then(|v| v)
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
        if on_stack(&self.code) {
            let mut regs = [Reg::Unset; STACK_REGS];
            let mut store = Store::default();
            let errs = &mut scratch.errs;
            if !errs.is_empty() {
                errs.clear();
            }
            let exit = exec(
                &self.code,
                &host,
                &mut regs[..self.code.nregs],
                &mut store,
                &mut [],
                errs,
                0,
                None,
            );
            if let Exit::Ret(Reg::Bool(b)) = exit {
                forget_if_empty(store);
                return Ok(b);
            }
            return verdict_of_exit(&self.source, exit, errs);
        }
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
    ) -> Result<CelNum, crate::CelError> {
        let cell = std::cell::RefCell::new(dispatch);
        let host = Dispatching {
            inner: FactsHost {
                facts,
                fields: &self.code.fields,
                wait: false,
            },
            dispatch: &cell,
        };
        let out = run(&self.code, &host, scratch, |r, errs| match r.num() {
            Some(n) => Ok(n),
            None => Err(reg::to_cel(r, errs).unwrap_or(CelValue::Null)),
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
        if on_stack(&self.code) {
            let mut regs = [Reg::Unset; STACK_REGS];
            let mut store = Store::default();
            let errs = &mut scratch.errs;
            if !errs.is_empty() {
                errs.clear();
            }
            let exit = exec(
                &self.code,
                host,
                &mut regs[..self.code.nregs],
                &mut store,
                &mut [],
                errs,
                0,
                None,
            );
            if let Exit::Ret(Reg::Str(s)) = exit {
                let tag = tags.iter().position(|t| *t == s);
                forget_if_empty(store);
                return Ok(tag);
            }
            return tag_of_exit(&self.source, exit, errs);
        }
        let out = run(&self.code, host, scratch, |r, errs| match r {
            Reg::Str(s) => Ok(tags.iter().position(|t| *t == s)),
            other => Err(reg::to_cel(other, errs).unwrap_or(CelValue::Null)),
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
fn as_bool(r: Reg<'_>, errs: &[ExecutionError]) -> Result<bool, CelValue> {
    match r {
        Reg::Bool(b) => Ok(b),
        other => Err(reg::to_cel(other, errs).unwrap_or(CelValue::Null)),
    }
}

/// `activation.rs::verdict`, for a run that already knows whether it produced a bool.
#[inline(always)]
fn verdict(
    source: &Arc<str>,
    out: Result<Result<bool, CelValue>, ExecutionError>,
) -> Result<bool, crate::CelError> {
    match out {
        Ok(Ok(b)) => Ok(b),
        other => verdict_err(source, other),
    }
}

/// The `CelError` a run that did not produce a bool answers. Cold: the formatting stays off the
/// path every successful decision takes.
#[cold]
#[inline(never)]
fn verdict_err(
    source: &Arc<str>,
    out: Result<Result<bool, CelValue>, ExecutionError>,
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
    /// A bound list's elements.
    Vals(&'a [CelValue], usize),
    /// A bound map's keys, in key order.
    MapKeys(&'a [(CelMapKey, CelValue)], usize),
    /// A lazy view's keys.
    LazyKeys(Box<dyn Iterator<Item = &'a CelKey> + 'a>),
    /// Not an iteration: the list a `map` / `filter` loop is appending to (`ListNew`).
    Build(Vec<Reg<'a>>),
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

thread_local! {
    /// The scratch the activation entry points (`eval`, `eval_result_with`, `eval_value`) run in,
    /// warmed by the first call on this thread. A run empties it before returning
    /// (`run_on_scratch`), so a call on a warm thread allocates only what its program builds.
    static EVAL_SCRATCH: std::cell::RefCell<FastScratch> =
        std::cell::RefCell::new(FastScratch::default());
}

/// `f` over this thread's [`EVAL_SCRATCH`] — or over a fresh scratch when it is already borrowed,
/// which is a CALL host evaluating CEL from inside a run: the outer run's registers are live.
fn with_eval_scratch<T>(f: impl FnOnce(&mut FastScratch) -> T) -> T {
    EVAL_SCRATCH.with(|s| match s.try_borrow_mut() {
        Ok(mut s) => f(&mut s),
        Err(_) => f(&mut FastScratch::default()),
    })
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

/// The largest register file a run takes on the stack instead of from its scratch.
const STACK_REGS: usize = 16;

/// Run `code` against `host`, turning the result into an owned value with `out` before anything
/// the run built is released.
#[inline]
fn run<'a, H: Host<'a>, T>(
    code: &'a Code,
    host: &H,
    scratch: &mut FastScratch,
    out: impl FnOnce(Reg<'a>, &[ExecutionError]) -> T,
) -> Result<T, ExecutionError> {
    if on_stack(code) {
        return run_on_stack(code, host, &mut scratch.errs, out);
    }
    run_on_scratch(code, host, scratch, out)
}

/// A run with no comprehension and a small register file: its registers live on the stack,
/// initialized for this call, so nothing is resized, re-lifetimed or cleared. A register is never
/// reused across calls: a stale `Reg::Str` would point into the PREVIOUS call's facts.
#[inline(always)]
fn run_on_stack<'a, H: Host<'a>, T>(
    code: &'a Code,
    host: &H,
    errs: &mut Vec<ExecutionError>,
    out: impl FnOnce(Reg<'a>, &[ExecutionError]) -> T,
) -> Result<T, ExecutionError> {
    let mut regs = [Reg::Unset; STACK_REGS];
    // Empty unless an op builds a value; dropped with everything that points into it, after `out`
    // has made the result owned.
    let mut store = Store::default();
    if !errs.is_empty() {
        errs.clear();
    }
    let result = match exec(
        code,
        host,
        &mut regs[..code.nregs],
        &mut store,
        &mut [],
        errs,
        0,
        None,
    ) {
        Exit::Ret(r) => Ok(out(r, errs)),
        Exit::Fail(e) => Err(*e),
        Exit::Need { .. } => Err(cannot_wait()),
    };
    forget_if_empty(store);
    result
}

/// Does `code` run on a stack register file? No comprehension, and few enough registers.
#[inline(always)]
fn on_stack(code: &Code) -> bool {
    code.nloops == 0 && code.nregs <= STACK_REGS
}

/// A store no op wrote to owns no allocation: skip its drop glue, an out-of-line call per run.
#[inline(always)]
fn forget_if_empty(store: Store<'_>) {
    if store.items.capacity() == 0 {
        std::mem::forget(store);
    }
}

/// The tag of a stack run that did not return a string. Cold, like [`verdict_of_exit`].
#[cold]
#[inline(never)]
fn tag_of_exit(
    source: &Arc<str>,
    exit: Exit<'_>,
    errs: &[ExecutionError],
) -> Result<Option<usize>, crate::CelError> {
    match exit {
        Exit::Ret(other) => Err(crate::CelError::Evaluation {
            source: source.clone(),
            message: format!(
                "produced {:?} rather than a string",
                reg::to_cel(other, errs).unwrap_or(CelValue::Null)
            ),
        }),
        Exit::Fail(e) => Err(crate::CelError::Evaluation {
            source: source.clone(),
            message: format!("could not be evaluated: {e}"),
        }),
        Exit::Need { .. } => Err(crate::CelError::Evaluation {
            source: source.clone(),
            message: format!("could not be evaluated: {}", cannot_wait()),
        }),
    }
}

/// The verdict of a stack run that did not return a bool. Cold: only an erroring or ill-typed
/// run reaches it.
#[cold]
#[inline(never)]
fn verdict_of_exit(
    source: &Arc<str>,
    exit: Exit<'_>,
    errs: &[ExecutionError],
) -> Result<bool, crate::CelError> {
    match exit {
        Exit::Ret(r) => verdict_err(source, Ok(as_bool(r, errs))),
        Exit::Fail(e) => verdict_err(source, Err(*e)),
        Exit::Need { .. } => verdict_err(source, Err(cannot_wait())),
    }
}

/// A run that paused although its host cannot wait.
#[cold]
#[inline(never)]
fn cannot_wait() -> ExecutionError {
    ExecutionError::InternalError("a run that cannot wait paused".into())
}

/// A run whose registers and iterations live in its scratch.
#[inline(never)]
fn run_on_scratch<'a, H: Host<'a>, T>(
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
        Exit::Fail(e) => Err(*e),
        // Only a host that waits pauses, and this run's does not.
        Exit::Need { .. } => Err(cannot_wait()),
    };
    regs.clear();
    iters.clear();
    store.items.clear();
    result
}

/// A register or iterator file `exec` indexes without a bounds check, on the strength of
/// [`Code::verify`]: every index an op names is below the count the file was sized to.
struct Unchecked<'r, T>(&'r mut [T]);

impl<T> std::ops::Index<usize> for Unchecked<'_, T> {
    type Output = T;
    #[inline(always)]
    fn index(&self, i: usize) -> &T {
        debug_assert!(i < self.0.len());
        // SAFETY: `Code::verify`; see the type.
        unsafe { self.0.get_unchecked(i) }
    }
}

impl<T> std::ops::IndexMut<usize> for Unchecked<'_, T> {
    #[inline(always)]
    fn index_mut(&mut self, i: usize) -> &mut T {
        debug_assert!(i < self.0.len());
        // SAFETY: `Code::verify`; see the type.
        unsafe { self.0.get_unchecked_mut(i) }
    }
}

/// How a run left `exec`.
enum Exit<'a> {
    Ret(Reg<'a>),
    Fail(Box<ExecutionError>),
    /// A read is not answerable yet. `pc` is the op that asked: resuming re-executes it, and
    /// nothing before it. Only a host that waits produces this.
    Need {
        handle: DemandHandle,
        pc: usize,
        inflight: Option<Box<ExecutionError>>,
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
    inflight: Option<Box<ExecutionError>>,
) -> Exit<'a> {
    let ops = &code.ops[..];
    debug_assert!(start < ops.len());
    // The next op, as a pointer: held in a machine register, never in memory, so no call can
    // make the loop reload it.
    let base = ops.as_ptr();
    // SAFETY: `start` is an op (0, or where a paused run stopped).
    let mut ip = unsafe { base.add(start) };
    let mut inflight = inflight;
    // Indexed without a bounds check: `Code::verify` checked every register and loop slot an op
    // names against `nregs` and `nloops`, and the run sized both files to them.
    debug_assert!(regs.len() >= code.nregs && iters.len() >= code.nloops);
    let regs = &mut Unchecked(regs);
    let iters = &mut Unchecked(iters);
    // SAFETY (every use): `Code::verify` checked every jump target against `ops.len()`.
    macro_rules! jump {
        ($to:expr) => {
            ip = unsafe { base.add($to as usize) }
        };
    }
    // The index of the op after the current one.
    macro_rules! pc {
        () => {
            // SAFETY: `ip` points into `ops`, from `base`.
            unsafe { ip.offset_from(base) as usize }
        };
    }
    // The op that asked for a value not answerable yet is `pc - 1`: `ip` has already moved past
    // it, and a pause puts it back, so the resumed run executes the same read again.
    macro_rules! need {
        ($h:expr) => {
            return Exit::Need {
                handle: $h,
                pc: pc!() - 1,
                inflight,
            }
        };
    }
    // An op, or an uncommon case of one, that `slow` answers.
    macro_rules! go_slow {
        ($op:expr) => {{
            let mut pc = pc!();
            match slow(
                $op,
                code,
                host,
                regs.0,
                st,
                iters.0,
                errs,
                &mut inflight,
                &mut pc,
            ) {
                Flow::Next => jump!(pc),
                Flow::Ret(r) => return Exit::Ret(r),
                Flow::Fail(e) => return Exit::Fail(e),
                Flow::Need(h) => {
                    jump!(pc);
                    need!(h)
                }
            }
        }};
    }
    // The next element of a loop's slot into `dst` (`Op::IterNext`), shared by `IterNext` and the
    // `IterScan` that scans first.
    macro_rules! iter_next {
        ($op:expr, $slot:expr, $dst:expr, $clear:expr, $pend:expr, $exit:expr, $err:expr) => {{
            // Each element is written straight to `dst`, never through a temporary.
            let d = &mut regs[$dst as usize];
            let more = match &mut iters[$slot as usize] {
                Iter::Idle => false,
                Iter::Regs(l, i) => match l.get(*i) {
                    Some(r) => {
                        *i += 1;
                        *d = *r;
                        true
                    }
                    None => false,
                },
                Iter::Pairs(m, i) => match m.get(*i) {
                    Some((k, _)) => {
                        *i += 1;
                        *d = *k;
                        true
                    }
                    None => false,
                },
                Iter::Vals(l, i) => match l.get(*i) {
                    Some(v) => {
                        *i += 1;
                        // A store per kind, not one merged 24-byte value: a merged one is
                        // assembled through the stack.
                        match v {
                            CelValue::Str(s) => *d = Reg::Str(s),
                            CelValue::Int(n) => *d = Reg::Int(*n),
                            CelValue::Num(n) => *d = Reg::Num(*n),
                            _ => *d = reg::of_cel(v),
                        }
                        true
                    }
                    None => false,
                },
                Iter::MapKeys(m, i) => match m.get(*i) {
                    Some((k, _)) => {
                        *i += 1;
                        match k {
                            CelMapKey::Str(s) => *d = Reg::Str(s.as_str()),
                            _ => *d = reg::key_reg(k),
                        }
                        true
                    }
                    None => false,
                },
                Iter::LazyKeys(_) | Iter::Build(_) => {
                    go_slow!($op);
                    continue;
                }
            };
            match more {
                true => {
                    if $clear != NO_REG {
                        regs[$clear as usize] = Reg::Unset;
                    }
                }
                false => {
                    iters[$slot as usize] = Iter::Idle;
                    match pending(regs.0, $pend) {
                        None => jump!($exit),
                        Some(i) => {
                            fault(&mut inflight, take_pending(errs, i));
                            jump!($err);
                        }
                    }
                }
            }
        }};
    }
    // The ops a decision runs most, inline; everything else through `slow`, which keeps this loop
    // small enough to hold its state in registers.
    #[cfg(feature = "profile")]
    profile::exec();
    loop {
        debug_assert!(pc!() < ops.len());
        // SAFETY: `Code::verify` checked every jump target against `ops.len()` and that the last
        // op never falls through, so `ip` — the start (0 or a resumed op), a target, or the op
        // after one that falls through — is always an op. Read in place, by reference: the arms
        // bind the fields they use, and only `slow` takes the whole op.
        let op = unsafe { &*ip };
        ip = unsafe { ip.add(1) };
        #[cfg(feature = "profile")]
        profile::op(op.name());
        match *op {
            Op::Const { dst, k } => regs[dst as usize] = code.konst(k),
            Op::Jump { to } => jump!(to),
            Op::BrTrue { r, to } => {
                if matches!(regs[r as usize], Reg::Bool(true)) {
                    jump!(to);
                }
            }
            Op::BrFalse { r, to } => {
                if matches!(regs[r as usize], Reg::Bool(false)) {
                    jump!(to);
                }
            }
            Op::Local { dst, src } => regs[dst as usize] = regs[src as usize],
            Op::Read { dst, f, want, err } => match host.read(f, want, st) {
                Ok(v) => regs[dst as usize] = v,
                Err(Miss::Err(e)) => {
                    inflight = Some(e);
                    jump!(err);
                }
                Err(Miss::Need(h)) => need!(h),
            },
            Op::CondCmpFK {
                f,
                cache,
                want,
                k,
                op: c,
                invert,
                else_,
                err,
            } => {
                let v = if cache != NO_CACHE && !matches!(regs[cache as usize], Reg::Unset) {
                    regs[cache as usize]
                } else {
                    match fill(host, f, want, st) {
                        Ok(v) => {
                            if cache != NO_CACHE {
                                regs[cache as usize] = v;
                            }
                            v
                        }
                        Err(Miss::Err(e)) => {
                            inflight = Some(e);
                            jump!(err);
                            continue;
                        }
                        Err(Miss::Need(h)) => need!(h),
                    }
                };
                match ordering(&v, code.kref(k)) {
                    Some(o) => {
                        if c.holds(o) == invert {
                            jump!(else_);
                        }
                    }
                    None => {
                        fault(&mut inflight, ExecutionError::NoSuchOverload);
                        jump!(err);
                    }
                }
            }
            Op::CondFR {
                a,
                f,
                cache,
                want,
                test,
                invert,
                else_,
                err,
            } => {
                // What a loop tests per element — a string for equality, a number for order —
                // against a field already cached: read in place, one compare, no copy of either
                // register and no second dispatch on the test. Anything else (the first read, a
                // mixed pair, a NaN) takes the general path below.
                if cache != NO_CACHE {
                    let hit = match (test, &regs[a as usize], &regs[cache as usize]) {
                        (FieldTest::Eq { ne }, Reg::Str(x), Reg::Str(y)) => Some((x == y) != ne),
                        (FieldTest::Cmp(c), Reg::Int(x), Reg::Int(y)) => Some(c.holds(x.cmp(y))),
                        (FieldTest::Cmp(c), Reg::Num(x), Reg::Num(y)) => {
                            x.partial_cmp(y).map(|o| c.holds(o))
                        }
                        (FieldTest::Cmp(c), Reg::Int(x), Reg::Num(y)) => {
                            crate::num::cmp_i64_f64(*x, *y).map(|o| c.holds(o))
                        }
                        (FieldTest::Cmp(c), Reg::Num(x), Reg::Int(y)) => {
                            crate::num::cmp_i64_f64(*y, *x).map(|o| c.holds(o.reverse()))
                        }
                        (FieldTest::Cmp(c), x, y) => {
                            mixed_order(x.num(), y.num()).map(|o| c.holds(o))
                        }
                        _ => None,
                    };
                    if let Some(b) = hit {
                        if b == invert {
                            jump!(else_);
                        }
                        continue;
                    }
                }
                let v = if cache != NO_CACHE && !matches!(regs[cache as usize], Reg::Unset) {
                    regs[cache as usize]
                } else {
                    match fill(host, f, want, st) {
                        Ok(v) => {
                            if cache != NO_CACHE {
                                regs[cache as usize] = v;
                            }
                            v
                        }
                        Err(Miss::Err(e)) => {
                            inflight = Some(e);
                            jump!(err);
                            continue;
                        }
                        Err(Miss::Need(h)) => need!(h),
                    }
                };
                let x = &regs[a as usize];
                match field_test(test, x, &v) {
                    Some(b) => {
                        if b == invert {
                            jump!(else_);
                        }
                    }
                    None => {
                        fault(&mut inflight, field_test_error(test, *x, v));
                        jump!(err);
                    }
                }
            }
            Op::CondCmpK {
                a,
                k,
                op: c,
                invert,
                else_,
                ..
            } => match ordering(&regs[a as usize], code.kref(k)) {
                Some(o) => {
                    if c.holds(o) == invert {
                        jump!(else_);
                    }
                }
                None => go_slow!(*op),
            },
            Op::ReadCached {
                dst,
                f,
                cache,
                want,
                err,
            } => {
                if !matches!(regs[cache as usize], Reg::Unset) {
                    regs[dst as usize] = regs[cache as usize];
                } else {
                    match fill(host, f, want, st) {
                        Ok(v) => {
                            regs[cache as usize] = v;
                            regs[dst as usize] = v;
                        }
                        Err(Miss::Err(e)) => {
                            inflight = Some(e);
                            jump!(err);
                        }
                        Err(Miss::Need(h)) => need!(h),
                    }
                }
            }
            Op::CondRead {
                f,
                invert,
                else_,
                err,
            } => match host.read(f, Want::Bool, st) {
                Ok(Reg::Bool(b)) => {
                    if b == invert {
                        jump!(else_);
                    }
                }
                Ok(_) => {
                    fault(&mut inflight, ExecutionError::NoSuchOverload);
                    jump!(err);
                }
                Err(Miss::Err(e)) => {
                    inflight = Some(e);
                    jump!(err);
                }
                Err(Miss::Need(h)) => need!(h),
            },
            Op::EqK { dst, a, k, ne } => {
                regs[dst as usize] = Reg::Bool(eq_k(&regs[a as usize], code.kref(k)) != ne)
            }
            Op::CondEqK { a, k, ne, else_ } => {
                if eq_k(&regs[a as usize], code.kref(k)) == ne {
                    jump!(else_);
                }
            }
            Op::CondEqFF {
                a,
                b,
                ne,
                else_,
                err,
            } => {
                let x = match host.read(a, Want::Str, st) {
                    Ok(v) => v,
                    Err(Miss::Err(e)) => {
                        inflight = Some(e);
                        jump!(err);
                        continue;
                    }
                    Err(Miss::Need(h)) => need!(h),
                };
                let y = match host.read(b, Want::Str, st) {
                    Ok(v) => v,
                    Err(Miss::Err(e)) => {
                        inflight = Some(e);
                        jump!(err);
                        continue;
                    }
                    Err(Miss::Need(h)) => need!(h),
                };
                if eq_k(&x, &y) == ne {
                    jump!(else_);
                }
            }
            Op::CondEqFK {
                a,
                k,
                ne,
                else_,
                err,
            } => match host.read(a, Want::Str, st) {
                Ok(x) => {
                    if eq_k(&x, code.kref(k)) == ne {
                        jump!(else_);
                    }
                }
                Err(Miss::Err(e)) => {
                    inflight = Some(e);
                    jump!(err);
                }
                Err(Miss::Need(h)) => need!(h),
            },
            Op::CondMatch {
                a,
                m,
                invert,
                else_,
                err,
            } => match regs[a as usize] {
                Reg::Str(s) => {
                    if code.matchers[m as usize].matches(s) == invert {
                        jump!(else_);
                    }
                }
                _ => {
                    fault(&mut inflight, ExecutionError::NoSuchOverload);
                    jump!(err);
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
                        jump!(else_);
                    }
                }
                _ => {
                    fault(&mut inflight, ExecutionError::NoSuchOverload);
                    jump!(err);
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
                        jump!(else_);
                    }
                }
                Err(Miss::Err(e)) => {
                    inflight = Some(e);
                    jump!(err);
                }
                Err(Miss::Need(h)) => need!(h),
            },
            Op::Eq { dst, a, b } => {
                regs[dst as usize] = Reg::Bool(eq_k(&regs[a as usize], &regs[b as usize]))
            }
            Op::Ne { dst, a, b } => {
                regs[dst as usize] = Reg::Bool(!eq_k(&regs[a as usize], &regs[b as usize]))
            }
            // Only the case that does nothing is inline: the left passed it on and the right is a
            // bool. Every other case — an error to raise or absorb — goes to `slow`.
            Op::Absorb { dst, a, or, .. }
                if matches!(
                    (regs[a as usize], regs[dst as usize]),
                    (Reg::Bool(l), Reg::Bool(_)) if l != or
                ) => {}
            Op::Match { dst, a, m, .. } if matches!(regs[a as usize], Reg::Str(_)) => {
                let Reg::Str(s) = regs[a as usize] else {
                    unreachable!()
                };
                regs[dst as usize] = Reg::Bool(code.matchers[m as usize].matches(s));
            }
            Op::Not { dst, a, .. } if matches!(regs[a as usize], Reg::Bool(_)) => {
                regs[dst as usize] = Reg::Bool(matches!(regs[a as usize], Reg::Bool(false)));
            }
            Op::Nsf { dst, a } => {
                regs[dst as usize] = Reg::Bool(!matches!(regs[a as usize], Reg::Bool(false)))
            }
            Op::Cmp {
                dst, a, b, op: c, ..
            } => match ordering(&regs[a as usize], &regs[b as usize]) {
                Some(o) => regs[dst as usize] = Reg::Bool(c.holds(o)),
                // Operands it does not order, NaN among them: `slow` raises.
                None => go_slow!(*op),
            },
            // A bound record's (or map's) member that is there. A missing one raises, a lazy view
            // is polled, a built map is searched: `slow`.
            Op::CondStrOp2F {
                f,
                cache,
                b,
                k,
                op: o,
                invert,
                else_,
                err,
            } => {
                let v = if cache != NO_CACHE && !matches!(regs[cache as usize], Reg::Unset) {
                    regs[cache as usize]
                } else {
                    match fill(host, f, Want::Str, st) {
                        Ok(v) => {
                            if cache != NO_CACHE {
                                regs[cache as usize] = v;
                            }
                            v
                        }
                        Err(Miss::Err(e)) => {
                            inflight = Some(e);
                            jump!(err);
                            continue;
                        }
                        Err(Miss::Need(h)) => need!(h),
                    }
                };
                match (v, regs[b as usize], code.konst(k)) {
                    (Reg::Str(x), Reg::Str(y), Reg::Str(z)) => {
                        if o.test(x, y, z) == invert {
                            jump!(else_);
                        }
                    }
                    // Only a string concatenates: what `+` would have refused.
                    _ => {
                        fault(&mut inflight, ExecutionError::NoSuchOverload);
                        jump!(err);
                    }
                }
            }
            Op::StrOp2 {
                dst,
                a,
                b,
                c,
                op: o,
                ..
            } => match (regs[a as usize], regs[b as usize], regs[c as usize]) {
                (Reg::Str(x), Reg::Str(y), Reg::Str(z)) => {
                    regs[dst as usize] = Reg::Bool(o.test(x, y, z))
                }
                _ => go_slow!(*op),
            },
            Op::Matches { dst, a, re, .. } if re != u32::MAX => {
                match (regs[a as usize], &code.regexes[re as usize]) {
                    (Reg::Str(s), Ok(r)) => regs[dst as usize] = Reg::Bool(r.is_match(s)),
                    _ => go_slow!(*op),
                }
            }
            Op::CondMatches {
                a,
                re,
                invert,
                else_,
                ..
            } => match (regs[a as usize], &code.regexes[re as usize]) {
                (Reg::Str(s), Ok(r)) => {
                    if r.is_match(s) == invert {
                        jump!(else_);
                    }
                }
                _ => go_slow!(*op),
            },
            Op::Arith {
                dst, a, b, op: o, ..
            } => match (regs[a as usize], regs[b as usize]) {
                (Reg::Int(x), Reg::Int(y)) => match o.int(x, y) {
                    Some(v) => regs[dst as usize] = v,
                    None => go_slow!(*op),
                },
                (Reg::Num(x), Reg::Num(y)) => regs[dst as usize] = o.float(x, y),
                // A double beside an integer: IEEE on both, as `crate::num::arith` does.
                (Reg::Num(x), Reg::Int(y)) => regs[dst as usize] = o.float(x, y as f64),
                (Reg::Int(x), Reg::Num(y)) => regs[dst as usize] = o.float(x as f64, y),
                // A wide integer, an overflow, a string or a duration, or a refusal: `slow`
                // (`fn arith`) builds it.
                _ => go_slow!(*op),
            },
            Op::ArithK {
                dst,
                a,
                k,
                op: o,
                rev,
                ..
            } => match (regs[a as usize], code.konst(k)) {
                (Reg::Int(x), Reg::Int(y)) => match if rev { o.int(y, x) } else { o.int(x, y) } {
                    Some(v) => regs[dst as usize] = v,
                    None => go_slow!(*op),
                },
                (Reg::Num(x), Reg::Num(y)) => {
                    regs[dst as usize] = if rev { o.float(y, x) } else { o.float(x, y) }
                }
                (Reg::Num(x), Reg::Int(y)) => {
                    let y = y as f64;
                    regs[dst as usize] = if rev { o.float(y, x) } else { o.float(x, y) }
                }
                (Reg::Int(x), Reg::Num(y)) => {
                    let x = x as f64;
                    regs[dst as usize] = if rev { o.float(y, x) } else { o.float(x, y) }
                }
                _ => go_slow!(*op),
            },
            // A caught error, out of the in-flight box (kept for the next failure): no allocation.
            Op::Catch { dst } => {
                errs.push(caught(&mut inflight));
                regs[dst as usize] = Reg::Err((errs.len() - 1) as u32);
            }
            Op::IterInit {
                slot, src, clear, ..
            } => {
                let it = match regs[src as usize] {
                    Reg::List(l) => Some(Iter::Regs(l, 0)),
                    Reg::Map(m) => Some(Iter::Pairs(m, 0)),
                    Reg::Val(CelValue::List(l)) => Some(Iter::Vals(l, 0)),
                    Reg::Val(CelValue::Map(m)) => Some(Iter::MapKeys(m.entries(), 0)),
                    _ => None,
                };
                match it {
                    Some(it) => {
                        iters[slot as usize] = it;
                        if clear != NO_REG {
                            regs[clear as usize] = Reg::Unset;
                        }
                    }
                    // A lazy view's keys, or a refusal: `slow`.
                    None => go_slow!(*op),
                }
            }
            Op::IndexIter { dst, slot, .. } => {
                let v = match &iters[slot as usize] {
                    Iter::MapKeys(m, i) if *i > 0 => Some(reg::of_cel(&m[*i - 1].1)),
                    Iter::Pairs(m, i) if *i > 0 => Some(m[*i - 1].1),
                    _ => None,
                };
                match v {
                    Some(v) => regs[dst as usize] = v,
                    None => go_slow!(*op),
                }
            }
            Op::Select { dst, obj, key, .. } => match regs[obj as usize] {
                Reg::Val(CelValue::Map(m)) => match m.get(code.names[key as usize].as_str()) {
                    // A store per kind, as `IterNext` does.
                    Some(CelValue::Str(s)) => regs[dst as usize] = Reg::Str(s),
                    Some(CelValue::Int(n)) => regs[dst as usize] = Reg::Int(*n),
                    Some(CelValue::Num(n)) => regs[dst as usize] = Reg::Num(*n),
                    Some(v) => regs[dst as usize] = reg::of_cel(v),
                    None => go_slow!(*op),
                },
                _ => go_slow!(*op),
            },
            Op::StrOp {
                dst, a, b, op: o, ..
            } => match (regs[a as usize], regs[b as usize]) {
                (Reg::Str(s), Reg::Str(t)) => regs[dst as usize] = Reg::Bool(o.test(s, t)),
                _ => go_slow!(*op),
            },
            Op::Has { dst, f, err } => match host.has(f, st) {
                Ok(b) => regs[dst as usize] = Reg::Bool(b),
                Err(Miss::Err(e)) => {
                    inflight = Some(e);
                    jump!(err);
                }
                Err(Miss::Need(h)) => need!(h),
            },
            Op::BrPending { r, to } => {
                if matches!(regs[r as usize], Reg::Err(_)) {
                    jump!(to);
                }
            }
            Op::Clear { r } => regs[r as usize] = Reg::Unset,
            // No pending error: nothing to raise. Raising one goes to `slow`.
            Op::RaisePending { pend, .. } if !matches!(regs[pend as usize], Reg::Err(_)) => {}
            Op::Inc { r } => match regs[r as usize] {
                // A comprehension's counter: an integer that never nears `i64::MAX`.
                Reg::Int(n) if n < i64::MAX => regs[r as usize] = Reg::Int(n + 1),
                Reg::Num(n) => regs[r as usize] = Arith::Add.float(n, 1.0),
                _ => {}
            },
            Op::Append { slot, src } => {
                if let Iter::Build(v) = &mut iters[slot as usize] {
                    v.push(regs[src as usize]);
                }
            }
            Op::BrSet { r, to } => {
                if !matches!(regs[r as usize], Reg::Unset) {
                    jump!(to);
                }
            }
            Op::Step {
                accu,
                step,
                pend,
                absorb,
            } => {
                let s = regs[step as usize];
                if absorb.absorbs(s) {
                    regs[pend as usize] = Reg::Unset;
                }
                regs[accu as usize] = s;
            }
            // A range over a slice, inline; a map's keys and a lazy view's go to `slow`.
            Op::IterNext {
                slot,
                dst,
                clear,
                pend,
                exit,
                err,
            } => iter_next!(*op, slot, dst, clear, pend, exit, err),
            // The same, past the elements the loop's body would pass over first.
            Op::IterScan {
                slot,
                dst,
                clear,
                pend,
                exit,
                err,
                scan,
            } => {
                let _skipped = scan::skip(
                    &code.scans[scan as usize],
                    &mut iters[slot as usize],
                    &*regs.0,
                    code,
                );
                #[cfg(feature = "profile")]
                profile::scanned(_skipped);
                iter_next!(*op, slot, dst, clear, pend, exit, err)
            }
            Op::Ret { r } => return Exit::Ret(regs[r as usize]),
            Op::RetK { k } => return Exit::Ret(code.konst(k)),
            _ => go_slow!(*op),
        }
    }
}

/// A cache register's first read: once per run, so out of line and cold — an arm that finds its
/// cache full runs no host code, and none of the host's inlined body competes for the loop's
/// machine registers.
#[cold]
#[inline(never)]
fn fill<'a, H: Host<'a>>(
    host: &H,
    f: u32,
    want: Want,
    st: &mut Store<'a>,
) -> Result<Reg<'a>, Miss> {
    host.read(f, want, st)
}

/// [`FieldTest`] of register `x` against field value `v`; `None` where the unfused ops refuse.
#[inline(always)]
fn field_test(test: FieldTest, x: &Reg<'_>, v: &Reg<'_>) -> Option<bool> {
    match test {
        // The string case matched here, not through `eq_k`: measured 16 instructions fewer per
        // element on a nested loop, where the extra level of matching is not folded away.
        FieldTest::Eq { ne } => Some(
            match (x, v) {
                (Reg::Str(a), Reg::Str(b)) => a == b,
                _ => eq_k(x, v),
            } != ne,
        ),
        FieldTest::Cmp(c) => ordering(x, v).map(|o| c.holds(o)),
        FieldTest::FieldRecv(o) => match (v, x) {
            (Reg::Str(s), Reg::Str(t)) => Some(o.test(s, t)),
            _ => None,
        },
        FieldTest::RegRecv(o) => match (x, v) {
            (Reg::Str(s), Reg::Str(t)) => Some(o.test(s, t)),
            _ => None,
        },
    }
}

/// The error the unfused spelling of a refused [`FieldTest`] raises: `Cmp`'s, or `StrOp`'s for
/// its receiver and argument.
#[cold]
#[inline(never)]
fn field_test_error(test: FieldTest, x: Reg<'_>, v: Reg<'_>) -> ExecutionError {
    let (recv, arg) = match test {
        FieldTest::Eq { .. } => unreachable!("an equality never fails"),
        FieldTest::Cmp(_) => {
            return reg::compare(x, v)
                .err()
                .unwrap_or(ExecutionError::NoSuchOverload)
        }
        FieldTest::FieldRecv(_) => (v, x),
        FieldTest::RegRecv(_) => (x, v),
    };
    let bad = if matches!(recv, Reg::Str(_)) {
        arg
    } else {
        recv
    };
    ExecutionError::UnexpectedType {
        got: type_name(bad).to_string(),
        want: "string".to_string(),
    }
}

/// `CondCmpFK`'s "no cache register: read the field where it occurs".
pub(crate) const NO_CACHE: R = R::MAX;

/// `IterScan`'s "scan my body's region, if it has one", as lowering leaves it: `scan::fuse` gives
/// every one its region's index, or makes it an `IterNext`.
pub(crate) const SCAN_WANTED: u16 = u16::MAX;

/// `IterNext`'s "no register to reset".
pub(crate) const NO_REG: R = R::MAX;

/// The index of the error pending in `pend`, if `pend` is a register and holds one.
#[inline(always)]
fn pending(regs: &[Reg<'_>], pend: R) -> Option<u32> {
    match regs.get(pend as usize) {
        Some(Reg::Err(i)) if pend != NO_REG => Some(*i),
        _ => None,
    }
}

/// A pending error, raised: its last use (its register is reset before it is caught into
/// again), so the newest one is moved out rather than copied.
#[cold]
#[inline(never)]
fn take_pending(errs: &mut Vec<ExecutionError>, i: u32) -> ExecutionError {
    if i as usize + 1 == errs.len() {
        errs.pop().expect("the pending error")
    } else {
        errs[i as usize].clone()
    }
}

/// `reg::compare`'s order where it has one, without building its error: `None` for operands it
/// refuses (a NaN, mismatched kinds), which `slow` then raises.
#[inline(always)]
fn ordering(a: &Reg<'_>, b: &Reg<'_>) -> Option<std::cmp::Ordering> {
    match (a, b) {
        (Reg::Int(x), Reg::Int(y)) => Some(x.cmp(y)),
        (Reg::Num(x), Reg::Num(y)) => x.partial_cmp(y),
        (Reg::Str(x), Reg::Str(y)) => Some(x.cmp(y)),
        (Reg::Dur(x), Reg::Dur(y)) => Some(x.cmp(y)),
        // A JSON integer against a fractional bound, inline; any wider pair out of line.
        (Reg::Int(x), Reg::Num(y)) => crate::num::cmp_i64_f64(*x, *y),
        (Reg::Num(x), Reg::Int(y)) => crate::num::cmp_i64_f64(*y, *x).map(|o| o.reverse()),
        (x, y) => mixed_order(x.num(), y.num()),
    }
}

/// Two numbers in different representations (or a `u64`), in exact order; `None` for a NaN or a
/// non-number. OUT of line, and handed the numbers BY VALUE: the exact comparison's `i128`
/// arithmetic inlined into `exec` cost the dispatch loop a register (measured: `exec` spilled its op
/// pointer to the stack, and every decision paid it, numeric or not), and a reference to a register
/// escaping into a call forces that register into memory on every path through the match.
#[inline(never)]
fn mixed_order(a: Option<CelNum>, b: Option<CelNum>) -> Option<std::cmp::Ordering> {
    a?.cmp_exact(b?)
}

/// Put `e` in flight. A handler takes the error out of its box and leaves the box behind
/// (`Catch`, `CatchPending`), so a run whose failures are caught and discarded — a loop over
/// failing elements — reuses one box rather than allocating one per failure. Only a host's
/// failure arrives in a box of its own.
#[cold]
#[inline(never)]
fn fault(inflight: &mut Option<Box<ExecutionError>>, e: ExecutionError) {
    match inflight {
        Some(b) => **b = e,
        None => *inflight = Some(Box::new(e)),
    }
}

/// The error in flight, taken out of its box for a handler to keep; the box stays for reuse.
fn caught(inflight: &mut Option<Box<ExecutionError>>) -> ExecutionError {
    let b = inflight.as_mut().expect("an error in flight");
    std::mem::replace(&mut **b, ExecutionError::NoSuchOverload)
}

/// What one op did.
enum Flow<'a> {
    Next,
    Ret(Reg<'a>),
    Fail(Box<ExecutionError>),
    /// Not answerable yet: the op did nothing, and `pc` is where `exec` left it.
    Need(DemandHandle),
}

/// The ops `exec` handles itself (some only in their common case; see [`handled_inline`]).
pub(crate) const INLINE: &[&str] = &[
    "Const",
    "Jump",
    "BrTrue",
    "BrFalse",
    "Local",
    "Read",
    "ReadCached",
    "CondRead",
    "EqK",
    "CondEqK",
    "CondMatch",
    "Cond",
    "CondTagIn",
    "Eq",
    "Ne",
    "Absorb",
    "Match",
    "CondEqFF",
    "CondEqFK",
    "CondCmpFK",
    "CondFR",
    "CondCmpK",
    "Select",
    "IndexIter",
    "Arith",
    "ArithK",
    "CondStrOp2F",
    "StrOp2",
    "Matches",
    "CondMatches",
    "IterInit",
    "Catch",
    "Not",
    "Nsf",
    "Cmp",
    "StrOp",
    "Has",
    "BrPending",
    "Clear",
    "RaisePending",
    "Inc",
    "Append",
    "BrSet",
    "Step",
    "IterNext",
    "IterScan",
    "Ret",
    "RetK",
];

/// The names of the ops `exec` handles inline, for `tests/fast_layout.rs`.
#[doc(hidden)]
pub fn inline_ops() -> &'static [&'static str] {
    INLINE
}

/// Would `exec` have handled `op` itself, given these registers? `slow` asserts it never sees one.
fn handled_inline(op: Op, regs: &[Reg<'_>], iters: &[Iter<'_>]) -> bool {
    match op {
        Op::Not { a, .. } => matches!(regs[a as usize], Reg::Bool(_)),
        Op::RaisePending { pend, .. } => !matches!(regs[pend as usize], Reg::Err(_)),
        Op::Cmp { a, b, .. } => ordering(&regs[a as usize], &regs[b as usize]).is_some(),
        // `handled_inline` sees no constant pool: `slow` answers only the unordered case.
        Op::CondCmpK { .. } => false,
        // Nor the names: `slow` answers the member that is missing, and every non-map.
        Op::Select { .. } => false,
        Op::Arith { a, b, op, .. } => match (regs[a as usize], regs[b as usize]) {
            (Reg::Num(_), Reg::Num(_) | Reg::Int(_)) | (Reg::Int(_), Reg::Num(_)) => true,
            (Reg::Int(x), Reg::Int(y)) => op.int(x, y).is_some(),
            _ => false,
        },
        Op::ArithK { .. } => false,
        Op::StrOp2 { a, b, c, .. } => matches!(
            (regs[a as usize], regs[b as usize], regs[c as usize]),
            (Reg::Str(_), Reg::Str(_), Reg::Str(_))
        ),
        // `handled_inline` sees no regex table: `slow` answers the refusals.
        Op::Matches { .. } | Op::CondMatches { .. } => false,
        Op::StrOp { a, b, .. } => {
            matches!(
                (regs[a as usize], regs[b as usize]),
                (Reg::Str(_), Reg::Str(_))
            )
        }
        Op::IterNext { slot, .. } | Op::IterScan { slot, .. } => {
            !matches!(iters[slot as usize], Iter::LazyKeys(_) | Iter::Build(_))
        }
        Op::IterInit { src, .. } => matches!(
            regs[src as usize],
            Reg::List(_) | Reg::Map(_) | Reg::Val(CelValue::List(_) | CelValue::Map(_))
        ),
        Op::IndexIter { slot, .. } => matches!(
            iters[slot as usize],
            Iter::MapKeys(_, i) | Iter::Pairs(_, i) if i > 0
        ),
        Op::Absorb { dst, a, or, .. } => matches!(
            (regs[a as usize], regs[dst as usize]),
            (Reg::Bool(l), Reg::Bool(_)) if l != or
        ),
        Op::Match { a, .. } => matches!(regs[a as usize], Reg::Str(_)),
        other => INLINE.contains(&other.name()),
    }
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
    inflight: &mut Option<Box<ExecutionError>>,
    pc: &mut usize,
) -> Flow<'a> {
    #[cfg(feature = "profile")]
    profile::slow(op.name());
    debug_assert!(
        !handled_inline(op, regs, iters),
        "{} reached slow, but exec handles it inline",
        op.name()
    );
    macro_rules! fail {
        ($e:expr, $to:expr) => {{
            fault(inflight, $e);
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
                Err(Miss::Err(e)) => {
                    *inflight = Some(e);
                    *pc = $to as usize;
                    return Flow::Next;
                }
                Err(Miss::Need(h)) => return Flow::Need(h),
            }
        };
    }
    // A lazy operand in a run that waits is POLLED, as a host read is: the op answers from the
    // poll, or pauses the run before it has touched anything.
    let waits = host.waits();
    match op {
        // Only ever inline: `exec` answers both in every case.
        Op::CondEqFF { .. }
        | Op::CondEqFK { .. }
        | Op::CondCmpFK { .. }
        | Op::CondFR { .. }
        | Op::CondStrOp2F { .. }
        | Op::Inc { .. }
        | Op::Append { .. }
        | Op::BrSet { .. }
        | Op::ReadCached { .. } => {
            unreachable!("{} reached slow", op.name())
        }
        Op::Const { dst, k } => regs[dst as usize] = code.konst(k),
        Op::CondCmpK {
            a,
            k,
            op,
            invert,
            else_,
            err,
        } => {
            let o = tryr!(reg::compare(regs[a as usize], code.konst(k)), err);
            if op.holds(o) == invert {
                *pc = else_ as usize;
            }
        }
        Op::CondMatches {
            a,
            re,
            invert,
            else_,
            err,
        } => {
            let Reg::Str(s) = regs[a as usize] else {
                fail!(ExecutionError::NoSuchOverload, err)
            };
            match &code.regexes[re as usize] {
                Ok(r) => {
                    if r.is_match(s) == invert {
                        *pc = else_ as usize;
                    }
                }
                Err(e) => fail!(e.clone(), err),
            }
        }
        Op::Raise { k, err } => match &code.consts[k as usize] {
            CVal::Err(e) => fail!(e.clone(), err),
            _ => fail!(ExecutionError::InternalError("not an error".into()), err),
        },
        Op::Read { dst, f, want, err } => {
            regs[dst as usize] = tryh!(host.read(f, want, st), err);
        }
        Op::Has { dst, f, err } => regs[dst as usize] = Reg::Bool(tryh!(host.has(f, st), err)),
        Op::Local { dst, src } => regs[dst as usize] = regs[src as usize],
        Op::Select { dst, obj, key, err } => {
            let name = &code.names[key as usize];
            if let Some(lazy) = lazy_of(waits, regs[obj as usize]) {
                // `reg::select` on a lazy: the member it answers, kept in the store.
                regs[dst as usize] = match tryr!(lazy::poll_read(lazy, name.as_str()), err) {
                    Access::Ready(v) => reg::of_owned(v, st),
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
                regs[dst as usize] = match tryr!(lazy::poll_presence(lazy, name.as_str()), err) {
                    Presence::Known(b) => Reg::Bool(b),
                    Presence::Pending(h) => return Flow::Need(h),
                };
                return Flow::Next;
            }
            let v = reg::has(regs[obj as usize], name);
            regs[dst as usize] = Reg::Bool(tryr!(v, err));
        }
        Op::Index { dst, a, b, err } | Op::IndexIter { dst, a, b, err, .. } => {
            if let (Some(lazy), Reg::Str(name)) =
                (lazy_of(waits, regs[a as usize]), regs[b as usize])
            {
                regs[dst as usize] = match tryr!(lazy::poll_read(lazy, name), err) {
                    Access::Ready(v) => reg::of_owned(v, st),
                    Access::Pending(h) => return Flow::Need(h),
                };
                return Flow::Next;
            }
            let v = reg::index(regs[a as usize], regs[b as usize], st);
            regs[dst as usize] = tryr!(v, err);
        }
        Op::Not { dst, a, err } => match regs[a as usize] {
            Reg::Bool(b) => regs[dst as usize] = Reg::Bool(!b),
            _ => fail!(ExecutionError::NoSuchOverload, err),
        },
        Op::Neg { dst, a, err } => match regs[a as usize].num() {
            Some(n) => match crate::num::neg(n) {
                Ok(v) => regs[dst as usize] = Reg::from(v),
                Err(_) => fail!(
                    ExecutionError::Overflow("negate", n.into(), CelValue::Null),
                    err
                ),
            },
            None => fail!(ExecutionError::NoSuchOverload, err),
        },
        Op::Eq { dst, a, b } => {
            regs[dst as usize] = Reg::Bool(reg::equals(regs[a as usize], regs[b as usize]))
        }
        Op::Ne { dst, a, b } => {
            regs[dst as usize] = Reg::Bool(!reg::equals(regs[a as usize], regs[b as usize]))
        }
        Op::Cmp { dst, a, b, op, err } => {
            let o = tryr!(reg::compare(regs[a as usize], regs[b as usize]), err);
            regs[dst as usize] = Reg::Bool(op.holds(o));
        }
        Op::Arith { dst, a, b, op, err } => {
            let v = arith(op, regs[a as usize], regs[b as usize], st, errs);
            regs[dst as usize] = tryr!(v, err);
        }
        Op::ArithK {
            dst,
            a,
            k,
            op,
            rev,
            err,
        } => {
            let (x, y) = if rev {
                (code.konst(k), regs[a as usize])
            } else {
                (regs[a as usize], code.konst(k))
            };
            regs[dst as usize] = tryr!(arith(op, x, y, st, errs), err);
        }
        Op::In { dst, a, b, err } => {
            if let (Reg::Str(name), Some(lazy)) =
                (regs[a as usize], lazy_of(waits, regs[b as usize]))
            {
                regs[dst as usize] = match tryr!(lazy::poll_presence(lazy, name), err) {
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
            (Reg::Str(s), Reg::Str(t)) => regs[dst as usize] = Reg::Bool(op.test(s, t)),
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
        Op::StrOp2 {
            dst,
            a,
            b,
            c,
            op,
            err,
        } => match (regs[a as usize], regs[b as usize], regs[c as usize]) {
            (Reg::Str(a), Reg::Str(b), Reg::Str(c)) => {
                regs[dst as usize] = Reg::Bool(op.test(a, b, c))
            }
            // Only a string concatenates: what `+` would have refused.
            _ => fail!(ExecutionError::NoSuchOverload, err),
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
            regs[dst as usize] = Reg::from(tryr!(reg::size(regs[a as usize]), err));
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
                regs[dst as usize] = Reg::Int(if millis {
                    d.num_milliseconds()
                } else {
                    d.num_seconds()
                })
            }
            _ => fail!(ExecutionError::NoSuchOverload, err),
        },
        Op::MakeList { dst, start, n } => {
            let items = regs[start as usize..start as usize + n as usize].to_vec();
            regs[dst as usize] = Reg::List(st.regs(items));
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
            regs[dst as usize] = Reg::Map(st.pairs(pairs));
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
            regs[dst as usize] = Reg::Bool(eq_k(&regs[a as usize], code.kref(k)) != ne)
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
        Op::CondEqK { a, k, ne, else_ } => {
            if eq_k(&regs[a as usize], code.kref(k)) == ne {
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
            errs.push(caught(inflight));
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
        Op::IterInit {
            slot,
            src,
            clear,
            err,
        } => {
            let it = match regs[src as usize] {
                Reg::List(l) => Iter::Regs(l, 0),
                Reg::Map(m) => Iter::Pairs(m, 0),
                Reg::Val(CelValue::List(l)) => Iter::Vals(l, 0),
                Reg::Val(CelValue::Map(m)) => Iter::MapKeys(m.entries(), 0),
                // A view with no keys is not iterable.
                Reg::Val(CelValue::Lazy(l)) => match l.keys() {
                    Some(keys) => Iter::LazyKeys(keys),
                    None => fail!(ExecutionError::NoSuchOverload, err),
                },
                _ => fail!(ExecutionError::NoSuchOverload, err),
            };
            iters[slot as usize] = it;
            if clear != NO_REG {
                regs[clear as usize] = Reg::Unset;
            }
        }
        Op::IterNext {
            slot,
            dst,
            clear,
            pend,
            exit,
            err,
        }
        | Op::IterScan {
            slot,
            dst,
            clear,
            pend,
            exit,
            err,
            ..
        } => {
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
                    reg::of_cel(v)
                }),
                Iter::MapKeys(m, i) => m.get(*i).map(|(k, _)| {
                    *i += 1;
                    reg::key_reg(k)
                }),
                Iter::LazyKeys(ks) => ks.next().map(|k| Reg::Str(k.as_str())),
                Iter::Build(_) => unreachable!("a list being built is not iterated"),
            };
            match next {
                Some(r) => {
                    regs[dst as usize] = r;
                    if clear != NO_REG {
                        regs[clear as usize] = Reg::Unset;
                    }
                }
                None => {
                    iters[slot as usize] = Iter::Idle;
                    match pending(regs, pend) {
                        None => *pc = exit as usize,
                        Some(i) => fail!(take_pending(errs, i), err),
                    }
                }
            }
        }
        Op::BrPending { r, to } => {
            if matches!(regs[r as usize], Reg::Err(_)) {
                *pc = to as usize;
            }
        }
        Op::Clear { r } => regs[r as usize] = Reg::Unset,
        Op::NumIn { dst, a, set } => {
            regs[dst as usize] = Reg::Bool(match regs[a as usize] {
                r => r
                    .num()
                    .is_some_and(|n| code.numsets[set as usize].contains(n)),
            })
        }
        Op::ListNew { slot, hint } => {
            let n = match regs[hint as usize] {
                Reg::List(l) => l.len(),
                Reg::Map(m) => m.len(),
                Reg::Val(CelValue::List(l)) => l.len(),
                Reg::Val(CelValue::Map(m)) => m.len(),
                _ => 0,
            };
            iters[slot as usize] = Iter::Build(Vec::with_capacity(n));
        }
        Op::ListFreeze { slot, dst } => {
            let Iter::Build(v) = std::mem::replace(&mut iters[slot as usize], Iter::Idle) else {
                unreachable!("ListFreeze without its ListNew")
            };
            regs[dst as usize] = Reg::List(st.built(v));
        }
        Op::Step {
            accu,
            step,
            pend,
            absorb,
        } => {
            let s = regs[step as usize];
            if absorb.absorbs(s) {
                regs[pend as usize] = Reg::Unset;
            }
            regs[accu as usize] = s;
        }
        Op::CatchPending { pend } => {
            // The FIRST error is the one reported; a later one stays in the in-flight box, to be
            // overwritten by the next failure.
            if !matches!(regs[pend as usize], Reg::Err(_)) {
                errs.push(caught(inflight));
                regs[pend as usize] = Reg::Err((errs.len() - 1) as u32);
            }
        }
        Op::RaisePending { pend, err } => {
            if let Reg::Err(i) = regs[pend as usize] {
                // Raising is the pending error's last use (its register is cleared before it is
                // caught into again): the newest one is moved out rather than copied.
                fail!(take_pending(errs, i), err);
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
                crate::CelValue::Int(x) => Reg::Int(x),
                crate::CelValue::UInt(x) => Reg::UInt(x),
                crate::CelValue::Null => Reg::Null,
                crate::CelValue::Str(x) => Reg::Str(st.str(x.to_string())),
                crate::CelValue::Bytes(x) => Reg::Bytes(st.bytes(x.to_vec())),
                crate::CelValue::Duration(d) => Reg::Dur(d.delta()),
                // A CALL host's record, read by member.
                lazy @ crate::CelValue::Lazy(_)
                    if matches!(entry.imp, crate::hostfn::HostImpl::PerCall) =>
                {
                    reg::of_owned(lazy, st)
                }
                crate::CelValue::Lazy(_) => fail!(
                    crate::hostfn::failure(&entry.name, "a host function returned a lazy value"),
                    err
                ),
                // A composite, kept in the store.
                composite => reg::of_owned(composite, st),
            };
        }
        Op::Ret { r } => return Flow::Ret(regs[r as usize]),
        Op::RetK { k } => return Flow::Ret(code.konst(k)),
        Op::Fail => return Flow::Fail(inflight.take().expect("an error in flight")),
    }
    Flow::Next
}

/// The lazy a register holds, for a run that waits; `None` otherwise, so the op takes its usual
/// path, "not yet" read as an error.
fn lazy_of<'a>(waits: bool, r: Reg<'a>) -> Option<&'a dyn LazyValue> {
    if waits {
        reg::lazy_of(r)
    } else {
        None
    }
}

/// Is tag `t` one of `mask`'s bits? `TAG_OTHER` (and any tag past the mask) is in none.
#[inline(always)]
fn in_mask(t: u8, mask: u64) -> bool {
    t < 64 && mask >> t & 1 == 1
}

/// A register as a host function's argument: a lazy view is the view itself, a string is copied
/// out, anything else converts to its value.
fn host_arg(r: Reg<'_>, errs: &[ExecutionError]) -> Option<crate::CelValue> {
    reg::to_cel(r, errs).ok()
}

/// `a == k` for a scalar constant `k`, with the string case — a tag, an enum value — inline.
#[inline(always)]
fn eq_k(a: &Reg<'_>, k: &Reg<'_>) -> bool {
    match (a, k) {
        (Reg::Str(x), Reg::Str(y)) => x == y,
        (Reg::Bool(x), Reg::Bool(y)) => x == y,
        (Reg::Int(x), Reg::Int(y)) => x == y,
        (Reg::Num(x), Reg::Num(y)) => x == y,
        _ => reg::equals(*a, *k),
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
            reg::to_cel(a, errs).unwrap_or(CelValue::Null),
            reg::to_cel(b, errs).unwrap_or(CelValue::Null),
        )
    };
    if let (Some(x), Some(y)) = (a.num(), b.num()) {
        return op.num(x, y).map(Reg::from);
    }
    Ok(match (op, a, b) {
        (Arith::Add, Reg::Str(x), Reg::Str(y)) => {
            let mut s = String::with_capacity(x.len() + y.len());
            s.push_str(x);
            s.push_str(y);
            Reg::Str(st.str(s))
        }
        (Arith::Add, Reg::Dur(x), Reg::Dur(y)) => Reg::Dur(
            x.checked_add(&y)
                .filter(crate::duration::in_cel_range)
                .ok_or(ExecutionError::Overflow(
                    "add",
                    CelValue::Null,
                    CelValue::Null,
                ))?,
        ),
        (Arith::Sub, Reg::Dur(x), Reg::Dur(y)) => Reg::Dur(
            x.checked_sub(&y)
                .filter(crate::duration::in_cel_range)
                .ok_or(ExecutionError::Overflow(
                    "sub",
                    CelValue::Null,
                    CelValue::Null,
                ))?,
        ),
        (Arith::Add, _, _) => match (reg::elements(a), reg::elements(b)) {
            (Some(mut x), Some(y)) => {
                x.extend(y);
                Reg::List(st.regs(x))
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
        // The one number type, whichever representation holds the value.
        Reg::Num(_) | Reg::Int(_) | Reg::UInt(_) => "double",
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
    inflight: Option<Box<ExecutionError>>,
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
    Vals(&'a [CelValue], usize),
    /// A list a `map` / `filter` loop was building, its elements re-homed.
    Build(Vec<Reg<'a>>),
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
    fn holds(&self, v: &CelValue) -> bool {
        self.consts.iter().any(|c| match c {
            CVal::Val(b) => std::ptr::eq(b, v),
            _ => false,
        })
    }

    /// Is `l` the elements of one of this program's constant lists?
    fn holds_list(&self, l: &[CelValue]) -> bool {
        self.consts.iter().any(|c| match c {
            CVal::Val(CelValue::List(x)) => std::ptr::eq(x.as_ptr(), l.as_ptr()),
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
        Reg::Val(v) if code.holds(v) => r,
        // One `Arc` bump: the value is shared, not copied.
        Reg::Val(v) => Reg::Val(out.value(v.clone())),
        Reg::List(l) => {
            let items = l.iter().map(|x| rehome(*x, code, out)).collect();
            Reg::List(out.regs(items))
        }
        Reg::Map(m) => {
            let pairs = m
                .iter()
                .map(|(k, v)| (rehome(*k, code, out), rehome(*v, code, out)))
                .collect();
            Reg::Map(out.pairs(pairs))
        }
        Reg::Unset
        | Reg::Bool(_)
        | Reg::Num(_)
        | Reg::Int(_)
        | Reg::UInt(_)
        | Reg::Null
        | Reg::Dur(_)
        | Reg::Err(_) => r,
    }
}

/// An iteration in flight, as a paused run holds it: what is left of it, in `out`.
fn hold<'a>(it: Iter<'a>, code: &'a Code, out: &mut Store<'a>) -> Held<'a> {
    let rest: Vec<Reg<'a>> = match it {
        Iter::Idle => return Held::Idle,
        Iter::Build(v) => {
            return Held::Build(v.into_iter().map(|r| rehome(r, code, out)).collect());
        }
        Iter::Vals(l, i) if code.holds_list(l) => return Held::Vals(l, i),
        Iter::Regs(l, i) => l[i..].to_vec(),
        Iter::Pairs(m, i) => m[i..].iter().map(|(k, _)| *k).collect(),
        Iter::Vals(l, i) => l[i..].iter().map(reg::of_cel).collect(),
        Iter::MapKeys(m, i) => m[i..].iter().map(|(k, _)| reg::key_reg(k)).collect(),
        Iter::LazyKeys(ks) => ks.map(|k| Reg::Str(k.as_str())).collect(),
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
            Held::Build(v) => Iter::Build(v),
        }
    }
}

impl FastProgram {
    /// Run `p` on until it finishes or a read is not answerable yet. The roots are `roots`,
    /// except the fields `facts` marks, which its provider answers.
    ///
    /// A pause leaves `pc` on the read that asked, so the next resume executes that read again and
    /// nothing before it.
    pub(crate) fn resume<F: Facts + ?Sized>(
        &self,
        p: Paused,
        roots: &Bindings,
        facts: Option<(&F, &[bool])>,
    ) -> Resumed {
        let ctx = RootsHost {
            roots,
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
            Exit::Fail(e) => Resumed::Done(verdict(&self.source, Err(*e))),
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
            | Op::CondEqFK { a: f, .. }
            | Op::TagIn { f, .. }
            | Op::CondTagIn { f, .. } = op
            {
                out[*f as usize] = true;
            }
            if let Op::CondEqFF { a, b, .. } = op {
                out[*a as usize] = true;
                out[*b as usize] = true;
            }
        }
        out
    }
}

/// The node kinds of a checked program, by expression id.
pub(crate) type Kinds = HashMap<u64, Kind>;

/// A run over a context of bound values, to the boundary value. For the crate's own harnesses.
#[cfg(feature = "conformance")]
pub(crate) fn run_value(p: &FastProgram, roots: &Bindings) -> Result<CelValue, ExecutionError> {
    p.eval_value(roots)
}

/// The sizes of the backend's hot types, for `tests/fast_layout.rs` and the ablation's `--listing`.
#[doc(hidden)]
pub fn layout_sizes() -> Vec<(&'static str, usize)> {
    use std::mem::size_of;
    vec![
        ("Reg", size_of::<Reg<'static>>()),
        ("Op", size_of::<Op>()),
        ("ExecutionError", size_of::<ExecutionError>()),
        (
            "Option<ExecutionError>",
            size_of::<Option<ExecutionError>>(),
        ),
        ("Result<Reg, Miss>", size_of::<Result<Reg<'static>, Miss>>()),
        ("Exit", size_of::<Exit<'static>>()),
        ("Flow", size_of::<Flow<'static>>()),
        (
            "Result<bool, CelError>",
            size_of::<Result<bool, crate::CelError>>(),
        ),
    ]
}

#[cfg(test)]
mod verify_tests {
    use super::*;

    fn code(ops: Vec<Op>, nconsts: usize) -> Code {
        let mut c = Code {
            ops,
            consts: (0..nconsts).map(|_| CVal::Bool(true)).collect(),
            nregs: 1,
            ..Code::default()
        };
        c.seal();
        c
    }

    #[test]
    fn a_well_formed_program_verifies() {
        assert!(code(vec![Op::RetK { k: 0 }], 1).verify().is_ok());
    }

    /// `exec` fetches ops and constants unchecked on the strength of `verify`, so each way a
    /// program can index past its arrays must be refused, naming the op.
    #[test]
    fn a_corrupt_program_is_refused() {
        let cases = [
            (vec![Op::Jump { to: 5 }], 1, "jumps to 5"),
            (
                vec![Op::Const { dst: 0, k: 3 }, Op::Ret { r: 0 }],
                1,
                "names constant 3",
            ),
            (vec![Op::Const { dst: 0, k: 0 }], 1, "fall through"),
            (
                vec![Op::BrTrue { r: 0, to: 9 }, Op::RetK { k: 0 }],
                1,
                "jumps to 9",
            ),
            (
                vec![Op::Local { dst: 0, src: 1 }, Op::Ret { r: 0 }],
                1,
                "names register 1",
            ),
            (vec![Op::Ret { r: 4 }], 1, "names register 4"),
            (
                vec![
                    Op::IterNext {
                        slot: 0,
                        dst: 0,
                        clear: NO_REG,
                        pend: NO_REG,
                        exit: 1,
                        err: 1,
                    },
                    Op::RetK { k: 0 },
                ],
                1,
                "names loop slot 0",
            ),
        ];
        for (ops, nconsts, want) in cases {
            let err = code(ops.clone(), nconsts)
                .verify()
                .expect_err(&format!("{ops:?} verified"));
            assert!(err.contains(want), "{ops:?}: {err}");
        }
        // A scanned `IterNext` and the region it names.
        let scan = |steps: Vec<scan::Step>| {
            let mut c = code(
                vec![
                    Op::IterScan {
                        slot: 0,
                        dst: 0,
                        clear: NO_REG,
                        pend: NO_REG,
                        exit: 1,
                        err: 1,
                        scan: 0,
                    },
                    Op::RetK { k: 0 },
                ],
                1,
            );
            c.nloops = 1;
            c.scans.push(scan::ScanBody {
                steps: steps.into(),
            });
            c
        };
        let field = |a: u8, cache: R, go: scan::Go| scan::Step::Field {
            a,
            cache,
            test: FieldTest::Eq { ne: false },
            invert: false,
            go,
        };
        assert!(scan(vec![field(0, 0, scan::Go::On)]).verify().is_ok());
        let mut member = scan(vec![
            scan::Step::Member { obj: 0, key: 0 },
            field(1, 0, scan::Go::On),
        ]);
        member.names.push(CelKey::new("k"));
        assert!(member.verify().is_ok(), "{:?}", member.verify());
        let scans = [
            (scan(vec![field(0, 9, scan::Go::On)]), "names register 9"),
            (scan(vec![field(1, 0, scan::Go::On)]), "names value 1"),
            (scan(vec![field(0, 0, scan::Go::Step(0))]), "jumps back"),
            (
                scan(vec![
                    scan::Step::Member { obj: 0, key: 0 },
                    field(1, 0, scan::Go::On),
                ]),
                "names member 0",
            ),
            (
                {
                    let mut c = scan(vec![
                        scan::Step::Member { obj: 0, key: 0 },
                        field(2, 0, scan::Go::On),
                    ]);
                    c.names.push(CelKey::new("k"));
                    c
                },
                "names value 2",
            ),
            (
                {
                    let mut c = scan(vec![field(0, 0, scan::Go::On)]);
                    c.scans.clear();
                    c
                },
                "names scan body 0",
            ),
        ];
        for (c, want) in scans {
            let err = c.verify().expect_err(&format!("{want}: verified"));
            assert!(err.contains(want), "{want}: {err}");
        }
    }
}
