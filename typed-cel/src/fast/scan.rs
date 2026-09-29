//! A loop's non-deciding elements, skipped inside its fetch.
//!
//! An `IterScan` — a predicate loop's `IterNext` with a region — first advances the loop's iterator past every
//! element for which the body would provably jump straight back to the loop's head having changed
//! nothing anything reads, then fetches the first element it cannot vouch for, as it always did, and
//! the body runs that element as it always did. The scan reads no host, raises nothing, never pauses
//! and writes no register, so a pause, an error, a deciding element, the pending-error protocol,
//! `exists_one`'s count and `filter`'s `Append` all happen in the ops they always happened in, on
//! the same elements.
//!
//! What the body does first for an element — its REGION, the leading ops `region` understands —
//! is recorded as [`Step`]s, evaluated per element with the same pure functions `exec` uses.

use super::reg;
use super::{Cmp, Code, Concat, FieldTest, Iter, Op, Pc, Reg, StrOp, NO_CACHE, NO_REG, R};

/// A step that does not jump.
const NO_TARGET: Pc = Pc::MAX;

/// The most steps a region holds.
pub(crate) const MAX_STEPS: usize = 16;

/// What a loop's body does first, for one element, as far as it is a pure test of it.
#[derive(Debug)]
pub(crate) struct ScanBody {
    pub(crate) steps: Box<[Step]>,
}

/// Where a step goes when it jumps.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Go {
    /// Back to the loop's head: the element does not decide, and is skipped.
    On,
    /// To a later step of the region.
    Step(u8),
    /// Anywhere else: the element is handed to the body.
    HandOff,
}

/// One op of the region. `a` indexes the region's values: 0 is the element.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Step {
    /// `CondFR`: value `a` against the field in `regs[cache]` by `test`; jumps when the test
    /// answers `invert`.
    Field {
        a: u8,
        cache: R,
        test: FieldTest,
        invert: bool,
        go: Go,
    },
    /// `CondEqK`: jumps when `eq_k(a, k) == ne`.
    EqK { a: u8, k: u32, ne: bool, go: Go },
    /// `CondCmpK`: jumps when `op` holds of `(a, k)` exactly when `invert` says.
    CmpK {
        a: u8,
        k: u32,
        op: Cmp,
        invert: bool,
        go: Go,
    },
    /// `CondStrOp2F`: `op.test(field, b, k)` — the field in `regs[cache]`, `b` a region value, `k`
    /// a string constant — jumps when it answers `invert`.
    Concat {
        cache: R,
        b: u8,
        k: u32,
        op: Concat,
        invert: bool,
        go: Go,
    },
    /// `RaisePending` on the chain register this element's fetch cleared: nothing is pending,
    /// since every leaf so far answered (a leaf that fails has handed the element off).
    Nop,
    /// `Jump` to the loop's head.
    On,
    /// `Select`: the present member `key` (`code.names[key]`) of value `obj`, a bound map or
    /// record, becomes the next region value. A missing member, or any other value, hands off.
    Member { obj: u8, key: u32 },
    /// `IndexIter` on the loop's own slot: the current entry's value becomes the next region value.
    Entry,
    /// `CondMatches`: `code.regexes[re]` over value `a`, a string; jumps when it answers `invert`.
    Pattern {
        a: u8,
        re: u32,
        invert: bool,
        go: Go,
    },
    /// `CondMatch`: `code.matchers[m]` over value `a`, a string; jumps when it answers `invert`.
    Matcher { a: u8, m: u32, invert: bool, go: Go },
}

impl Step {
    fn set_go(&mut self, to: Go) {
        match self {
            Step::Field { go, .. }
            | Step::EqK { go, .. }
            | Step::CmpK { go, .. }
            | Step::Concat { go, .. }
            | Step::Pattern { go, .. }
            | Step::Matcher { go, .. } => *go = to,
            Step::Nop | Step::On | Step::Member { .. } | Step::Entry => {}
        }
    }

    /// The region values the step reads, and its cache register, if any.
    pub(crate) fn operands(&self) -> (&[u8], Option<R>) {
        match self {
            Step::Field { a, cache, .. } => (std::slice::from_ref(a), Some(*cache)),
            Step::EqK { a, .. }
            | Step::CmpK { a, .. }
            | Step::Pattern { a, .. }
            | Step::Matcher { a, .. } => (std::slice::from_ref(a), None),
            Step::Concat { b, cache, .. } => (std::slice::from_ref(b), Some(*cache)),
            Step::Member { obj, .. } => (std::slice::from_ref(obj), None),
            Step::Nop | Step::On | Step::Entry => (&[], None),
        }
    }

    /// The constant the step compares with, if any.
    pub(crate) fn konst(&self) -> Option<u32> {
        match self {
            Step::EqK { k, .. } | Step::CmpK { k, .. } | Step::Concat { k, .. } => Some(*k),
            _ => None,
        }
    }

    /// Whether the step defines the next region value.
    pub(crate) fn defines(&self) -> bool {
        matches!(self, Step::Member { .. } | Step::Entry)
    }

    /// The regex and the matcher the step runs, if any.
    pub(crate) fn tables(&self) -> (Option<u32>, Option<u32>) {
        match self {
            Step::Pattern { re, .. } => (Some(*re), None),
            Step::Matcher { m, .. } => (None, Some(*m)),
            _ => (None, None),
        }
    }

    /// The member name the step selects, if any.
    pub(crate) fn name(&self) -> Option<u32> {
        match self {
            Step::Member { key, .. } => Some(*key),
            _ => None,
        }
    }

    pub(crate) fn go(&self) -> Go {
        match self {
            Step::Field { go, .. }
            | Step::EqK { go, .. }
            | Step::CmpK { go, .. }
            | Step::Concat { go, .. }
            | Step::Pattern { go, .. }
            | Step::Matcher { go, .. } => *go,
            // Falls through to the next step; `On` never gets there (`passes` answers it).
            Step::Nop | Step::Member { .. } | Step::Entry => Go::HandOff,
            Step::On => Go::On,
        }
    }
}

thread_local! {
    /// Set only by [`with_unfused_loops`].
    static UNFUSED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Run `f` lowering no scan: every loop lowered on this thread inside `f` runs each element
/// through its body's ops. For differential tests only.
#[doc(hidden)]
pub fn with_unfused_loops<T>(f: impl FnOnce() -> T) -> T {
    let was = UNFUSED.with(|c| c.replace(true));
    let out = f();
    UNFUSED.with(|c| c.set(was));
    out
}

/// The region of the body after the `IterNext` at `h`, if some path through it goes on.
fn region(ops: &[Op], h: usize) -> Option<ScanBody> {
    let Op::IterScan {
        dst, clear, slot, ..
    } = ops[h]
    else {
        return None;
    };
    // Which register holds which region value (a value may be in several: `Local` copies one),
    // and how many values there are. The element is value 0, in `dst`.
    let mut vals: Vec<(R, u8)> = vec![(dst, 0)];
    let mut count: u8 = 1;
    let val = |vals: &[(R, u8)], r: R| vals.iter().find(|(h, _)| *h == r).map(|(_, v)| *v);
    // `r` now holds value `v`: what it held before is gone (a body reuses its temporaries), and a
    // test reading `r` reads `v`.
    let define = |vals: &mut Vec<(R, u8)>, r: R, v: u8| {
        vals.retain(|(h, _)| *h != r);
        vals.push((r, v));
    };
    let mut steps: Vec<Step> = Vec::new();
    // Step index → its op's index, and its jump target, resolved once the region is known.
    let (mut at, mut raw): (Vec<usize>, Vec<Pc>) = (Vec::new(), Vec::new());
    let mut pc = h + 1;
    while pc < ops.len() && steps.len() < MAX_STEPS {
        let (step, target) = match ops[pc] {
            Op::CondFR {
                a,
                cache,
                test,
                invert,
                else_,
                ..
            } if cache != NO_CACHE => {
                let Some(a) = val(&vals, a) else { break };
                let go = Go::HandOff;
                (
                    Step::Field {
                        a,
                        cache,
                        test,
                        invert,
                        go,
                    },
                    else_,
                )
            }
            Op::CondEqK { a, k, ne, else_ } => {
                let Some(a) = val(&vals, a) else { break };
                (
                    Step::EqK {
                        a,
                        k,
                        ne,
                        go: Go::HandOff,
                    },
                    else_,
                )
            }
            Op::CondCmpK {
                a,
                k,
                op,
                invert,
                else_,
                ..
            } => {
                let Some(a) = val(&vals, a) else { break };
                (
                    Step::CmpK {
                        a,
                        k,
                        op,
                        invert,
                        go: Go::HandOff,
                    },
                    else_,
                )
            }
            Op::CondStrOp2F {
                cache,
                b,
                k,
                op,
                invert,
                else_,
                ..
            } if cache != NO_CACHE => {
                let Some(b) = val(&vals, b) else { break };
                (
                    Step::Concat {
                        cache,
                        b,
                        k,
                        op,
                        invert,
                        go: Go::HandOff,
                    },
                    else_,
                )
            }
            // The chain's pending error, reset by this element's fetch: nothing to raise when
            // every leaf answered, and a leaf that fails has already handed the element off.
            Op::RaisePending { pend, .. } if clear != NO_REG && pend == clear => {
                (Step::Nop, NO_TARGET)
            }
            Op::Select { dst, obj, key, .. } => {
                let Some(obj) = val(&vals, obj) else { break };
                define(&mut vals, dst, count);
                count += 1;
                (Step::Member { obj, key }, NO_TARGET)
            }
            Op::IndexIter { dst, slot: s, .. } if s == slot => {
                define(&mut vals, dst, count);
                count += 1;
                (Step::Entry, NO_TARGET)
            }
            // A copy: `dst` holds the same value, and no step runs for it.
            Op::Local { dst, src } => {
                let Some(v) = val(&vals, src) else { break };
                define(&mut vals, dst, v);
                pc += 1;
                continue;
            }
            Op::CondMatches {
                a,
                re,
                invert,
                else_,
                ..
            } => {
                let Some(a) = val(&vals, a) else { break };
                (
                    Step::Pattern {
                        a,
                        re,
                        invert,
                        go: Go::HandOff,
                    },
                    else_,
                )
            }
            Op::CondMatch {
                a,
                m,
                invert,
                else_,
                ..
            } => {
                let Some(a) = val(&vals, a) else { break };
                (
                    Step::Matcher {
                        a,
                        m,
                        invert,
                        go: Go::HandOff,
                    },
                    else_,
                )
            }
            // Back to the head: the element goes on. Nothing after it runs for this element.
            Op::Jump { to } if to as usize == h => {
                steps.push(Step::On);
                at.push(pc);
                raw.push(NO_TARGET);
                break;
            }
            // Forward over what this path does not run (a split chain's cold copy): the walk goes
            // on at the target, still in increasing op order, so it ends and every step's jump
            // resolves forward. A step jumping into what was passed over hands off.
            Op::Jump { to } if to as usize > pc => {
                pc = to as usize;
                continue;
            }
            _ => break,
        };
        steps.push(step);
        at.push(pc);
        raw.push(target);
        pc += 1;
    }
    // Each jump: to the head goes on, to a later step of the region is that step, anywhere else
    // (backward, past the region, the loop's exit) hands the element to the body.
    let mut on = steps.iter().any(|s| matches!(s, Step::On));
    for (s, t) in raw.iter().enumerate() {
        if *t == NO_TARGET {
            continue;
        }
        let go = if *t as usize == h {
            on = true;
            Go::On
        } else {
            match at.iter().position(|p| *p == *t as usize) {
                Some(j) if j > s => Go::Step(j as u8),
                _ => Go::HandOff,
            }
        };
        steps[s].set_go(go);
    }
    on.then(|| ScanBody {
        steps: steps.into(),
    })
}

/// Give every `IterScan` its body's region, or make it the `IterNext` it otherwise is. Runs once
/// labels are op indices (`Lower::finish`): a region's jumps are resolved against them.
pub(crate) fn fuse(code: &mut Code) {
    let unfused = UNFUSED.with(|u| u.get());
    for h in 0..code.ops.len() {
        let Op::IterScan {
            slot,
            dst,
            clear,
            pend,
            exit,
            err,
            ..
        } = code.ops[h]
        else {
            continue;
        };
        code.ops[h] = match if unfused { None } else { region(&code.ops, h) } {
            Some(body) => {
                code.scans.push(body);
                Op::IterScan {
                    slot,
                    dst,
                    clear,
                    pend,
                    exit,
                    err,
                    scan: (code.scans.len() - 1) as u16,
                }
            }
            None => Op::IterNext {
                slot,
                dst,
                clear,
                pend,
                exit,
                err,
            },
        };
    }
}

/// Skip the elements `body` passes over; how many. Stops at the first element it cannot vouch
/// for, leaving it unconsumed.
///
/// Two out-of-line loops, so a one-test loop's element that does not pass — a kept `filter`
/// element, the deciding one — costs a call into a small frame, not the region walker's.
#[inline(always)]
pub(crate) fn skip<'a>(
    body: &ScanBody,
    it: &mut Iter<'a>,
    regs: &[Reg<'a>],
    code: &'a Code,
) -> usize {
    match &body.steps[..] {
        [step] => match skip_one(step, it, regs, code) {
            Some(n) => n,
            None => skip_region(&body.steps, it, regs, code),
        },
        steps => match skip_members(steps, it, regs, code) {
            Some(n) => n,
            None => skip_region(steps, it, regs, code),
        },
    }
}

/// [`skip`] for any region, one element at a time through [`passes`].
#[inline(never)]
fn skip_region<'a>(steps: &[Step], it: &mut Iter<'a>, regs: &[Reg<'a>], code: &'a Code) -> usize {
    // Where each `Member` step found its member in the last record: records of one type keep
    // their members at the same index.
    let mut hints = [0usize; MAX_STEPS];
    // The region's values, set up once: a step reads only values defined before it for the same
    // element (`Code::verify`), so what an earlier element left past them is never read.
    let mut vals = [Reg::Unset; MAX_STEPS + 1];
    match it {
        Iter::Vals(l, i) => {
            let start = *i;
            while let Some(v) = l.get(*i) {
                if !passes(
                    steps,
                    reg::of_cel(v),
                    None,
                    &mut hints,
                    &mut vals,
                    regs,
                    code,
                ) {
                    break;
                }
                *i += 1;
            }
            *i - start
        }
        Iter::Regs(l, i) => {
            let start = *i;
            while let Some(r) = l.get(*i) {
                if !passes(steps, *r, None, &mut hints, &mut vals, regs, code) {
                    break;
                }
                *i += 1;
            }
            *i - start
        }
        Iter::MapKeys(m, i) => {
            let start = *i;
            while let Some((k, v)) = m.get(*i) {
                let entry = Some(reg::of_cel(v));
                if !passes(
                    steps,
                    reg::key_reg(k),
                    entry,
                    &mut hints,
                    &mut vals,
                    regs,
                    code,
                ) {
                    break;
                }
                *i += 1;
            }
            *i - start
        }
        Iter::Pairs(m, i) => {
            let start = *i;
            while let Some((k, v)) = m.get(*i) {
                if !passes(steps, *k, Some(*v), &mut hints, &mut vals, regs, code) {
                    break;
                }
                *i += 1;
            }
            *i - start
        }
        // A lazy view's keys, an idle or building slot: nothing to skip; `IterNext` does it all.
        Iter::Idle | Iter::LazyKeys(_) | Iter::Build(_) => 0,
    }
}

/// Pass over elements while `$pass` holds of the element at `*$i` of `$l`; how many.
macro_rules! pass_while {
    ($l:expr, $i:expr, |$v:ident| $pass:expr) => {{
        let start = *$i;
        while let Some($v) = $l.get(*$i) {
            if !$pass {
                break;
            }
            *$i += 1;
        }
        Some(*$i - start)
    }};
}

/// The one-test regions a loop runs most — the element tested against a field or a constant,
/// every jump going on — as loops over a bound list's values (or a bound map's string keys) that
/// test each element as it lies: the other operand read once, no register built, no step
/// dispatched per element. An element of another kind stops the loop and is handed off, as
/// `passes` would hand off or answer it the same way. `None`: not one of these shapes.
#[inline(never)]
fn skip_one<'a>(step: &Step, it: &mut Iter<'a>, regs: &[Reg<'a>], code: &'a Code) -> Option<usize> {
    use crate::CelMapKey as K;
    use crate::CelValue as V;
    match (*step, it) {
        (
            Step::Field {
                a: 0,
                cache,
                test,
                invert,
                go: Go::On,
            },
            Iter::Vals(l, i),
        ) => match (test, regs[cache as usize]) {
            // The field's first read is the body's.
            (_, Reg::Unset) => Some(0),
            (FieldTest::Eq { ne }, Reg::Str(y)) => {
                pass_while!(
                    l,
                    i,
                    |v| matches!(v, V::Str(s) if ((&**s == y) != ne) == invert)
                )
            }
            (FieldTest::Eq { ne }, Reg::Num(y)) => {
                pass_while!(
                    l,
                    i,
                    |v| matches!(v, V::Num(x) if ((*x == y) != ne) == invert)
                )
            }
            (FieldTest::Cmp(c), Reg::Num(y)) => pass_while!(l, i, |v| matches!(
                v, V::Num(x) if x.partial_cmp(&y).is_some_and(|o| c.holds(o) == invert)
            )),
            (FieldTest::Cmp(c), Reg::Str(y)) => pass_while!(l, i, |v| matches!(
                v, V::Str(x) if c.holds((**x).cmp(y)) == invert
            )),
            // The field is the receiver: `f.startsWith(x)`.
            (FieldTest::FieldRecv(o), Reg::Str(y)) => {
                pass_while!(l, i, |v| matches!(v, V::Str(x) if o.test(y, x) == invert))
            }
            // The element holds the field: `x.contains(f)`, the needle the same for every element,
            // so its searcher is built once.
            (FieldTest::RegRecv(StrOp::Contains), Reg::Str(y)) => {
                Some(pass_containing(l, i, y, invert))
            }
            // The element is: `x.startsWith(f)`.
            (FieldTest::RegRecv(o), Reg::Str(y)) => {
                pass_while!(l, i, |v| matches!(v, V::Str(x) if o.test(x, y) == invert))
            }
            _ => None,
        },
        (
            Step::Field {
                a: 0,
                cache,
                test: FieldTest::Eq { ne },
                invert,
                go: Go::On,
            },
            Iter::MapKeys(m, i),
        ) => match regs[cache as usize] {
            Reg::Unset => Some(0),
            Reg::Str(y) => pass_while!(m, i, |e| matches!(
                &e.0, K::Str(s) if ((s.as_str() == y) != ne) == invert
            )),
            _ => None,
        },
        (
            Step::Pattern {
                a: 0,
                re,
                invert,
                go: Go::On,
            },
            Iter::Vals(l, i),
        ) => match &code.regexes[re as usize] {
            Ok(r) => Some(pass_matching(l, i, r, invert)),
            Err(_) => Some(0),
        },
        (
            Step::Matcher {
                a: 0,
                m,
                invert,
                go: Go::On,
            },
            Iter::Vals(l, i),
        ) => {
            let m = &code.matchers[m as usize];
            pass_while!(l, i, |v| matches!(v, V::Str(x) if m.matches(x) == invert))
        }
        (
            Step::EqK {
                a: 0,
                k,
                ne,
                go: Go::On,
            },
            Iter::Vals(l, i),
        ) => match code.konst(k) {
            Reg::Str(y) => pass_while!(l, i, |v| matches!(v, V::Str(s) if (&**s == y) == ne)),
            Reg::Num(y) => pass_while!(l, i, |v| matches!(v, V::Num(x) if (*x == y) == ne)),
            _ => None,
        },
        (
            Step::CmpK {
                a: 0,
                k,
                op,
                invert,
                go: Go::On,
            },
            Iter::Vals(l, i),
        ) => match code.konst(k) {
            Reg::Num(y) => pass_while!(l, i, |v| matches!(
                v, V::Num(x) if x.partial_cmp(&y).is_some_and(|o| op.holds(o) == invert)
            )),
            _ => None,
        },
        _ => None,
    }
}

/// The most member tests `skip_members` runs per element.
const MAX_PAIRS: usize = 4;

/// One member test of `skip_members`, its field read once and its kind decided once: the member
/// tested as it lies where the kinds are the common ones, through `field_test` otherwise.
#[derive(Clone, Copy)]
enum Probe<'a> {
    /// A number member against a number field, by order.
    NumCmp(Cmp, f64),
    /// A string member against a string field, for equality (`!=` when `ne`).
    StrEq(bool, &'a str),
    /// A number member against a number field, for equality.
    NumEq(bool, f64),
    /// Anything else.
    Any(FieldTest, Reg<'a>),
    /// The field is not read yet: the body reads it.
    Unread,
}

impl Probe<'_> {
    /// `Some(field_test(test, member, field))`, or `None` where it refuses.
    #[inline(always)]
    fn test(&self, v: &crate::CelValue) -> Option<bool> {
        use crate::CelValue as V;
        match (self, v) {
            (Probe::NumCmp(c, y), V::Num(x)) => x.partial_cmp(y).map(|o| c.holds(o)),
            (Probe::StrEq(ne, y), V::Str(x)) => Some((&**x == *y) != *ne),
            (Probe::NumEq(ne, y), V::Num(x)) => Some((*x == *y) != *ne),
            (Probe::Any(test, field), v) => super::field_test(*test, &reg::of_cel(v), field),
            // A member of an unexpected kind, or an unread field: the body's.
            _ => None,
        }
    }
}

/// A record loop's region — each step pair a member of the element, then a test of it against a
/// field, the test going on when it jumps — as one loop over a bound list of records: each field
/// read once, each member found where the last record had it, an element skipped as soon as one
/// test goes on. `exists(i, i.a == f && i.b > g)` and `all(i, i.b > g)` are this shape. An element
/// that is not a bound record, lacks a member, fails a test, reaches a field still unread, or passes
/// every test is handed off. `None`: not this shape.
#[inline(never)]
fn skip_members<'a>(
    steps: &[Step],
    it: &mut Iter<'a>,
    regs: &[Reg<'a>],
    code: &'a Code,
) -> Option<usize> {
    let Iter::Vals(l, i) = it else { return None };
    if steps.len() % 2 != 0 || steps.len() > 2 * MAX_PAIRS {
        return None;
    }
    // (member name, its probe, what jumping means)
    let mut pairs: [(&str, Probe<'a>, bool); MAX_PAIRS] = [("", Probe::Unread, false); MAX_PAIRS];
    let n = steps.len() / 2;
    for (j, pair) in steps.chunks(2).enumerate() {
        let [Step::Member { obj: 0, key }, Step::Field {
            a,
            cache,
            test,
            invert,
            go: Go::On,
        }] = *pair
        else {
            return None;
        };
        if a as usize != j + 1 {
            return None;
        }
        // A field still unread (`Unset`) hands off the element that reaches its test — the body
        // reads it — which a record whose first test already goes on never does.
        let probe = match (test, regs[cache as usize]) {
            (_, Reg::Unset) => Probe::Unread,
            (FieldTest::Cmp(c), Reg::Num(y)) => Probe::NumCmp(c, y),
            (FieldTest::Eq { ne }, Reg::Str(y)) => Probe::StrEq(ne, y),
            (FieldTest::Eq { ne }, Reg::Num(y)) => Probe::NumEq(ne, y),
            (test, field) => Probe::Any(test, field),
        };
        pairs[j] = (code.names[key as usize].as_str(), probe, invert);
    }
    let mut hints = [0usize; MAX_PAIRS];
    let start = *i;
    'elements: while let Some(crate::CelValue::Map(m)) = l.get(*i) {
        for (j, (name, probe, invert)) in pairs[..n].iter().enumerate() {
            let Some(v) = m.get_at(name, &mut hints[j]) else {
                break 'elements;
            };
            match probe.test(v) {
                // Goes on: skip the element.
                Some(b) if b == *invert => {
                    *i += 1;
                    continue 'elements;
                }
                Some(_) => {}
                None => break 'elements,
            }
        }
        // Every test passed on: the body decides.
        break;
    }
    Some(*i - start)
}

/// `skip_one`'s substring loop: `memchr`'s searcher for the needle, built once — a SIMD
/// prefilter chosen at run time — where `str::contains` builds a searcher per call.
#[inline(never)]
fn pass_containing(l: &[crate::CelValue], i: &mut usize, needle: &str, invert: bool) -> usize {
    let finder = memchr::memmem::Finder::new(needle.as_bytes());
    pass_while!(l, i, |v| matches!(
        v, crate::CelValue::Str(x) if finder.find(x.as_bytes()).is_some() == invert
    ))
    .unwrap_or(0)
}

/// `skip_one`'s regex loop, in a frame of its own: small enough that the regex's search — and its
/// check that a haystack cannot match at all, which rejects most elements — inlines into it, where
/// inside `skip_one` it was an out-of-line call per element.
#[inline(never)]
fn pass_matching(l: &[crate::CelValue], i: &mut usize, r: &regex::Regex, invert: bool) -> usize {
    pass_while!(
        l,
        i,
        |v| matches!(v, crate::CelValue::Str(x) if r.is_match(x) == invert)
    )
    .unwrap_or(0)
}

/// Whether the region reaches GO ON for this element, every step answering. Each step's jump
/// condition is its `exec` arm's (`src/fast/mod.rs`); a step that would read the host or fail
/// hands the element off instead.
#[inline(always)]
fn passes<'a>(
    steps: &[Step],
    elem: Reg<'a>,
    entry: Option<Reg<'a>>,
    hints: &mut [usize; MAX_STEPS],
    vals: &mut [Reg<'a>; MAX_STEPS + 1],
    regs: &[Reg<'a>],
    code: &'a Code,
) -> bool {
    vals[0] = elem;
    let mut defined = 1;
    let mut s = 0;
    while let Some(step) = steps.get(s) {
        let jumps = match *step {
            Step::Member { obj, key } => {
                let Reg::Val(crate::CelValue::Map(m)) = vals[obj as usize] else {
                    // Not a bound map or record: the body's `Select` answers it.
                    return false;
                };
                match m.get_at(code.names[key as usize].as_str(), &mut hints[s]) {
                    Some(v) => vals[defined] = reg::of_cel(v),
                    // Missing: the body's `Select` raises.
                    None => return false,
                }
                defined += 1;
                false
            }
            Step::Entry => {
                let Some(v) = entry else { return false };
                vals[defined] = v;
                defined += 1;
                false
            }
            Step::Field {
                a,
                cache,
                test,
                invert,
                ..
            } => {
                let v = &regs[cache as usize];
                if matches!(v, Reg::Unset) {
                    // The first read is the body's.
                    return false;
                }
                match super::field_test(test, &vals[a as usize], v) {
                    Some(b) => b == invert,
                    // It fails: the body raises.
                    None => return false,
                }
            }
            Step::EqK { a, k, ne, .. } => super::eq_k(&vals[a as usize], code.kref(k)) == ne,
            Step::CmpK {
                a, k, op, invert, ..
            } => match super::ordering(&vals[a as usize], code.kref(k)) {
                Some(o) => op.holds(o) == invert,
                None => return false,
            },
            Step::Concat {
                cache,
                b,
                k,
                op,
                invert,
                ..
            } => match (&regs[cache as usize], &vals[b as usize], code.kref(k)) {
                (Reg::Str(x), Reg::Str(y), Reg::Str(z)) => op.test(x, y, z) == invert,
                // The first read, or a refusal: the body's.
                _ => return false,
            },
            Step::Pattern { a, re, invert, .. } => {
                match (&vals[a as usize], &code.regexes[re as usize]) {
                    (Reg::Str(x), Ok(r)) => r.is_match(x) == invert,
                    // Not a string, or a pattern that does not compile: the body raises.
                    _ => return false,
                }
            }
            Step::Matcher { a, m, invert, .. } => match &vals[a as usize] {
                Reg::Str(x) => code.matchers[m as usize].matches(x) == invert,
                _ => return false,
            },
            Step::Nop => false,
            Step::On => return true,
        };
        if !jumps {
            s += 1;
            continue;
        }
        match step.go() {
            Go::On => return true,
            Go::Step(t) => s = t as usize,
            Go::HandOff => return false,
        }
    }
    // Fell off the region: the body decides.
    false
}
