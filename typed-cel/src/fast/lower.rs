//! Lowering a CHECKED tree to the fast backend's register code.
//!
//! One walk, in the dialect's evaluation order (left to right; a member call's arguments before its
//! target): the order a node's operands are lowered is the order they run, so the reads happen in
//! that order and the error reported is the one the order meets. Errors do not unwind: every op
//! that can fail names the handler its failure jumps to, which is known here because handlers are
//! LEXICAL — the left operand of `&&`/`||`, the argument of `@not_strictly_false`, a
//! comprehension's step, or the top.

use std::collections::HashMap;
use std::sync::Arc;

use crate::common::ast::{
    operators, CallExpr, ComprehensionExpr, EntryExpr, Expr, IdedExpr, LiteralValue,
};
use crate::num::CelNum;
use crate::CelKey;
use crate::CelValue;
use crate::ExecutionError;

use super::host::{FieldPath, Step, Want};
use super::matcher::{NumSet, StrMatcher};
use super::reg::map_key;
use super::{
    Absorb, Arith, CVal, Cmp, Code, Concat, FieldTest, Kind, Op, Pc, StrOp, NO_CACHE, NO_REG, R,
    SCAN_WANTED,
};

/// Registers from here up are placeholders for a loop-invariant comprehension's result, each
/// given a real register past every other one when the program is finished. No expression needs
/// this many registers.
const PINNED: R = 0xC000;

/// Return where the result is known, rather than jumping to the one `Ret`: a `Jump` to a `Ret` is
/// that `Ret`, and a `Const` straight into the returned register, then `Ret`, is one `RetK`. Every
/// arm of a conditional that produces a constant ends a run in one op.
fn ret_early(ops: &mut [Op]) {
    for i in 0..ops.len() {
        if let Op::Jump { to } = ops[i] {
            if let Op::Ret { r } = ops[to as usize] {
                ops[i] = Op::Ret { r };
            }
        }
    }
    for i in 0..ops.len().saturating_sub(1) {
        if let (Op::Const { dst, k }, Op::Ret { r }) = (ops[i], ops[i + 1]) {
            if dst == r {
                ops[i] = Op::RetK { k };
            }
        }
    }
}

/// Is `e` a `&&`, `||` or `!` — a bool whose operands a branch can test without building them?
fn is_logic(e: &IdedExpr) -> bool {
    matches!(&e.expr, Expr::Call(c) if c.target.is_none()
    && matches!(
        (c.func_name.as_str(), c.args.len()),
        (operators::LOGICAL_AND | operators::LOGICAL_OR, 2) | (operators::LOGICAL_NOT, 1)
    ))
}

thread_local! {
    /// Set only by [`with_literal_comprehensions`]: every comprehension lowers as its expansion
    /// reads, so a test can hold a recognized loop's answers against the literal loop's.
    static LITERAL_COMPREHENSIONS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Run `f` with the predicate-loop lowering off: every `exists`/`all`/`exists_one` lowered on this
/// thread inside `f` is the expansion's literal loop. For differential tests only.
#[doc(hidden)]
pub fn with_literal_comprehensions<T>(f: impl FnOnce() -> T) -> T {
    let was = LITERAL_COMPREHENSIONS.with(|c| c.replace(true));
    let out = f();
    LITERAL_COMPREHENSIONS.with(|c| c.set(was));
    out
}

/// The longest list literal whose predicate loop is unrolled rather than built and iterated.
const MAX_UNROLLED: usize = 16;

/// The fewest `==`/`startsWith` leaves an `||` chain needs before it is answered by a matcher.
/// Below it the chain is cheaper as written.
const MIN_CHAIN: usize = 2;

pub(crate) fn lower(
    e: &IdedExpr,
    kinds: &HashMap<u64, Kind>,
    slots: &[(Arc<str>, CelValue)],
    hosts: &Arc<crate::hostfn::HostTable>,
    enums: &crate::hostfn::EnumTable,
) -> Result<Code, String> {
    lower_with(e, kinds, slots, hosts, enums, None, Folds::default())
}

/// The calls folded so far, by node id — each call's value, or `None` when running it failed —
/// and the ops that running them executed. Shared by a lowering and every lowering it starts to
/// fold a call, so each node is run once.
#[derive(Clone, Default)]
struct Folds(std::rc::Rc<std::cell::RefCell<FoldState>>);

#[derive(Default)]
struct FoldState {
    values: HashMap<u64, Option<CelValue>>,
    ops: Vec<&'static str>,
}

/// [`lower`], with the node `unfolded` (by id) never folded into a constant: the node being
/// lowered to compute its own constant (`Lower::fold_call`).
fn lower_with(
    e: &IdedExpr,
    kinds: &HashMap<u64, Kind>,
    slots: &[(Arc<str>, CelValue)],
    hosts: &Arc<crate::hostfn::HostTable>,
    enums: &crate::hostfn::EnumTable,
    unfolded: Option<u64>,
    folds: Folds,
) -> Result<Code, String> {
    let mut l = Lower {
        kinds,
        enums,
        code: Code {
            hosts: Arc::clone(hosts),
            ..Code::default()
        },
        names: HashMap::new(),
        fields: HashMap::new(),
        labels: Vec::new(),
        cold: Vec::new(),
        pinned: None,
        scope: Vec::new(),
        ranges: Vec::new(),
        slots: Vec::new(),
        next: 0,
        loops: 0,
        cached: HashMap::new(),
        pins: 0,
        unfolded,
        folds,
    };
    for (name, value) in slots {
        let k = l.konst(CVal::Val(value.clone()));
        l.slots.push((name.to_string(), k, value.clone()));
    }
    l.cache_reads(e)?;
    let fail = l.label();
    if is_logic(e) {
        // A `&&`/`||`/`!` result as a branch to one of two constant returns: the branch lowering
        // keeps absorption without building each operand's bool, and lets a comparison fuse with
        // the branch on it (`CondEqFF`, `CondEqK`, …).
        let otherwise = l.label();
        l.branch(e, otherwise, false, fail)?;
        let t = l.konst(CVal::Bool(true));
        l.push(Op::RetK { k: t });
        l.place(otherwise);
        let f = l.konst(CVal::Bool(false));
        l.push(Op::RetK { k: f });
    } else {
        let out = l.tmp()?;
        l.expr(e, out, fail)?;
        l.push(Op::Ret { r: out });
    }
    l.place(fail);
    l.push(Op::Fail);
    l.finish()
}

struct Lower<'k> {
    kinds: &'k HashMap<u64, Kind>,
    /// The environment's closed string sets.
    enums: &'k crate::hostfn::EnumTable,
    code: Code,
    names: HashMap<String, u32>,
    fields: HashMap<(String, Vec<(String, bool)>), u32>,
    /// Label id → where it was placed. Every jump target is a label id until `finish`.
    labels: Vec<Option<Place>>,
    /// Out-of-line code — a short-circuit's constant, a caught error's bookkeeping — appended after
    /// the main line, so the path a decision usually takes runs straight through.
    cold: Vec<Op>,
    /// The pc a jump lands on most recently — an op there cannot be fused with the one before it.
    pinned: Option<Pc>,
    /// Comprehension variables in scope, innermost last.
    scope: Vec<(String, R)>,
    /// The loops the walk is inside that iterate a collection: its range expression, the
    /// register the range is in, the loop variable's register and the loop's slot — so `m[k]`
    /// over the loop's own map and key is the iteration's current entry (`IndexIter`).
    ranges: Vec<(IdedExpr, R, R, u16)>,
    /// A residual's constant slots: name, constant, value.
    slots: Vec<(String, u32, CelValue)>,
    next: u16,
    /// How many loop bodies the walk is inside.
    loops: u32,
    /// The fields read more than once, each with the register its first read is kept in
    /// (`ReadCached`): chosen before the walk by [`Lower::cache_reads`].
    cached: HashMap<u32, R>,
    /// Loop-invariant comprehensions given a [`PINNED`] register so far.
    pins: u16,
    /// The node never folded: the one this lowering exists to compute (`fold_call`).
    unfolded: Option<u64>,
    /// Each call already folded, shared with the lowerings that fold (`Folds`).
    folds: Folds,
}

type Label = Pc;

/// Where a predicate loop's verdict goes.
#[derive(Clone, Copy)]
enum Outcome {
    /// Into a register.
    Value(R),
    /// A branch: to `target` when the verdict is `jump_if`, else fall through.
    Branch { target: Label, jump_if: bool },
}

/// What a conditional's arms compute.
#[derive(Clone, Copy)]
enum Arm {
    /// Their value.
    Value,
    /// Whether their value equals (`false`) or differs from (`true`) a scalar constant.
    EqK(u32, bool),
}

#[derive(Clone, Copy)]
enum Place {
    Hot(Pc),
    Cold(Pc),
}

impl Lower<'_> {
    fn push(&mut self, op: Op) {
        self.code.ops.push(op);
    }

    fn label(&mut self) -> Label {
        self.labels.push(None);
        (self.labels.len() - 1) as Label
    }

    fn place(&mut self, l: Label) {
        let pc = self.code.ops.len() as Pc;
        self.labels[l as usize] = Some(Place::Hot(pc));
        self.pinned = Some(pc);
    }

    /// `Clear r` — folded into the `IterNext` just before it when no jump lands between: a
    /// loop body's per-element reset rides the fetch.
    fn clear(&mut self, r: R) {
        let n = self.code.ops.len();
        if self.pinned != Some(n as Pc) {
            if let Some(Op::IterNext { clear, .. } | Op::IterScan { clear, .. }) =
                self.code.ops.last_mut()
            {
                if *clear == NO_REG {
                    *clear = r;
                    return;
                }
            }
        }
        self.push(Op::Clear { r });
    }

    fn place_cold(&mut self, l: Label) {
        self.labels[l as usize] = Some(Place::Cold(self.cold.len() as Pc));
    }

    fn push_cold(&mut self, op: Op) {
        self.cold.push(op);
    }

    fn tmp(&mut self) -> Result<R, String> {
        let r = self.next;
        self.next = self
            .next
            .checked_add(1)
            .ok_or("the expression needs more registers than the backend has")?;
        self.code.nregs = self.code.nregs.max(self.next as usize);
        Ok(r)
    }

    fn konst(&mut self, v: CVal) -> u32 {
        self.code.consts.push(v);
        (self.code.consts.len() - 1) as u32
    }

    fn name(&mut self, n: &str) -> u32 {
        if let Some(i) = self.names.get(n) {
            return *i;
        }
        self.code.names.push(CelKey::new(n));
        let i = (self.code.names.len() - 1) as u32;
        self.names.insert(n.to_string(), i);
        i
    }

    fn field(&mut self, root: &str, steps: &[(String, bool)]) -> u32 {
        let key = (root.to_string(), steps.to_vec());
        if let Some(i) = self.fields.get(&key) {
            return *i;
        }
        self.code.fields.push(FieldPath {
            root: root.to_string(),
            steps: steps
                .iter()
                .map(|(n, _)| Step {
                    name: CelKey::new(n),
                })
                .collect(),
        });
        let i = (self.code.fields.len() - 1) as u32;
        self.fields.insert(key, i);
        i
    }

    /// `x`, a read of a closed-set field, is one of `lits` (`ne`: is not): one tag test, when
    /// every literal is a listed value. `false` — nothing lowered — otherwise.
    fn try_tag_in(
        &mut self,
        x: &IdedExpr,
        lits: &[String],
        ne: bool,
        dst: R,
        h: Label,
    ) -> Result<bool, String> {
        let Some((root, steps)) = self.path(x) else {
            return Ok(false);
        };
        let names: Vec<&str> = std::iter::once(root.as_str())
            .chain(steps.iter().map(|(n, _)| n.as_str()))
            .collect();
        let Some(values) = self.enums.at(&names).cloned() else {
            return Ok(false);
        };
        let mut mask = 0u64;
        for lit in lits {
            match crate::hostfn::tag_of(&values, lit) {
                crate::hostfn::TAG_OTHER => return Ok(false),
                t => mask |= 1 << t,
            }
        }
        let set = match self
            .code
            .enum_sets
            .iter()
            .position(|v| Arc::ptr_eq(v, &values))
        {
            Some(i) => i,
            None => {
                self.code.enum_sets.push(values);
                self.code.enum_sets.len() - 1
            }
        };
        let set = u16::try_from(set).map_err(|_| "too many closed sets")?;
        let f = self.field(&root, &steps);
        self.push(Op::TagIn {
            dst,
            f,
            set,
            mask,
            ne,
            err: h,
        });
        Ok(true)
    }

    fn kind(&self, e: &IdedExpr) -> Kind {
        self.kinds.get(&e.id).copied().unwrap_or(Kind::Dyn)
    }

    fn local(&self, name: &str) -> Option<R> {
        self.scope
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, r)| *r)
    }

    fn slot(&self, name: &str) -> Option<&(String, u32, CelValue)> {
        self.slots.iter().find(|(n, ..)| n == name)
    }

    /// Resolve every label to its pc.
    fn finish(mut self) -> Result<Code, String> {
        self.assign_pinned()?;
        self.code.folded = self.folds.0.borrow().ops.clone();
        let hot = self.code.ops.len() as Pc;
        self.code.ops.append(&mut self.cold);
        let labels = self.labels;
        let at = |l: Pc| match labels[l as usize].expect("every label is placed") {
            Place::Hot(pc) => pc,
            Place::Cold(i) => hot + i,
        };
        for op in &mut self.code.ops {
            op.retarget(&at);
        }
        ret_early(&mut self.code.ops);
        super::scan::fuse(&mut self.code);
        self.code.seal();
        self.code
            .verify()
            .map_err(|e| format!("the lowered program is malformed: {e}"))?;
        Ok(self.code)
    }

    /// Give each loop-invariant comprehension its result register, past every register an
    /// expression uses, so nothing else writes it during a run.
    fn assign_pinned(&mut self) -> Result<(), String> {
        let mut next = self.code.nregs;
        let mut take = || -> Result<R, String> {
            let r = R::try_from(next)
                .ok()
                .filter(|r| *r < PINNED)
                .ok_or("the expression needs more registers than the backend has")?;
            next += 1;
            Ok(r)
        };
        let mut pinned = Vec::with_capacity(self.pins as usize);
        for _ in 0..self.pins {
            pinned.push(take()?);
        }
        let real = |r: R| {
            if r >= PINNED {
                pinned[(r - PINNED) as usize]
            } else {
                r
            }
        };
        for op in self.code.ops.iter_mut().chain(self.cold.iter_mut()) {
            match op {
                Op::BrSet { r, .. } => *r = real(*r),
                Op::Local { dst, src } => {
                    *dst = real(*dst);
                    *src = real(*src);
                }
                _ => {}
            }
        }
        self.code.nregs = next;
        Ok(())
    }

    /// Choose, before the walk, the fields worth keeping: one read at two or more sites, or at one
    /// inside a loop body, always as the same `Want`. Each gets a register below every other one,
    /// and its reads lower to `ReadCached`. The count mirrors the walk's own reads closely, not
    /// exactly — a field cached that the walk reads once, or read twice and not cached, costs a
    /// register or a re-read, never an answer.
    fn cache_reads(&mut self, e: &IdedExpr) -> Result<(), String> {
        let mut seen: HashMap<(String, Vec<(String, bool)>), (u32, bool, Option<Want>)> =
            HashMap::new();
        self.scan_reads(e, 0, &mut seen);
        let mut chosen: Vec<_> = seen
            .into_iter()
            .filter(|(_, (sites, in_loop, want))| (*sites > 1 || *in_loop) && want.is_some())
            .collect();
        chosen.sort_by(|a, b| a.0.cmp(&b.0));
        for ((root, steps), _) in chosen {
            let f = self.field(&root, &steps);
            let r = self.tmp()?;
            self.cached.insert(f, r);
        }
        Ok(())
    }

    fn scan_reads(
        &mut self,
        e: &IdedExpr,
        loops: u32,
        seen: &mut HashMap<(String, Vec<(String, bool)>), (u32, bool, Option<Want>)>,
    ) {
        if self.constant(e).is_some() {
            return;
        }
        let mut read = |this: &Self, e: &IdedExpr| -> bool {
            let Some(key) = this.path(e) else {
                return false;
            };
            let want = want(this.kind(e));
            let s = seen.entry(key).or_insert((0, false, Some(want)));
            s.0 += 1;
            s.1 |= loops > 0;
            if s.2 != Some(want) {
                s.2 = None;
            }
            true
        };
        match &e.expr {
            Expr::Ident(_) => {
                read(self, e);
            }
            Expr::Select(s) if s.test => self.scan_reads(&s.operand, loops, seen),
            Expr::Select(s) => {
                if !read(self, e) {
                    self.scan_reads(&s.operand, loops, seen);
                }
            }
            Expr::Call(c) => {
                if c.func_name == operators::INDEX && read(self, e) {
                    return;
                }
                if let Some(t) = c.target.as_deref() {
                    self.scan_reads(t, loops, seen);
                }
                for a in &c.args {
                    self.scan_reads(a, loops, seen);
                }
            }
            Expr::List(l) => {
                for x in &l.elements {
                    self.scan_reads(x, loops, seen);
                }
            }
            Expr::Map(m) => {
                for entry in &m.entries {
                    let EntryExpr::MapEntry(me) = &entry.expr;
                    self.scan_reads(&me.key, loops, seen);
                    self.scan_reads(&me.value, loops, seen);
                }
            }
            Expr::Comprehension(c) => {
                self.scan_reads(&c.iter_range, loops, seen);
                self.scan_reads(&c.accu_init, loops, seen);
                let depth = self.scope.len();
                // Names only: `path` asks whether a name is a loop variable, not its register.
                self.scope.push((c.accu_var.clone(), 0));
                self.scope.push((c.iter_var.clone(), 0));
                self.scan_reads(&c.loop_cond, loops + 1, seen);
                self.scan_reads(&c.loop_step, loops + 1, seen);
                self.scope.truncate(depth + 1);
                self.scan_reads(&c.result, loops, seen);
                self.scope.truncate(depth);
            }
            Expr::Literal(_) | Expr::Unspecified => {}
        }
    }

    /// `Read`, or `ReadCached` for a field [`Lower::cache_reads`] chose.
    fn read(&mut self, dst: R, f: u32, want: Want, err: Label) {
        self.push(match self.cached.get(&f) {
            Some(&cache) => Op::ReadCached {
                dst,
                f,
                cache,
                want,
                err,
            },
            None => Op::Read { dst, f, want, err },
        });
    }

    // ---- the walk ----

    /// Lower `e` so its value lands in `dst`; a failure jumps to `h`.
    fn expr(&mut self, e: &IdedExpr, dst: R, h: Label) -> Result<(), String> {
        let mark = self.next;
        let out = self.expr_inner(e, dst, h);
        self.next = mark;
        out
    }

    fn expr_inner(&mut self, e: &IdedExpr, dst: R, h: Label) -> Result<(), String> {
        if let Some(v) = self.constant(e) {
            let k = self.konst(v);
            self.push(Op::Const { dst, k });
            return Ok(());
        }
        match &e.expr {
            Expr::Literal(_) => unreachable!("a literal is a constant"),
            Expr::Ident(name) => {
                if let Some(r) = self.local(name) {
                    self.push(Op::Local { dst, src: r });
                } else if let Some((_, k, _)) = self.slot(name) {
                    let k = *k;
                    self.push(Op::Const { dst, k });
                } else {
                    let f = self.field(name, &[]);
                    let want = want(self.kind(e));
                    self.read(dst, f, want, h);
                }
            }
            Expr::Select(s) => {
                if s.test {
                    if let Some((root, mut steps)) = self.path(&s.operand) {
                        steps.push((s.field.clone(), false));
                        let f = self.field(&root, &steps);
                        self.push(Op::Has { dst, f, err: h });
                    } else {
                        let obj = self.operand(&s.operand, h)?;
                        let key = self.name(&s.field);
                        self.push(Op::HasOf {
                            dst,
                            obj,
                            key,
                            err: h,
                        });
                    }
                } else if let Some((root, steps)) = self.path(e) {
                    let f = self.field(&root, &steps);
                    let want = want(self.kind(e));
                    self.read(dst, f, want, h);
                } else {
                    // A loop variable is selected from in place.
                    let obj = self.operand(&s.operand, h)?;
                    let key = self.name(&s.field);
                    self.push(Op::Select {
                        dst,
                        obj,
                        key,
                        err: h,
                    });
                }
            }
            Expr::List(l) => {
                let start = self.next;
                for _ in &l.elements {
                    self.tmp()?;
                }
                for (i, el) in l.elements.iter().enumerate() {
                    self.expr(el, start + i as R, h)?;
                }
                let n = u16::try_from(l.elements.len()).map_err(|_| "a list literal too long")?;
                self.push(Op::MakeList { dst, start, n });
            }
            Expr::Map(m) => {
                let start = self.next;
                for _ in 0..m.entries.len() * 2 {
                    self.tmp()?;
                }
                for (i, entry) in m.entries.iter().enumerate() {
                    let EntryExpr::MapEntry(me) = &entry.expr;
                    let k = start + 2 * i as R;
                    self.expr(&me.key, k, h)?;
                    // A map literal checks each key BEFORE its value runs.
                    self.push(Op::CheckKey { r: k, err: h });
                    self.expr(&me.value, k + 1, h)?;
                }
                let n = u16::try_from(m.entries.len()).map_err(|_| "a map literal too long")?;
                self.push(Op::MakeMap { dst, start, n });
            }
            Expr::Call(c) => self.call(e, c, dst, h)?,
            Expr::Comprehension(c) => {
                if self.loops > 0 && !self.scope.iter().any(|(n, _)| names(e, n)) {
                    self.invariant_comprehension(c, dst, h)?
                } else {
                    self.comprehension(c, dst, h)?
                }
            }
            Expr::Unspecified => return Err("an unspecified expression".into()),
        }
        Ok(())
    }

    /// The root and member steps `e` reads, when it is a path from a root the HOST supplies —
    /// not a comprehension variable, not a constant slot.
    fn path(&self, e: &IdedExpr) -> Option<(String, Vec<(String, bool)>)> {
        match &e.expr {
            Expr::Ident(n) if self.local(n).is_none() && self.slot(n).is_none() => {
                Some((n.clone(), Vec::new()))
            }
            Expr::Select(s) if !s.test && self.kind_is_container(&s.operand) => {
                let (root, mut steps) = self.path(&s.operand)?;
                steps.push((s.field.clone(), false));
                Some((root, steps))
            }
            Expr::Call(c)
                if c.func_name == operators::INDEX
                    && c.target.is_none()
                    && c.args.len() == 2
                    && self.kind_is_container(&c.args[0]) =>
            {
                let Expr::Literal(LiteralValue::String(k)) = &c.args[1].expr else {
                    return None;
                };
                let (root, mut steps) = self.path(&c.args[0])?;
                steps.push((k.inner().to_string(), true));
                Some((root, steps))
            }
            _ => None,
        }
    }

    fn kind_is_container(&self, e: &IdedExpr) -> bool {
        matches!(self.kind(e), Kind::Record | Kind::Map)
    }

    /// The value `e` always has, when it has one without running: a literal, a list or map literal
    /// of those, `duration` of a string literal. A literal that CANNOT be built (a map literal
    /// with a key that is no key) is not a constant; it fails when it runs, as it does evaluated.
    fn constant(&self, e: &IdedExpr) -> Option<CVal> {
        let v = self.constant_value(e)?;
        Some(match v {
            CelValue::Bool(b) => CVal::Bool(b),
            CelValue::Num(_) | CelValue::Int(_) | CelValue::UInt(_) => {
                CVal::Num(v.num().expect("a number"))
            }
            CelValue::Null => CVal::Null,
            CelValue::Str(s) => CVal::Str(Box::from(&*s)),
            CelValue::Bytes(b) => CVal::Bytes(b.to_vec().into_boxed_slice()),
            CelValue::Duration(d) => CVal::Dur(d.delta()),
            // A literal list or map: one constant.
            other => CVal::Val(other),
        })
    }

    fn constant_value(&self, e: &IdedExpr) -> Option<CelValue> {
        match &e.expr {
            Expr::Literal(l) => Some(match l {
                LiteralValue::Boolean(b) => CelValue::Bool(*b.inner()),
                LiteralValue::Int(i) => CelValue::Int(*i),
                LiteralValue::UInt(u) => CelValue::from(*u),
                // Canonical: a literal `2.0` is the integer 2.
                LiteralValue::Double(d) => CelValue::from(CelNum::from_f64(*d.inner())),
                LiteralValue::String(s) => CelValue::Str(s.inner().into()),
                LiteralValue::Bytes(b) => CelValue::Bytes(b.inner().into()),
                LiteralValue::Null => CelValue::Null,
            }),
            Expr::List(l) => Some(CelValue::List(
                l.elements
                    .iter()
                    .map(|el| self.constant_value(el))
                    .collect::<Option<_>>()?,
            )),
            // `!` of a bool constant, `-` of a number constant: nothing to read, nothing to fail.
            Expr::Call(c)
                if c.target.is_none()
                    && c.args.len() == 1
                    && matches!(
                        c.func_name.as_str(),
                        operators::LOGICAL_NOT | operators::NEGATE
                    ) =>
            {
                match (c.func_name.as_str(), self.constant_value(&c.args[0])?) {
                    (operators::LOGICAL_NOT, CelValue::Bool(b)) => Some(CelValue::Bool(!b)),
                    // An overflowing negation (`-18446744073709551615`) is not folded: it
                    // fails when it runs, with the operator's error.
                    (
                        operators::NEGATE,
                        v @ (CelValue::Num(_) | CelValue::Int(_) | CelValue::UInt(_)),
                    ) => crate::num::neg(v.num()?).ok().map(CelValue::from),
                    _ => None,
                }
            }
            // Any other call over constants: run it (`fold_call`).
            Expr::Call(c) if self.unfolded != Some(e.id) => {
                if let Some(v) = self.folds.0.borrow().values.get(&e.id) {
                    return v.clone();
                }
                let closed = c
                    .target
                    .as_deref()
                    .map_or(true, |t| self.constant_value(t).is_some())
                    && c.args.iter().all(|a| self.constant_value(a).is_some());
                let v = if closed { self.fold_call(e) } else { None };
                self.folds.0.borrow_mut().values.insert(e.id, v.clone());
                v
            }
            Expr::Map(m) => {
                let mut out = Vec::with_capacity(m.entries.len());
                for entry in &m.entries {
                    let EntryExpr::MapEntry(me) = &entry.expr;
                    let k = map_key(&self.constant_value(&me.key)?)?;
                    let v = self.constant_value(&me.value)?;
                    out.push((k, v));
                }
                // A later duplicate key wins, as a map literal's does.
                Some(CelValue::Map(crate::CelMap::new(out)))
            }
            _ => None,
        }
    }

    /// A call whose operands are all constants, run once, here: lowered on its own (with itself
    /// unfolded) and evaluated over no roots, as the specializer runs a closed subtree. Only an
    /// answer is a constant; a failure keeps the call, so it fails at run time, in place. A host
    /// function is pure by contract (`register_host`); a CALL host fails with no dispatcher here,
    /// and so is never folded.
    fn fold_call(&self, e: &IdedExpr) -> Option<CelValue> {
        let code = lower_with(
            e,
            self.kinds,
            &[],
            &self.code.hosts,
            self.enums,
            Some(e.id),
            self.folds.clone(),
        )
        .ok()?;
        {
            let mut f = self.folds.0.borrow_mut();
            for op in &code.ops {
                if !f.ops.contains(&op.name()) {
                    f.ops.push(op.name());
                }
            }
        }
        let program = super::FastProgram {
            code,
            source: Arc::from(""),
        };
        program
            .eval_value(&crate::bindings::Bindings::default())
            .ok()
    }

    /// The value `e` has at compile time, as a constant slot or a literal.
    fn known(&self, e: &IdedExpr) -> Option<CelValue> {
        match &e.expr {
            Expr::Ident(n) if self.local(n).is_none() => Some(self.slot(n)?.2.clone()),
            _ => self.constant_value(e),
        }
    }

    /// The strings a collection known at compile time holds, as `in` and a comprehension see
    /// them: a list's elements, or a map's keys.
    fn known_strings(&self, e: &IdedExpr) -> Option<Vec<String>> {
        match self.known(e)? {
            CelValue::List(items) => items
                .iter()
                .map(|v| match v {
                    CelValue::Str(s) => Some(s.to_string()),
                    _ => None,
                })
                .collect(),
            CelValue::Map(m) => m
                .entries()
                .iter()
                .map(|(k, _)| match k {
                    crate::CelMapKey::Str(s) => Some(s.as_str().to_string()),
                    _ => None,
                })
                .collect(),
            _ => None,
        }
    }

    /// The numbers a LIST known at compile time holds, when every element is one.
    fn known_nums(&self, e: &IdedExpr) -> Option<Vec<CelNum>> {
        let CelValue::List(items) = self.known(e)? else {
            return None;
        };
        items.iter().map(CelValue::num).collect()
    }

    fn numset(&mut self, nums: Vec<CelNum>) -> u32 {
        self.code.numsets.push(NumSet::new(nums));
        (self.code.numsets.len() - 1) as u32
    }

    fn call(&mut self, e: &IdedExpr, c: &CallExpr, dst: R, h: Label) -> Result<(), String> {
        let n = c.func_name.as_str();
        let args = &c.args;
        match (n, c.target.as_deref(), args.len()) {
            (operators::CONDITIONAL, None, 3) => self.ternary(args, dst, h, Arm::Value)?,
            (operators::LOGICAL_OR | operators::LOGICAL_AND, None, 2) => {
                let or = n == operators::LOGICAL_OR;
                if or && self.try_match_chain(e, dst, h)? {
                    return Ok(());
                }
                // The LEFT operand's error is caught; the right one's propagates, even when the
                // left was an error too: when both sides fail, the RIGHT side's error is reported.
                // The right operand lands in `dst` directly: when the left passed it on, it IS the
                // answer, and `Absorb` has work only when the left was an error.
                let a = self.tmp()?;
                let (caught, right, short, end) =
                    (self.label(), self.label(), self.label(), self.label());
                self.expr(&args[0], a, caught)?;
                self.push(if or {
                    Op::BrTrue { r: a, to: short }
                } else {
                    Op::BrFalse { r: a, to: short }
                });
                self.place(right);
                self.expr(&args[1], dst, h)?;
                self.push(Op::Absorb { dst, a, or, err: h });
                self.place(end);
                let k = self.konst(CVal::Bool(or));
                self.place_cold(short);
                self.push_cold(Op::Const { dst, k });
                self.push_cold(Op::Jump { to: end });
                self.place_cold(caught);
                self.push_cold(Op::Catch { dst: a });
                self.push_cold(Op::Jump { to: right });
            }
            (operators::INDEX, None, 2) => {
                if let Some((root, steps)) = self.path(e) {
                    let f = self.field(&root, &steps);
                    let want = want(self.kind(e));
                    self.read(dst, f, want, h);
                    return Ok(());
                }
                if self.try_literal_index(&args[0], &args[1], dst, h)? {
                    return Ok(());
                }
                if let Some((a, b, slot)) = self.iter_index(&args[0], &args[1]) {
                    self.push(Op::IndexIter {
                        dst,
                        a,
                        b,
                        slot,
                        err: h,
                    });
                    return Ok(());
                }
                let (a, b) = self.two(&args[0], &args[1], h)?;
                self.push(Op::Index { dst, a, b, err: h });
            }
            (operators::IN, None, 2) => {
                // `"k" in x` for a record or map `x` read from a root: a presence question on the
                // member `k`, asked exactly as `has(x.k)` asks it (a lazy answers `presence`, a map
                // `contains_key`) — so a provider that answers by
                // field, a streamed document among them, never has to hand over the whole of `x`.
                if let (Some(k), true) =
                    (string_literal(&args[0]), self.kind_is_container(&args[1]))
                {
                    if let Some((root, mut steps)) = self.path(&args[1]) {
                        steps.push((k.to_string(), false));
                        let f = self.field(&root, &steps);
                        self.push(Op::Has { dst, f, err: h });
                        return Ok(());
                    }
                }
                if self.kind(&args[0]) == Kind::Str {
                    if let Some(set) = self.known_strings(&args[1]) {
                        if !set.is_empty() && self.try_tag_in(&args[0], &set, false, dst, h)? {
                            return Ok(());
                        }
                        let a = self.tmp()?;
                        self.expr(&args[0], a, h)?;
                        let m = self.matcher(set, Vec::new());
                        self.push(Op::Match { dst, a, m, err: h });
                        return Ok(());
                    }
                }
                if let Some(nums) = self.known_nums(&args[1]) {
                    let a = self.operand(&args[0], h)?;
                    let set = self.numset(nums);
                    self.push(Op::NumIn { dst, a, set });
                    return Ok(());
                }
                if self.try_in_literal(&args[0], &args[1], dst, h)? {
                    return Ok(());
                }
                let (a, b) = self.two(&args[0], &args[1], h)?;
                self.push(Op::In { dst, a, b, err: h });
            }
            (operators::EQUALS | operators::NOT_EQUALS, None, 2) => {
                let ne = n == operators::NOT_EQUALS;
                let op = if ne { Concat::Ne } else { Concat::Eq };
                if self.try_concat(&args[1], &args[0], op, false, dst, h)?
                    || self.try_concat(&args[0], &args[1], op, true, dst, h)?
                {
                    return Ok(());
                }
                // Against a scalar constant: one operand to run, and nothing to load. A constant
                // has no effect, so the other operand runs exactly where it did.
                for (x, y) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                    if let Some(c) = self.constant(y).filter(CVal::is_scalar) {
                        let k = self.konst(c);
                        return self.eq_k(x, k, ne, dst, h);
                    }
                }
                let (a, b) = self.two(&args[0], &args[1], h)?;
                self.push(if n == operators::EQUALS {
                    Op::Eq { dst, a, b }
                } else {
                    Op::Ne { dst, a, b }
                });
            }
            (
                operators::LESS
                | operators::LESS_EQUALS
                | operators::GREATER
                | operators::GREATER_EQUALS,
                None,
                2,
            ) => {
                let op = match n {
                    operators::LESS => Cmp::Lt,
                    operators::LESS_EQUALS => Cmp::Le,
                    operators::GREATER => Cmp::Gt,
                    _ => Cmp::Ge,
                };
                let (a, b) = self.two(&args[0], &args[1], h)?;
                self.push(Op::Cmp {
                    dst,
                    a,
                    b,
                    op,
                    err: h,
                });
            }
            (
                operators::ADD | operators::SUBSTRACT | operators::MULTIPLY | operators::DIVIDE,
                None,
                2,
            ) => {
                let op = match n {
                    operators::ADD => Arith::Add,
                    operators::SUBSTRACT => Arith::Sub,
                    operators::MULTIPLY => Arith::Mul,
                    _ => Arith::Div,
                };
                // A numeric constant on one side is read by the op, not loaded every time.
                let num_k = |this: &Self, e: &IdedExpr| match this.constant(e) {
                    Some(CVal::Num(n)) => Some(n),
                    _ => None,
                };
                let konst = match (num_k(self, &args[0]), num_k(self, &args[1])) {
                    (None, Some(k)) if self.kind(&args[0]) == Kind::Num => {
                        Some((&args[0], k, false))
                    }
                    (Some(k), None) if self.kind(&args[1]) == Kind::Num => {
                        Some((&args[1], k, true))
                    }
                    _ => None,
                };
                if let Some((x, k, rev)) = konst {
                    let a = self.operand(x, h)?;
                    let k = self.konst(CVal::Num(k));
                    self.push(Op::ArithK {
                        dst,
                        a,
                        k,
                        op,
                        rev,
                        err: h,
                    });
                    return Ok(());
                }
                let (a, b) = self.two(&args[0], &args[1], h)?;
                self.push(Op::Arith {
                    dst,
                    a,
                    b,
                    op,
                    err: h,
                });
            }
            (operators::LOGICAL_NOT, None, 1) => {
                let a = self.tmp()?;
                self.expr(&args[0], a, h)?;
                self.push(Op::Not { dst, a, err: h });
            }
            (operators::NEGATE, None, 1) => {
                let a = self.tmp()?;
                self.expr(&args[0], a, h)?;
                self.push(Op::Neg { dst, a, err: h });
            }
            (operators::NOT_STRICTLY_FALSE, None, 1) => {
                let a = self.tmp()?;
                let caught = self.label();
                let join = self.label();
                self.expr(&args[0], a, caught)?;
                self.push(Op::Jump { to: join });
                self.place(caught);
                self.push(Op::Catch { dst: a });
                self.place(join);
                self.push(Op::Nsf { dst, a });
            }
            ("size", None, 1) => {
                let a = self.tmp()?;
                self.expr(&args[0], a, h)?;
                self.push(Op::Size { dst, a, err: h });
            }
            ("size", Some(t), 0) => {
                let a = self.tmp()?;
                self.expr(t, a, h)?;
                self.push(Op::Size { dst, a, err: h });
            }
            ("startsWith" | "endsWith", Some(t), 1)
                if self.try_concat(
                    t,
                    &args[0],
                    if n == "startsWith" {
                        Concat::Prefix
                    } else {
                        Concat::Suffix
                    },
                    false,
                    dst,
                    h,
                )? || self.try_concat(
                    &args[0],
                    t,
                    if n == "startsWith" {
                        Concat::StartsWith
                    } else {
                        Concat::EndsWith
                    },
                    true,
                    dst,
                    h,
                )? => {}
            ("startsWith" | "endsWith" | "contains", Some(t), 1) => {
                let op = match n {
                    "startsWith" => StrOp::StartsWith,
                    "endsWith" => StrOp::EndsWith,
                    _ => StrOp::Contains,
                };
                // Every argument runs BEFORE the target.
                let (b, a) = self.two(&args[0], t, h)?;
                self.push(Op::StrOp {
                    dst,
                    a,
                    b,
                    op,
                    err: h,
                });
            }
            ("matches", Some(t), 1) => {
                let re = match &args[0].expr {
                    Expr::Literal(LiteralValue::String(p)) => self.regex(p.inner()),
                    _ => u32::MAX,
                };
                // A literal pattern is compiled already (`re`), and has no effect: it is not loaded.
                let (b, a) = if re == u32::MAX {
                    self.two(&args[0], t, h)?
                } else {
                    let a = self.operand(t, h)?;
                    (a, a)
                };
                self.push(Op::Matches {
                    dst,
                    a,
                    b,
                    re,
                    err: h,
                });
            }
            ("duration", None, 1) => {
                if let Expr::Literal(LiteralValue::String(s)) = &args[0].expr {
                    let k = match crate::duration::parse_duration(s.inner()) {
                        Ok((_, d)) => self.konst(CVal::Dur(d)),
                        Err(e) => {
                            let err = ExecutionError::function_error("duration", e.to_string());
                            let k = self.konst(CVal::Err(err));
                            self.push(Op::Raise { k, err: h });
                            return Ok(());
                        }
                    };
                    self.push(Op::Const { dst, k });
                    return Ok(());
                }
                let a = self.tmp()?;
                self.expr(&args[0], a, h)?;
                self.push(Op::Duration { dst, a, err: h });
            }
            ("getSeconds" | "getMilliseconds", Some(t), 0) => {
                let a = self.tmp()?;
                self.expr(t, a, h)?;
                self.push(Op::DurPart {
                    dst,
                    a,
                    millis: n == "getMilliseconds",
                    err: h,
                });
            }
            _ if self.code.hosts.index_of(n, c.target.is_some()).is_some() => {
                let ix = self
                    .code
                    .hosts
                    .index_of(n, c.target.is_some())
                    .expect("registered");
                let member = usize::from(c.target.is_some());
                let count = u16::try_from(args.len() + member)
                    .map_err(|_| "a host call with too many arguments")?;
                let start = self.next;
                for _ in 0..count {
                    self.tmp()?;
                }
                // Every argument runs BEFORE the target; the target is the call's first argument.
                for (i, a) in args.iter().enumerate() {
                    self.expr(a, start + (member + i) as R, h)?;
                }
                if let Some(t) = c.target.as_deref() {
                    self.expr(t, start, h)?;
                }
                self.push(Op::Host {
                    dst,
                    start,
                    n: count,
                    h: ix,
                    err: h,
                });
            }
            _ => {
                return Err(format!(
                    "`{n}` with {} argument(s){} has no lowering",
                    args.len(),
                    if c.target.is_some() {
                        " and a target"
                    } else {
                        ""
                    }
                ))
            }
        }
        Ok(())
    }

    /// `c ? a : b`, each arm lowered by `arm` into `dst`. The condition is lowered as control flow
    /// (`branch`), so `f == "x" && !g ? … : …` tests and jumps rather than building a bool.
    fn ternary(&mut self, args: &[IdedExpr], dst: R, h: Label, arm: Arm) -> Result<(), String> {
        let else_ = self.label();
        let end = self.label();
        self.branch(&args[0], else_, false, h)?;
        self.arm(&args[1], arm, dst, h)?;
        self.push(Op::Jump { to: end });
        self.place(else_);
        self.arm(&args[2], arm, dst, h)?;
        self.place(end);
        Ok(())
    }

    /// Lower the bool `e` as a branch: jump to `target` when its value is `jump_if`, fall through
    /// otherwise; an error (or a non-bool) fails to `h`, as `try_bool(e)?` does.
    ///
    /// `&&`/`||` keep their absorption without building a bool (`logic_chain`).
    fn branch(
        &mut self,
        e: &IdedExpr,
        target: Label,
        jump_if: bool,
        h: Label,
    ) -> Result<(), String> {
        let mark = self.next;
        let out = self.branch_inner(e, target, jump_if, h);
        self.next = mark;
        out
    }

    fn branch_inner(
        &mut self,
        e: &IdedExpr,
        target: Label,
        jump_if: bool,
        h: Label,
    ) -> Result<(), String> {
        if self.constant(e).is_none() {
            if let Expr::Call(c) = &e.expr {
                if c.target.is_none() && c.args.len() == 1 && c.func_name == operators::LOGICAL_NOT
                {
                    // `!` fails exactly where `try_bool` would.
                    return self.branch(&c.args[0], target, !jump_if, h);
                }
                let or = c.func_name == operators::LOGICAL_OR;
                if c.target.is_none()
                    && c.args.len() == 2
                    && (or || c.func_name == operators::LOGICAL_AND)
                    && !(or && self.matches_chain(e))
                {
                    return self.logic_chain(e, or, target, jump_if, h);
                }
            }
            if self.try_cmp_branch(e, target, jump_if, h)? {
                return Ok(());
            }
            if self.try_field_branch(e, target, jump_if, h)? {
                return Ok(());
            }
            // A predicate loop as control flow — unless `expr` would lower it another way: once,
            // cached, as a loop-invariant (`invariant_comprehension`), or by a known-set matcher
            // or an unrolling over a constant or literal range.
            if let Expr::Comprehension(c) = &e.expr {
                let invariant = self.loops > 0 && !self.scope.iter().any(|(n, _)| names(e, n));
                // A collection known at compile time — a residual's `$kN` slot is one — is
                // `try_match_exists`' (a matcher or a number set: one lookup, not a loop).
                if c.iter_var2.is_none()
                    && !invariant
                    && self.constant(&c.iter_range).is_none()
                    && self.known_strings(&c.iter_range).is_none()
                    && self.known_nums(&c.iter_range).is_none()
                    && !matches!(c.iter_range.expr, Expr::List(_))
                    && self.try_predicate_loop(c, Outcome::Branch { target, jump_if }, h)?
                {
                    return Ok(());
                }
            }
        }
        let cond = self.tmp()?;
        self.expr(e, cond, h)?;
        // `Const k; Read f; StrOp2 f, b, k` — a field tested against a concatenation ending in a
        // constant — and the branch on it: one `CondStrOp2F`, unless a jump lands inside.
        let n = self.code.ops.len();
        if n >= 3 && !matches!(self.pinned, Some(p) if p as usize + 2 >= n) {
            let read = match self.code.ops[n - 2] {
                Op::Read {
                    dst,
                    f,
                    want: Want::Str,
                    err,
                } => Some((dst, f, NO_CACHE, err)),
                Op::ReadCached {
                    dst,
                    f,
                    cache,
                    want: Want::Str,
                    err,
                } => Some((dst, f, cache, err)),
                _ => None,
            };
            if let (
                Op::Const { dst: kr, k },
                Some((ra, f, cache, rerr)),
                Op::StrOp2 {
                    dst: d,
                    a,
                    b,
                    c,
                    op,
                    err,
                },
            ) = (self.code.ops[n - 3], read, self.code.ops[n - 1])
            {
                if d == cond && a == ra && c == kr && b != kr && b != ra && rerr == err {
                    self.code.ops.truncate(n - 3);
                    self.push(Op::CondStrOp2F {
                        f,
                        cache,
                        b,
                        k,
                        op,
                        invert: jump_if,
                        else_: target,
                        err,
                    });
                    return Ok(());
                }
            }
        }
        // `Const k; Cmp a, k` — a comparison with a constant — and the branch on it: one op, unless
        // a jump lands on the comparison or after it.
        let n = self.code.ops.len();
        if n >= 2 && !matches!(self.pinned, Some(p) if p as usize + 1 >= n) {
            if let (
                Op::Const { dst: kr, k },
                Op::Cmp {
                    dst: d,
                    a,
                    b,
                    op,
                    err,
                },
            ) = (self.code.ops[n - 2], self.code.ops[n - 1])
            {
                // `k op x` is `x flip(op) k`.
                let fused = match (a == kr, b == kr) {
                    (false, true) => Some((a, op)),
                    (true, false) => Some((b, op.flip())),
                    _ => None,
                };
                if let (true, Some((a, op))) = (d == cond, fused) {
                    self.code.ops.truncate(n - 2);
                    self.push(Op::CondCmpK {
                        a,
                        k,
                        op,
                        invert: jump_if,
                        else_: target,
                        err,
                    });
                    return Ok(());
                }
            }
        }
        // Fuse the op that produced the bool with the branch on it — unless a jump lands between.
        let fused = match self.code.ops.last().copied() {
            _ if self.pinned == Some(self.code.ops.len() as Pc) => None,
            Some(Op::Read {
                dst: d,
                f,
                want: Want::Bool,
                err,
            }) if d == cond => Some(Op::CondRead {
                f,
                invert: jump_if,
                else_: target,
                err,
            }),
            Some(Op::EqK { dst: d, a, k, ne }) if d == cond => Some(Op::CondEqK {
                a,
                k,
                ne: ne != jump_if,
                else_: target,
            }),
            Some(Op::TagIn {
                dst: d,
                f,
                set,
                mask,
                ne,
                err,
            }) if d == cond => Some(Op::CondTagIn {
                f,
                set,
                mask,
                invert: jump_if != ne,
                else_: target,
                err,
            }),
            Some(Op::Match { dst: d, a, m, err }) if d == cond => Some(Op::CondMatch {
                a,
                m,
                invert: jump_if,
                else_: target,
                err,
            }),
            Some(Op::Matches {
                dst: d,
                a,
                b,
                re,
                err,
            }) if d == cond && re != u32::MAX && a == b => Some(Op::CondMatches {
                a,
                re,
                invert: jump_if,
                else_: target,
                err,
            }),
            _ => None,
        };
        match fused {
            Some(op) => *self.code.ops.last_mut().expect("the condition's op") = op,
            None => self.push(Op::Cond {
                r: cond,
                invert: jump_if,
                else_: target,
                err: h,
            }),
        }
        self.fuse_reads(jump_if);
        Ok(())
    }

    /// Fold the string reads a comparison-and-branch just lowered to into it:
    /// `Read a; Read b; Eq|Ne; Cond` becomes `CondEqFF`, `Read a; CondEqK` becomes `CondEqFK`.
    /// Reads keep their order and their shared error handler, so a failing read raises the same
    /// error at the same point. Nothing fuses across a jump target: a label placed on any op but
    /// the first would be left pointing past the fused op.
    fn fuse_reads(&mut self, jump_if: bool) {
        let ops = &self.code.ops;
        let n = ops.len();
        let lands_from = |from: usize| matches!(self.pinned, Some(p) if p as usize >= from);
        let read_str = |op: Op| match op {
            Op::Read {
                dst,
                f,
                want: Want::Str,
                err,
            } => Some((dst, f, err)),
            _ => None,
        };
        if n >= 4 && !lands_from(n - 3) {
            if let (
                Some((ra, fa, ea)),
                Some((rb, fb, eb)),
                eq,
                Op::Cond {
                    r, invert, else_, ..
                },
            ) = (
                read_str(ops[n - 4]),
                read_str(ops[n - 3]),
                ops[n - 2],
                ops[n - 1],
            ) {
                let cmp = match eq {
                    Op::Eq { dst, a, b } if dst == r && a == ra && b == rb => Some(false),
                    Op::Ne { dst, a, b } if dst == r && a == ra && b == rb => Some(true),
                    _ => None,
                };
                if let (Some(ne_op), true, true) = (cmp, ea == eb, ra != rb) {
                    debug_assert_eq!(invert, jump_if);
                    self.code.ops.truncate(n - 4);
                    self.code.ops.push(Op::CondEqFF {
                        a: fa,
                        b: fb,
                        ne: jump_if != ne_op,
                        else_,
                        err: ea,
                    });
                    return;
                }
            }
        }
        let ops = &self.code.ops;
        let n = ops.len();
        if n >= 2 && !lands_from(n - 1) {
            if let (Some((ra, fa, ea)), Op::CondEqK { a, k, ne, else_ }) =
                (read_str(ops[n - 2]), ops[n - 1])
            {
                if a == ra {
                    self.code.ops.truncate(n - 2);
                    self.code.ops.push(Op::CondEqFK {
                        a: fa,
                        k,
                        ne,
                        else_,
                        err: ea,
                    });
                }
            }
        }
    }

    /// A maximal `&&` (or `||`) chain as a branch to `target` when its result is `jump_if`:
    /// every leaf a branch in turn, left to right, rather than a tree of pairs.
    ///
    /// The ABSORBING value (`false` for `&&`, `true` for `||`) on any leaf decides, whatever
    /// failed before it — the leaf jumps straight out. A failing leaf is caught and the chain goes
    /// on; with no absorbing leaf, the LAST failure is the chain's error. That is the binary rule
    /// (an absorbing side decides; when both sides fail the right side's error is reported)
    /// applied over any tree of the same operator, whose rightmost failure is always the one
    /// that survives.
    ///
    /// ```text
    ///        Clear E                               (when a leaf can fail)
    ///        <leaf₁ as a branch: absorbing → SETTLED; error → C₁>
    /// N₁:    …
    ///        <leafₙ …>
    /// Nₙ:    RaisePending E                        the last failure, if any
    /// Cᵢ:    Catch E; Jump Nᵢ                      (cold)
    /// ```
    fn logic_chain(
        &mut self,
        e: &IdedExpr,
        or: bool,
        target: Label,
        jump_if: bool,
        h: Label,
    ) -> Result<(), String> {
        let op = if or {
            operators::LOGICAL_OR
        } else {
            operators::LOGICAL_AND
        };
        let mut leaves = Vec::new();
        chain_leaves(e, op, &mut leaves);
        // A constant leaf that passes the result on changes nothing; one that settles it settles
        // the chain, whatever the leaves around it do (their reads have no effect, and their
        // failures are absorbed).
        let mut kept = Vec::with_capacity(leaves.len());
        for leaf in leaves {
            match self.constant(leaf) {
                Some(CVal::Bool(b)) if b != or => {}
                Some(CVal::Bool(_)) => {
                    if jump_if == or {
                        self.push(Op::Jump { to: target });
                    }
                    return Ok(());
                }
                _ => kept.push(leaf),
            }
        }
        match kept.as_slice() {
            // Every leaf passed: the non-absorbing value.
            [] => {
                if jump_if != or {
                    self.push(Op::Jump { to: target });
                }
                return Ok(());
            }
            // One leaf is the chain, its failure the chain's.
            [one] => return self.branch(one, target, jump_if, h),
            _ => {}
        }
        let leaves = kept;
        // Only a failure with a leaf after it can be absorbed; the last leaf's is the chain's
        // when no earlier leaf can fail.
        let last = leaves.len() - 1;
        let fallible = leaves[..last].iter().any(|l| !self.infallible(l));
        let mut budget = SPLIT_NODES;
        if fallible && leaves.iter().all(|l| self.small(l, &mut budget)) {
            return self.split_chain(&leaves, or, target, jump_if, h);
        }
        let pend = self.tmp()?;
        if fallible {
            self.clear(pend);
        }
        let settled = if jump_if == or { target } else { self.label() };
        for (i, leaf) in leaves.into_iter().enumerate() {
            if i == last && !fallible {
                self.branch(leaf, settled, or, h)?;
                continue;
            }
            let (next, caught) = (self.label(), self.label());
            self.branch(leaf, settled, or, caught)?;
            self.place(next);
            self.place_cold(caught);
            self.push_cold(Op::Catch { dst: pend });
            self.push_cold(Op::Jump { to: next });
        }
        if fallible {
            self.push(Op::RaisePending { pend, err: h });
        }
        if jump_if != or {
            self.push(Op::Jump { to: target });
            self.place(settled);
        }
        Ok(())
    }

    /// Does `e` fit in `budget` nodes, a constant subtree counted as one, with no comprehension
    /// (a loop is never lowered twice)?
    fn small(&self, e: &IdedExpr, budget: &mut i32) -> bool {
        *budget -= 1;
        if *budget < 0 {
            return false;
        }
        if self.constant(e).is_some() {
            return true;
        }
        match &e.expr {
            Expr::Ident(_) | Expr::Literal(_) => true,
            Expr::Select(s) => self.small(&s.operand, budget),
            Expr::Call(c) => {
                c.target.as_deref().map_or(true, |t| self.small(t, budget))
                    && c.args.iter().all(|a| self.small(a, budget))
            }
            _ => false,
        }
    }

    /// [`Lower::logic_chain`] for a fallible chain, with nothing pending on the path no leaf
    /// fails: only a caught failure makes an error pending, so the leaves run twice over — as
    /// written, and again after a failure, in a copy that ends by raising it. The path no leaf
    /// fails on carries no `Clear` and no `RaisePending`, and its last leaf branches to where the
    /// chain's non-absorbing value goes (a loop's next element) itself.
    ///
    /// ```text
    ///        <leaf₁: absorbing → SETTLED; error → C₁>
    ///        …
    ///        <leafₙ: non-absorbing → TARGET; error → h>     (or: absorbing → TARGET, then Jump END)
    ///        Jump SETTLED
    /// P₂:    <leaf₂: absorbing → SETTLED; error → C₂>        the copy, after a failure
    ///        …
    ///        <leafₙ: absorbing → SETTLED; error → h>
    ///        RaisePending E; Jump TARGET                    (or: fall through to END)
    /// Cᵢ:    Catch E; Jump Pᵢ₊₁                              (cold)
    /// ```
    ///
    /// The rightmost failure is still the chain's: every `Catch` overwrites `E`, and the last
    /// leaf's own failure goes straight to `h` in both copies.
    fn split_chain(
        &mut self,
        leaves: &[&IdedExpr],
        or: bool,
        target: Label,
        jump_if: bool,
        h: Label,
    ) -> Result<(), String> {
        let last = leaves.len() - 1;
        let pend = self.tmp()?;
        // Where the chain's non-absorbing value jumps; `None` when it falls through past the chain.
        let nonabs = (jump_if != or).then_some(target);
        let settled = if jump_if == or { target } else { self.label() };
        let end = self.label();
        let caught: Vec<Label> = (0..last).map(|_| self.label()).collect();
        let copy: Vec<Label> = (0..=last).map(|_| self.label()).collect();
        for (i, leaf) in leaves.iter().enumerate() {
            if i < last {
                self.branch(leaf, settled, or, caught[i])?;
            } else if let Some(t) = nonabs {
                self.branch(leaf, t, !or, h)?;
                self.push(Op::Jump { to: settled });
            } else {
                self.branch(leaf, settled, or, h)?;
                self.push(Op::Jump { to: end });
            }
        }
        for (i, leaf) in leaves.iter().enumerate().skip(1) {
            self.place(copy[i]);
            let err = if i < last { caught[i] } else { h };
            self.branch(leaf, settled, or, err)?;
        }
        self.push(Op::RaisePending { pend, err: h });
        match nonabs {
            Some(t) => {
                self.push(Op::Jump { to: t });
                self.place(settled);
            }
            None => self.place(end),
        }
        for i in 0..last {
            self.place_cold(caught[i]);
            self.push_cold(Op::Catch { dst: pend });
            self.push_cold(Op::Jump { to: copy[i + 1] });
        }
        Ok(())
    }

    /// `f < k` (any ordering, either side) for a field `f` and a constant `k`, as a branch: one
    /// `CondCmpFK`, reading through `f`'s cache register when it has one.
    fn try_cmp_branch(
        &mut self,
        e: &IdedExpr,
        target: Label,
        jump_if: bool,
        h: Label,
    ) -> Result<bool, String> {
        let Expr::Call(c) = &e.expr else {
            return Ok(false);
        };
        let op = match (c.func_name.as_str(), c.target.is_none(), c.args.len()) {
            (operators::LESS, true, 2) => Cmp::Lt,
            (operators::LESS_EQUALS, true, 2) => Cmp::Le,
            (operators::GREATER, true, 2) => Cmp::Gt,
            (operators::GREATER_EQUALS, true, 2) => Cmp::Ge,
            _ => return Ok(false),
        };
        let (field, konst, op) = match (
            self.constant(&c.args[0]).filter(CVal::is_scalar),
            self.constant(&c.args[1]).filter(CVal::is_scalar),
        ) {
            (None, Some(k)) => (&c.args[0], k, op),
            // `k < f` is `f > k`: the constant has no effect, so the read runs where it did.
            (Some(k), None) => (&c.args[1], k, op.flip()),
            _ => return Ok(false),
        };
        let Some((root, steps)) = self.path(field) else {
            return Ok(false);
        };
        let f = self.field(&root, &steps);
        let want = want(self.kind(field));
        let cache = self.cached.get(&f).copied().unwrap_or(NO_CACHE);
        let k = self.konst(konst);
        self.push(Op::CondCmpFK {
            f,
            cache,
            want,
            k,
            op,
            invert: jump_if,
            else_: target,
            err: h,
        });
        Ok(true)
    }

    /// `x == f`, `f < x`, `f.startsWith(x)`, … for a field `f` (a root path) and an operand `x`,
    /// as one `CondFR`: the test normalized to "register op field", the field read through its
    /// cache register. The field is read after `x` is in its register, so fusing never moves a
    /// field read ahead of a failure that came first: when the field runs first in source order —
    /// the left operand of a comparison, or the ARGUMENT of a string test (an argument runs before
    /// its receiver) — `x` must be a loop variable, which cannot fail.
    fn try_field_branch(
        &mut self,
        e: &IdedExpr,
        target: Label,
        jump_if: bool,
        h: Label,
    ) -> Result<bool, String> {
        let Expr::Call(c) = &e.expr else {
            return Ok(false);
        };
        let is_field =
            |this: &Self, x: &IdedExpr| this.constant(x).is_none() && this.path(x).is_some();
        // (the field, the other operand, the test, whether the field runs first)
        let (field, other, test, field_first) =
            match (c.func_name.as_str(), c.target.as_deref(), c.args.as_slice()) {
                (n, None, [l, r]) => {
                    let (test, flipped) = match n {
                        operators::EQUALS => (FieldTest::Eq { ne: false }, None),
                        operators::NOT_EQUALS => (FieldTest::Eq { ne: true }, None),
                        operators::LESS => (FieldTest::Cmp(Cmp::Lt), Some(Cmp::Gt)),
                        operators::LESS_EQUALS => (FieldTest::Cmp(Cmp::Le), Some(Cmp::Ge)),
                        operators::GREATER => (FieldTest::Cmp(Cmp::Gt), Some(Cmp::Lt)),
                        operators::GREATER_EQUALS => (FieldTest::Cmp(Cmp::Ge), Some(Cmp::Le)),
                        _ => return Ok(false),
                    };
                    match (is_field(self, l), is_field(self, r)) {
                        // `x op f`
                        (false, true) => (r, l, test, false),
                        // `f op x` is `x flip(op) f`
                        (true, false) => (l, r, flipped.map_or(test, FieldTest::Cmp), true),
                        _ => return Ok(false),
                    }
                }
                (n @ ("startsWith" | "endsWith" | "contains"), Some(recv), [arg]) => {
                    let o = match n {
                        "startsWith" => StrOp::StartsWith,
                        "endsWith" => StrOp::EndsWith,
                        _ => StrOp::Contains,
                    };
                    // Every argument runs BEFORE the target.
                    match (is_field(self, recv), is_field(self, arg)) {
                        (true, false) => (recv, arg, FieldTest::FieldRecv(o), false),
                        (false, true) => (arg, recv, FieldTest::RegRecv(o), true),
                        _ => return Ok(false),
                    }
                }
                _ => return Ok(false),
            };
        let (kf, kx) = (self.kind(field), self.kind(other));
        let kinds = match test {
            FieldTest::Eq { .. } => {
                kf == kx && matches!(kf, Kind::Num | Kind::Str | Kind::Bool | Kind::Duration)
            }
            FieldTest::Cmp(_) => kf == kx && matches!(kf, Kind::Num | Kind::Str | Kind::Duration),
            FieldTest::FieldRecv(_) | FieldTest::RegRecv(_) => kf == Kind::Str && kx == Kind::Str,
        };
        if !kinds {
            return Ok(false);
        }
        // A concatenation tested is `try_concat`'s: `StrOp2` tests it unbuilt.
        if let Expr::Call(cat) = &other.expr {
            if cat.func_name == operators::ADD && cat.target.is_none() {
                return Ok(false);
            }
        }
        let a = match &other.expr {
            Expr::Ident(n) if self.local(n).is_some() => self.local(n).expect("a local"),
            _ if !field_first => self.operand(other, h)?,
            _ => return Ok(false),
        };
        let (root, steps) = self.path(field).expect("a field");
        let f = self.field(&root, &steps);
        let want = want(kf);
        let cache = self.cached.get(&f).copied().unwrap_or(NO_CACHE);
        self.push(Op::CondFR {
            a,
            f,
            cache,
            want,
            test,
            invert: jump_if,
            else_: target,
            err: h,
        });
        Ok(true)
    }

    /// `m[k]` where `k` is the variable of an enclosing loop over the map `m` itself: that loop's
    /// range register, `k`'s register and the loop's slot. Reading `m` again would read what the
    /// loop already read (a field cannot change during a run), so it is not read.
    fn iter_index(&self, map: &IdedExpr, key: &IdedExpr) -> Option<(R, R, u16)> {
        let Expr::Ident(n) = &key.expr else {
            return None;
        };
        let var = self.local(n)?;
        if self.kind(map) != Kind::Map {
            return None;
        }
        self.ranges
            .iter()
            .rev()
            .find(|(range, _, v, _)| *v == var && same_shape(range, map))
            .map(|(_, r, v, slot)| (*r, *v, *slot))
    }

    /// Would `try_match_chain` answer this `||` tree with a matcher?
    fn matches_chain(&self, e: &IdedExpr) -> bool {
        if num_chain(e).is_some() {
            return true;
        }
        let mut leaves = Vec::new();
        or_leaves(e, &mut leaves);
        if leaves.len() < MIN_CHAIN {
            return false;
        }
        let mut needle: Option<&IdedExpr> = None;
        for leaf in leaves {
            let Some((n, _, _)) = literal_leaf(leaf) else {
                return false;
            };
            if !self.pure_string(n) {
                return false;
            }
            match needle {
                None => needle = Some(n),
                Some(m) if same_shape(m, n) => {}
                Some(_) => return false,
            }
        }
        true
    }

    fn arm(&mut self, e: &IdedExpr, arm: Arm, dst: R, h: Label) -> Result<(), String> {
        match arm {
            Arm::Value => self.expr(e, dst, h),
            Arm::EqK(k, ne) => self.eq_k(e, k, ne, dst, h),
        }
    }

    /// `x == k` (or `!=`) for a scalar constant `k`. Over a conditional the comparison moves into
    /// its arms — `(c ? "a" : "b") == "a"` is `c ? true : false` — which runs the same operands
    /// in the same order, and folds where an arm is itself a constant.
    fn eq_k(&mut self, x: &IdedExpr, k: u32, ne: bool, dst: R, h: Label) -> Result<(), String> {
        let mark = self.next;
        let out = self.eq_k_inner(x, k, ne, dst, h);
        self.next = mark;
        out
    }

    fn eq_k_inner(
        &mut self,
        x: &IdedExpr,
        k: u32,
        ne: bool,
        dst: R,
        h: Label,
    ) -> Result<(), String> {
        if let Expr::Call(c) = &x.expr {
            if c.func_name == operators::CONDITIONAL && c.target.is_none() && c.args.len() == 3 {
                return self.ternary(&c.args, dst, h, Arm::EqK(k, ne));
            }
        }
        if let Some(c) = self.constant(x).filter(CVal::is_scalar) {
            let same = super::reg::equals(c.reg_of(), self.code.consts[k as usize].reg_of());
            let k = self.konst(CVal::Bool(same != ne));
            self.push(Op::Const { dst, k });
            return Ok(());
        }
        if let CVal::Str(lit) = &self.code.consts[k as usize] {
            let lit = [lit.to_string()];
            if self.try_tag_in(x, &lit, ne, dst, h)? {
                return Ok(());
            }
        }
        let a = self.operand(x, h)?;
        self.push(Op::EqK { dst, a, k, ne });
        Ok(())
    }

    /// The register `e`'s value is in: a loop variable's own, read in place, or a fresh one `e` is
    /// lowered into. Only ever read by the op that takes it.
    fn operand(&mut self, e: &IdedExpr, h: Label) -> Result<R, String> {
        if let Expr::Ident(n) = &e.expr {
            if let Some(r) = self.local(n) {
                return Ok(r);
            }
        }
        let r = self.tmp()?;
        self.expr(e, r, h)?;
        Ok(r)
    }

    /// Can `e` never fail, whatever its loop variables hold? `==`/`!=` over constants and loop
    /// variables, and `&&`/`||`/`!` of those: a predicate that cannot fail needs no pending-error
    /// bookkeeping.
    fn infallible(&self, e: &IdedExpr) -> bool {
        let simple = |x: &IdedExpr| {
            self.constant(x).is_some()
                || matches!(&x.expr, Expr::Ident(n) if self.local(n).is_some())
        };
        let Expr::Call(c) = &e.expr else {
            return false;
        };
        if c.target.is_some() {
            return false;
        }
        match (c.func_name.as_str(), c.args.as_slice()) {
            (operators::EQUALS | operators::NOT_EQUALS, [a, b]) => simple(a) && simple(b),
            (operators::LOGICAL_AND | operators::LOGICAL_OR, [a, b]) => {
                self.infallible(a) && self.infallible(b)
            }
            (operators::LOGICAL_NOT, [a]) => self.infallible(a),
            _ => false,
        }
    }

    /// `a` tested against `cat` by `op`, when `cat` is a two-piece string concatenation `b + c`:
    /// one `StrOp2` over the pieces, the concatenation never built. `a_first` is whether `a`
    /// runs before the pieces (it is the call's argument, or `=='s` left) or after them; either
    /// way every operand runs, and reads, exactly where it did. `false` — nothing lowered — when
    /// `cat` is no such concatenation. A chain of three or more pieces builds all but its last.
    fn try_concat(
        &mut self,
        a: &IdedExpr,
        cat: &IdedExpr,
        op: Concat,
        a_first: bool,
        dst: R,
        h: Label,
    ) -> Result<bool, String> {
        let Expr::Call(c) = &cat.expr else {
            return Ok(false);
        };
        let pieces = match (c.func_name.as_str(), c.target.as_deref(), c.args.as_slice()) {
            (operators::ADD, None, [x, y]) => (x, y),
            _ => return Ok(false),
        };
        // Only strings: a string `+` cannot fail, so leaving it unbuilt moves no error.
        if [a, cat, pieces.0, pieces.1]
            .iter()
            .any(|e| self.kind(e) != Kind::Str)
            || self.constant(cat).is_some()
        {
            return Ok(false);
        }
        // Each operand in place where it already is (a loop variable), else in a register of its own.
        let ra_first = if a_first {
            Some(self.operand(a, h)?)
        } else {
            None
        };
        let rb = self.operand(pieces.0, h)?;
        let rc = self.operand(pieces.1, h)?;
        let ra = match ra_first {
            Some(r) => r,
            None => self.operand(a, h)?,
        };
        self.push(Op::StrOp2 {
            dst,
            a: ra,
            b: rb,
            c: rc,
            op,
            err: h,
        });
        Ok(true)
    }

    /// `x in [a, b, …]` over a list literal that is not a constant: `x`, then every element in
    /// order (each read, and each failure, where building the list did them), then an `==` chain
    /// over the registers — the list itself never built. A constant element is compared as one.
    fn try_in_literal(
        &mut self,
        x: &IdedExpr,
        list: &IdedExpr,
        dst: R,
        h: Label,
    ) -> Result<bool, String> {
        let Expr::List(l) = &list.expr else {
            return Ok(false);
        };
        if l.elements.is_empty() || self.constant(list).is_some() {
            return Ok(false);
        }
        let rx = self.operand(x, h)?;
        let mut items = Vec::with_capacity(l.elements.len());
        for el in &l.elements {
            items.push(match self.constant(el).filter(CVal::is_scalar) {
                Some(c) => Err(self.konst(c)),
                None => Ok(self.operand(el, h)?),
            });
        }
        let end = self.label();
        let last = items.len() - 1;
        for (i, item) in items.into_iter().enumerate() {
            self.push(match item {
                Ok(b) => Op::Eq { dst, a: rx, b },
                Err(k) => Op::EqK {
                    dst,
                    a: rx,
                    k,
                    ne: false,
                },
            });
            if i < last {
                self.push(Op::BrTrue { r: dst, to: end });
            }
        }
        self.place(end);
        Ok(true)
    }

    /// `{k: v, …}[K]` for a map literal whose keys are constants, `K` a constant key it has: every
    /// entry's value runs in order (its failure is still the map's), and the last one under `K`
    /// is the answer — the map never built. A key the literal lacks keeps the built lowering,
    /// whose `no such key` it is.
    fn try_literal_index(
        &mut self,
        map: &IdedExpr,
        key: &IdedExpr,
        dst: R,
        h: Label,
    ) -> Result<bool, String> {
        let Expr::Map(m) = &map.expr else {
            return Ok(false);
        };
        if self.constant(map).is_some() {
            return Ok(false);
        }
        let Some(k) = self.constant_value(key).as_ref().and_then(map_key) else {
            return Ok(false);
        };
        let mut chosen = None;
        for (i, entry) in m.entries.iter().enumerate() {
            let EntryExpr::MapEntry(me) = &entry.expr;
            match self.constant_value(&me.key).as_ref().and_then(map_key) {
                Some(ki) if ki == k => chosen = Some(i),
                Some(_) => {}
                None => return Ok(false),
            }
        }
        let Some(chosen) = chosen else {
            return Ok(false);
        };
        for (i, entry) in m.entries.iter().enumerate() {
            let EntryExpr::MapEntry(me) = &entry.expr;
            if i == chosen {
                self.expr(&me.value, dst, h)?;
            } else if self.constant(&me.value).is_none() {
                let t = self.tmp()?;
                self.expr(&me.value, t, h)?;
            }
        }
        Ok(true)
    }

    /// Lower two operands in order into fresh registers.
    fn two(&mut self, x: &IdedExpr, y: &IdedExpr, h: Label) -> Result<(R, R), String> {
        let a = self.operand(x, h)?;
        let b = self.operand(y, h)?;
        Ok((a, b))
    }

    fn regex(&mut self, pattern: &str) -> u32 {
        self.code
            .regexes
            .push(
                regex::Regex::new(pattern).map_err(|err| ExecutionError::FunctionError {
                    function: "matches".to_string(),
                    message: format!("'{pattern}' not a valid regex:\n{err}"),
                }),
            );
        (self.code.regexes.len() - 1) as u32
    }

    fn matcher(&mut self, eq: Vec<String>, prefix: Vec<String>) -> u32 {
        self.code.matchers.push(StrMatcher::new(
            eq.into_iter().map(String::into_boxed_str).collect(),
            prefix.into_iter().map(String::into_boxed_str).collect(),
        ));
        (self.code.matchers.len() - 1) as u32
    }

    // ---- pattern recognition ----

    /// A whole `||` tree whose every leaf is `N == "lit"`, `"lit" == N` or `N.startsWith("lit")`
    /// over ONE string needle `N` — a specialized `exists` over a known list, unrolled — is
    /// answered by one read of `N` and a matcher. Only a WHOLE tree: every leaf's only failure is
    /// reading `N`, so the tree fails exactly when `N` does, with `N`'s error.
    fn try_match_chain(&mut self, e: &IdedExpr, dst: R, h: Label) -> Result<bool, String> {
        if let Some((needle, nums)) = num_chain(e) {
            let a = self.operand(needle, h)?;
            let set = self.numset(nums);
            self.push(Op::NumIn { dst, a, set });
            return Ok(true);
        }
        let mut leaves = Vec::new();
        or_leaves(e, &mut leaves);
        if leaves.len() < MIN_CHAIN {
            return Ok(false);
        }
        let mut needle: Option<&IdedExpr> = None;
        let (mut eq, mut prefix) = (Vec::new(), Vec::new());
        for leaf in leaves {
            let Some((n, lit, is_prefix)) = literal_leaf(leaf) else {
                return Ok(false);
            };
            if !self.pure_string(n) {
                return Ok(false);
            }
            match needle {
                None => needle = Some(n),
                Some(m) if same_shape(m, n) => {}
                Some(_) => return Ok(false),
            }
            if is_prefix {
                prefix.push(lit.to_string());
            } else {
                eq.push(lit.to_string());
            }
        }
        let needle = needle.expect("at least one leaf");
        if prefix.is_empty() && self.try_tag_in(needle, &eq, false, dst, h)? {
            return Ok(true);
        }
        let a = self.tmp()?;
        self.expr(needle, a, h)?;
        let m = self.matcher(eq, prefix);
        self.push(Op::Match { dst, a, m, err: h });
        Ok(true)
    }

    /// A string-typed expression whose value is the same every time it is read: a path from a
    /// root, a comprehension variable, a slot.
    fn pure_string(&self, e: &IdedExpr) -> bool {
        self.kind(e) == Kind::Str && pure(e)
    }

    /// `L.exists(r, <leaves over r>)` over a KNOWN list of strings, each leaf `N == r`, `r == N`,
    /// `N.startsWith(r)` or `N.startsWith(r + "lit")` with one needle `N` that names neither loop
    /// variable: one matcher built from `L` directly, however long `L` is. An empty `L` reads
    /// nothing and is `false`, as the loop is.
    fn try_match_exists(
        &mut self,
        c: &ComprehensionExpr,
        dst: R,
        h: Label,
    ) -> Result<bool, String> {
        let Expr::Literal(LiteralValue::Boolean(init)) = &c.accu_init.expr else {
            return Ok(false);
        };
        if *init.inner() || !matches!(&c.result.expr, Expr::Ident(n) if *n == c.accu_var) {
            return Ok(false);
        }
        let Expr::Call(step) = &c.loop_step.expr else {
            return Ok(false);
        };
        if step.func_name != operators::LOGICAL_OR
            || step.args.len() != 2
            || !matches!(&step.args[0].expr, Expr::Ident(n) if *n == c.accu_var)
        {
            return Ok(false);
        }
        let mut leaves = Vec::new();
        or_leaves(&step.args[1], &mut leaves);
        let Some(list) = self.known_strings(&c.iter_range) else {
            return self.try_numset_exists(c, &leaves, dst, h);
        };
        let r = c.iter_var.as_str();
        let mut needle: Option<&IdedExpr> = None;
        let mut shapes: Vec<Leaf> = Vec::new();
        let hosts = Arc::clone(&self.code.hosts);
        for leaf in leaves {
            let Some((n, shape)) = var_leaf(leaf, r, &hosts) else {
                return Ok(false);
            };
            if !self.pure_string(n) || mentions(n, r) || mentions(n, &c.accu_var) {
                return Ok(false);
            }
            match needle {
                None => needle = Some(n),
                Some(m) if same_shape(m, n) => {}
                Some(_) => return Ok(false),
            }
            shapes.push(shape);
        }
        let Some(needle) = needle else {
            return Ok(false);
        };
        if list.is_empty() {
            let k = self.konst(CVal::Bool(false));
            self.push(Op::Const { dst, k });
            return Ok(true);
        }
        let (mut eq, mut prefix) = (Vec::new(), Vec::new());
        for item in &list {
            for shape in &shapes {
                match shape {
                    Leaf::Eq => eq.push(item.clone()),
                    Leaf::Prefix(suffix) => prefix.push(format!("{item}{suffix}")),
                    // A pure function of a known element is known. One that fails, or answers
                    // something other than a string, keeps the loop: it fails when it runs.
                    Leaf::HostPrefix(ix) => {
                        let Some(call) = hosts.entries[*ix as usize].closure() else {
                            return Ok(false);
                        };
                        match call(&[crate::CelValue::Str(item.as_str().into())]) {
                            Ok(crate::CelValue::Str(p)) => prefix.push(p.to_string()),
                            _ => return Ok(false),
                        }
                    }
                }
            }
        }
        let a = self.tmp()?;
        self.expr(needle, a, h)?;
        let m = self.matcher(eq, prefix);
        self.push(Op::Match { dst, a, m, err: h });
        Ok(true)
    }

    /// `L.exists(v, N == v || …)` over a KNOWN list of numbers, every leaf `N == v` or `v == N`
    /// with one needle `N` naming neither loop variable: `N`, then one `NumIn`. An empty `L`
    /// reads nothing and is `false`, as the loop is.
    fn try_numset_exists(
        &mut self,
        c: &ComprehensionExpr,
        leaves: &[&IdedExpr],
        dst: R,
        h: Label,
    ) -> Result<bool, String> {
        let Some(nums) = self.known_nums(&c.iter_range) else {
            return Ok(false);
        };
        let hosts = Arc::clone(&self.code.hosts);
        let r = c.iter_var.as_str();
        let mut needle: Option<&IdedExpr> = None;
        for leaf in leaves {
            let Some((n, Leaf::Eq)) = var_leaf(leaf, r, &hosts) else {
                return Ok(false);
            };
            if !pure(n) || mentions(n, r) || mentions(n, &c.accu_var) {
                return Ok(false);
            }
            match needle {
                None => needle = Some(n),
                Some(m) if same_shape(m, n) => {}
                Some(_) => return Ok(false),
            }
        }
        let Some(needle) = needle else {
            return Ok(false);
        };
        if nums.is_empty() {
            let k = self.konst(CVal::Bool(false));
            self.push(Op::Const { dst, k });
            return Ok(true);
        }
        let a = self.operand(needle, h)?;
        let set = self.numset(nums);
        self.push(Op::NumIn { dst, a, set });
        Ok(true)
    }

    // ---- comprehensions ----

    /// A comprehension inside a loop body that names no variable in scope has one value per run:
    /// computed the first time the body reaches it, kept in a pinned register, copied after.
    /// Its error is not kept — a later reach computes it again and fails again, as each did.
    ///
    /// ```text
    ///        BrSet C → HAVE
    ///        <comprehension → T>
    ///        Local C ← T
    /// HAVE:  Local dst ← C
    /// ```
    fn invariant_comprehension(
        &mut self,
        c: &ComprehensionExpr,
        dst: R,
        h: Label,
    ) -> Result<(), String> {
        let pin = PINNED + self.pins;
        self.pins = self
            .pins
            .checked_add(1)
            .filter(|p| PINNED.checked_add(*p).is_some())
            .ok_or("too many loop-invariant comprehensions")?;
        let have = self.label();
        self.push(Op::BrSet { r: pin, to: have });
        let t = self.tmp()?;
        // Outside every loop: its own loop body, not the enclosing one, is what `loops` counts.
        let loops = std::mem::replace(&mut self.loops, 0);
        let out = self.comprehension(c, t, h);
        self.loops = loops;
        out?;
        self.push(Op::Local { dst: pin, src: t });
        self.place(have);
        self.push(Op::Local { dst, src: pin });
        Ok(())
    }

    /// `map` and `filter`, recognized by their expansion, appending to one list in place: the
    /// expansion's step `@result + [e]` copies the whole accumulator every element (quadratic).
    ///
    /// ```text
    ///        <iter_range → S>; IterInit S; Clear P; ListNew B (sized for S)
    /// HEAD:  IterNext → X, else DONE
    ///        <P as a branch: false → HEAD; error → CAUGHT>   (filter, three-argument map)
    ///        <e → T; error → CAUGHT>
    ///        Append B ← T
    ///        Jump HEAD
    /// CAUGHT: CatchPending P; Jump HEAD                      (cold) the FIRST error is kept
    /// DONE:  RaisePending P
    ///        ListFreeze B → dst
    /// ```
    ///
    /// As in the expansion, an error in any element's step is reported after every element ran.
    fn try_build_loop(&mut self, c: &ComprehensionExpr, dst: R, h: Label) -> Result<bool, String> {
        if LITERAL_COMPREHENSIONS.with(|l| l.get()) || empty_collection(&c.iter_range) {
            return Ok(false);
        }
        let Some((keep, e)) = build_loop(c) else {
            return Ok(false);
        };
        if keep.is_some_and(|p| names(p, &c.accu_var)) || names(e, &c.accu_var) {
            return Ok(false);
        }
        let range = self.tmp()?;
        self.expr(&c.iter_range, range, h)?;
        let slot = self.code.nloops as u16;
        let build = slot + 1;
        self.code.nloops += 2;
        let (var, pend, item) = (self.tmp()?, self.tmp()?, self.tmp()?);
        self.push(Op::IterInit {
            slot,
            src: range,
            clear: NO_REG,
            err: h,
        });
        self.push(Op::Clear { r: pend });
        self.push(Op::ListNew {
            slot: build,
            hint: range,
        });
        let (head, caught, done) = (self.label(), self.label(), self.label());
        self.place(head);
        self.push(Op::IterNext {
            slot,
            dst: var,
            clear: NO_REG,
            pend: NO_REG,
            exit: done,
            err: done,
        });
        let depth = self.scope.len();
        self.scope.push((c.iter_var.clone(), var));
        self.ranges.push((c.iter_range.clone(), range, var, slot));
        self.loops += 1;
        if let Some(p) = keep {
            self.branch(p, head, false, caught)?;
        }
        self.expr(e, item, caught)?;
        self.push(Op::Append {
            slot: build,
            src: item,
        });
        self.push(Op::Jump { to: head });
        self.loops -= 1;
        self.scope.truncate(depth);
        self.ranges.pop();
        self.place_cold(caught);
        self.push_cold(Op::CatchPending { pend });
        self.push_cold(Op::Jump { to: head });
        self.place(done);
        self.push(Op::RaisePending { pend, err: h });
        self.push(Op::ListFreeze { slot: build, dst });
        Ok(true)
    }

    /// `exists`, `all` and `exists_one`, recognized by their expansion, as a loop whose predicate
    /// is a BRANCH: no accumulator to copy, no loop condition to re-evaluate each turn.
    ///
    /// ```text
    ///        <iter_range → S>; IterInit S; Clear P
    /// HEAD:  IterNext → X, else DONE
    ///        <P as a branch: to SETTLED on the absorbing value; error → CAUGHT>
    ///        Jump HEAD
    /// SETTLED: Const dst ← absorbing; Jump END       (cold)
    /// CAUGHT:  CatchPending P; Jump HEAD             (cold) the FIRST error is the one kept
    /// DONE:  RaisePending P                          a passing loop reports its first error
    ///        Const dst ← !absorbing
    /// END:
    /// ```
    ///
    /// An absorbing element decides even over an earlier element's error, as the expansion's
    /// step does (it clears the pending error); a loop with none reports the first error.
    /// `exists_one` never absorbs: its predicate branches past an `Inc` of a count, the count
    /// is the expansion's `@result`, and every element runs — a later error still raises.
    fn try_predicate_loop(
        &mut self,
        c: &ComprehensionExpr,
        out: Outcome,
        h: Label,
    ) -> Result<bool, String> {
        if LITERAL_COMPREHENSIONS.with(|l| l.get()) || empty_collection(&c.iter_range) {
            return Ok(false);
        }
        let Some((shape, pred)) = predicate_loop(c) else {
            return Ok(false);
        };
        // The predicate never names the accumulator in an expansion; a tree that does is not one.
        if names(pred, &c.accu_var) {
            return Ok(false);
        }
        if let Expr::List(l) = &c.iter_range.expr {
            if l.elements.len() <= MAX_UNROLLED && self.constant(&c.iter_range).is_none() {
                let Outcome::Value(dst) = out else {
                    return Ok(false);
                };
                self.unrolled_predicate(c, shape, pred, &l.elements, dst, h)?;
                return Ok(true);
            }
        }
        // `exists_one` counts, then decides over the count: only as a value.
        if shape == Shape::ExistsOne && matches!(out, Outcome::Branch { .. }) {
            return Ok(false);
        }
        let range = self.tmp()?;
        self.expr(&c.iter_range, range, h)?;
        let slot = self.code.nloops as u16;
        self.code.nloops += 1;
        let (var, pend) = (self.tmp()?, self.tmp()?);
        let count = match shape {
            Shape::ExistsOne => Some(self.tmp()?),
            _ => None,
        };
        let fallible = !self.infallible_in(pred, &c.iter_var, var);
        // The pending error is reset as the loop starts, and raised by the fetch that ends it.
        let pending = if fallible { pend } else { NO_REG };
        self.push(Op::IterInit {
            slot,
            src: range,
            clear: pending,
            err: h,
        });
        if let Some(count) = count {
            let zero = self.konst(CVal::Num(CelNum::Int(0)));
            self.push(Op::Const {
                dst: count,
                k: zero,
            });
        }
        let absorbing = shape == Shape::Exists;
        // Where the loop goes when it runs out: its non-deciding value's destination, directly
        // when it is a branch that jumps on that value.
        let (head, caught, done) = (self.label(), self.label(), self.label());
        let exit = match out {
            Outcome::Branch { target, jump_if }
                if shape != Shape::ExistsOne && jump_if != absorbing =>
            {
                target
            }
            _ => done,
        };
        self.place(head);
        self.push(Op::IterScan {
            slot,
            dst: var,
            clear: NO_REG,
            pend: pending,
            exit,
            err: h,
            // An element handed to the body decides the loop (or, for `exists_one`, is a rare
            // match), so a scan's failed test is paid about once per decision: worth asking for.
            // A `filter`'s kept element is handed off every time, and is not.
            scan: SCAN_WANTED,
        });
        let depth = self.scope.len();
        self.scope.push((c.iter_var.clone(), var));
        self.ranges.push((c.iter_range.clone(), range, var, slot));
        self.loops += 1;
        match (shape, count) {
            (Shape::ExistsOne, Some(count)) => {
                self.branch(pred, head, false, caught)?;
                self.push(Op::Inc { r: count });
                self.push(Op::Jump { to: head });
            }
            _ => {
                // An element that does not decide the loop goes straight back for the next — the
                // test's own branch, no `Jump` — and the one that decides falls through.
                self.branch(pred, head, !absorbing, caught)?;
                match out {
                    Outcome::Value(dst) => {
                        let end = self.label();
                        let k = self.konst(CVal::Bool(absorbing));
                        self.push(Op::Const { dst, k });
                        self.push(Op::Jump { to: end });
                        self.place(done);
                        let passing = self.konst(CVal::Bool(!absorbing));
                        self.push(Op::Const { dst, k: passing });
                        self.place(end);
                    }
                    // Decided: the absorbing value. Run out: the other one — which `exit`
                    // already sends to `target` when it jumps there.
                    Outcome::Branch { target, jump_if } => {
                        if jump_if == absorbing {
                            self.push(Op::Jump { to: target });
                            self.place(done);
                        } else {
                            // Decided falls through; run out already jumped (`exit`).
                            self.place(done);
                        }
                    }
                }
            }
        }
        self.loops -= 1;
        self.scope.truncate(depth);
        self.ranges.pop();
        self.place_cold(caught);
        self.push_cold(Op::CatchPending { pend });
        self.push_cold(Op::Jump { to: head });
        if let (Some(count), Outcome::Value(dst)) = (count, out) {
            self.place(done);
            self.scope.push((c.accu_var.clone(), count));
            self.expr(&c.result, dst, h)?;
            self.scope.truncate(depth);
        }
        Ok(true)
    }

    /// [`Lower::infallible`] of `pred` with the loop variable `var` in scope at `r`.
    fn infallible_in(&mut self, pred: &IdedExpr, var: &str, r: R) -> bool {
        self.scope.push((var.to_string(), r));
        let out = self.infallible(pred);
        self.scope.pop();
        out
    }

    /// `try_predicate_loop` over a list LITERAL of up to [`MAX_UNROLLED`] elements, straight-line:
    /// each element runs, then the predicate over it, in turn — no list, no iteration.
    ///
    /// Building the list ran EVERY element before any predicate, so an element that fails fails
    /// the decision even after an earlier one decided. The deciding jump therefore lands in a
    /// continuation that runs the elements still unrun (each exactly once per decision, as
    /// before), and only then answers. A predicate's failure is kept, first only, as the loop's.
    ///
    /// ```text
    ///        Clear P                                  (when the predicate can fail)
    ///        <e₁ → R₁>; <pred(R₁): absorbing → HIT₁; error → C₁>
    ///        …
    ///        <eₙ → Rₙ>; <pred(Rₙ): absorbing → HITₙ; error → Cₙ>
    ///        RaisePending P; Const dst ← !absorbing; Jump END
    /// HIT₁:  <e₂ → _>
    /// …
    /// HITₙ₋₁: <eₙ → _>
    /// HITₙ:  Const dst ← absorbing
    /// END:
    /// ```
    fn unrolled_predicate(
        &mut self,
        c: &ComprehensionExpr,
        shape: Shape,
        pred: &IdedExpr,
        elements: &[IdedExpr],
        dst: R,
        h: Label,
    ) -> Result<(), String> {
        let pend = self.tmp()?;
        let probe = self.tmp()?;
        let fallible = !self.infallible_in(pred, &c.iter_var, probe);
        if fallible {
            self.push(Op::Clear { r: pend });
        }
        let count = match shape {
            Shape::ExistsOne => {
                let count = self.tmp()?;
                let zero = self.konst(CVal::Num(CelNum::Int(0)));
                self.push(Op::Const {
                    dst: count,
                    k: zero,
                });
                Some(count)
            }
            _ => None,
        };
        let absorbing = shape == Shape::Exists;
        let hits: Vec<Label> = elements.iter().map(|_| self.label()).collect();
        let depth = self.scope.len();
        for (el, hit) in elements.iter().zip(&hits) {
            let mark = self.next;
            let r = self.operand(el, h)?;
            let (next, caught) = (self.label(), self.label());
            self.scope.push((c.iter_var.clone(), r));
            match count {
                Some(count) => {
                    self.branch(pred, next, false, caught)?;
                    self.push(Op::Inc { r: count });
                }
                None => self.branch(pred, *hit, absorbing, caught)?,
            }
            self.scope.truncate(depth);
            self.next = mark;
            self.place(next);
            self.place_cold(caught);
            self.push_cold(Op::CatchPending { pend });
            self.push_cold(Op::Jump { to: next });
        }
        if fallible {
            self.push(Op::RaisePending { pend, err: h });
        }
        match count {
            Some(count) => {
                self.scope.push((c.accu_var.clone(), count));
                self.expr(&c.result, dst, h)?;
                self.scope.truncate(depth);
                // An `exists_one` never decides early: its continuation is never reached.
                for hit in hits {
                    self.place(hit);
                }
            }
            None => {
                let end = self.label();
                let passing = self.konst(CVal::Bool(!absorbing));
                self.push(Op::Const { dst, k: passing });
                self.push(Op::Jump { to: end });
                for (i, hit) in hits.iter().enumerate() {
                    self.place(*hit);
                    if let Some(rest) = elements.get(i + 1) {
                        if self.constant(rest).is_none() {
                            let t = self.tmp()?;
                            self.expr(rest, t, h)?;
                        }
                    }
                }
                let k = self.konst(CVal::Bool(absorbing));
                self.push(Op::Const { dst, k });
                self.place(end);
            }
        }
        Ok(())
    }

    /// A comprehension: the first pending step error is kept, and an absorbing accumulator clears it.
    ///
    /// ```text
    ///        <accu_init → A>                enclosing scope
    ///        <iter_range → S>
    ///        IterInit S
    ///        Clear P                        no pending error
    /// HEAD:  IterNext → T, else EXIT
    ///        BrPending P → BIND             a pending error skips the condition
    ///        <loop_cond → C>                its error propagates
    ///        Cond C, false → EXIT
    /// BIND:  Local I ← T
    ///        <loop_step → X>                its error → STEP_ERR
    ///        Step A ← X (an absorbing X clears P)
    ///        Jump HEAD
    /// STEP_ERR: CatchPending P; Jump HEAD   the FIRST error is the one kept
    /// EXIT:  RaisePending P
    ///        <result → dst>
    /// ```
    fn comprehension(&mut self, c: &ComprehensionExpr, dst: R, h: Label) -> Result<(), String> {
        if c.iter_var2.is_some() {
            return Err("a two-variable comprehension".into());
        }
        if self.try_match_exists(c, dst, h)?
            || self.try_predicate_loop(c, Outcome::Value(dst), h)?
            || self.try_build_loop(c, dst, h)?
        {
            return Ok(());
        }
        let accu = self.tmp()?;
        self.expr(&c.accu_init, accu, h)?;
        let depth = self.scope.len();
        // A fold over an empty literal never runs its body — which the checker therefore did not
        // type — so only the result is lowered, over the initial accumulator.
        if empty_collection(&c.iter_range) {
            self.scope.push((c.accu_var.clone(), accu));
            self.expr(&c.result, dst, h)?;
            self.scope.truncate(depth);
            return Ok(());
        }
        let range = self.tmp()?;
        self.expr(&c.iter_range, range, h)?;
        let slot = self.code.nloops as u16;
        self.code.nloops += 1;
        let (item, iter, pend, cond, step) = (
            self.tmp()?,
            self.tmp()?,
            self.tmp()?,
            self.tmp()?,
            self.tmp()?,
        );
        self.push(Op::IterInit {
            slot,
            src: range,
            clear: NO_REG,
            err: h,
        });
        self.push(Op::Clear { r: pend });
        let (head, bind, step_err, exit) = (self.label(), self.label(), self.label(), self.label());
        self.place(head);
        self.push(Op::IterNext {
            slot,
            dst: item,
            clear: NO_REG,
            pend: NO_REG,
            exit: exit,
            err: exit,
        });
        self.push(Op::BrPending { r: pend, to: bind });
        self.scope.push((c.accu_var.clone(), accu));
        self.scope.push((c.iter_var.clone(), iter));
        self.loops += 1;
        self.expr(&c.loop_cond, cond, h)?;
        self.push(Op::Cond {
            r: cond,
            invert: false,
            else_: exit,
            err: h,
        });
        self.place(bind);
        self.push(Op::Local {
            dst: iter,
            src: item,
        });
        self.expr(&c.loop_step, step, step_err)?;
        self.loops -= 1;
        self.push(Op::Step {
            accu,
            step,
            pend,
            absorb: absorb_of(&c.loop_step),
        });
        self.push(Op::Jump { to: head });
        self.place(step_err);
        self.push(Op::CatchPending { pend });
        self.push(Op::Jump { to: head });
        self.place(exit);
        self.push(Op::RaisePending { pend, err: h });
        self.expr(&c.result, dst, h)?;
        self.scope.truncate(depth);
        Ok(())
    }
}

fn want(k: Kind) -> Want {
    match k {
        Kind::Bool => Want::Bool,
        Kind::Num => Want::Num,
        Kind::Str => Want::Str,
        Kind::Bytes => Want::Bytes,
        Kind::Duration => Want::Dur,
        _ => Want::Any,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    Exists,
    All,
    ExistsOne,
}

/// The shape and the predicate of an `exists` / `all` / `exists_one` expansion
/// (`src/parser/macros.rs`), matched in full: init, condition, step and result.
fn predicate_loop(c: &ComprehensionExpr) -> Option<(Shape, &IdedExpr)> {
    let accu = |e: &IdedExpr| matches!(&e.expr, Expr::Ident(n) if *n == c.accu_var);
    let call = |e: &'_ IdedExpr, f: &str, n: usize| -> bool {
        matches!(&e.expr, Expr::Call(k) if k.target.is_none() && k.func_name == f && k.args.len() == n)
    };
    let Expr::Call(step) = &c.loop_step.expr else {
        return None;
    };
    if step.target.is_some() {
        return None;
    }
    match (
        &c.accu_init.expr,
        step.func_name.as_str(),
        step.args.as_slice(),
    ) {
        (Expr::Literal(LiteralValue::Boolean(b)), operators::LOGICAL_OR, [a, p])
            if !*b.inner() && accu(a) && accu(&c.result) =>
        {
            // `@not_strictly_false(!@result)`
            let Expr::Call(nsf) = &c.loop_cond.expr else {
                return None;
            };
            (call(&c.loop_cond, operators::NOT_STRICTLY_FALSE, 1)
                && call(&nsf.args[0], operators::LOGICAL_NOT, 1)
                && matches!(&nsf.args[0].expr, Expr::Call(n) if accu(&n.args[0])))
            .then_some((Shape::Exists, p))
        }
        (Expr::Literal(LiteralValue::Boolean(b)), operators::LOGICAL_AND, [a, p])
            if *b.inner() && accu(a) && accu(&c.result) =>
        {
            // `@not_strictly_false(@result)`
            (call(&c.loop_cond, operators::NOT_STRICTLY_FALSE, 1)
                && matches!(&c.loop_cond.expr, Expr::Call(n) if accu(&n.args[0])))
            .then_some((Shape::All, p))
        }
        (Expr::Literal(LiteralValue::Int(0)), operators::CONDITIONAL, [p, inc, same]) => {
            // `p ? @result + 1 : @result`, looping while `true`, answering `@result == 1`.
            let one = |e: &IdedExpr| matches!(&e.expr, Expr::Literal(LiteralValue::Int(1)));
            let inc_ok = matches!(&inc.expr, Expr::Call(k)
                if k.target.is_none() && k.func_name == operators::ADD
                    && k.args.len() == 2 && accu(&k.args[0]) && one(&k.args[1]));
            let cond_ok = matches!(&c.loop_cond.expr,
                Expr::Literal(LiteralValue::Boolean(t)) if *t.inner());
            let result_ok = matches!(&c.result.expr, Expr::Call(k)
                if k.target.is_none() && k.func_name == operators::EQUALS
                    && k.args.len() == 2 && accu(&k.args[0]) && one(&k.args[1]));
            (inc_ok && accu(same) && cond_ok && result_ok).then_some((Shape::ExistsOne, p))
        }
        _ => None,
    }
}

/// Does `e` name the binding `var` in scope where `e` is? Exact over every node kind, where
/// [`mentions`] answers `true` for any it does not walk.
fn names(e: &IdedExpr, var: &str) -> bool {
    match &e.expr {
        Expr::Ident(n) => n == var,
        Expr::Literal(_) | Expr::Unspecified => false,
        Expr::Select(s) => names(&s.operand, var),
        Expr::Call(c) => {
            c.target.as_deref().is_some_and(|t| names(t, var))
                || c.args.iter().any(|a| names(a, var))
        }
        Expr::List(l) => l.elements.iter().any(|x| names(x, var)),
        Expr::Map(m) => m.entries.iter().any(|entry| {
            let EntryExpr::MapEntry(me) = &entry.expr;
            names(&me.key, var) || names(&me.value, var)
        }),
        // A nested comprehension's own accumulator or variable of the same name shadows `var`
        // in its body.
        Expr::Comprehension(c) => {
            names(&c.iter_range, var)
                || names(&c.accu_init, var)
                || (c.accu_var != var
                    && c.iter_var != var
                    && c.iter_var2.as_deref() != Some(var)
                    && [&c.loop_cond, &c.loop_step, &c.result]
                        .into_iter()
                        .any(|x| names(x, var)))
        }
    }
}

/// The filter (if any) and the element of a `map` / `filter` expansion (`src/parser/macros.rs`),
/// matched in full: `[]`, looping while `true`, a step `@result + [e]` or
/// `p ? @result + [e] : @result`, answering `@result`.
fn build_loop(c: &ComprehensionExpr) -> Option<(Option<&IdedExpr>, &IdedExpr)> {
    let accu = |e: &IdedExpr| matches!(&e.expr, Expr::Ident(n) if *n == c.accu_var);
    fn append<'e>(e: &'e IdedExpr, accu: &dyn Fn(&IdedExpr) -> bool) -> Option<&'e IdedExpr> {
        let Expr::Call(k) = &e.expr else { return None };
        match (k.func_name.as_str(), k.target.as_deref(), k.args.as_slice()) {
            (operators::ADD, None, [a, l]) if accu(a) => match &l.expr {
                Expr::List(l) if l.elements.len() == 1 => Some(&l.elements[0]),
                _ => None,
            },
            _ => None,
        }
    }
    let starts_empty = matches!(&c.accu_init.expr, Expr::List(l) if l.elements.is_empty());
    let loops_while_true =
        matches!(&c.loop_cond.expr, Expr::Literal(LiteralValue::Boolean(t)) if *t.inner());
    if !starts_empty || !loops_while_true || !accu(&c.result) {
        return None;
    }
    if let Some(e) = append(&c.loop_step, &accu) {
        return Some((None, e));
    }
    let Expr::Call(k) = &c.loop_step.expr else {
        return None;
    };
    match (k.func_name.as_str(), k.target.as_deref(), k.args.as_slice()) {
        (operators::CONDITIONAL, None, [p, add, same]) if accu(same) => {
            append(add, &accu).map(|e| (Some(p), e))
        }
        _ => None,
    }
}

/// Which accumulator value settles a step: `false` for `&&`, `true` for `||`.
fn absorb_of(step: &IdedExpr) -> Absorb {
    match &step.expr {
        Expr::Call(c) if c.func_name == operators::LOGICAL_AND => Absorb::OnFalse,
        Expr::Call(c) if c.func_name == operators::LOGICAL_OR => Absorb::OnTrue,
        _ => Absorb::Never,
    }
}

/// `[]`, `{}`, or a `map`/`filter` over one: a fold over it never runs its body.
fn empty_collection(e: &IdedExpr) -> bool {
    match &e.expr {
        Expr::List(l) => l.elements.is_empty(),
        Expr::Map(m) => m.entries.is_empty(),
        Expr::Comprehension(c) => {
            matches!(&c.accu_init.expr, Expr::List(l) if l.elements.is_empty())
                && empty_collection(&c.iter_range)
        }
        _ => false,
    }
}

/// The leaves of the maximal tree of the binary operator `op` rooted at `e`, left to right.
/// The most nodes a chain's leaves may have, together, for [`Lower::split_chain`] to lower them
/// twice. A leaf that is itself a chain is split in its turn, so the bound keeps nesting from
/// multiplying the copies.
const SPLIT_NODES: i32 = 48;

fn chain_leaves<'e>(e: &'e IdedExpr, op: &str, out: &mut Vec<&'e IdedExpr>) {
    match &e.expr {
        Expr::Call(c) if c.func_name == op && c.target.is_none() && c.args.len() == 2 => {
            chain_leaves(&c.args[0], op, out);
            chain_leaves(&c.args[1], op, out);
        }
        _ => out.push(e),
    }
}

/// The leaves of the maximal `||` tree rooted at `e`.
fn or_leaves<'e>(e: &'e IdedExpr, out: &mut Vec<&'e IdedExpr>) {
    match &e.expr {
        Expr::Call(c)
            if c.func_name == operators::LOGICAL_OR && c.target.is_none() && c.args.len() == 2 =>
        {
            or_leaves(&c.args[0], out);
            or_leaves(&c.args[1], out);
        }
        _ => out.push(e),
    }
}

fn string_literal(e: &IdedExpr) -> Option<&str> {
    match &e.expr {
        Expr::Literal(LiteralValue::String(s)) => Some(s.inner()),
        _ => None,
    }
}

/// A whole `||` tree of at least [`MIN_CHAIN`] leaves, each `N == <number>` or `<number> == N`
/// over ONE pure needle `N`: the needle and the numbers. Every leaf's only failure is reading
/// `N`, so the tree fails exactly when `N` does, with `N`'s error — and answers as a number set.
fn num_chain(e: &IdedExpr) -> Option<(&IdedExpr, Vec<CelNum>)> {
    let mut leaves = Vec::new();
    or_leaves(e, &mut leaves);
    if leaves.len() < MIN_CHAIN {
        return None;
    }
    let num = |x: &IdedExpr| match &x.expr {
        Expr::Literal(LiteralValue::Double(d)) => Some(CelNum::from_f64(*d.inner())),
        Expr::Literal(LiteralValue::Int(i)) => Some(CelNum::Int(*i)),
        Expr::Literal(LiteralValue::UInt(u)) => Some(CelNum::from(*u)),
        _ => None,
    };
    let mut needle: Option<&IdedExpr> = None;
    let mut nums = Vec::with_capacity(leaves.len());
    for leaf in leaves {
        let Expr::Call(c) = &leaf.expr else {
            return None;
        };
        let (n, k) = match (c.func_name.as_str(), c.target.as_deref(), c.args.as_slice()) {
            (operators::EQUALS, None, [a, b]) => match (num(a), num(b)) {
                (None, Some(k)) => (a, k),
                (Some(k), None) => (b, k),
                _ => return None,
            },
            _ => return None,
        };
        if !pure(n) {
            return None;
        }
        match needle {
            None => needle = Some(n),
            Some(m) if same_shape(m, n) => {}
            Some(_) => return None,
        }
        nums.push(k);
    }
    Some((needle?, nums))
}

/// `N == "lit"` / `"lit" == N` → `(N, lit, false)`; `N.startsWith("lit")` → `(N, lit, true)`.
fn literal_leaf(e: &IdedExpr) -> Option<(&IdedExpr, &str, bool)> {
    let Expr::Call(c) = &e.expr else { return None };
    match (c.func_name.as_str(), c.target.as_deref(), c.args.as_slice()) {
        (operators::EQUALS, None, [a, b]) => match (string_literal(a), string_literal(b)) {
            (None, Some(lit)) => Some((a, lit, false)),
            (Some(lit), None) => Some((b, lit, false)),
            _ => None,
        },
        ("startsWith", Some(t), [p]) => Some((t, string_literal(p)?, true)),
        _ => None,
    }
}

/// What one leaf over the loop variable asks of the needle.
enum Leaf {
    /// `N == r`.
    Eq,
    /// `N.startsWith(r + suffix)` (`N.startsWith(r)` is the empty suffix).
    Prefix(String),
    /// `N.startsWith(H(r))` for the pure one-argument host function `H` at this index: the prefix
    /// is `H` of the element, computed once per element at lowering.
    HostPrefix(u16),
}

/// A leaf over the loop variable `r`: `N == r` / `r == N` → `(N, Eq)`; `N.startsWith(r)` →
/// `(N, Prefix(""))`; `N.startsWith(r + "lit")` → `(N, Prefix(lit))`; `N.startsWith(H(r))` for a
/// one-argument host function `H` → `(N, HostPrefix(H))`.
fn var_leaf<'e>(
    e: &'e IdedExpr,
    r: &str,
    hosts: &crate::hostfn::HostTable,
) -> Option<(&'e IdedExpr, Leaf)> {
    let is_r = |x: &IdedExpr| matches!(&x.expr, Expr::Ident(n) if n == r);
    let Expr::Call(c) = &e.expr else { return None };
    match (c.func_name.as_str(), c.target.as_deref(), c.args.as_slice()) {
        (operators::EQUALS, None, [a, b]) if is_r(b) && !is_r(a) => Some((a, Leaf::Eq)),
        (operators::EQUALS, None, [a, b]) if is_r(a) && !is_r(b) => Some((b, Leaf::Eq)),
        ("startsWith", Some(t), [p]) if is_r(p) => Some((t, Leaf::Prefix(String::new()))),
        ("startsWith", Some(t), [p]) => {
            let Expr::Call(inner) = &p.expr else {
                return None;
            };
            match (
                inner.func_name.as_str(),
                inner.target.as_deref(),
                inner.args.as_slice(),
            ) {
                (operators::ADD, None, [x, lit]) if is_r(x) => {
                    Some((t, Leaf::Prefix(string_literal(lit)?.to_string())))
                }
                (name, None, [x]) if is_r(x) => {
                    Some((t, Leaf::HostPrefix(hosts.index_of(name, false)?)))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Reads nothing but paths: the same value on every read.
fn pure(e: &IdedExpr) -> bool {
    match &e.expr {
        Expr::Ident(_) => true,
        Expr::Select(s) => !s.test && pure(&s.operand),
        Expr::Call(c) if c.func_name == operators::INDEX && c.target.is_none() => {
            c.args.len() == 2 && pure(&c.args[0]) && string_literal(&c.args[1]).is_some()
        }
        _ => false,
    }
}

/// Does `e` name `var`?
fn mentions(e: &IdedExpr, var: &str) -> bool {
    match &e.expr {
        Expr::Ident(n) => n == var,
        Expr::Select(s) => mentions(&s.operand, var),
        Expr::Call(c) => {
            c.target.as_deref().is_some_and(|t| mentions(t, var))
                || c.args.iter().any(|a| mentions(a, var))
        }
        Expr::Literal(_) => false,
        _ => true,
    }
}

/// Structural equality of two pure paths, ids aside.
fn same_shape(a: &IdedExpr, b: &IdedExpr) -> bool {
    match (&a.expr, &b.expr) {
        (Expr::Ident(x), Expr::Ident(y)) => x == y,
        (Expr::Select(x), Expr::Select(y)) => {
            x.field == y.field && x.test == y.test && same_shape(&x.operand, &y.operand)
        }
        (Expr::Call(x), Expr::Call(y)) => {
            x.func_name == y.func_name
                && x.target.is_none()
                && y.target.is_none()
                && x.args.len() == y.args.len()
                && x.args.iter().zip(&y.args).all(|(p, q)| same_shape(p, q))
        }
        (Expr::Literal(x), Expr::Literal(y)) => x == y,
        _ => false,
    }
}
