//! Lowering a CHECKED tree to the fast backend's register code.
//!
//! One walk, in the evaluator's own evaluation order (`objects.rs::resolve_val`): the order a
//! node's operands are lowered is the order they run, so the same reads happen and the same error
//! is the one reported. Errors do not unwind: every op that can fail names the handler its failure
//! jumps to, which is known here because handlers are LEXICAL — the left operand of `&&`/`||`, the
//! argument of `@not_strictly_false`, a comprehension's step, or the top.

use std::collections::HashMap;
use std::sync::Arc;

use crate::common::ast::{
    operators, CallExpr, ComprehensionExpr, EntryExpr, Expr, IdedExpr, LiteralValue,
};
use crate::common::types::CelString;
use crate::common::value::Val;
use crate::objects::Value;
use crate::ExecutionError;

use super::host::{FieldPath, Step, Want};
use super::matcher::StrMatcher;
use super::reg::map_key;
use super::{Absorb, Arith, CVal, Cmp, Code, Kind, Op, Pc, StrOp, R};

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

/// The fewest `==`/`startsWith` leaves an `||` chain needs before it is answered by a matcher.
/// Below it the chain is cheaper as written.
const MIN_CHAIN: usize = 2;

pub(crate) fn lower(
    e: &IdedExpr,
    kinds: &HashMap<u64, Kind>,
    slots: &[(Arc<str>, Value)],
    hosts: &Arc<crate::hostfn::HostTable>,
    enums: &crate::hostfn::EnumTable,
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
        slots: Vec::new(),
        next: 0,
    };
    for (name, value) in slots {
        let val = Box::<dyn Val>::try_from(value.clone())
            .map_err(|e| format!("the constant slot `{name}` has no run-time form: {e}"))?;
        let k = l.konst(CVal::Dyn(val, false));
        l.slots.push((name.to_string(), k, value.clone()));
    }
    let fail = l.label();
    let out = l.tmp()?;
    l.expr(e, out, fail)?;
    l.push(Op::Ret { r: out });
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
    /// A residual's constant slots: name, constant, value.
    slots: Vec<(String, u32, Value)>,
    next: u16,
}

type Label = Pc;

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
        self.code.names.push(CelString::from(n));
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
                .map(|(n, indexed)| Step {
                    name: CelString::from(n.as_str()),
                    indexed: *indexed,
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

    fn slot(&self, name: &str) -> Option<&(String, u32, Value)> {
        self.slots.iter().find(|(n, ..)| n == name)
    }

    /// Resolve every label to its pc.
    fn finish(mut self) -> Result<Code, String> {
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
        self.code.seal();
        Ok(self.code)
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
                    self.push(Op::Read {
                        dst,
                        f,
                        want,
                        err: h,
                    });
                }
            }
            Expr::Select(s) => {
                if s.test {
                    if let Some((root, mut steps)) = self.path(&s.operand) {
                        steps.push((s.field.clone(), false));
                        let f = self.field(&root, &steps);
                        self.push(Op::Has { dst, f, err: h });
                    } else {
                        let obj = self.tmp()?;
                        self.expr(&s.operand, obj, h)?;
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
                    self.push(Op::Read {
                        dst,
                        f,
                        want,
                        err: h,
                    });
                } else {
                    let obj = self.tmp()?;
                    self.expr(&s.operand, obj, h)?;
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
                    // objects.rs: the key is converted BEFORE its value runs.
                    self.push(Op::CheckKey { r: k, err: h });
                    self.expr(&me.value, k + 1, h)?;
                }
                let n = u16::try_from(m.entries.len()).map_err(|_| "a map literal too long")?;
                self.push(Op::MakeMap { dst, start, n });
            }
            Expr::Call(c) => self.call(e, c, dst, h)?,
            Expr::Comprehension(c) => self.comprehension(c, dst, h)?,
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
            Value::Bool(b) => CVal::Bool(b),
            Value::Float(f) => CVal::Num(f),
            Value::Null => CVal::Null,
            Value::String(s) => CVal::Str(Box::from(s.as_str())),
            Value::Bytes(b) => CVal::Bytes(b.to_vec().into_boxed_slice()),
            Value::Duration(d) => CVal::Dur(d),
            // A literal list or map is OWNED where the evaluator builds it.
            other => CVal::Dyn(Box::<dyn Val>::try_from(other).ok()?, true),
        })
    }

    fn constant_value(&self, e: &IdedExpr) -> Option<Value> {
        match &e.expr {
            Expr::Literal(l) => Some(match l {
                LiteralValue::Boolean(b) => Value::Bool(*b.inner()),
                LiteralValue::Int(i) => Value::Float(*i as f64),
                LiteralValue::Double(d) => Value::Float(*d.inner()),
                LiteralValue::String(s) => Value::String(Arc::new(s.inner().to_string())),
                LiteralValue::Bytes(b) => Value::Bytes(Arc::new(b.inner().to_vec())),
                LiteralValue::Null => Value::Null,
            }),
            Expr::List(l) => Some(Value::List(Arc::new(
                l.elements
                    .iter()
                    .map(|el| self.constant_value(el))
                    .collect::<Option<Vec<_>>>()?,
            ))),
            // `!` of a bool constant, `-` of a number constant: nothing to read, nothing to fail.
            Expr::Call(c) if c.target.is_none() && c.args.len() == 1 => {
                match (c.func_name.as_str(), self.constant_value(&c.args[0])?) {
                    (operators::LOGICAL_NOT, Value::Bool(b)) => Some(Value::Bool(!b)),
                    (operators::NEGATE, Value::Float(f)) => Some(Value::Float(-f)),
                    _ => None,
                }
            }
            Expr::Map(m) => {
                let mut out = HashMap::with_capacity(m.entries.len());
                for entry in &m.entries {
                    let EntryExpr::MapEntry(me) = &entry.expr;
                    let k = self.constant_value(&me.key)?;
                    map_key(&k)?;
                    let v = self.constant_value(&me.value)?;
                    let key: crate::objects::Key = k.try_into().ok()?;
                    out.insert(key, v);
                }
                Some(Value::Map(crate::objects::Map { map: Arc::new(out) }))
            }
            _ => None,
        }
    }

    /// The string elements of a list known at compile time: a constant slot or a literal.
    fn known_strings(&self, e: &IdedExpr) -> Option<Vec<String>> {
        let v = match &e.expr {
            Expr::Ident(n) if self.local(n).is_none() => self.slot(n)?.2.clone(),
            _ => self.constant_value(e)?,
        };
        let Value::List(items) = v else { return None };
        items
            .iter()
            .map(|v| match v {
                Value::String(s) => Some(s.to_string()),
                _ => None,
            })
            .collect()
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
                // left was an error too (objects.rs, `LOGICAL_OR` / `LOGICAL_AND`). The right
                // operand lands in `dst` directly: when the left passed it on, it IS the answer,
                // and `Absorb` has work only when the left was an error.
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
                    self.push(Op::Read {
                        dst,
                        f,
                        want,
                        err: h,
                    });
                    return Ok(());
                }
                let (a, b) = self.two(&args[0], &args[1], h)?;
                self.push(Op::Index { dst, a, b, err: h });
            }
            (operators::IN, None, 2) => {
                // `"k" in x` for a record or map `x` read from a root: a presence question on the
                // member `k`, asked exactly as `has(x.k)` asks it (`objects.rs`, `operators::IN`:
                // a lazy answers `presence`, a map `contains_key`) — so a provider that answers by
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
                let (a, b) = self.two(&args[0], &args[1], h)?;
                self.push(Op::In { dst, a, b, err: h });
            }
            (operators::EQUALS | operators::NOT_EQUALS, None, 2) => {
                let ne = n == operators::NOT_EQUALS;
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
            ("startsWith" | "endsWith" | "contains", Some(t), 1) => {
                let op = match n {
                    "startsWith" => StrOp::StartsWith,
                    "endsWith" => StrOp::EndsWith,
                    _ => StrOp::Contains,
                };
                // Every argument runs BEFORE the target (objects.rs, the member-call arm).
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
                let (b, a) = self.two(&args[0], t, h)?;
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
                // Every argument runs BEFORE the target (objects.rs, the member-call arm); the
                // target is the call's first argument.
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
    /// `&&`/`||` keep the evaluator's absorption without building a bool: an erroring left
    /// operand is caught (out of line) and the right one still decides — and where the right one
    /// would have been passed on the left's value, `RaiseIfErr` raises the left's error instead.
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
                    return self.logic_branch(&c.args[0], &c.args[1], or, target, jump_if, h);
                }
            }
        }
        let cond = self.tmp()?;
        self.expr(e, cond, h)?;
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
        Ok(())
    }

    /// `a || b` / `a && b` as a branch to `target` when the result is `jump_if`.
    ///
    /// The left operand SETTLES it (`true` for `||`, `false` for `&&`) or passes it on. When the
    /// right operand settles it too, the left's error was absorbed; when the right one passes, the
    /// result is the left's error if it had one — `RaiseIfErr` — and the right one's value if not.
    fn logic_branch(
        &mut self,
        left: &IdedExpr,
        right: &IdedExpr,
        or: bool,
        target: Label,
        jump_if: bool,
        h: Label,
    ) -> Result<(), String> {
        let a = self.tmp()?;
        let (caught, b, settled, passed) = (self.label(), self.label(), self.label(), self.label());
        self.expr(left, a, caught)?;
        // The left operand settles it: `or` is the settling value.
        self.push(if or {
            Op::BrTrue { r: a, to: settled }
        } else {
            Op::BrFalse { r: a, to: settled }
        });
        self.place(b);
        if jump_if == or {
            // Settling goes to `target`; passing falls through, once the left's error is raised.
            self.branch(right, target, or, h)?;
            self.push(Op::RaiseIfErr { r: a, err: h });
            // `settled` is the jump to `target` itself.
            self.place_cold(settled);
            self.push_cold(Op::Jump { to: target });
        } else {
            // Settling falls through; passing goes to `target`, once the left's error is raised.
            self.branch(right, passed, !or, h)?;
            self.place(settled);
            self.place_cold(passed);
            self.push_cold(Op::RaiseIfErr { r: a, err: h });
            self.push_cold(Op::Jump { to: target });
        }
        self.place_cold(caught);
        self.push_cold(Op::Catch { dst: a });
        self.push_cold(Op::Jump { to: b });
        Ok(())
    }

    /// Would `try_match_chain` answer this `||` tree with a matcher?
    fn matches_chain(&self, e: &IdedExpr) -> bool {
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
        let a = self.tmp()?;
        self.expr(x, a, h)?;
        self.push(Op::EqK { dst, a, k, ne });
        Ok(())
    }

    /// Lower two operands in order into fresh registers.
    fn two(&mut self, x: &IdedExpr, y: &IdedExpr, h: Label) -> Result<(R, R), String> {
        let a = self.tmp()?;
        let b = self.tmp()?;
        self.expr(x, a, h)?;
        self.expr(y, b, h)?;
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
        let Some(list) = self.known_strings(&c.iter_range) else {
            return Ok(false);
        };
        let mut leaves = Vec::new();
        or_leaves(&step.args[1], &mut leaves);
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
                        match call(&[crate::CelValue::Str(item.clone())]) {
                            Ok(crate::CelValue::Str(p)) => prefix.push(p),
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

    // ---- comprehensions ----

    /// `objects.rs`'s `Expr::Comprehension` arm:
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
    ///        <result → dst>; Own dst
    /// ```
    fn comprehension(&mut self, c: &ComprehensionExpr, dst: R, h: Label) -> Result<(), String> {
        if c.iter_var2.is_some() {
            return Err("a two-variable comprehension".into());
        }
        if self.try_match_exists(c, dst, h)? {
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
            self.push(Op::Own { r: dst });
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
            err: h,
        });
        self.push(Op::Clear { r: pend });
        let (head, bind, step_err, exit) = (self.label(), self.label(), self.label(), self.label());
        self.place(head);
        self.push(Op::IterNext {
            slot,
            dst: item,
            exit,
        });
        self.push(Op::BrPending { r: pend, to: bind });
        self.scope.push((c.accu_var.clone(), accu));
        self.scope.push((c.iter_var.clone(), iter));
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
        self.push(Op::Own { r: dst });
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

/// Which accumulator value settles a step: `false` for `&&`, `true` for `||` (`objects.rs`,
/// `absorbs`).
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
