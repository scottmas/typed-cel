//! Partial evaluation: folding the values that are known now out of a desugared tree.
//!
//! The tree is a CHECKED one: the fold computes every value on the backend that runs the residual
//! (a closed subtree is lowered with `FastProgram::lower_node` and run) and places a scalar back into the tree through [`reify`], the single
//! conversion from a value to the literal expression that evaluates to it, and a composite into a
//! typed constant slot.

use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use crate::bindings::Bindings;
use crate::bounds::CelLimits;
use crate::check::{build_parts, classify, Fold};
use crate::check::{Checker, TypeEnv};
use crate::common::ast::{
    operators, CallExpr, ComprehensionExpr, EntryExpr, Expr, IdedEntryExpr, IdedExpr, ListExpr,
    LiteralValue, MapEntryExpr, MapExpr, SelectExpr,
};
use crate::demand::DemandSet;
use crate::fast::{FastProgram, Kinds};
use crate::hostfn::{EnumTable, HostTable};
use crate::ty::CelTy;
use crate::CelValue;

/// The literal expression that evaluates to `v`, or `None` when no CEL literal can spell it.
///
/// Reify-then-evaluate is the identity: every number is a `Float` and reifies as a `Double`
/// literal, integral or not — there is no runtime integer to reify (`removed: integer values`). A duration becomes the `duration("…")` call the desugarer
/// produces for a duration literal. Map entries are sorted by key so the rendering is
/// deterministic. Refused: a non-finite double (the parser has no literal for it), a lazy view, and
/// any container holding one of those.
///
/// Ids are 0; the caller that assembles a finished tree numbers it.
pub fn reify(v: &CelValue) -> Option<IdedExpr> {
    let lit = |l: LiteralValue| Some(node(Expr::Literal(l)));
    match v {
        CelValue::Bool(b) => lit(LiteralValue::Boolean((*b).into())),
        CelValue::Num(f) if f.is_finite() => lit(LiteralValue::Double((*f).into())),
        CelValue::Num(_) => None,
        CelValue::Str(s) => lit(LiteralValue::String(s.to_string().into())),
        CelValue::Bytes(b) => lit(LiteralValue::Bytes(b.to_vec().into())),
        CelValue::Null => lit(LiteralValue::Null),
        CelValue::Duration(d) => Some(node(Expr::Call(CallExpr {
            func_name: "duration".to_string(),
            target: None,
            args: vec![node(Expr::Literal(LiteralValue::String(
                duration_spelling(&d.delta()).into(),
            )))],
        }))),
        CelValue::List(items) => {
            let elements = items.iter().map(reify).collect::<Option<Vec<_>>>()?;
            Some(node(Expr::List(ListExpr::new(elements))))
        }
        // A map's entries are already in key order.
        CelValue::Map(m) => {
            let entries = m
                .iter()
                .map(|(k, v)| {
                    Some(IdedEntryExpr {
                        id: 0,
                        expr: EntryExpr::MapEntry(MapEntryExpr {
                            key: reify(&k.to_value())?,
                            value: reify(v)?,
                        }),
                    })
                })
                .collect::<Option<Vec<_>>>()?;
            Some(node(Expr::Map(MapExpr { entries })))
        }
        CelValue::Lazy(_) => None,
    }
}

/// A spelling `duration()` parses back to exactly `d`: sign, whole seconds, remaining
/// nanoseconds, each part omitted when zero, and `0s` for zero.
fn duration_spelling(d: &chrono::Duration) -> String {
    let neg = *d < chrono::Duration::zero();
    let abs = if neg { -*d } else { *d };
    let secs = abs.num_seconds();
    let nanos = (abs - chrono::Duration::seconds(secs))
        .num_nanoseconds()
        .unwrap_or(0);
    let mut s = String::new();
    if neg {
        s.push('-');
    }
    if secs != 0 {
        s.push_str(&format!("{secs}s"));
    }
    if nanos != 0 {
        s.push_str(&format!("{nanos}ns"));
    }
    if secs == 0 && nanos == 0 {
        s.push_str("0s");
    }
    s
}

fn node(expr: Expr) -> IdedExpr {
    IdedExpr { id: 0, expr }
}

/// One constant slot: a known composite the residual reads, named `$kN`, with the type the
/// original program was checked at for the node it replaces — never a type inferred from the value.
pub(crate) struct Slot {
    pub(crate) name: String,
    pub(crate) value: CelValue,
    pub(crate) ty: CelTy,
}

/// The known composites a residual reads, by slot. The residual names a slot as `Expr::Ident("$kN")`;
/// [`CelProgram::evaluate`](crate::CelProgram::evaluate) and [`emit`](crate::emit) bind every slot
/// themselves, so a caller never sees one.
///
/// Values only: a `CelTy` holds `Rc`, and a compiled program is `Send + Sync`. The slots' types
/// exist while the residual is re-checked, inside `specialize`.
#[derive(Clone, Debug, Default)]
pub(crate) struct ConstPool {
    slots: Vec<(Arc<str>, CelValue)>,
}

impl ConstPool {
    pub(crate) fn new(slots: Vec<(Arc<str>, CelValue)>) -> ConstPool {
        ConstPool { slots }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    pub(crate) fn slots(&self) -> &[(Arc<str>, CelValue)] {
        &self.slots
    }

    /// `// $k0 = <value>`, one line per slot, for a residual's `source()`.
    pub(crate) fn legend(&self) -> String {
        self.slots
            .iter()
            .map(|(name, v)| {
                let text = reify(v)
                    .and_then(|e| crate::unparse::unparse(&e).ok())
                    .unwrap_or_else(|| format!("{v:?}"));
                format!("\n// {name} = {text}")
            })
            .collect()
    }
}

/// Is `name` a constant slot's name (`$k` and a number)? No CEL identifier can be one, so a slot
/// never collides with a variable an author declared.
pub(crate) fn is_slot_name(name: &str) -> bool {
    name.strip_prefix("$k")
        .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

/// Fold a CHECKED tree against the values in `known`, treating exactly the names in `roots` as known
/// roots. A known SCALAR the residual still reads is written out as a literal; a known composite
/// becomes a slot of the returned pool, typed by `types` (the checker's type for every node of `e`,
/// by id).
///
/// Returns the raw residual: no id renumbering and no check that it reads no known root. The slots are numbered in the order the
/// residual first reads them (pre-order), and a slot the fold made and then dropped is not kept.
///
/// The third value is every lowering refusal the fold met (see [`Folder::refused`]).
pub(crate) fn fold_typed(
    e: &IdedExpr,
    known: &Bindings,
    roots: &BTreeSet<String>,
    limits: CelLimits,
    types: &HashMap<u64, CelTy>,
    lowering: Lowering<'_>,
) -> (IdedExpr, Vec<Slot>, Vec<String>) {
    let mut f = Folder::new(known, roots, limits, types, lowering);
    let folded = f.fold(e);
    let mut residual = f.residualize(folded, e);
    let made = std::mem::take(&mut f.pool.slots);
    let slots = compact(&mut residual, made);
    (residual, slots, f.refused)
}

/// Keep the slots `e` reads, renamed `$k0`, `$k1`, … in pre-order of first read.
fn compact(e: &mut IdedExpr, made: Vec<Slot>) -> Vec<Slot> {
    fn walk(
        e: &mut IdedExpr,
        made: &mut [Option<Slot>],
        kept: &mut Vec<Slot>,
        renamed: &mut HashMap<String, String>,
    ) {
        match &mut e.expr {
            Expr::Ident(n) if is_slot_name(n) => {
                if let Some(new) = renamed.get(n.as_str()) {
                    *n = new.clone();
                    return;
                }
                let at = made
                    .iter()
                    .position(|s| s.as_ref().is_some_and(|s| s.name == *n));
                let Some(mut slot) = at.and_then(|i| made[i].take()) else {
                    return;
                };
                let new = format!("$k{}", kept.len());
                renamed.insert(n.clone(), new.clone());
                *n = new.clone();
                slot.name = new;
                kept.push(slot);
            }
            Expr::Unspecified | Expr::Ident(_) | Expr::Literal(_) => {}
            Expr::Select(s) => walk(&mut s.operand, made, kept, renamed),
            Expr::Call(c) => {
                if let Some(t) = c.target.as_mut() {
                    walk(t, made, kept, renamed);
                }
                for a in c.args.iter_mut() {
                    walk(a, made, kept, renamed);
                }
            }
            Expr::List(l) => {
                for x in l.elements.iter_mut() {
                    walk(x, made, kept, renamed);
                }
            }
            Expr::Map(m) => {
                for entry in m.entries.iter_mut() {
                    let EntryExpr::MapEntry(me) = &mut entry.expr;
                    walk(&mut me.key, made, kept, renamed);
                    walk(&mut me.value, made, kept, renamed);
                }
            }
            Expr::Comprehension(c) => {
                walk(&mut c.iter_range, made, kept, renamed);
                walk(&mut c.accu_init, made, kept, renamed);
                walk(&mut c.loop_cond, made, kept, renamed);
                walk(&mut c.loop_step, made, kept, renamed);
                walk(&mut c.result, made, kept, renamed);
            }
        }
    }
    // The fold's names are provisional `$kN` too. Renaming may map `$k3` to `$k0` while a later
    // provisional `$k0` is still to be visited, so a name is looked up by its PROVISIONAL spelling
    // (in `renamed`, then in `made`), and a node is rewritten once.
    let mut made: Vec<Option<Slot>> = made.into_iter().map(Some).collect();
    let mut kept = Vec::new();
    let mut renamed = HashMap::new();
    walk(e, &mut made, &mut kept, &mut renamed);
    kept
}

/// The typed fold's slot table while it runs.
struct Pooling<'t> {
    types: &'t HashMap<u64, CelTy>,
    slots: Vec<Slot>,
}

/// A container value: what a slot holds. Everything else is a scalar and reifies to a literal.
fn is_composite(v: &CelValue) -> bool {
    matches!(v, CelValue::List(_) | CelValue::Map(_))
}

/// Are `a` and `b` the SAME value — not CEL-equal: `0.0` and `-0.0` differ, and a NaN is itself?
/// Two reads that intern to one slot must be indistinguishable to every operation.
fn same(a: &CelValue, b: &CelValue) -> bool {
    match (a, b) {
        (CelValue::Num(x), CelValue::Num(y)) => x.to_bits() == y.to_bits(),
        (CelValue::List(x), CelValue::List(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| same(p, q))
        }
        (CelValue::Map(x), CelValue::Map(y)) => {
            x.len() == y.len()
                && x.iter()
                    .zip(y.iter())
                    .all(|((k, v), (l, w))| k == l && same(v, w))
        }
        (CelValue::Bool(_), CelValue::Bool(_))
        | (CelValue::Str(_), CelValue::Str(_))
        | (CelValue::Bytes(_), CelValue::Bytes(_))
        | (CelValue::Null, CelValue::Null)
        | (CelValue::Duration(_), CelValue::Duration(_)) => a == b,
        // A lazy view is never interned.
        _ => false,
    }
}

/// What folding one node produced: a value (the node is gone) or an expression (the node stays).
pub(crate) enum Folded {
    Value(CelValue),
    Expr(IdedExpr),
}

/// A comprehension variable in scope, innermost last.
enum Local {
    /// Bound to one element of a known range while that range is being unrolled.
    Known(String, CelValue),
    /// The iteration or accumulator variable of a loop that stays in the residual.
    Unknown(String),
}

impl Local {
    fn name(&self) -> &str {
        match self {
            Local::Known(n, _) | Local::Unknown(n) => n,
        }
    }
}

/// The partial evaluator. Every value it folds is computed by the backend
/// ([`FastProgram::lower_node`]) — the engine that runs the residual — on a subtree whose every free
/// identifier is known; everything else is rebuilt from folded children, with only the rewrites
/// the dialect's semantics license.
pub(crate) struct Folder<'k> {
    known: &'k Bindings,
    roots: &'k BTreeSet<String>,
    locals: Vec<Local>,
    // Read by the unroll of a known range, which bounds how many copies of a body it makes.
    limits: CelLimits,
    /// The constant slots a known composite becomes.
    pool: Pooling<'k>,
    /// The checker's kind of every node of the tree being folded, for lowering a closed subtree.
    kinds: &'k Kinds,
    hosts: &'k Arc<HostTable>,
    enums: &'k EnumTable,
    /// Why a closed subtree did not lower, first one first. Non-empty makes the specialization fail.
    pub(crate) refused: Vec<String>,
    /// Test door: fail every lowering (`fork::specialize_with_lowering_refused`).
    refuse_all: bool,
}

/// What the backend needs to lower a closed subtree: the kind of every node of the original tree,
/// and the environment's host functions and closed string sets.
pub(crate) struct Lowering<'k> {
    pub(crate) kinds: &'k Kinds,
    pub(crate) hosts: &'k Arc<HostTable>,
    pub(crate) enums: &'k EnumTable,
    /// Test door: refuse every lowering.
    pub(crate) refuse_all: bool,
}

impl<'k> Folder<'k> {
    pub(crate) fn new(
        known: &'k Bindings,
        roots: &'k BTreeSet<String>,
        limits: CelLimits,
        types: &'k HashMap<u64, CelTy>,
        lowering: Lowering<'k>,
    ) -> Folder<'k> {
        Folder {
            known,
            roots,
            locals: Vec::new(),
            limits,
            pool: Pooling {
                types,
                slots: Vec::new(),
            },
            kinds: lowering.kinds,
            hosts: lowering.hosts,
            enums: lowering.enums,
            refused: Vec::new(),
            refuse_all: lowering.refuse_all,
        }
    }

    /// The expression that stands for the known value `v` in place of `at`: a literal for a scalar;
    /// a constant slot for a composite, typed as the checker typed `at`. `None` when neither exists,
    /// and the caller keeps the node that produced `v`.
    fn place(&mut self, v: &CelValue, at: &IdedExpr) -> Option<IdedExpr> {
        let pool = &mut self.pool;
        if !is_composite(v) {
            return reify(v);
        }
        // A slot's legend spells its value, so a value no literal can spell is not pooled.
        reify(v)?;
        let ty = pool.types.get(&at.id)?.clone();
        let name = match pool.slots.iter().find(|s| s.ty == ty && same(&s.value, v)) {
            Some(s) => s.name.clone(),
            None => {
                let name = format!("$k{}", pool.slots.len());
                pool.slots.push(Slot {
                    name: name.clone(),
                    value: v.clone(),
                    ty,
                });
                name
            }
        };
        Some(node(Expr::Ident(name)))
    }

    /// Can a known element be placed WITHOUT the node that produced it, as a literal? Unrolling
    /// needs this of every element, so it unrolls only over scalars: an element that is itself a
    /// composite keeps the loop, over its slot.
    fn placeable_element(&self, v: &CelValue) -> bool {
        !is_composite(v) && reify(v).is_some()
    }

    /// A CLOSED node is evaluated, and only an `Ok` replaces it. A closed node that errors is kept
    /// with its children folded, so the error happens again at run time, in the same place — it
    /// is never baked into a literal.
    pub(crate) fn fold(&mut self, e: &IdedExpr) -> Folded {
        if self.is_closed(e, &mut Vec::new()) {
            if let Ok(v) = self.eval(e) {
                return Folded::Value(v);
            }
        }
        self.structural(e)
    }

    /// Place a folded result inside a residual node. A value no literal can spell is replaced by
    /// the node that produced it, rebuilt from its folded children.
    pub(crate) fn residualize(&mut self, f: Folded, original: &IdedExpr) -> IdedExpr {
        match f {
            Folded::Expr(x) => x,
            // A literal folds to itself: keep it as AUTHORED. Re-spelling it through `reify` would
            // turn `u.a > 1` into `u.a > 1.0` — the same value (`removed: integer values` makes
            // every number a double), but not the text anyone wrote.
            Folded::Value(_) if matches!(original.expr, Expr::Literal(_)) => original.clone(),
            Folded::Value(v) => match self.place(&v, original) {
                Some(lit) => lit,
                None => match self.structural(original) {
                    Folded::Expr(x) => x,
                    // `structural` hands back a value only from a conditional whose branch it
                    // picked, where `settle` never lets that value be one `reify` refuses, or
                    // from an unrolled predicate, whose value is a bool.
                    Folded::Value(_) => original.clone(),
                },
            },
        }
    }

    /// A closed subtree's value, computed by the backend — the engine that runs the residual.
    /// `Err(())` keeps the node: the error recurs at run time, in place. A lowering refusal is
    /// recorded in `refused`, which fails the whole specialization.
    fn eval(&mut self, e: &IdedExpr) -> Result<CelValue, ()> {
        let lowered = if self.refuse_all {
            Err("lowering refused by the test door".to_string())
        } else {
            FastProgram::lower_node(e, self.kinds, self.hosts, self.enums)
        };
        let program = match lowered {
            Ok(p) => p,
            Err(why) => {
                self.refused.push(why);
                return Err(());
            }
        };
        let mut scope = self.known.clone();
        for l in &self.locals {
            if let Local::Known(n, v) = l {
                // Later (inner) locals are set last and win, over a root of the same name too —
                // an unbound identifier in the lowered subtree is a root READ, served from this
                // scope.
                scope.set(n, v.clone());
            }
        }
        program.eval_value(&scope).map_err(|_| ())
    }

    /// Every free identifier of `e` is a known root or a known local. A function NAME is not an
    /// identifier: `f(known)` is closed, and when the known context has no `f` its evaluation
    /// fails and the call is kept — which is how an unknown function stays symbolic.
    fn is_closed(&self, e: &IdedExpr, bound: &mut Vec<String>) -> bool {
        match &e.expr {
            Expr::Literal(_) => true,
            Expr::Ident(n) => {
                if bound.iter().rev().any(|b| b == n) {
                    return true;
                }
                match self.locals.iter().rev().find(|l| l.name() == n) {
                    Some(Local::Known(..)) => true,
                    Some(Local::Unknown(_)) => false,
                    None => self.roots.contains(n),
                }
            }
            Expr::Select(s) => self.is_closed(&s.operand, bound),
            Expr::Call(c) => {
                c.target
                    .as_deref()
                    .map_or(true, |t| self.is_closed(t, bound))
                    && c.args.iter().all(|a| self.is_closed(a, bound))
            }
            Expr::List(l) => l.elements.iter().all(|x| self.is_closed(x, bound)),
            Expr::Map(m) => m.entries.iter().all(|en| match &en.expr {
                EntryExpr::MapEntry(me) => {
                    self.is_closed(&me.key, bound) && self.is_closed(&me.value, bound)
                }
            }),
            Expr::Comprehension(c) => {
                if !self.is_closed(&c.iter_range, bound) || !self.is_closed(&c.accu_init, bound) {
                    return false;
                }
                // The loop's own variables are defined by the loop and do not make it open.
                let depth = bound.len();
                bound.push(c.iter_var.clone());
                if let Some(v2) = &c.iter_var2 {
                    bound.push(v2.clone());
                }
                bound.push(c.accu_var.clone());
                let inner = self.is_closed(&c.loop_cond, bound)
                    && self.is_closed(&c.loop_step, bound)
                    && self.is_closed(&c.result, bound);
                bound.truncate(depth);
                inner
            }
            Expr::Unspecified => false,
        }
    }

    /// Fold `e` and place the result in a residual node.
    fn fold_expr(&mut self, e: &IdedExpr) -> IdedExpr {
        let f = self.fold(e);
        self.residualize(f, e)
    }

    /// Rebuild a node from folded children, applying the value-directed rewrites.
    fn structural(&mut self, e: &IdedExpr) -> Folded {
        let expr = match &e.expr {
            // A known root or known local reaching here holds a value no literal can spell (it
            // came through `residualize`), and stays a read.
            Expr::Literal(_) | Expr::Unspecified | Expr::Ident(_) => {
                return Folded::Expr(e.clone())
            }
            Expr::Call(c) => return self.call(e, c),
            Expr::Comprehension(c) => return self.comprehension(e, c),
            Expr::Select(s) => Expr::Select(SelectExpr {
                operand: Box::new(self.fold_expr(&s.operand)),
                field: s.field.clone(),
                test: s.test,
            }),
            Expr::List(l) => Expr::List(ListExpr::new(
                l.elements.iter().map(|x| self.fold_expr(x)).collect(),
            )),
            Expr::Map(m) => Expr::Map(MapExpr {
                entries: m
                    .entries
                    .iter()
                    .map(|en| {
                        let EntryExpr::MapEntry(me) = &en.expr;
                        IdedEntryExpr {
                            id: en.id,
                            expr: EntryExpr::MapEntry(MapEntryExpr {
                                key: self.fold_expr(&me.key),
                                value: self.fold_expr(&me.value),
                            }),
                        }
                    })
                    .collect(),
            }),
        };
        Folded::Expr(IdedExpr { id: e.id, expr })
    }

    fn call(&mut self, e: &IdedExpr, c: &CallExpr) -> Folded {
        match (c.func_name.as_str(), c.args.len()) {
            (operators::LOGICAL_AND, 2) => return self.logic(e, c, false),
            (operators::LOGICAL_OR, 2) => return self.logic(e, c, true),
            (operators::CONDITIONAL, 3) => return self.ternary(e, c),
            _ => {}
        }
        let target = c.target.as_deref().map(|t| Box::new(self.fold_expr(t)));
        let args = c.args.iter().map(|a| self.fold_expr(a)).collect();
        Folded::Expr(IdedExpr {
            id: e.id,
            expr: Expr::Call(CallExpr {
                func_name: c.func_name.clone(),
                target,
                args,
            }),
        })
    }

    /// `_&&_` (`absorbing == false`) and `_||_` (`absorbing == true`), by the dialect's rule for them.
    fn logic(&mut self, e: &IdedExpr, c: &CallExpr, absorbing: bool) -> Folded {
        let l = self.fold(&c.args[0]);
        let r = self.fold(&c.args[1]);
        let lb = as_bool(&l);
        let rb = as_bool(&r);
        // The absorbing value on EITHER side decides, whatever the other side is — an error
        // included: `(Err, Some(false))` is `false` for `&&` and `(Err, Some(true))` is `true` for
        // `||`, and the right side runs whenever the left alone does not decide.
        if lb == Some(absorbing) || rb == Some(absorbing) {
            return Folded::Value(CelValue::Bool(absorbing));
        }
        // Both sides are the identity value: the answer is the identity value.
        if lb.is_some() && rb.is_some() {
            return Folded::Value(CelValue::Bool(!absorbing));
        }
        // The identity value drops out: the tree is checked, so the other operand is a bool, and
        // `true && x` answers exactly what `x` does — its value, or its error.
        match (lb, rb) {
            (Some(_), None) => return r,
            (None, Some(_)) => return l,
            _ => {}
        }
        let l = self.residualize(l, &c.args[0]);
        let r = self.residualize(r, &c.args[1]);
        Folded::Expr(IdedExpr {
            id: e.id,
            expr: Expr::Call(CallExpr {
                func_name: c.func_name.clone(),
                target: None,
                args: vec![l, r],
            }),
        })
    }

    /// `_?_:_`: a non-bool condition fails, and ONLY the chosen
    /// branch, so a known bool condition picks its branch and the other is dropped unevaluated.
    fn ternary(&mut self, e: &IdedExpr, c: &CallExpr) -> Folded {
        let cond = self.fold(&c.args[0]);
        match as_bool(&cond) {
            Some(true) => self.settle(&c.args[1]),
            Some(false) => self.settle(&c.args[2]),
            None => {
                let cond = self.residualize(cond, &c.args[0]);
                let a = self.fold_expr(&c.args[1]);
                let b = self.fold_expr(&c.args[2]);
                Folded::Expr(IdedExpr {
                    id: e.id,
                    expr: Expr::Call(CallExpr {
                        func_name: c.func_name.clone(),
                        target: None,
                        args: vec![cond, a, b],
                    }),
                })
            }
        }
    }

    /// Fold `e`, and when that yields a value no literal can spell, the rebuilt `e` instead — so a
    /// caller that later residualizes the result against a DIFFERENT node never falls back to it.
    fn settle(&mut self, e: &IdedExpr) -> Folded {
        match self.fold(e) {
            Folded::Value(v) if reify(&v).is_none() => {
                Folded::Expr(self.residualize(Folded::Value(v), e))
            }
            f => f,
        }
    }

    /// A comprehension: unrolled when its range is known and its shape allows it, else kept.
    /// The range is folded once, here, and handed to whichever of the two runs.
    fn comprehension(&mut self, e: &IdedExpr, c: &ComprehensionExpr) -> Folded {
        if c.iter_var2.is_some() {
            // Not produced by the parser, and refused by the checker.
            return Folded::Expr(e.clone());
        }
        let range = self.fold(&c.iter_range);
        if let Folded::Value(v) = &range {
            if let Some(done) = self.unroll(c, v) {
                return done;
            }
        }
        self.keep_loop(e, c, range)
    }

    /// Replace a loop over the known `range` with what it computes: a balanced `||` chain for
    /// `exists`, a balanced `&&` chain for `all` (over a list's elements, or a map's keys in sorted
    /// order), and a list literal for a two-argument `map` over a list. `None` keeps the loop:
    /// `exists_one`, `filter`, three-argument `map`, a `map` over a map (whose iteration order the
    /// dialect does not fix), a range over `max_unroll`, an element no literal can spell, and any
    /// step or result that is not the expander's.
    ///
    /// Each copy of the body is folded with the element bound as a known local, so an inner loop
    /// that rebinds the same name shadows it, as scopes do.
    fn unroll(&mut self, c: &ComprehensionExpr, range: &CelValue) -> Option<Folded> {
        let shape = classify(c)?;
        // The loop's answer is its accumulator; anything else is not a shape this rewrite knows.
        if !matches!(&c.result.expr, Expr::Ident(n) if *n == c.accu_var) {
            return None;
        }
        let items: Vec<CelValue> = match (range, &shape) {
            (CelValue::List(items), _) => items.to_vec(),
            // Keys in sorted order: a map's entries are.
            (CelValue::Map(m), Fold::Predicate) => m.iter().map(|(k, _)| k.to_value()).collect(),
            _ => return None,
        };
        if items.len() > self.limits.max_unroll || items.iter().any(|v| !self.placeable_element(v))
        {
            return None;
        }
        match shape {
            Fold::Predicate => {
                // `exists`: init `false`, step `_||_`(@result, P); `all`: init `true`, step
                // `_&&_`(@result, P). `absorbing` is the value that decides the chain.
                let Expr::Literal(LiteralValue::Boolean(init)) = &c.accu_init.expr else {
                    return None;
                };
                let absorbing = !*init.inner();
                let op = if absorbing {
                    operators::LOGICAL_OR
                } else {
                    operators::LOGICAL_AND
                };
                let Expr::Call(step) = &c.loop_step.expr else {
                    return None;
                };
                if step.func_name != op
                    || step.args.len() != 2
                    || !matches!(&step.args[0].expr, Expr::Ident(n) if *n == c.accu_var)
                {
                    return None;
                }
                let pred = &step.args[1];
                let mut terms = Vec::new();
                for item in items {
                    self.locals.push(Local::Known(c.iter_var.clone(), item));
                    let f = self.fold(pred);
                    let decided = as_bool(&f);
                    // Residualize BEFORE popping: its fallback re-folds `pred`, which needs the
                    // element bound.
                    let term = match decided {
                        Some(_) => None,
                        None => Some(self.residualize(f, pred)),
                    };
                    self.locals.pop();
                    match (decided, term) {
                        // The chain absorbs every other copy, error or unknown alike — as
                        // `&&`/`||` do, and as the loop's pending error is cleared
                        // by an absorbing accumulator.
                        (Some(b), _) if b == absorbing => {
                            return Some(Folded::Value(CelValue::Bool(absorbing)))
                        }
                        // The identity element drops out.
                        (Some(_), _) => {}
                        (None, Some(t)) => terms.push(t),
                        (None, None) => unreachable!("an undecided copy is residualized"),
                    }
                }
                Some(match terms.len() {
                    0 => Folded::Value(CelValue::Bool(!absorbing)),
                    // The loop computed `identity op P`, and `P` is a checked bool: the identity
                    // drops out.
                    1 => Folded::Expr(terms.pop().expect("one term")),
                    _ => Folded::Expr(balanced(op, terms)),
                })
            }
            Fold::Build => {
                let (filter, appended) = build_parts(&c.loop_step)?;
                if filter.is_some() || !matches!(range, CelValue::List(_)) {
                    return None;
                }
                let mut elements = Vec::with_capacity(items.len());
                for item in items {
                    self.locals.push(Local::Known(c.iter_var.clone(), item));
                    let f = self.fold(appended);
                    elements.push(self.residualize(f, appended));
                    self.locals.pop();
                }
                Some(Folded::Expr(node(Expr::List(ListExpr::new(elements)))))
            }
            Fold::CountingPredicate => None,
        }
    }

    /// A comprehension that stays in the residual: the range and the author's parts are folded,
    /// with the loop's variables in scope as unknowns so they shadow any known root of the same
    /// name. The expander's plumbing — `accu_init`, `loop_cond`, the step's outer operator and
    /// `result` — is carried verbatim, because the backend's error absorption, the checker's
    /// classification and the bytecode emitter all read it.
    fn keep_loop(&mut self, e: &IdedExpr, c: &ComprehensionExpr, range: Folded) -> Folded {
        let range = self.residualize(range, &c.iter_range);
        let depth = self.locals.len();
        self.locals.push(Local::Unknown(c.iter_var.clone()));
        self.locals.push(Local::Unknown(c.accu_var.clone()));
        let step = self.fold_step_parts(&c.loop_step, classify(c));
        self.locals.truncate(depth);
        Folded::Expr(IdedExpr {
            id: e.id,
            expr: Expr::Comprehension(Box::new(ComprehensionExpr {
                iter_range: range,
                loop_step: step,
                ..(*c).clone()
            })),
        })
    }

    /// Rebuild a loop step with the author's sub-expressions folded and the expander's operator
    /// nodes kept:
    ///
    /// - predicate: `_&&_`/`_||_`(@result, PRED) — fold `PRED`;
    /// - counting predicate: `_?_:_`(PRED, @result + 1, @result) — fold `PRED`;
    /// - build: `_+_`(@result, [APPENDED]), optionally under `_?_:_`(FILTER, …, @result) — fold
    ///   `FILTER` and `APPENDED`.
    ///
    /// An unrecognised step is copied whole.
    fn fold_step_parts(&mut self, step: &IdedExpr, shape: Option<Fold>) -> IdedExpr {
        let Expr::Call(c) = &step.expr else {
            return step.clone();
        };
        let mut c = c.clone();
        match shape {
            Some(Fold::Predicate) if c.args.len() == 2 => {
                c.args[1] = self.fold_expr(&c.args[1]);
            }
            Some(Fold::CountingPredicate)
                if c.func_name == operators::CONDITIONAL && c.args.len() == 3 =>
            {
                c.args[0] = self.fold_expr(&c.args[0]);
            }
            Some(Fold::Build) => {
                if c.func_name == operators::CONDITIONAL && c.args.len() == 3 {
                    c.args[0] = self.fold_expr(&c.args[0]);
                    let Some(add) = self.fold_appended(&c.args[1]) else {
                        return step.clone();
                    };
                    c.args[1] = add;
                } else {
                    return self.fold_appended(step).unwrap_or_else(|| step.clone());
                }
            }
            _ => return step.clone(),
        }
        IdedExpr {
            id: step.id,
            expr: Expr::Call(c),
        }
    }

    /// `_+_`(@result, [APPENDED]) with `APPENDED` folded, or `None` for any other shape.
    fn fold_appended(&mut self, add: &IdedExpr) -> Option<IdedExpr> {
        let Expr::Call(c) = &add.expr else {
            return None;
        };
        if c.func_name != operators::ADD || c.args.len() != 2 {
            return None;
        }
        let Expr::List(l) = &c.args[1].expr else {
            return None;
        };
        if l.elements.len() != 1 {
            return None;
        }
        let appended = self.fold_expr(&l.elements[0]);
        let mut c = c.clone();
        c.args[1] = IdedExpr {
            id: c.args[1].id,
            expr: Expr::List(ListExpr::new(vec![appended])),
        };
        Some(IdedExpr {
            id: add.id,
            expr: Expr::Call(c),
        })
    }
}

fn call2(op: &str, left: IdedExpr, right: IdedExpr) -> IdedExpr {
    node(Expr::Call(CallExpr {
        func_name: op.to_string(),
        target: None,
        args: vec![left, right],
    }))
}

/// `terms[0] op terms[1] op …`, grouped exactly as the parser groups a written run
/// (`LogicManager::balanced_tree`), so the nesting depth is `ceil(log2 n)`. `terms.len() >= 2`.
fn balanced(op: &str, terms: Vec<IdedExpr>) -> IdedExpr {
    fn build(op: &str, terms: &mut [Option<IdedExpr>], lo: usize, hi: usize) -> IdedExpr {
        let mid = (lo + hi).div_ceil(2);
        let left = if mid == lo {
            terms[mid].take().expect("each term is placed once")
        } else {
            build(op, terms, lo, mid - 1)
        };
        let right = if mid == hi {
            terms[mid + 1].take().expect("each term is placed once")
        } else {
            build(op, terms, mid + 1, hi)
        };
        call2(op, left, right)
    }
    let n = terms.len();
    let mut slots: Vec<Option<IdedExpr>> = terms.into_iter().map(Some).collect();
    build(op, &mut slots, 0, n - 2)
}

fn as_bool(f: &Folded) -> Option<bool> {
    match f {
        Folded::Value(CelValue::Bool(b)) => Some(*b),
        _ => None,
    }
}

/// The desugared tree a compiled program runs.
#[cfg_attr(not(feature = "conformance"), allow(dead_code))]
pub fn expression_of(p: &crate::CelProgram) -> &IdedExpr {
    p.program().expression()
}

/// Fresh ids, pre-order, from 1.
///
/// Unrolling clones a body once per element, so a folded tree repeats ids. Nothing evaluates by id,
/// but the source map and any id-keyed table downstream assume each id names one node.
pub fn renumber(e: &mut IdedExpr) {
    fn walk(e: &mut IdedExpr, next: &mut u64) {
        e.id = *next;
        *next += 1;
        match &mut e.expr {
            Expr::Unspecified | Expr::Ident(_) | Expr::Literal(_) => {}
            Expr::Select(s) => walk(&mut s.operand, next),
            Expr::Call(c) => {
                if let Some(t) = c.target.as_mut() {
                    walk(t, next);
                }
                for a in c.args.iter_mut() {
                    walk(a, next);
                }
            }
            Expr::List(l) => {
                for x in l.elements.iter_mut() {
                    walk(x, next);
                }
            }
            Expr::Map(m) => {
                for entry in m.entries.iter_mut() {
                    entry.id = *next;
                    *next += 1;
                    let EntryExpr::MapEntry(me) = &mut entry.expr;
                    walk(&mut me.key, next);
                    walk(&mut me.value, next);
                }
            }
            Expr::Comprehension(c) => {
                walk(&mut c.iter_range, next);
                walk(&mut c.accu_init, next);
                walk(&mut c.loop_cond, next);
                walk(&mut c.loop_step, next);
                walk(&mut c.result, next);
            }
        }
    }
    walk(e, &mut 1);
}

/// `Err(rendered path)` when `e` reads a root in `roots` that no comprehension variable shadows.
///
/// Syntactic: a read is an identifier, and the path is the chain of field selections on it.
pub fn check_no_known_read(e: &IdedExpr, roots: &BTreeSet<String>) -> Result<(), String> {
    fn walk(e: &IdedExpr, roots: &BTreeSet<String>, bound: &mut Vec<String>) -> Result<(), String> {
        match &e.expr {
            Expr::Ident(n) if roots.contains(n) && !bound.contains(n) => Err(n.clone()),
            Expr::Unspecified | Expr::Ident(_) | Expr::Literal(_) => Ok(()),
            Expr::Select(s) => {
                walk(&s.operand, roots, bound).map_err(|p| format!("{p}.{}", s.field))
            }
            Expr::Call(c) => {
                if let Some(t) = &c.target {
                    walk(t, roots, bound)?;
                }
                c.args.iter().try_for_each(|a| walk(a, roots, bound))
            }
            Expr::List(l) => l.elements.iter().try_for_each(|x| walk(x, roots, bound)),
            Expr::Map(m) => m.entries.iter().try_for_each(|entry| {
                let EntryExpr::MapEntry(me) = &entry.expr;
                walk(&me.key, roots, bound)?;
                walk(&me.value, roots, bound)
            }),
            Expr::Comprehension(c) => {
                walk(&c.iter_range, roots, bound)?;
                walk(&c.accu_init, roots, bound)?;
                let depth = bound.len();
                bound.push(c.iter_var.clone());
                bound.extend(c.iter_var2.clone());
                bound.push(c.accu_var.clone());
                let r = walk(&c.loop_cond, roots, bound)
                    .and_then(|_| walk(&c.loop_step, roots, bound))
                    .and_then(|_| walk(&c.result, roots, bound));
                bound.truncate(depth);
                r
            }
        }
    }
    walk(e, roots, &mut Vec::new())
}

/// Check a finished residual against the roster the original compiled against, and hand back its
/// demand — exactly what the residual reads, from the same harvester that produced the
/// original's. Each constant slot is declared with its type (`slots`) and names no demand.
///
/// The checker is the STRICT one `compile` uses: a known composite is a slot typed from the
/// declaration, not a literal that could type weaker than the schema did, so every residual of a
/// program that checked is itself a program that checks. `Err` carries why the residual is not an
/// expression of the original's `result` type that checks: the fold produced it, so that is a
/// defect of the fold, never of the author.
pub(crate) fn recheck(
    types: &TypeEnv,
    max_depth: u32,
    e: &IdedExpr,
    slots: &[(String, CelTy)],
    result: CelTy,
) -> Result<(DemandSet, HashMap<u64, CelTy>), String> {
    let checker = Checker::new(types, max_depth);
    let (ty, demand, node_types) = checker.with_consts(slots).run_typed(e).map_err(|errors| {
        let first = errors.first().map(|e| e.message.as_str()).unwrap_or("");
        format!("the residual does not type-check: {first}")
    })?;
    if ty != result {
        return Err(format!(
            "the residual is {}, not {}",
            ty.name(),
            result.name()
        ));
    }
    Ok((demand, node_types))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn roster() -> TypeEnv {
        let mut t = TypeEnv::new();
        t.declare(
            "req",
            crate::Record::new("req", [("path", CelTy::Str), ("size", CelTy::Num)]).into(),
        );
        t
    }

    fn tree(src: &str) -> IdedExpr {
        crate::parser::Parser::default().parse(src).expect("parses")
    }

    #[test]
    fn an_ill_typed_residual_is_refused_with_the_checker_message() {
        let e = recheck(&roster(), 32, &tree("req.path > 1.0"), &[], CelTy::Bool)
            .expect_err("ill-typed");
        assert!(e.starts_with("the residual does not type-check: "), "{e}");
    }

    #[test]
    fn a_residual_that_is_not_bool_is_refused() {
        let e = recheck(&roster(), 32, &tree("req.size + 1.0"), &[], CelTy::Bool)
            .expect_err("not bool");
        assert_eq!(e, "the residual is double, not bool");
    }

    #[test]
    fn the_recheck_refuses_a_type_error() {
        for src in ["[1] == ['a']", "req.path > 1.0", "req.path.startsWith(1.0)"] {
            let e = recheck(&roster(), 32, &tree(src), &[], CelTy::Bool)
                .expect_err("a type error is refused by the re-check");
            assert!(
                e.starts_with("the residual does not type-check: "),
                "{src}: {e}"
            );
        }
    }

    #[test]
    fn a_well_typed_residual_hands_back_its_demand() {
        let (d, _) =
            recheck(&roster(), 32, &tree("req.size > 1.0"), &[], CelTy::Bool).expect("checks");
        assert_eq!(d.to_string(), "[req ▸ \"size\"]");
    }
}
