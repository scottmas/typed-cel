//! The cost-model rig shared by `tests/perf_cliffs.rs` (the red pins) and `tests/perf_harvest.rs`
//! (the sweep that found them): one roster shaped like a chokepoint's `req` + a bound `policy`, a
//! `Facts` over JSON, and one measured decision on each leg a program can run on.
//!
//! Everything here is COUNTED with `typed_cel::profile` — ops dispatched, `slow` entries, host field
//! reads, values built, allocations — never timed. A binary using it installs
//! `typed_cel::profile::CountingAlloc` as its global allocator, or every allocation count is 0
//! (`assert_counting` says so loudly).

use typed_cel::fork::ast::{EntryExpr, Expr, IdedExpr};
use typed_cel::profile::{self, RunProfile};
use typed_cel::CompileOpts;
use typed_cel::{
    emit, CelActivation, CelEnvironment, CelProgram, CelTy, FactPoll, Facts, FastProgram,
    FastScratch, FieldId, FieldPath, Vm,
};
use serde_json::{json, Value as J};

use super::{record, record_opt};

/// Fail loudly when the binary did not install the counting allocator: an allocation budget
/// measured against a silent 0 is a vacuous green.
pub fn assert_counting() {
    assert!(
        profile::alloc_counting_installed(),
        "install `typed_cel::profile::CountingAlloc` as this binary's #[global_allocator]"
    );
}

fn item() -> CelTy {
    record(
        "item",
        &[
            ("id", CelTy::Str),
            ("qty", CelTy::Num),
            ("tags", CelTy::list(CelTy::Str)),
        ],
    )
}

/// `req` (the request a chokepoint decides on: scalars, plus two request-side lists) and `policy`
/// (what an operator binds once: lists, records, maps).
pub fn env() -> CelEnvironment {
    let mut e = CelEnvironment::new();
    let deep = record(
        "req.a",
        &[(
            "b",
            record(
                "req.a.b",
                &[(
                    "c",
                    record(
                        "req.a.b.c",
                        &[("d", record("req.a.b.c.d", &[("e", CelTy::Str)]))],
                    ),
                )],
            ),
        )],
    );
    e.declare(
        "req",
        record_opt(
            "req",
            &[
                ("path", CelTy::Str),
                ("name", CelTy::Str),
                ("other", CelTy::Str),
                ("long", CelTy::Str),
                ("n", CelTy::Num),
                ("flag", CelTy::Bool),
                ("d", CelTy::Duration),
                ("opt", CelTy::Str),
                ("a", deep),
                ("tags", CelTy::list(CelTy::Str)),
                ("nums", CelTy::list(CelTy::Num)),
            ],
            &["opt"],
        ),
    );
    e.declare(
        "policy",
        record(
            "policy",
            &[
                ("roots", CelTy::list(CelTy::Str)),
                ("names", CelTy::list(CelTy::Str)),
                ("nums", CelTy::list(CelTy::Num)),
                ("items", CelTy::list(item())),
                ("m", CelTy::map(CelTy::Str, CelTy::Num)),
                ("limit", CelTy::Duration),
            ],
        ),
    );
    e
}

/// A `policy` binding with `n` of each collection. No root matches `/req/...`, no name is `"zz"`,
/// every number is at least 1: an `exists` scans them all, an `all` holds throughout.
pub fn policy(n: usize) -> J {
    let roots: Vec<String> = (0..n).map(|i| format!("/root{i:04}")).collect();
    let names: Vec<String> = (0..n).map(|i| format!("name{i:04}")).collect();
    let nums: Vec<f64> = (0..n).map(|i| (i + 1) as f64).collect();
    let items: Vec<J> = (0..n)
        .map(|i| json!({"id": format!("id{i:04}"), "qty": (i + 1) as f64, "tags": ["t0", "t1", "t2"]}))
        .collect();
    let m: serde_json::Map<String, J> = (0..n)
        .map(|i| (format!("key{i:04}"), json!((i + 1) as f64)))
        .collect();
    json!({"roots": roots, "names": names, "nums": nums, "items": items, "m": m, "limit": "5s"})
}

/// A `req` binding: `n` request-side list elements and a `long` string of `n * 64` bytes.
pub fn req(n: usize) -> J {
    let tags: Vec<String> = (0..n).map(|i| format!("tag{i:04}")).collect();
    let nums: Vec<f64> = (0..n).map(|i| (i + 1) as f64).collect();
    json!({
        "path": "/req/x/y.txt", "name": "zz", "other": "yy", "long": "ab".repeat(n * 32),
        "n": 0.5, "flag": true, "d": "90s", "opt": "o",
        "a": {"b": {"c": {"d": {"e": "leaf"}}}},
        "tags": tags, "nums": nums,
    })
}

#[derive(Clone, Debug)]
enum FactVal {
    Absent,
    Bool(bool),
    Num(f64),
    Str(String),
    Dur(i64),
}

/// `Facts` over JSON: every field the program reads resolved once. `None` when the program reads a
/// list or record whole (a `Facts` serves scalars only).
pub struct JsonFacts {
    vals: Vec<FactVal>,
}

impl JsonFacts {
    pub fn new(fields: &[FieldPath], roots: &[(&str, &J)]) -> Option<JsonFacts> {
        let mut vals = Vec::new();
        for field in fields {
            let mut at = roots
                .iter()
                .find(|(n, _)| *n == field.root())
                .map(|(_, v)| *v);
            for seg in field.segments() {
                at = match at {
                    Some(J::Object(o)) => o.get(seg),
                    Some(_) => return None,
                    None => None,
                };
            }
            vals.push(match at {
                None => FactVal::Absent,
                Some(J::Bool(b)) => FactVal::Bool(*b),
                Some(J::Number(n)) => FactVal::Num(n.as_f64()?),
                // Every string field of this roster that a program reads as a duration is `d` or
                // `limit`; the others are strings. The kind is the program's: a `Want::Dur` read
                // asks `duration_ms`, a string read asks `str`, so both are kept.
                Some(J::String(s)) => match (field.segments().last(), s.strip_suffix('s')) {
                    (Some("d" | "limit"), Some(secs)) => {
                        FactVal::Dur(secs.parse::<i64>().ok()? * 1000)
                    }
                    _ => FactVal::Str(s.clone()),
                },
                Some(_) => return None,
            });
        }
        Some(JsonFacts { vals })
    }
}

impl Facts for JsonFacts {
    fn bool(&self, f: FieldId) -> Option<bool> {
        match &self.vals[f.index()] {
            FactVal::Bool(b) => Some(*b),
            _ => None,
        }
    }
    fn num(&self, f: FieldId) -> Option<f64> {
        match &self.vals[f.index()] {
            FactVal::Num(n) => Some(*n),
            _ => None,
        }
    }
    fn str(&self, f: FieldId) -> Option<&str> {
        match &self.vals[f.index()] {
            FactVal::Str(s) => Some(s),
            _ => None,
        }
    }
    fn duration_ms(&self, f: FieldId) -> Option<i64> {
        match &self.vals[f.index()] {
            FactVal::Dur(ms) => Some(*ms),
            _ => None,
        }
    }
    fn has(&self, f: FieldId) -> bool {
        !matches!(self.vals[f.index()], FactVal::Absent)
    }
    fn poll(&self, _: FieldId) -> FactPoll {
        FactPoll::Ready
    }
}

/// Which engine path a decision ran on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Leg {
    /// `Vm::eval` over an activation binding `req` and `policy` (what `CelProgram::evaluate` runs).
    Act,
    /// `FastProgram::decide` over `Facts` — only for a program that reads scalars only.
    Facts,
    /// `policy` bound at compile time (`specialize`); the residual decided over `req`'s `Facts`,
    /// or evaluated over a `req` activation when it still reads a `req` collection.
    SpecKnown,
    /// `req` bound at compile time, `policy` left unknown: the residual evaluated over `policy`.
    SpecUnknown,
}

impl Leg {
    pub const ALL: [Leg; 4] = [Leg::Act, Leg::Facts, Leg::SpecKnown, Leg::SpecUnknown];

    pub fn name(self) -> &'static str {
        match self {
            Leg::Act => "act",
            Leg::Facts => "facts",
            Leg::SpecKnown => "spec_known",
            Leg::SpecUnknown => "spec_unknown",
        }
    }
}

/// One program, ready to decide on one leg.
pub struct Prepared {
    pub leg: Leg,
    /// The program the leg runs (the residual on a specialized leg).
    pub program: CelProgram,
    pub fast: FastProgram,
    facts: Option<JsonFacts>,
    act: CelActivation,
    code: Option<typed_cel::CelBytecode>,
    /// What `specialize` did, on a specialized leg.
    pub specialize: Option<RunProfile>,
}

/// `src` prepared on `leg` over `policy`/`req`; `None` when the leg does not apply (a `Facts`
/// leg over a program that reads a collection whole).
pub fn prepare(env: &CelEnvironment, src: &str, leg: Leg, policy: &J, req: &J) -> Option<Prepared> {
    let compiled = env
        .compile(src, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("`{src}` does not compile: {e}"));
    let bind = |roots: &[(&str, &J)]| {
        let mut a = env.activation();
        for (n, v) in roots {
            a.bind(n, v).unwrap_or_else(|e| panic!("{n} binds: {e}"));
        }
        a
    };
    let facts_over =
        |fast: &FastProgram, roots: &[(&str, &J)]| JsonFacts::new(fast.fields(), roots);
    Some(match leg {
        Leg::Act => {
            let code = emit(&compiled).expect("emits");
            Prepared {
                leg,
                fast: FastProgram::new(&compiled).expect("lowers"),
                program: compiled,
                facts: None,
                act: bind(&[("req", req), ("policy", policy)]),
                code: Some(code),
                specialize: None,
            }
        }
        Leg::Facts => {
            let fast = FastProgram::new(&compiled).expect("lowers");
            let facts = facts_over(&fast, &[("req", req), ("policy", policy)])?;
            Prepared {
                leg,
                fast,
                program: compiled,
                facts: Some(facts),
                act: env.activation(),
                code: None,
                specialize: None,
            }
        }
        Leg::SpecKnown | Leg::SpecUnknown => {
            let (known, rest) = if leg == Leg::SpecKnown {
                (("policy", policy), ("req", req))
            } else {
                (("req", req), ("policy", policy))
            };
            let known_act = bind(&[known]);
            let (residual, sp) = profile::measure(|| {
                env.compile(
                    compiled.source(),
                    &CompileOpts {
                        known: Some(&known_act),
                        ..Default::default()
                    },
                )
            });
            let residual = residual.unwrap_or_else(|e| panic!("`{src}` specializes: {e}"));
            let fast = FastProgram::new(&residual).expect("the residual lowers");
            let facts = facts_over(&fast, &[rest]);
            Prepared {
                leg,
                fast,
                program: residual,
                act: bind(&[rest]),
                facts,
                code: None,
                specialize: Some(sp),
            }
        }
    })
}

impl Prepared {
    /// One decision.
    pub fn run(&self, scratch: &mut FastScratch) -> Result<bool, typed_cel::CelError> {
        match (&self.facts, &self.code) {
            (Some(f), _) => self.fast.decide(f, scratch),
            (None, Some(code)) => Vm::new().eval(code, &self.act),
            (None, None) => self.fast.eval(&self.act),
        }
    }

    /// One WARMED decision, counted: the verdict and what it cost.
    pub fn measure(&self) -> (Result<bool, typed_cel::CelError>, RunProfile) {
        let mut scratch = FastScratch::default();
        let _ = self.run(&mut scratch);
        profile::measure(|| self.run(&mut scratch))
    }

    /// The path this leg actually decided on, for a report.
    pub fn how(&self) -> &'static str {
        match (&self.facts, &self.code) {
            (Some(_), _) => "decide(facts)",
            (None, Some(_)) => "Vm::eval(act)",
            (None, None) => "eval(act)",
        }
    }
}

/// Nodes in a checked tree.
pub fn nodes(e: &IdedExpr) -> usize {
    1 + match &e.expr {
        Expr::Call(c) => {
            c.target.as_deref().map_or(0, nodes) + c.args.iter().map(nodes).sum::<usize>()
        }
        Expr::Select(s) => nodes(&s.operand),
        Expr::List(l) => l.elements.iter().map(nodes).sum(),
        Expr::Map(m) => m
            .entries
            .iter()
            .map(|en| match &en.expr {
                EntryExpr::MapEntry(me) => nodes(&me.key) + nodes(&me.value),
            })
            .sum(),
        Expr::Comprehension(c) => {
            nodes(&c.iter_range)
                + nodes(&c.accu_init)
                + nodes(&c.loop_cond)
                + nodes(&c.loop_step)
                + nodes(&c.result)
        }
        _ => 0,
    }
}

/// Is `e` closed over nothing a run supplies — literals only, composed? (A `$kN` constant slot is
/// an identifier and does not count: folding it is what made it a slot.)
fn literal_only(e: &IdedExpr) -> bool {
    match &e.expr {
        Expr::Literal(_) => true,
        Expr::Call(c) => {
            c.target.as_deref().map_or(true, literal_only) && c.args.iter().all(literal_only)
        }
        Expr::List(l) => l.elements.iter().all(literal_only),
        _ => false,
    }
}

/// The calls in a residual whose every operand is a literal: work the partial evaluator left for
/// every decision to redo. (`duration("5s")` is how a duration literal is spelled, and is not one.)
pub fn foldable_calls(e: &IdedExpr, out: &mut Vec<String>) {
    match &e.expr {
        Expr::Call(c) => {
            let spelled_duration = c.func_name == "duration" && c.args.len() == 1;
            if !spelled_duration && !c.args.is_empty() && literal_only(e) {
                out.push(format!("{}/{}", c.func_name, c.args.len()));
                return;
            }
            if let Some(t) = c.target.as_deref() {
                foldable_calls(t, out);
            }
            for a in &c.args {
                foldable_calls(a, out);
            }
        }
        Expr::Select(s) => foldable_calls(&s.operand, out),
        Expr::List(l) => l.elements.iter().for_each(|x| foldable_calls(x, out)),
        Expr::Map(m) => m.entries.iter().for_each(|en| match &en.expr {
            EntryExpr::MapEntry(me) => {
                foldable_calls(&me.key, out);
                foldable_calls(&me.value, out);
            }
        }),
        Expr::Comprehension(c) => {
            for x in [
                &c.iter_range,
                &c.accu_init,
                &c.loop_cond,
                &c.loop_step,
                &c.result,
            ] {
                foldable_calls(x, out);
            }
        }
        _ => {}
    }
}
