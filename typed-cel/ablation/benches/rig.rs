//! The rig `cliffs.rs` and `loops.rs` share: the roster, its data, the three ways a decision runs,
//! and one timed measurement.

use std::hint::black_box;
use std::time::Instant;

use typed_cel::{
    emit, CelActivation, CelEnvironment, CelTy, CompileOpts, FactPoll, Facts, FastProgram,
    FastScratch, FieldId, FieldPath, Record, Vm,
};
use serde_json::{json, Value as J};

use crate::pmu;

fn rec(origin: &str, fields: &[(&str, CelTy)]) -> CelTy {
    Record::new(origin, fields.iter().map(|(n, t)| (*n, t.clone()))).into()
}

/// The roster of `tests/support/perf.rs`, minus the fields no row here reads.
pub fn env() -> CelEnvironment {
    let mut e = CelEnvironment::new();
    let item = rec(
        "item",
        &[
            ("id", CelTy::Str),
            ("qty", CelTy::Num),
            ("tags", CelTy::list(CelTy::Str)),
        ],
    );
    let req: CelTy = Record::new(
        "req",
        [
            ("path", CelTy::Str),
            ("name", CelTy::Str),
            ("other", CelTy::Str),
            ("n", CelTy::Num),
            ("flag", CelTy::Bool),
            ("d", CelTy::Duration),
            ("opt", CelTy::Str),
        ],
    )
    .with_optional(["opt"])
    .into();
    e.declare("req", req);
    e.declare(
        "policy",
        rec(
            "policy",
            &[
                ("roots", CelTy::list(CelTy::Str)),
                ("names", CelTy::list(CelTy::Str)),
                ("nums", CelTy::list(CelTy::Num)),
                ("items", CelTy::list(item)),
                ("m", CelTy::map(CelTy::Str, CelTy::Num)),
                ("long", CelTy::list(CelTy::Str)),
            ],
        ),
    );
    e
}

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
    // 200-byte strings with no `zz` in them: a substring search reads every byte.
    let long: Vec<String> = (0..n)
        .map(|i| format!("{}{i:04}", "a/".repeat(98)))
        .collect();
    json!({"roots": roots, "names": names, "nums": nums, "items": items, "m": m, "long": long})
}

pub fn req() -> J {
    json!({"path": "/req/x/y.txt", "name": "zz", "other": "yy", "n": 0.5, "flag": true,
           "d": "90s", "opt": "o"})
}

enum V {
    Absent,
    Bool(bool),
    Num(f64),
    Str(String),
}

struct JsonFacts(Vec<V>);

impl JsonFacts {
    fn new(fields: &[FieldPath], req: &J) -> Option<JsonFacts> {
        let mut out = Vec::new();
        for f in fields {
            if f.root() != "req" {
                return None;
            }
            let mut at = Some(req);
            for seg in f.segments() {
                at = at.and_then(|v| v.get(seg));
            }
            out.push(match at {
                None => V::Absent,
                Some(J::Bool(b)) => V::Bool(*b),
                Some(J::Number(n)) => V::Num(n.as_f64()?),
                Some(J::String(s)) => V::Str(s.clone()),
                Some(_) => return None,
            });
        }
        Some(JsonFacts(out))
    }
}

impl Facts for JsonFacts {
    fn bool(&self, f: FieldId) -> Option<bool> {
        match &self.0[f.index()] {
            V::Bool(b) => Some(*b),
            _ => None,
        }
    }
    fn num(&self, f: FieldId) -> Option<f64> {
        match &self.0[f.index()] {
            V::Num(n) => Some(*n),
            _ => None,
        }
    }
    fn str(&self, f: FieldId) -> Option<&str> {
        match &self.0[f.index()] {
            V::Str(s) => Some(s),
            _ => None,
        }
    }
    fn has(&self, f: FieldId) -> bool {
        !matches!(self.0[f.index()], V::Absent)
    }
    fn poll(&self, _: FieldId) -> FactPoll {
        FactPoll::Ready
    }
}

#[derive(Clone, Copy)]
pub enum Leg {
    /// `Vm::eval` over an activation binding `req` and `policy`.
    Act,
    /// `decide` over `req`'s `Facts`.
    Facts,
    /// `policy` specialized in; the residual decided over `req`'s `Facts`.
    Spec,
}

pub struct Row {
    pub decide: Box<dyn FnMut() -> bool>,
}

pub fn prepare(env: &CelEnvironment, src: &str, leg: Leg, n: usize) -> Row {
    let p = env
        .compile(src, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("{src}: {e}"));
    let (pol, rq) = (policy(n), req());
    let bind = |roots: &[(&str, &J)]| -> CelActivation {
        let mut a = env.activation();
        for (name, v) in roots {
            a.bind(name, v).expect("binds");
        }
        a
    };
    match leg {
        Leg::Act => {
            let code = emit(&p).expect("emits");
            let act = bind(&[("req", &rq), ("policy", &pol)]);
            let vm = Vm::new();
            Row {
                decide: Box::new(move || vm.eval(&code, &act).unwrap_or(false)),
            }
        }
        Leg::Facts | Leg::Spec => {
            let residual = match leg {
                Leg::Spec => env
                    .compile(
                        src,
                        &CompileOpts {
                            known: Some(&bind(&[("policy", &pol)])),
                            ..Default::default()
                        },
                    )
                    .expect("specializes"),
                _ => p,
            };
            let fast = FastProgram::new(&residual).expect("lowers");
            let facts = JsonFacts::new(fast.fields(), &rq).expect("reads req scalars only");
            let mut scratch = FastScratch::default();
            Row {
                decide: Box::new(move || fast.decide(&facts, &mut scratch).unwrap_or(false)),
            }
        }
    }
}

/// The median ns per decision over 15 timed runs of at least 20 ms each, and the cycles and
/// instructions per decision where the PMU is readable.
pub fn measure(row: &mut Row, ctr: &Option<pmu::Ctr>) -> (f64, Option<[f64; 4]>) {
    for _ in 0..1000 {
        black_box((row.decide)());
    }
    let mut per = Vec::new();
    for _ in 0..15 {
        let mut iters = 1usize;
        loop {
            let t = Instant::now();
            for _ in 0..iters {
                black_box((row.decide)());
            }
            let el = t.elapsed();
            if el.as_millis() >= 20 {
                per.push(el.as_nanos() as f64 / iters as f64);
                break;
            }
            iters *= 2;
        }
    }
    per.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let ns = per[per.len() / 2];
    let counts = ctr.as_ref().map(|c| {
        let iters = ((20_000_000.0 / ns.max(1.0)) as usize).max(1);
        let mut f = |_| (row.decide)();
        pmu::per_call(c, 1, iters, &mut f)
    });
    (ns, counts)
}
