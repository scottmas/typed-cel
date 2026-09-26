//! The differential gate: `Vm` — the fast backend, the only one — beside the absorbed evaluator,
//! over generated typed expressions (eager and lazy), the conformance corpus, and the one piece of
//! pattern recognition the backend does (the matcher), held to the loop it replaces.
//!
//! Every test collects EVERY mismatch, each with a one-line reproduction, and fails once with the
//! whole list — a first-failure report would hide how wide a divergence is. There is no fallback:
//! every test asserts how many cases RAN on the backend, not merely that none disagreed.

#[path = "../conformance/harness/mod.rs"]
mod harness;
#[path = "support/mod.rs"]
mod support;

use std::collections::BTreeSet;
use std::sync::atomic::Ordering;
use std::sync::Arc;

use harness::case::Binding;
use harness::exclusions::Exclusions;
use harness::{conformance_dir, corpus};
use support::gen::{roster, same_outcome, typed_json, Gen, JsonLazy, SEEDS};
use typed_cel::fork::{self, Context, Program};
use typed_cel::{
    CelActivation, CelEnvironment, CelError, CelLimits, CelTy, CelValue, FastProgram, Vm,
};

const TYPED_PER_SEED: usize = 1000;
const ACTIVATIONS_PER_EXPRESSION: usize = 3;

fn fail_on(what: &str, mismatches: &[String]) {
    assert!(
        mismatches.is_empty(),
        "{} {what} mismatch(es):\n\n{}",
        mismatches.len(),
        mismatches.join("\n\n")
    );
}

/// Seed `seed`'s typed expressions, each with its activations' JSON.
#[allow(clippy::type_complexity)]
fn typed_batch(seed: u64) -> Vec<(String, Vec<Vec<(&'static str, serde_json::Value)>>)> {
    let mut g = Gen::new(seed);
    (0..TYPED_PER_SEED)
        .map(|_| {
            let src = g.typed_bool(4);
            let acts = (0..ACTIVATIONS_PER_EXPRESSION)
                .map(|_| typed_json(&mut g))
                .collect();
            (src, acts)
        })
        .collect()
}

fn compile_typed(src: &str, whence: &str) -> typed_cel::CelProgram {
    roster().compile(src).unwrap_or_else(|e| {
        panic!("{whence}: the typed generator produced `{src}`, which does not compile:\n{e}")
    })
}

/// Both `Ok` and equal, or both `Err` with identical text.
fn same_verdict(a: &Result<bool, CelError>, b: &Result<bool, CelError>) -> bool {
    match (a, b) {
        (Ok(x), Ok(y)) => x == y,
        (Err(x), Err(y)) => x.to_string() == y.to_string(),
        _ => false,
    }
}

fn render(json: &[(&'static str, serde_json::Value)]) -> String {
    json.iter()
        .map(|(k, v)| format!("{k}={v}"))
        .collect::<Vec<_>>()
        .join(" ")
}

#[test]
fn generated_typed_expressions_evaluate_the_same_through_the_public_api() {
    let env = roster();
    let mut compared = 0usize;
    let (mut ok, mut err) = (0usize, 0usize);
    let mut mismatches = Vec::new();
    for seed in SEEDS {
        for (index, (src, acts)) in typed_batch(seed).iter().enumerate() {
            let whence = format!("seed={seed:#x}, index={index}");
            let program = compile_typed(src, &whence);
            let bytecode = typed_cel::emit(&program).expect("emits");
            for json in acts {
                let mut act = env.activation();
                for (name, v) in json {
                    act.bind(name, v)
                        .unwrap_or_else(|e| panic!("{whence}: binding {name}={v}: {e}"));
                }
                let a = program.evaluate(&act);
                let b = Vm::new().eval(&bytecode, &act);
                compared += 1;
                match &a {
                    Ok(_) => ok += 1,
                    Err(_) => err += 1,
                }
                if !same_verdict(&a, &b) {
                    mismatches.push(format!(
                        "{whence}: {src}\n  with {}\n  evaluate: {a:?}\n  vm:       {b:?}",
                        render(json)
                    ));
                }
            }
        }
    }
    fail_on("typed", &mismatches);
    eprintln!("typed: {compared} ran on the backend ({ok} Ok, {err} Err)");
    assert_eq!(
        compared,
        SEEDS.len() * TYPED_PER_SEED * ACTIVATIONS_PER_EXPRESSION,
        "every generated program runs on the backend"
    );
    assert!(
        err * 10 >= compared,
        "only {err} of {compared} runs are errors"
    );
}

/// What one lazy evaluation observed: its verdict and the counters of `r` and `m`.
#[derive(Debug)]
struct Observed {
    verdict: Result<bool, CelError>,
    members: (usize, usize),
    keys: (usize, usize),
}

fn observe(
    json: &[(&'static str, serde_json::Value)],
    run: &dyn Fn(&CelActivation) -> Result<bool, CelError>,
) -> Observed {
    let mut act = roster().activation();
    let mut lazy = |name: &str| -> Arc<JsonLazy> {
        let (_, v) = json.iter().find(|(k, _)| *k == name).expect("bound");
        let view = Arc::new(JsonLazy::new(v.as_object().expect("an object").clone()));
        act.bind_lazy(name, CelValue::Lazy(Arc::clone(&view) as _))
            .expect("declared");
        view
    };
    let (r, m) = (lazy("r"), lazy("m"));
    for (name, v) in json.iter().filter(|(k, _)| *k != "r" && *k != "m") {
        act.bind(name, v).expect("binds");
    }
    let verdict = run(&act);
    Observed {
        verdict,
        members: (
            r.members.load(Ordering::SeqCst),
            m.members.load(Ordering::SeqCst),
        ),
        keys: (
            r.key_calls.load(Ordering::SeqCst),
            m.key_calls.load(Ordering::SeqCst),
        ),
    }
}

#[test]
fn lazy_reads_agree_on_generated_expressions() {
    let mut compared = 0usize;
    let mut mismatches = Vec::new();
    for seed in SEEDS {
        for (index, (src, acts)) in typed_batch(seed).iter().enumerate() {
            let whence = format!("seed={seed:#x}, index={index}");
            let program = compile_typed(src, &whence);
            let bytecode = typed_cel::emit(&program).expect("emits");
            for json in acts {
                let a = observe(json, &|act| program.evaluate(act));
                let b = observe(json, &|act| Vm::new().eval(&bytecode, act));
                compared += 1;
                if !same_verdict(&a.verdict, &b.verdict)
                    || a.members != b.members
                    || a.keys != b.keys
                {
                    mismatches.push(format!(
                        "{whence}: {src}\n  with {}\n  evaluate: {a:?}\n  vm:       {b:?}",
                        render(json)
                    ));
                }
            }
        }
    }
    fail_on("lazy", &mismatches);
    assert_eq!(
        compared,
        SEEDS.len() * TYPED_PER_SEED * ACTIVATIONS_PER_EXPRESSION,
        "every generated program runs on the backend"
    );
}

/// Every op the backend has, reached by the typed generator or the conformance corpus — an op
/// no generated program lowers to is an op no differential above has run. `RaisePending`,
/// `CatchPending`, `BrPending` and `Clear` are a kept loop's error bookkeeping, which only a
/// comprehension the specializer did not unroll reaches; the corpus's loops and `mix_equation` do.
#[test]
fn the_generators_reach_every_op() {
    const EVERY_OP: &[&str] = &[
        "Const",
        "Raise",
        "Read",
        "Has",
        "Local",
        "Own",
        "Select",
        "HasOf",
        "Index",
        "Not",
        "Neg",
        "Eq",
        "Ne",
        "Cmp",
        "Arith",
        "In",
        "Match",
        "StrOp",
        "Matches",
        "Size",
        "Duration",
        "DurPart",
        "MakeList",
        "CheckKey",
        "MakeMap",
        "Jump",
        "BrTrue",
        "BrFalse",
        "Cond",
        "CondRead",
        "CondEqK",
        "CondMatch",
        "RaiseIfErr",
        "EqK",
        "Catch",
        "Absorb",
        "Nsf",
        "IterInit",
        "IterNext",
        "BrPending",
        "Clear",
        "Step",
        "CatchPending",
        "RaisePending",
        "Ret",
        "RetK",
        "Fail",
        "Host",
        "TagIn",
        "CondTagIn",
    ];
    let mut reached: BTreeSet<&'static str> = BTreeSet::new();
    for (index, (src, _)) in typed_batch(SEEDS[0]).iter().enumerate() {
        let program = compile_typed(src, &format!("typed index={index}"));
        let fast = FastProgram::new(&program).expect("lowers");
        reached.extend(fast.op_names());
    }
    for (id, _, program, _) in typed_lane_cases() {
        let fast = fast(&program, &id);
        reached.extend(fast.op_names());
    }
    // Host calls: the host generator `tests/host_functions.rs` runs its differential over.
    let hosts = support::gen::host_roster();
    let mut g = Gen::new(SEEDS[0] ^ 0x4057);
    for _ in 0..100 {
        let src = g.host_bool(4);
        let program = hosts.compile(&src).expect("the host generator compiles");
        reached.extend(FastProgram::new(&program).expect("lowers").op_names());
    }
    // Tag tests over a closed string set, in value and branch position: the shapes
    // `tests/enum_tags.rs` runs its generated differential over.
    let mut tags = CelEnvironment::new();
    tags.declare("e", CelTy::Str);
    tags.declare_enum(&["e"], &["a", "b"]).expect("declares");
    for src in [
        r#"e == "a""#,
        r#"(e == "a" || e == "b") ? e == "b" : false"#,
    ] {
        let program = tags.compile(src).expect("compiles");
        reached.extend(FastProgram::new(&program).expect("lowers").op_names());
    }
    let want: BTreeSet<&str> = EVERY_OP.iter().copied().collect();
    let unknown: Vec<_> = reached.difference(&want).collect();
    assert!(unknown.is_empty(), "not in EVERY_OP: {unknown:?}");
    // The ops neither generator lowers to yet — each is a gap in the typed generator, recorded
    // exactly so it can only shrink: a map literal with a computed value (`MakeMap`, `CheckKey`),
    // `-x` on a non-constant, `duration(x)` / `getSeconds()` on a computed duration, a select on a
    // computed record, and a matcher in branch position (reached by `under_any_matches_the_exists_
    // shape`, not by a generator).
    const NOT_YET_GENERATED: &[&str] = &[
        "CheckKey",
        "CondMatch",
        "DurPart",
        "Duration",
        "MakeMap",
        "Neg",
        "Select",
    ];
    let missing: Vec<&str> = want.difference(&reached).copied().collect();
    assert_eq!(
        missing, NOT_YET_GENERATED,
        "the ops no generated program lowers to changed — shrink NOT_YET_GENERATED to match"
    );
}

/// Every case the conformance harness RUNS (the checker admits it and the evaluator agrees with the corpus):
/// its id, its expression, the program checked against its bindings' types, and the bindings.
fn typed_lane_cases() -> Vec<(String, String, typed_cel::CelProgram, Context<'static>)> {
    let exclusions = Exclusions::load(&conformance_dir().join("EXCLUSIONS.toml")).expect("loads");
    let mut out = Vec::new();
    for case in corpus().cases() {
        if exclusions.reason_for(case).is_some() {
            continue;
        }
        if harness::run::run(case) != harness::run::Outcome::Pass {
            continue;
        }
        let id = case.unique_id();
        let mut env = CelEnvironment::new();
        let mut ctx = Context::default();
        for (name, binding) in &case.bindings {
            let Binding::Value(v) = binding else {
                panic!("{id}: binding `{name}` is not a value");
            };
            let ty = harness::run::type_of(v).expect("the harness typed it");
            env.declare(name.clone(), ty);
            let value = harness::run::to_runtime(v).expect("the harness bound it");
            ctx.add_variable_from_value(name.clone(), value);
        }
        let program = fork::compile_any(&env, &case.expr)
            .unwrap_or_else(|e| panic!("{id}: the harness admitted `{}`: {e}", case.expr));
        out.push((id, case.expr.clone(), program, ctx));
    }
    out
}

/// Every checked program lowers — there is no fallback to count it against.
fn fast(program: &typed_cel::CelProgram, whence: &str) -> FastProgram {
    FastProgram::new(program).unwrap_or_else(|e| {
        panic!(
            "{whence}: the fast backend refused a checked program `{}`:\n{e}",
            program.source()
        )
    })
}

/// The conformance corpus on the backend: every case the harness runs, run on the backend too, with
/// the evaluator's exact outcome — value or error.
#[test]
fn the_conformance_corpus_runs_on_the_fast_backend() {
    let cases = typed_lane_cases();
    let mut ran = 0usize;
    let mut mismatches = Vec::new();
    for (id, expr, program, ctx) in &cases {
        let code = fast(program, id);
        let want = Program::compile(expr).expect("parses").execute(ctx);
        let got = fork::fast_value(&code, ctx);
        ran += 1;
        if !same_outcome(&want, &got) {
            mismatches.push(format!(
                "{id}\n  expr: {expr}\n  evaluator: {want:?}\n  fast:      {got:?}"
            ));
        }
    }
    fail_on("conformance", &mismatches);
    eprintln!("conformance: {ran} cases ran on the backend");
    assert_eq!(ran, cases.len());
    assert!(ran >= 400, "only {ran} conformance cases ran");
}

// ---- the matcher ----

/// Roots a policy might write: `/` itself, trailing slashes, a name and its extension (`/ws` vs
/// `/wsx`), bytes below `/` (`-`, `.`), `..` segments, the empty string and non-ASCII.
const ROOTS: &[&str] = &[
    "/",
    "/ws",
    "/ws/",
    "/wsx",
    "/ws-a",
    "/ws.b",
    "/ws/..",
    "/a/../b",
    "",
    "/ws//",
    "/w",
    "/x/y/z",
    "/ünï",
    "/etc",
    "/etc/passwd",
    "/proc",
    "/tmp/",
    "//",
];

fn paths(roots: &[String]) -> Vec<String> {
    let mut out: Vec<String> = [
        "/ws",
        "/ws/",
        "/ws/x",
        "/wsx",
        "/wsx/y",
        "/ws-a/x",
        "/ws.b",
        "/",
        "",
        "//",
        "/w",
        "/ws/../etc",
        "/a/../b/c",
        "/x/y/z/w",
        "/ünï/q",
        "/etcetera",
        "/etc/passwd/x",
        "/tmp",
        "/tmp//x",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    for r in roots {
        for suffix in ["", "/", "x", "/q", "-"] {
            out.push(format!("{r}{suffix}"));
        }
        if let Some(shorter) = r.get(..r.len().saturating_sub(1)) {
            out.push(shorter.to_string());
        }
    }
    out
}

fn root_lists() -> Vec<Vec<String>> {
    let mut g = Gen::new(0x5EED_0F_A11);
    let mut lists: Vec<Vec<String>> = vec![
        Vec::new(),
        vec!["/ws".into()],
        vec!["/ws/".into()],
        vec!["/".into()],
        ROOTS.iter().map(|s| s.to_string()).collect(),
    ];
    for i in 0..40 {
        let n = 1 + g.below(if i % 2 == 0 { 8 } else { 40 });
        let mut l: Vec<String> = (0..n).map(|_| g.pick(ROOTS).to_string()).collect();
        // Past the scan threshold, with roots that are prefixes of each other.
        if i % 3 == 0 {
            for k in 0..20 {
                l.push(format!("/data/d{k:02}"));
                l.push(format!("/data/d{k:02}/sub"));
            }
        }
        lists.push(l);
    }
    lists
}

fn under_env(max_unroll: usize) -> CelEnvironment {
    let limits = CelLimits {
        max_unroll,
        ..CelLimits::default()
    };
    let mut e = CelEnvironment::with_limits(limits);
    e.declare("roots", CelTy::list(CelTy::Str));
    e.declare("p", CelTy::Str);
    e
}

/// `UnderAny` is the `exists` it replaces: over every generated root list and every path, the
/// specialized residual on the fast backend — unrolled into an `||` chain (default `max_unroll`)
/// and kept as a loop over its constant slot (`max_unroll = 0`) — answers as the evaluator does on
/// the unspecialized program, and as the plain Rust reading of the same words does. Each residual
/// MUST have lowered to a matcher, and the sorted shape must have been reached.
#[test]
fn under_any_matches_the_exists_shape() {
    const SRC: &str = r#"roots.exists(r, p == r || p.startsWith(r + "/"))"#;
    let mut compared = 0usize;
    let mut sorted_seen = false;
    let mut mismatches = Vec::new();
    for roots in root_lists() {
        let roots_json = serde_json::json!(roots);
        for (shape, max_unroll) in [("unrolled", 256usize), ("loop", 0usize)] {
            let env = under_env(max_unroll);
            let original = env.compile(SRC).expect("compiles");
            let mut known = env.activation();
            known.bind("roots", &roots_json).expect("binds");
            let residual = env.specialize(&original, &known).expect("specializes");
            let code = FastProgram::new(&residual).expect("lowers");
            if !roots.is_empty() {
                assert!(
                    code.matcher_count() >= 1,
                    "{shape} residual of {roots:?} did not lower to a matcher:\n{}",
                    residual.source()
                );
            }
            sorted_seen |= code.has_sorted_matcher();
            for p in paths(&roots) {
                let p_json = serde_json::json!(p);
                let mut full = env.activation();
                full.bind("roots", &roots_json).expect("binds");
                full.bind("p", &p_json).expect("binds");
                let mut open = env.activation();
                open.bind("p", &p_json).expect("binds");
                let want = original.evaluate(&full);
                let got = code.eval(&open);
                let rust = roots
                    .iter()
                    .any(|r| p == *r || p.starts_with(&format!("{r}/")));
                compared += 1;
                if want.as_ref().ok() != Some(&rust) || got.as_ref().ok() != Some(&rust) {
                    mismatches.push(format!(
                        "{shape}: roots={roots:?} p={p:?}: evaluator {want:?}, fast {got:?}, rust {rust}"
                    ));
                }
            }
        }
    }
    fail_on("under_any", &mismatches);
    assert!(sorted_seen, "no root list reached the sorted matcher");
    assert!(compared >= 5000, "only {compared} comparisons");
}

/// `dir_prefix(r)`: `r` with EVERY trailing slash trimmed, then one `/` — so `/ws/` lies above
/// `/ws/x` exactly as `/ws` does, and `/` and `""` are both the prefix `/`.
fn dir_prefix(r: &str) -> String {
    format!("{}/", r.trim_end_matches('/'))
}

fn under_env_with_dir_prefix(max_unroll: usize) -> CelEnvironment {
    let mut e = under_env(max_unroll);
    e.register_host(
        "dirPrefix",
        &[CelTy::Str],
        CelTy::Str,
        false,
        Arc::new(|a: &[CelValue]| match a {
            [CelValue::Str(r)] => Ok(CelValue::Str(dir_prefix(r))),
            _ => Err(CelError::Evaluation {
                source: Arc::from("dirPrefix"),
                message: "expects one string".into(),
            }),
        }),
    )
    .expect("registers");
    e
}

/// The same shape with the prefix computed by a PURE HOST function: unrolled, every call folds
/// to a literal and the chain becomes a matcher; kept as a loop, the matcher is built by calling
/// the host once per element at lowering. Either way the answer is the evaluator's on the
/// unspecialized program, and the Rust reading of `r.trim_end_matches('/') + "/"` — which a root
/// written with a trailing slash (`/ws/`) is the case that tells apart from `r + "/"`.
#[test]
fn under_any_with_a_host_prefix_trims_every_trailing_slash() {
    const SRC: &str = r#"roots.exists(r, p == r || p.startsWith(dirPrefix(r)))"#;
    let mut compared = 0usize;
    let mut mismatches = Vec::new();
    let mut lists = root_lists();
    lists.push(vec!["/ws//".into(), "/".into(), "".into()]);
    for roots in lists {
        let roots_json = serde_json::json!(roots);
        for (shape, max_unroll) in [("unrolled", 256usize), ("loop", 0usize)] {
            let env = under_env_with_dir_prefix(max_unroll);
            let original = env.compile(SRC).expect("compiles");
            let mut known = env.activation();
            known.bind("roots", &roots_json).expect("binds");
            let residual = env.specialize(&original, &known).expect("specializes");
            let code = FastProgram::new(&residual).expect("lowers");
            if !roots.is_empty() {
                assert!(
                    code.matcher_count() >= 1,
                    "{shape} residual of {roots:?} did not lower to a matcher:\n{}",
                    residual.source()
                );
                assert!(
                    !code.op_names().contains(&"Host"),
                    "{shape}: the host call survived lowering:\n{}",
                    code.listing()
                );
            }
            for p in paths(&roots) {
                let p_json = serde_json::json!(p);
                let mut full = env.activation();
                full.bind("roots", &roots_json).expect("binds");
                full.bind("p", &p_json).expect("binds");
                let mut open = env.runtime().activation();
                open.bind_fact("p", CelValue::Str(p.clone()));
                let want = original.evaluate(&full);
                let got = code.eval(&open);
                let rust = roots
                    .iter()
                    .any(|r| p == *r || p.starts_with(&dir_prefix(r)));
                compared += 1;
                if want.as_ref().ok() != Some(&rust) || got.as_ref().ok() != Some(&rust) {
                    mismatches.push(format!(
                        "{shape}: roots={roots:?} p={p:?}: evaluator {want:?}, fast {got:?}, rust {rust}"
                    ));
                }
            }
        }
    }
    fail_on("under_any (dirPrefix)", &mismatches);
    assert!(compared >= 5000, "only {compared} comparisons");

    // The boundary row the `r + "/"` spelling gets wrong.
    let env = under_env_with_dir_prefix(0);
    let original = env.compile(SRC).expect("compiles");
    let mut known = env.activation();
    known
        .bind("roots", &serde_json::json!(["/ws/"]))
        .expect("binds");
    let code =
        FastProgram::new(&env.specialize(&original, &known).expect("specializes")).expect("lowers");
    let mut act = env.runtime().activation();
    act.bind_fact("p", CelValue::Str("/ws/x".into()));
    assert_eq!(code.eval(&act).map_err(|e| e.to_string()), Ok(true));
}
