//! The backend over generated programs: every op reached by a generator or the conformance lane,
//! and the one piece of pattern recognition the backend does (the matcher), held to the loop it
//! replaces and to the plain Rust reading of the same words.
//!
//! Every test collects EVERY mismatch, each with a one-line reproduction, and fails once with the
//! whole list — a first-failure report would hide how wide a divergence is — and asserts how many
//! cases RAN, not merely that none disagreed.

#[path = "../conformance/harness/mod.rs"]
mod harness;
#[path = "support/mod.rs"]
mod support;

use typed_cel::CompileOpts;
use std::collections::BTreeSet;
use std::sync::Arc;

use harness::case::Binding;
use harness::exclusions::Exclusions;
use harness::{conformance_dir, corpus};
use support::gen::{roster, typed_batch, Gen, SEEDS};
use typed_cel::fork;
use typed_cel::{CelEnvironment, CelError, CelLimits, CelTy, CelValue, FastProgram};

fn fail_on(what: &str, mismatches: &[String]) {
    assert!(
        mismatches.is_empty(),
        "{} {what} mismatch(es):\n\n{}",
        mismatches.len(),
        mismatches.join("\n\n")
    );
}

fn compile_typed(src: &str, whence: &str) -> typed_cel::CelProgram {
    roster()
        .compile(src, &CompileOpts::default())
        .unwrap_or_else(|e| {
            panic!("{whence}: the typed generator produced `{src}`, which does not compile:\n{e}")
        })
}

/// Every op the backend has, reached by the typed generator or the conformance corpus — an op
/// no generated program lowers to is an op no generated test (`tests/generated_golden.rs`,
/// `tests/metamorphic.rs`) has run. `RaisePending`,
/// `CatchPending`, `BrPending` and `Clear` are a kept loop's error bookkeeping, which only a
/// comprehension the specializer did not unroll reaches; the corpus's loops and `mix_equation` do.
#[test]
fn the_generators_reach_every_op() {
    const EVERY_OP: &[&str] = &[
        "Const",
        "Raise",
        "Read",
        "ReadCached",
        "Has",
        "Local",
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
        "StrOp2",
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
        "CondEqFF",
        "CondEqFK",
        "EqK",
        "Catch",
        "Absorb",
        "Nsf",
        "IterInit",
        "IterNext",
        "IterScan",
        "BrPending",
        "Clear",
        "Inc",
        "NumIn",
        "CondCmpFK",
        "CondFR",
        "CondCmpK",
        "IndexIter",
        "ArithK",
        "CondStrOp2F",
        "CondMatches",
        "ListNew",
        "Append",
        "ListFreeze",
        "BrSet",
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
        // A call over constants runs at lowering, on the backend: its ops ran too.
        reached.extend(fast.folded_op_names());
    }
    for (id, program) in lane_programs() {
        let fast = fast(&program, &id);
        reached.extend(fast.op_names());
        reached.extend(fast.folded_op_names());
    }
    // Host calls: the host generator `tests/host_functions.rs` runs its differential over.
    let hosts = support::gen::host_roster();
    let mut g = Gen::new(SEEDS[0] ^ 0x4057);
    for _ in 0..100 {
        let src = g.host_bool(4);
        let program = hosts
            .compile(&src, &CompileOpts::default())
            .expect("the host generator compiles");
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
        let program = tags
            .compile(src, &CompileOpts::default())
            .expect("compiles");
        reached.extend(FastProgram::new(&program).expect("lowers").op_names());
    }
    let want: BTreeSet<&str> = EVERY_OP.iter().copied().collect();
    let unknown: Vec<_> = reached.difference(&want).collect();
    assert!(unknown.is_empty(), "not in EVERY_OP: {unknown:?}");
    // The ops neither generator lowers to yet — each is a gap in the typed generator, recorded
    // exactly so it can only shrink: a map literal with a computed value (`MakeMap`, `CheckKey`),
    // `-x` on a non-constant, `duration(x)` on a computed string, and a matcher in branch position (reached by `under_any_matches_the_exists_
    // shape`, not by a generator). `Nsf`, `BrPending` and `Step` are the literal comprehension
    // loop's condition and step bookkeeping, and `MakeList` its `[e]` step: every macro's
    // expansion now lowers past them (`try_predicate_loop`, `try_build_loop`), and only a
    // comprehension of no macro's shape — or the literal lowering `tests/comprehensions.rs` holds
    // the others against — still reaches them. `IndexIter` is `m[k]` inside a loop over `m`: the
    // typed generator never indexes by a loop's key, and teaching it to would move every frozen
    // row of `tests/generated_golden.rs`; `a_map_loop_answers_as_the_expansion_does` holds it
    // against the literal lowering's `Index`. `CondMatches` is `matches()` over a literal pattern
    // in branch position: the typed generator writes no `matches`, and
    // `a_field_test_in_a_loop_answers_as_the_expansion_does` holds it.
    const NOT_YET_GENERATED: &[&str] = &[
        "BrPending",
        "CheckKey",
        "CondMatch",
        "CondMatches",
        "Duration",
        "IndexIter",
        "MakeList",
        "MakeMap",
        "Neg",
        "Nsf",
        "Step",
    ];
    let missing: Vec<&str> = want.difference(&reached).copied().collect();
    assert_eq!(
        missing, NOT_YET_GENERATED,
        "the ops no generated program lowers to changed — shrink NOT_YET_GENERATED to match"
    );
}

/// Every case the conformance lane RUNS (the checker admits it and the backend agrees with the
/// corpus): its id and its program, checked against its bindings' types.
fn lane_programs() -> Vec<(String, typed_cel::CelProgram)> {
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
        for (name, binding) in &case.bindings {
            let Binding::Value(v) = binding else {
                panic!("{id}: binding `{name}` is not a value");
            };
            env.declare(
                name.clone(),
                harness::run::type_of(v).expect("the harness typed it"),
            );
        }
        let program = fork::compile_any(&env, &case.expr)
            .unwrap_or_else(|e| panic!("{id}: the harness admitted `{}`: {e}", case.expr));
        out.push((id, program));
    }
    assert!(out.len() >= 400, "only {} lane cases", out.len());
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
/// specialized residual — unrolled into an `||` chain (default `max_unroll`) and kept as a loop over
/// its constant slot (`max_unroll = 0`) — answers as the unspecialized program does, and as the
/// plain Rust reading of the same words does. Each residual
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
            let original = env.compile(SRC, &CompileOpts::default()).expect("compiles");
            let mut known = env.activation();
            known.bind("roots", &roots_json).expect("binds");
            let residual = env
                .compile(
                    original.source(),
                    &CompileOpts {
                        known: Some(&known),
                        ..Default::default()
                    },
                )
                .expect("specializes");
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
                        "{shape}: roots={roots:?} p={p:?}: original {want:?}, residual {got:?}, rust {rust}"
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
            [CelValue::Str(r)] => Ok(CelValue::from(dir_prefix(r))),
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
/// the host once per element at lowering. Either way the answer is the unspecialized program's,
/// and the Rust reading of `r.trim_end_matches('/') + "/"` — which a root
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
            let original = env.compile(SRC, &CompileOpts::default()).expect("compiles");
            let mut known = env.activation();
            known.bind("roots", &roots_json).expect("binds");
            let residual = env
                .compile(
                    original.source(),
                    &CompileOpts {
                        known: Some(&known),
                        ..Default::default()
                    },
                )
                .expect("specializes");
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
                open.bind_fact("p", CelValue::from(p.as_str()));
                let want = original.evaluate(&full);
                let got = code.eval(&open);
                let rust = roots
                    .iter()
                    .any(|r| p == *r || p.starts_with(&dir_prefix(r)));
                compared += 1;
                if want.as_ref().ok() != Some(&rust) || got.as_ref().ok() != Some(&rust) {
                    mismatches.push(format!(
                        "{shape}: roots={roots:?} p={p:?}: original {want:?}, residual {got:?}, rust {rust}"
                    ));
                }
            }
        }
    }
    fail_on("under_any (dirPrefix)", &mismatches);
    assert!(compared >= 5000, "only {compared} comparisons");

    // The boundary row the `r + "/"` spelling gets wrong.
    let env = under_env_with_dir_prefix(0);
    let original = env.compile(SRC, &CompileOpts::default()).expect("compiles");
    let mut known = env.activation();
    known
        .bind("roots", &serde_json::json!(["/ws/"]))
        .expect("binds");
    let code = FastProgram::new(
        &env.compile(
            original.source(),
            &CompileOpts {
                known: Some(&known),
                ..Default::default()
            },
        )
        .expect("specializes"),
    )
    .expect("lowers");
    let mut act = env.runtime().activation();
    act.bind_fact("p", CelValue::Str("/ws/x".into()));
    assert_eq!(code.eval(&act).map_err(|e| e.to_string()), Ok(true));
}

/// The specializer's law, over every generated program: bind any one root as known and
/// specialize, then run the residual on the others — it answers exactly as the program does with
/// every root bound. Verdict alike, and error alike (by message: the source a message names
/// is the residual's, not the original's).
#[test]
fn specialized_generated_programs_answer_as_unspecialized() {
    fn message(e: &typed_cel::CelError) -> String {
        match e {
            typed_cel::CelError::Evaluation { message, .. } => message.clone(),
            other => other.to_string(),
        }
    }
    let env = roster();
    let mut compared = 0usize;
    let mut mismatches = Vec::new();
    for seed in SEEDS {
        for (index, (src, acts)) in typed_batch(seed).iter().enumerate() {
            let original = compile_typed(src, &format!("seed={seed:#x} index={index}"));
            for act in acts {
                let Some((known_name, known_value)) = act.first() else {
                    continue;
                };
                let mut known = env.activation();
                known.bind(known_name, known_value).expect("binds");
                let residual = match env.compile(
                    original.source(),
                    &CompileOpts {
                        known: Some(&known),
                        ..Default::default()
                    },
                ) {
                    Ok(r) => r,
                    Err(e) => {
                        mismatches.push(format!("{src}\n  specialize over `{known_name}`: {e}"));
                        continue;
                    }
                };
                let mut full = env.activation();
                let mut rest = env.activation();
                for (i, (name, value)) in act.iter().enumerate() {
                    full.bind(name, value).expect("binds");
                    if i > 0 {
                        rest.bind(name, value).expect("binds");
                    }
                }
                let want = original.evaluate(&full).map_err(|e| message(&e));
                let got = residual.evaluate(&rest).map_err(|e| message(&e));
                compared += 1;
                if want != got {
                    mismatches.push(format!(
                        "{src}\n  known {known_name} = {known_value}\n  residual: {}\n  want {want:?}\n  got  {got:?}",
                        residual.source()
                    ));
                }
            }
        }
    }
    fail_on("specialize-then-run", &mismatches);
    assert!(compared >= 5000, "compared only {compared}");
}

/// The shapes the specializer rewrites — a conditional compared to one of its arms, a double
/// negation, a call that closes once its arguments fold — answer as written, over every state of
/// their unknown operands, an unbound (erroring) one included. The generator rarely spells them,
/// so they are enumerated here.
#[test]
fn the_rewritten_shapes_answer_as_written() {
    fn message(e: &typed_cel::CelError) -> String {
        match e {
            typed_cel::CelError::Evaluation { message, .. } => message.clone(),
            other => other.to_string(),
        }
    }
    let mut env = typed_cel::CelEnvironment::new();
    env.declare("x", CelTy::Bool);
    env.declare("y", CelTy::Bool);
    env.declare("k", CelTy::Str);
    env.declare("t", CelTy::Bool);
    let shapes = [
        r#"(x ? "a" : "b") == k"#,
        r#"(x ? "a" : "b") != k"#,
        r#"k == (x && y ? "a" : "b")"#,
        r#"k != (x || y ? "a" : "b")"#,
        "!!(x || y)",
        "!(t || x)",
        "!(t && x)",
        r#"y && !(t || k == "a")"#,
    ];
    let mut compared = 0usize;
    let mut mismatches = Vec::new();
    for src in shapes {
        let original = env.compile(src, &CompileOpts::default()).expect("compiles");
        for k in ["a", "b", "z"] {
            for t in [true, false] {
                let mut known = env.activation();
                known.bind("k", &serde_json::json!(k)).expect("binds");
                known.bind("t", &serde_json::json!(t)).expect("binds");
                let residual = env
                    .compile(
                        original.source(),
                        &CompileOpts {
                            known: Some(&known),
                            ..Default::default()
                        },
                    )
                    .expect("specializes");
                for x in [Some(true), Some(false), None] {
                    for y in [Some(true), Some(false), None] {
                        let mut full = env.activation();
                        let mut rest = env.activation();
                        full.bind("k", &serde_json::json!(k)).expect("binds");
                        full.bind("t", &serde_json::json!(t)).expect("binds");
                        for (name, v) in [("x", x), ("y", y)] {
                            if let Some(v) = v {
                                full.bind(name, &serde_json::json!(v)).expect("binds");
                                rest.bind(name, &serde_json::json!(v)).expect("binds");
                            }
                        }
                        let want = original.evaluate(&full).map_err(|e| message(&e));
                        let got = residual.evaluate(&rest).map_err(|e| message(&e));
                        compared += 1;
                        if want != got {
                            mismatches.push(format!(
                                "{src} with k={k} t={t} x={x:?} y={y:?}\n  residual: {}\n  want {want:?}\n  got  {got:?}",
                                residual.source()
                            ));
                        }
                    }
                }
            }
        }
    }
    fail_on("rewritten-shape", &mismatches);
    assert_eq!(compared, 8 * 3 * 2 * 9);
}
