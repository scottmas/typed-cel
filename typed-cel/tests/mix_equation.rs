//! The mix equation: specializing a program against the roots known now, then evaluating the
//! residual on the rest, is evaluating the program on everything — on the reference evaluator and
//! over bound values and read by field alike.
//!
//! ```text
//! column 1   P.evaluate(K ∪ U)                          the original, over bound values
//! column 2   env.compile(P, {known: K})?.evaluate(U)      the residual, over bound values
//! column 3   residual.decide(JsonFacts(U))              the residual, read by field
//! ```
//!
//! Two outcomes agree when both are `Ok(b)` with the same `b`, or both are `Err(_)`. Error identity
//! is not compared: an evaluation error embeds the program's source, which differs between `P` and
//! its residual by construction, and the residual's grouping may meet a different operand's error
//! first.
//!
//! Precondition: every bound value conforms to its declared type. `bind` enforces it for JSON; a
//! `LazyValue` serving a number for a `bool` field could make `true && x` (native:
//! `NoSuchOverload`) and its residual `x` differ. Every case here binds through `bind` only.
//!
//! A fourth column, the original read by field, is a GUARD: when it disagrees with column 1 the row
//! is reported as a host defect, so a column-3 failure is never pinned on the specializer. Columns 3
//! and 4 run only where every field the program reads is a scalar.

#[path = "support/mod.rs"]
mod support;

use serde_json::{json, Value as J};
use support::gen::Gen;
use support::mix::{self, Row};
use support::record;
use typed_cel::{CelEnvironment, CelLimits, CelTy};

/// Four fixed seeds, so a failing row reproduces from its printed (seed, index) alone — remote
/// `cargo` forwards no environment variable.
const SEEDS: [u64; 4] = [
    0x9E37_79B9_7F4A_7C15,
    0xD1B5_4A32_D192_ED03,
    0x2545_F491_4F6C_DD1D,
    0x6A09_E667_F3BC_C908,
];
const CASES_PER_SEED: usize = 500;

/// Every generated row, labelled with its seed and index.
fn rows() -> Vec<(String, Row)> {
    let mut out = Vec::with_capacity(SEEDS.len() * CASES_PER_SEED);
    for seed in SEEDS {
        let mut g = Gen::new(seed);
        for index in 0..CASES_PER_SEED {
            let case = mix::case(&mut g, index);
            let env = mix::roster(case.limits);
            let row = mix::row(&env, &case.source, case.known, case.completion);
            out.push((format!("seed {seed:#x} case {index}"), row));
        }
    }
    out
}

#[test]
fn the_mix_equation_holds() {
    let rows = rows();
    assert!(rows.len() >= 2_000, "only {} rows", rows.len());
    // No fallback: every residual lowers.
    let fast = rows.iter().filter(|(_, r)| r.ran_fast()).count();
    let by_field = rows.iter().filter(|(_, r)| r.c3.is_some()).count();
    println!(
        "{fast} of {} residuals lowered; column 3 (read by field) ran on {by_field}",
        rows.len()
    );
    let failing: Vec<&(String, Row)> = rows
        .iter()
        .filter(|(_, r)| !r.holds() || !r.guard_holds())
        .collect();
    // Two populations, reported apart: a residual that DISAGREES, and a program `specialize`
    // REFUSED (with default limits no generated program exceeds a bound, so every refusal is a
    // defect too). Refusals are tallied by message, so a new kind stands out from a known one.
    let (refused, disagree): (Vec<&&(String, Row)>, Vec<&&(String, Row)>) =
        failing.iter().partition(|(_, r)| r.residual.is_err());
    let mut kinds = std::collections::BTreeMap::<String, usize>::new();
    for (_, r) in &refused {
        let msg = r.residual.as_ref().err().expect("refused");
        let kind = msg.lines().last().unwrap_or_default().trim().to_string();
        *kinds.entry(kind).or_default() += 1;
    }
    let first = |rows: &[&&(String, Row)]| {
        rows.iter()
            .take(3)
            .map(|(label, r)| r.report(label))
            .collect::<Vec<_>>()
            .join("\n\n")
    };
    assert!(
        failing.is_empty(),
        "{} of {} rows fail: {} disagree, {} refused\n\nrefusals by message:\n{}\n\nfirst disagreements:\n{}\n\nfirst refusals:\n{}",
        failing.len(),
        rows.len(),
        disagree.len(),
        refused.len(),
        kinds
            .iter()
            .map(|(k, n)| format!("  {n:4}  {k}"))
            .collect::<Vec<_>>()
            .join("\n"),
        first(&disagree),
        first(&refused),
    );
    assert_eq!(fast, rows.len(), "a residual did not lower");
    // Measured: 1212 of 2000. The floor keeps column 3 a real population.
    assert!(
        by_field * 2 >= rows.len(),
        "column 3 ran on only {by_field} of {} rows",
        rows.len()
    );
}

#[test]
fn the_generator_is_not_vacuous() {
    let rows = rows();
    let n = rows.len() as f64;
    let share =
        |pred: &dyn Fn(&Row) -> bool| rows.iter().filter(|(_, r)| pred(r)).count() as f64 / n;

    let ok_true = share(&|r| r.c1 == Ok(true));
    let ok_false = share(&|r| r.c1 == Ok(false));
    let err = share(&|r| r.c1.is_err());
    let folded = share(&|r| r.residual_source() != r.original_rendered);
    let constant = share(&|r| matches!(r.residual_source(), "true" | "false"));
    let unrolled = share(&|r| r.residual.is_ok() && r.residual_loops < r.original_loops);
    let loops = share(&|r| r.original_loops > 0);
    let all_known = share(&|r| r.completion.is_empty());

    println!(
        "mix population over {} rows:\n  column 1 Ok(true)  {:5.1}%\n  column 1 Ok(false) {:5.1}%\n  column 1 Err       {:5.1}%\n  residual differs from the original      {:5.1}%\n  residual is a bare constant            {:5.1}%\n  fewer comprehensions (an unroll)       {:5.1}%\n  original has a comprehension           {:5.1}%\n  every root known                       {:5.1}%",
        rows.len(),
        ok_true * 100.0,
        ok_false * 100.0,
        err * 100.0,
        folded * 100.0,
        constant * 100.0,
        unrolled * 100.0,
        loops * 100.0,
        all_known * 100.0,
    );

    assert!(
        ok_true >= 0.10,
        "column 1 is Ok(true) in only {:.1}%",
        ok_true * 100.0
    );
    assert!(
        ok_false >= 0.10,
        "column 1 is Ok(false) in only {:.1}%",
        ok_false * 100.0
    );
    assert!(err >= 0.05, "column 1 is Err in only {:.1}%", err * 100.0);
    assert!(
        folded >= 0.30,
        "the residual differs from the original in only {:.1}%",
        folded * 100.0
    );
    assert!(
        constant >= 0.05,
        "the residual is a bare constant in only {:.1}%",
        constant * 100.0
    );
    assert!(
        unrolled >= 0.05,
        "an unroll happened in only {:.1}%",
        unrolled * 100.0
    );
}

// ---- the worked examples of `tests/specialize_api.rs`, as rows ----

fn api_env() -> CelEnvironment {
    let mut e = CelEnvironment::with_limits(CelLimits::default());
    e.declare(
        "policy",
        record(
            "policy",
            &[
                (
                    "fs",
                    record(
                        "policy.fs",
                        &[
                            ("open", CelTy::Bool),
                            ("root", CelTy::Str),
                            ("deny_roots", CelTy::list(CelTy::Str)),
                        ],
                    ),
                ),
                ("limit", CelTy::Num),
            ],
        ),
    );
    e.declare(
        "req",
        record(
            "req",
            &[
                ("path", CelTy::Str),
                ("size", CelTy::Num),
                ("flag", CelTy::Bool),
            ],
        ),
    );
    e
}

fn policy(open: bool) -> J {
    json!({"fs": {"open": open, "root": "/ws", "deny_roots": ["/etc", "/proc"]}, "limit": 7})
}

fn req(path: &str, size: f64) -> J {
    json!({"path": path, "size": size, "flag": false})
}

const DENY: &str =
    r#"policy.fs.deny_roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#;
const OPEN: &str = "policy.fs.open || req.path.startsWith(policy.fs.root)";
const LIMIT: &str = "req.size > policy.limit + 1.0";

/// Run one worked example through [`mix::row`], assert the property holds, and check the
/// hand-written residual and column-1 expectation on the same row.
fn worked(src: &str, p: J, r: J, residual: &str, want: Option<bool>) {
    let env = api_env();
    let label = format!("`{src}` with req = {r}");
    let row = mix::row(&env, src, vec![("policy", p)], vec![("req", r)]);
    assert!(row.holds() && row.guard_holds(), "{}", row.report(&label));
    assert_eq!(row.residual_source(), residual, "{label}");
    if let Some(want) = want {
        assert_eq!(row.c1, Ok(want), "{label}");
    }
}

#[test]
fn the_worked_examples_are_rows() {
    let deny = r#"((req.path == "/etc") || req.path.startsWith("/etc/")) || ((req.path == "/proc") || req.path.startsWith("/proc/"))"#;
    for (path, denied) in [
        ("/etc", true),
        ("/etc/passwd", true),
        ("/etcetera", false),
        ("/proc/1/mem", true),
        ("/home", false),
    ] {
        worked(DENY, policy(false), req(path, 1.0), deny, Some(denied));
    }

    for path in ["/ws/a", "/home"] {
        worked(OPEN, policy(true), req(path, 1.0), "true", Some(true));
        worked(
            OPEN,
            policy(false),
            req(path, 1.0),
            r#"req.path.startsWith("/ws")"#,
            Some(path.starts_with("/ws")),
        );
    }

    for (size, want) in [(7.5, false), (9.0, true)] {
        worked(
            LIMIT,
            policy(false),
            req("/x", size),
            "req.size > 8",
            Some(want),
        );
    }
}
