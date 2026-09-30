//! ONE `compile`: a source (text or a kept `Parsed`) and
//! `CompileOpts` (the required result type, and the values known now). Checking always happens
//! inside it, with the known values in view.

#[path = "support/mod.rs"]
mod support;

use typed_cel::{CelEnvironment, CelError, CelLimits, CelTy, CompileOpts, Record};
use serde_json::json;
use support::gen;
use support::known::fold_text;

fn fold_env() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.declare("k", CelTy::Num);
    env.declare("t", CelTy::Bool);
    env.declare("f", CelTy::Bool);
    env.declare(
        "p",
        Record::new(
            "p",
            [(
                "fs",
                CelTy::from(Record::new(
                    "fs",
                    [("root", CelTy::Str), ("names", CelTy::list(CelTy::Str))],
                )),
            )],
        ),
    );
    env.declare(
        "u",
        Record::new(
            "u",
            [("a", CelTy::Num), ("b", CelTy::Bool), ("s", CelTy::Str)],
        ),
    );
    env
}

/// The residual that specializing produced is what compiling with the same values known produces.
/// A representative slice of the literal residuals `tests/specialize_fold.rs`,
/// `specialize_unroll.rs` and `specialize_api.rs` pin — those suites run through this same
/// `compile` now, so every literal they assert is part of this claim.
#[test]
fn compiling_with_known_values_is_what_specializing_was() {
    let env = fold_env();
    let known = [
        ("k", json!(10.0)),
        ("t", json!(true)),
        ("f", json!(false)),
        ("p", json!({"fs": {"root": "/ws", "names": ["a", "b"]}})),
    ];
    for (src, want) in [
        ("u.b && f", "false"),
        ("f && u.b", "false"),
        ("u.b || t", "true"),
        ("(u.a > 1) && t", "u.a > 1"),
        ("u.b && (p.fs.root == \"/x\")", "false"),
        ("u.a < k", "u.a < 10"),
        (
            "p.fs.names.exists(n, u.s == n)",
            "(u.s == \"a\") || (u.s == \"b\")",
        ),
    ] {
        assert_eq!(fold_text(&env, &known, src), want, "`{src}`");
    }
}

/// Holding a `Parsed` and compiling it is compiling its text: the same residual source, the same
/// demand, the same answers — over the whole typed generator batch.
#[test]
fn a_parsed_source_compiles_like_its_text() {
    let env = gen::roster();
    let mut compared = 0;
    for (src, acts) in gen::typed_batch(7) {
        let parsed = env
            .parse(&src)
            .unwrap_or_else(|e| panic!("`{src}` parses: {e}"));
        assert_eq!(parsed.source(), src);
        let from_text = env.compile(&src, &CompileOpts::default());
        let from_parsed = env.compile(&parsed, &CompileOpts::default());
        let (a, b) = match (from_text, from_parsed) {
            (Ok(a), Ok(b)) => (a, b),
            (Err(a), Err(b)) => {
                assert_eq!(a.to_string(), b.to_string(), "`{src}`");
                continue;
            }
            (a, b) => panic!("`{src}`: text {a:?}, parsed {b:?}"),
        };
        assert_eq!(a.source(), b.source());
        assert_eq!(format!("{:?}", a.demand()), format!("{:?}", b.demand()));
        for binds in acts {
            let mut act = env.activation();
            for (name, v) in &binds {
                act.bind(name, v).expect("binds");
            }
            assert_eq!(
                format!("{:?}", a.evaluate(&act)),
                format!("{:?}", b.evaluate(&act)),
                "`{src}` over {binds:?}"
            );
        }
        compared += 1;
    }
    assert!(compared > 900, "only {compared} programs compiled");
}

/// Everything after the fold still runs inside `compile`: the residual's cost is re-bounded, and a
/// fold that cannot lower is refused as a specialization failure — not skipped because the
/// original checked.
#[test]
fn the_residual_is_rechecked() {
    let mut env = CelEnvironment::with_limits(CelLimits {
        max_cost: 1_000,
        ..CelLimits::default()
    });
    env.declare(
        "policy",
        Record::new("policy", [("roots", CelTy::list(CelTy::Str))]),
    );
    env.declare("req", Record::new("req", [("path", CelTy::Str)]));
    let src = "policy.roots.exists(r, req.path == r)";
    env.compile(src, &CompileOpts::default())
        .expect("the original is under the cost bound");
    let roots: Vec<String> = (0..256).map(|i| format!("/r{i}")).collect();
    let mut known = env.activation();
    known.bind("policy", &json!({ "roots": roots })).unwrap();
    let opts = CompileOpts {
        known: Some(&known),
        ..Default::default()
    };
    match env.compile(src, &opts) {
        Err(CelError::Bounds { message, .. }) => {
            assert!(message.starts_with("the specialized form"), "{message}")
        }
        other => panic!("want the residual's cost refused, got {other:?}"),
    }
    let mut small = env.activation();
    small.bind("policy", &json!({ "roots": ["/a"] })).unwrap();
    let opts = CompileOpts {
        known: Some(&small),
        ..Default::default()
    };
    match typed_cel::fork::compile_with_lowering_refused(&env, src, &opts) {
        Err(CelError::Specialize { source, .. }) => assert_eq!(&*source, src),
        other => panic!("want a Specialize refusal, got {other:?}"),
    }
}

#[test]
fn parsed_roots_are_syntactic() {
    let env = CelEnvironment::new();
    let roots = |src: &str| {
        env.parse(src)
            .unwrap_or_else(|e| panic!("{e}"))
            .roots()
            .into_iter()
            .collect::<Vec<_>>()
    };
    // Nothing is declared: `parse` checks nothing, so an undeclared root is still a root.
    assert_eq!(
        roots("policy.a > 1 && xs.all(policy, policy > 0)"),
        ["policy", "xs"]
    );
    assert_eq!(roots("xs.all(p, p > 0)"), ["xs"]);
    assert_eq!(roots("xs.map(p, p.q).exists(q, q == r)"), ["r", "xs"]);
    assert_eq!(roots("has(body.a) && 1s < uptime"), ["body", "uptime"]);
}

/// There is one public compile. A second entry point is a second place a check can be skipped.
#[test]
fn the_one_compile_is_the_only_compile() {
    let lib = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/lib.rs"))
        .expect("reads lib.rs");
    let code = support::code_only(&lib);
    assert!(
        !code.contains("fn compile_returning"),
        "compile_returning is back"
    );
    assert!(
        !code.contains("pub fn specialize("),
        "a public specialize is back"
    );
    assert_eq!(
        code.matches("pub fn compile<").count() + code.matches("pub fn compile(").count(),
        1,
        "exactly one `pub fn compile`"
    );
}
