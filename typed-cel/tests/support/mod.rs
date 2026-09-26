//! One environment, shared by the checker's test files.
//!
//! Deliberately hand-built rather than derived from a schema: these tests are about the CHECKER.

#![allow(dead_code)]

use typed_cel::fork;
use typed_cel::{CelEnvironment, CelError, CelTy, CelValue, ExecutionError, FastProgram, Record};

/// Comparing the VM with the evaluator (and generating what to
/// compare them on).
pub mod gen;

/// The specializer fold's tests: specialize a checked program and render the residual.
pub mod known;

/// Owned stream events and a fragmenting tokenizer, for governed values and streamed runs.
pub mod events;

/// The mix equation's typed roster, case generator and three-column row.
pub mod mix;

/// A record with no optional fields and no index signature.
pub fn record(origin: &str, fields: &[(&str, CelTy)]) -> CelTy {
    Record::new(origin, fields.iter().map(|(n, t)| (*n, t.clone()))).into()
}

/// A record with some fields declared optional (`{"a?": "string"}`).
pub fn record_opt(origin: &str, fields: &[(&str, CelTy)], optional: &[&str]) -> CelTy {
    Record::new(origin, fields.iter().map(|(n, t)| (*n, t.clone())))
        .with_optional(optional.iter().copied())
        .into()
}

/// `Record{ elapsed: Duration, count: Num }` — the system environment's one event shape.
pub fn event() -> CelTy {
    record(
        "event",
        &[("elapsed", CelTy::Duration), ("count", CelTy::Num)],
    )
}

fn doc() -> CelTy {
    record("document", &[("id", CelTy::Str), ("owner_id", CelTy::Str)])
}

/// The roster both test files check against. Wide on purpose: one environment serving many
/// expressions is the shape the policy compiler uses, and building a fresh one per assertion would
/// hide a leak between them.
pub fn env() -> CelEnvironment {
    let mut e = CelEnvironment::new();
    e.declare(
        "body",
        record(
            "body",
            &[
                ("user_id", CelTy::Str),
                ("owner_id", CelTy::Str),
                ("tenant_id", CelTy::Str),
                ("amount", CelTy::Num),
                ("name", CelTy::Str),
                ("note", CelTy::Str),
                ("email", CelTy::Str),
                ("id", CelTy::Str),
                ("items", CelTy::list(doc())),
                ("documents", CelTy::list(doc())),
                ("tags", CelTy::list(CelTy::Str)),
                (
                    "project",
                    record(
                        "body.project",
                        &[("owner", record("body.project.owner", &[("id", CelTy::Str)]))],
                    ),
                ),
                // A schema that declared `unknown`. `Dyn` is unknown, NOT any.
                ("blob", CelTy::Dyn),
                // An OPEN object derives `map(string, dyn)` — not a `Dyn`. The VALUE is what
                // requires narrowing, so `body.open['k']` compiles.
                ("open", CelTy::map(CelTy::Str, CelTy::Dyn)),
            ],
        ),
    );
    e.declare(
        "session",
        record(
            "session",
            &[
                ("user_id", CelTy::Str),
                ("tenant_id", CelTy::Str),
                ("roles", CelTy::list(CelTy::Str)),
                ("allowed_ids", CelTy::list(CelTy::Str)),
            ],
        ),
    );
    e.declare("context", record("context", &[("risk_score", CelTy::Num)]));
    // Reached by INDEX only: backtick quoting is a known bug, and typing headers as a map to make
    // `headers['content-type']` resolve would discard unknown-key detection for exactly the
    // variables an attacker most influences.
    e.declare(
        "headers",
        record_opt(
            "headers",
            &[("content-type", CelTy::Str), ("x-request-id", CelTy::Str)],
            &["x-request-id"],
        ),
    );
    e.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    e.declare("a", CelTy::list(doc()));
    e.declare("b", CelTy::list(doc()));
    e.declare("c", CelTy::list(doc()));

    // The system half.
    e.declare("uptime", CelTy::Duration);
    e.declare(
        "signals",
        record("signals", &[("ready", event()), ("stopping", event())]),
    );
    e.declare(
        "listeners",
        CelTy::map(
            CelTy::Str,
            record("listener", &[("listen", event()), ("accept", event())]),
        ),
    );
    e.declare(
        "files",
        CelTy::map(
            CelTy::Str,
            record("file", &[("opened", event()), ("closed", event())]),
        ),
    );
    e.declare(
        "metrics",
        record(
            "metrics",
            &[
                (
                    "cpu",
                    record(
                        "metrics.cpu",
                        &[
                            ("now", CelTy::Num),
                            ("max", CelTy::map(CelTy::Str, CelTy::Num)),
                        ],
                    ),
                ),
                (
                    "rss",
                    record("metrics.rss", &[("now", CelTy::Num), ("changed", event())]),
                ),
                (
                    "fds",
                    record("metrics.fds", &[("now", CelTy::Num), ("changed", event())]),
                ),
            ],
        ),
    );
    e
}

/// Assert `expr` compiles against the shared environment.
pub fn ok(expr: &str) {
    if let Err(e) = env().compile(expr) {
        panic!("expected `{expr}` to check, got:\n{e}");
    }
}

/// Assert `expr` does NOT compile, and hand back the rendered diagnostic.
pub fn err(expr: &str) -> String {
    match env().compile(expr) {
        Ok(_) => panic!("expected `{expr}` to fail the checker, but it compiled"),
        Err(e) => e.to_string(),
    }
}

/// The structured error, for tests that inspect more than the rendering.
pub fn err_raw(expr: &str) -> CelError {
    match env().compile(expr) {
        Ok(_) => panic!("expected `{expr}` to fail the checker, but it compiled"),
        Err(e) => e,
    }
}

/// Assert every listed fragment appears in the rendered diagnostic.
pub fn err_mentions(expr: &str, fragments: &[&str]) -> String {
    let rendered = err(expr);
    for f in fragments {
        assert!(
            rendered.contains(f),
            "diagnostic for `{expr}` should mention {f:?}:\n{rendered}"
        );
    }
    rendered
}

/// Strip `//`-comments. STRING LITERALS ARE KEPT.
///
/// Keeping them is the whole difference between a gate and a decoration. The leak this crate
/// actually had was `if root == "metrics" && agg == "max"` — one environment's variable names, in
/// a general-purpose data structure, entirely inside string literals. A scanner that stripped
/// strings would have reported that file clean and this test would have been a decoration.
///
/// Comments go, because a doc comment explaining WHY a library file must not name a policy concept
/// necessarily names one, and scanning prose would force the explanation out of the code.
pub fn code_only(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for line in text.lines() {
        // Naive, and adequate: a `//` inside a string literal truncates the line early, which can
        // only ever make this scan MISS something, never invent a leak. There are none today.
        let line = match line.find("//") {
            Some(ix) => &line[..ix],
            None => line,
        };
        out.push_str(line);
        out.push('\n');
    }
    out
}

/// `src` on the backend over `binds`, checked against `env`, for a program the checker ADMITS. A refused program panics: it has no run-time
/// answer in this dialect, and a test that wanted one is a test of a construct the dialect deleted.
pub fn run(
    env: &CelEnvironment,
    src: &str,
    binds: &[(&str, CelValue)],
) -> Result<CelValue, ExecutionError> {
    let program =
        fork::compile_any(env, src).unwrap_or_else(|e| panic!("`{src}` does not check:\n{e}"));
    let code =
        FastProgram::new(&program).unwrap_or_else(|e| panic!("`{src}` does not lower:\n{e}"));
    let mut act = env.runtime().activation();
    for (name, v) in binds {
        act.bind_fact(name, v.clone());
    }
    fork::fast_value(&code, &act)
}

/// A closed program (no roots) on the backend.
pub fn run_closed(src: &str) -> Result<CelValue, ExecutionError> {
    run(&CelEnvironment::new(), src, &[])
}

/// The refusal of a closed program — by the parser or the checker, never for its result type
/// (`compile_any` admits every result). Panics when it compiles.
pub fn refused_closed(src: &str) -> CelError {
    match fork::compile_any(&CelEnvironment::new(), src) {
        Ok(_) => panic!("expected `{src}` to be refused, but it compiled"),
        Err(e) => e,
    }
}
