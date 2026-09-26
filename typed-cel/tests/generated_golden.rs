//! The frozen answers of the generated programs.
//!
//! The typed generator (`support::gen::typed_batch`) and the host-call generator
//! (`support::gen::host_batch`) produce thousands of (program, activation) runs, each with ONE known
//! answer — the answer the tree evaluator and the fast backend agreed on while both existed. This file
//! pins every one of them, so an answer can never silently move again.
//!
//! One line per run, no source text (the program regenerates from its seed, and the source is what
//! makes an error message differ between a program and its residual):
//!
//! ```text
//! <seed:#x> <index> <activation> ok true
//! <seed:#x> <index> <activation> err could not be evaluated: No such key: t
//! ```
//!
//! The `err` text is `CelError::Evaluation`'s `message` only, with `\` and newlines escaped. Rewrite the files ONLY on purpose:
//!
//! ```bash
//! cargo test -p typed-cel --test generated_golden --config 'env.CYNCH_CEL_WRITE_GOLDEN="1"'
//! ```

#[path = "support/mod.rs"]
mod support;

use std::path::Path;

use support::gen::{
    host_batch, host_roster, roster, typed_batch, Batch, ACTIVATIONS_PER_EXPRESSION, HOST_PER_SEED,
    SEEDS, TYPED_PER_SEED,
};
use typed_cel::{emit, CelEnvironment, CelError, Vm};

fn render(out: &Result<bool, CelError>) -> String {
    match out {
        Ok(b) => format!("ok {b}"),
        // A host error's text can span lines; one run is one line.
        Err(CelError::Evaluation { message, .. }) => {
            format!("err {}", message.replace('\\', "\\\\").replace('\n', "\\n"))
        }
        Err(other) => panic!("a generated program failed outside evaluation: {other}"),
    }
}

fn check_or_write(name: &str, lines: &[String]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/golden")
        .join(name);
    let text = lines.join("\n") + "\n";
    if std::env::var_os("CYNCH_CEL_WRITE_GOLDEN").is_some() {
        std::fs::create_dir_all(path.parent().unwrap()).expect("creates tests/golden");
        std::fs::write(&path, &text).expect("writes the golden");
        return;
    }
    let want = std::fs::read_to_string(&path)
        .expect("the golden exists: run with CYNCH_CEL_WRITE_GOLDEN=1");
    let mut diffs = Vec::new();
    for (i, (w, g)) in want.lines().zip(text.lines()).enumerate() {
        if w != g {
            diffs.push(format!(
                "line {}: golden `{w}`\n        now    `{g}`",
                i + 1
            ));
        }
    }
    assert_eq!(
        want.lines().count(),
        text.lines().count(),
        "{name}: row count moved"
    );
    assert!(
        diffs.is_empty(),
        "{name}: {} row(s) moved:\n{}",
        diffs.len(),
        diffs.join("\n")
    );
}

/// Every run of `batch(seed)` for every seed, through `run`, rendered one line each.
fn lines(
    env: &CelEnvironment,
    batch: fn(u64) -> Batch,
    run: &dyn Fn(&typed_cel::CelProgram, &typed_cel::CelActivation) -> Result<bool, CelError>,
) -> Vec<String> {
    let mut out = Vec::new();
    for seed in SEEDS {
        for (index, (src, acts)) in batch(seed).iter().enumerate() {
            let program = env
                .compile(src)
                .unwrap_or_else(|e| panic!("seed={seed:#x}, index={index}: `{src}`:\n{e}"));
            for (a, json) in acts.iter().enumerate() {
                let mut act = env.activation();
                for (name, v) in json {
                    act.bind(name, v).unwrap_or_else(|e| {
                        panic!("seed={seed:#x}, index={index}: binding {name}={v}: {e}")
                    });
                }
                out.push(format!(
                    "{seed:#x} {index} {a} {}",
                    render(&run(&program, &act))
                ));
            }
        }
    }
    out
}

fn on_the_backend(
    program: &typed_cel::CelProgram,
    act: &typed_cel::CelActivation,
) -> Result<bool, CelError> {
    Vm::new().eval(&emit(program).expect("emits"), act)
}

#[test]
fn the_typed_generator_answers_as_frozen() {
    check_or_write(
        "typed_generator.txt",
        &lines(&roster(), typed_batch, &on_the_backend),
    );
}

#[test]
fn the_host_generator_answers_as_frozen() {
    check_or_write(
        "host_generator.txt",
        &lines(&host_roster(), host_batch, &on_the_backend),
    );
}

/// A golden of all-`err` (or all one verdict) would pin nothing.
#[test]
fn the_golden_is_not_one_sided() {
    for (name, rows) in [
        ("typed_generator.txt", SEEDS.len() * TYPED_PER_SEED),
        ("host_generator.txt", SEEDS.len() * HOST_PER_SEED),
    ] {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/golden")
            .join(name);
        let text = std::fs::read_to_string(&path).expect("the golden exists");
        let total = text.lines().count();
        let count = |tail: &str| text.lines().filter(|l| l.contains(tail)).count();
        let (t, f, e) = (count(" ok true"), count(" ok false"), count(" err "));
        eprintln!("{name}: {total} rows — {t} ok true, {f} ok false, {e} err");
        assert_eq!(
            total,
            rows * ACTIVATIONS_PER_EXPRESSION,
            "{name}: row count"
        );
        assert_eq!(t + f + e, total, "{name}: every row is ok or err");
        assert!(
            t * 4 >= total,
            "{name}: only {t} of {total} rows are `ok true`"
        );
        assert!(
            f * 4 >= total,
            "{name}: only {f} of {total} rows are `ok false`"
        );
        assert!(
            e * 10 >= total,
            "{name}: only {e} of {total} rows are `err`"
        );
    }
}
