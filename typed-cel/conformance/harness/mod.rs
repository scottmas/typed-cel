//! The conformance harness: read google/cel-spec's corpus, run it against this crate, and report
//! three honest outcomes per case.
//!
//! Shared by `tests/conformance.rs` and `src/bin/conformance-report.rs` via `#[path]`, so the
//! report and the tests cannot disagree about what a case is or whether it passed. It is NOT part
//! of the crate's public API — the dialect does not ship a corpus reader.
//!
//! # The three outcomes
//!
//! ```text
//! PASS       the case runs and matches the expected value
//! EXCLUDED   the dialect does not implement this construct — REQUIRES a row in EXCLUSIONS.toml
//!            naming the case and a reason that cites a README dialect row
//! FAIL       neither of the above. A red test. There is no fourth state.
//! ```
//!
//! No test here passes BY panicking, on purpose — `no_should_panic_anywhere` greps these files
//! for the attribute, which is why this paragraph does not spell it. cel-rust's own harness reports
//! `2343 passed; 0 failed` while 1455 of those "pass" by panicking — a green board encoding 62%
//! failure. An EXCLUDED case does not become a test at all; it is accounted for in the report and
//! in the partition test, so it can never read as a pass.

// This module is `#[path]`-included by TWO targets — `tests/conformance.rs` and the
// `conformance-report` bin — and each uses a different subset of it. Without this, every item the
// other target uses is a dead-code warning in this one, and the real warnings drown.
#![allow(dead_code)]

pub mod case;
pub mod exclusions;
pub mod gen;
pub mod run;
pub mod textproto;

use std::path::PathBuf;

/// `typed-cel/conformance`.
pub fn conformance_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("conformance")
}

pub fn corpus_dir() -> PathBuf {
    conformance_dir().join("corpus")
}

/// The corpus, parsed once per process. 548K of textproto across 29 files is a few milliseconds
/// once and unaffordable per test.
pub fn corpus() -> &'static case::Corpus {
    static CORPUS: std::sync::OnceLock<case::Corpus> = std::sync::OnceLock::new();
    CORPUS.get_or_init(|| {
        case::Corpus::load(&corpus_dir()).unwrap_or_else(|e| panic!("loading the corpus: {e}"))
    })
}
