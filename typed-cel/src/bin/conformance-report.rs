//! The conformance report, and the generator for the per-case tests.
//!
//! ```text
//! cargo run -p typed-cel --features conformance --bin conformance-report
//! cargo run -p typed-cel --features conformance --bin conformance-report -- --write
//! cargo run -p typed-cel --features conformance --bin conformance-report -- --failures [file]
//! cargo run -p typed-cel --features conformance --bin conformance-report -- --sections
//! cargo run -p typed-cel --features conformance --bin conformance-report -- --list <file>
//! ```
//!
//! Without `--write` it prints the table and exits. With `--write` it regenerates
//! `conformance/{report.md, gen/cases.rs, baseline.toml}`, all three of which are checked in — a
//! hand-maintained compatibility table is a lie with a timestamp, so the table is generated,
//! committed, and held to the code by `the_conformance_table_is_current`.
//!
//! The generation itself lives in `conformance/harness/gen.rs`, so the tests run the same code
//! this bin does. This file is argument parsing and the triage views.

#[path = "../../conformance/harness/mod.rs"]
mod harness;

use std::collections::BTreeMap;

use harness::exclusions::Exclusions;
use harness::gen::{self, Reported};
use harness::run::Outcome;
use harness::{conformance_dir, corpus};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let exclusions = Exclusions::load(&conformance_dir().join("EXCLUSIONS.toml"))
        .unwrap_or_else(|e| panic!("{e}"));

    // `--failures [file-stem]` — every non-excluded case that failed, with why. Triage input for
    // deciding whether a red is a bug to fix or a construct to exclude.
    if let Some(i) = args.iter().position(|a| a == "--failures") {
        let only = args.get(i + 1).filter(|a| !a.starts_with("--"));
        for case in corpus().cases() {
            if only.is_some_and(|f| f != &case.file) {
                continue;
            }
            if let Reported::Ran(Outcome::Refused(why) | Outcome::Fail(why)) =
                gen::outcome_of(case, &exclusions)
            {
                // One line per failure, always: corpus expressions contain literal newlines and
                // tabs (`parse/whitespace`), and an unescaped dump silently turns one failure
                // into several rows that a `sort | uniq -c` then miscounts.
                println!(
                    "{}\t{}\t{}",
                    case.unique_id(),
                    case.expr.escape_debug(),
                    why.escape_debug()
                );
            }
        }
        return;
    }

    // `--sections` — total/pass/fail per file+section. What decides whether an exclusion belongs
    // at section level (the whole section is about the construct) or case level (it is not).
    if args.iter().any(|a| a == "--sections") {
        let mut acc: BTreeMap<(&str, &str), (usize, usize, usize)> = BTreeMap::new();
        for case in corpus().cases() {
            let e = acc
                .entry((case.file.as_str(), case.section.as_str()))
                .or_default();
            e.0 += 1;
            match gen::outcome_of(case, &exclusions) {
                Reported::Excluded(_) => e.2 += 1,
                Reported::Ran(Outcome::Pass | Outcome::PassStatic(_)) => e.1 += 1,
                Reported::Ran(Outcome::Refused(_) | Outcome::Fail(_)) => {}
            }
        }
        for ((file, section), (total, pass, excluded)) in acc {
            let fail = total - pass - excluded;
            if fail > 0 {
                println!(
                    "{file}/{section}\ttotal={total}\tpass={pass}\tfail={fail}\texcluded={excluded}"
                );
            }
        }
        return;
    }

    // `--list <file-stem>` — every case in a file, one escaped line each. Used when writing an
    // exclusion by hand, to name cases from the corpus rather than from memory.
    if let Some(i) = args.iter().position(|a| a == "--list") {
        let only = args.get(i + 1).cloned().unwrap_or_default();
        for case in corpus().cases().filter(|c| c.file == only) {
            println!(
                "{}\t{}\t{}",
                case.section,
                case.name,
                case.expr.escape_debug()
            );
        }
        return;
    }

    let report = gen::report(&exclusions);
    print!("{report}");

    if args.iter().any(|a| a == "--write") {
        let dir = conformance_dir();
        std::fs::create_dir_all(dir.join("gen")).expect("conformance/gen");
        std::fs::write(dir.join("gen/cases.rs"), gen::cases_rs(&exclusions)).expect("gen/cases.rs");
        std::fs::write(dir.join("report.md"), &report).expect("report.md");
        std::fs::write(dir.join("baseline.toml"), gen::baseline_toml(&exclusions))
            .expect("baseline.toml");

        // The README's compatibility block, spliced in place. A hand-maintained compatibility
        // table is a lie with a timestamp, and the README is the document people actually read —
        // so it gets the same treatment as report.md rather than a pointer and a promise.
        let readme_path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("README.md");
        let readme = std::fs::read_to_string(&readme_path).expect("README.md");
        let spliced =
            gen::readme_with_summary(&readme, &exclusions).unwrap_or_else(|e| panic!("{e}"));
        std::fs::write(&readme_path, spliced).expect("README.md");

        eprintln!("wrote conformance/{{gen/cases.rs, report.md, baseline.toml}} and README.md");
    }
}
