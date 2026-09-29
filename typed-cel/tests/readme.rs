//! `README.md` is a contract, so it is checked like one.
//!
//! Three documents state the same dialect — `README.md`, `conformance/EXCLUSIONS.toml` and
//! `tests/dialect.rs` — and the normal failure is that two of them agree while the third drifts.
//! Nobody notices, because the two that agree are the two anyone re-reads. So each is held to the
//! others mechanically rather than reviewed by eye:
//!
//! ```text
//!   README removal row   ->  a rejection test in tests/dialect.rs   (every_removal_row_has_a_rejection_test)
//!   README addition row  ->  a public item in src/                  (every_addition_row_has_public_api)
//!   README numbers       ->  a live corpus run                      (the_conformance_summary_is_current)
//!   no README bug table  ->  no failing corpus section              (every_failing_section_is_a_known_bug)
//!   EXCLUSIONS reason    ->  a README dialect row                   (every_exclusion_reason_appears_here)
//! ```
//!
//! The last one is also checked from the harness side, in `tests/conformance.rs`, through the
//! PARSED exclusion rules. Here it is checked from the document side, over the file's text. The
//! duplication is deliberate and cheap: a change that fools one reader — a reason spelled into a
//! comment, a table cell that stops being a table cell — has to fool a different reader as well.

#[path = "../conformance/harness/mod.rs"]
mod harness;

use std::collections::BTreeSet;
use std::path::PathBuf;

use harness::conformance_dir;
use harness::exclusions::Exclusions;
use harness::gen;

fn crate_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn readme() -> String {
    std::fs::read_to_string(crate_dir().join("README.md")).expect("README.md")
}

/// The cells of one markdown table row, trimmed. `None` for anything that is not a row, including
/// the `|---|---|` separator.
fn row_cells(line: &str) -> Option<Vec<&str>> {
    let line = line.trim();
    let inner = line.strip_prefix('|')?.strip_suffix('|')?;
    if inner.chars().all(|c| matches!(c, '-' | ':' | '|' | ' ')) {
        return None;
    }
    Some(inner.split('|').map(str::trim).collect())
}

/// Rows of the table under `heading`, up to the next heading of any level.
///
/// Scoped to a section on purpose: "the rows whose first cell starts with `removed:`" would keep
/// working if the Removed table were deleted and its rows moved somewhere else entirely, which is
/// exactly the drift these tests exist to see.
fn rows_under(readme: &str, heading: &str) -> Vec<Vec<String>> {
    let mut out = Vec::new();
    let mut inside = false;
    for line in readme.lines() {
        if line.starts_with('#') {
            inside = line.trim_end() == heading;
            continue;
        }
        if inside {
            if let Some(cells) = row_cells(line) {
                if cells
                    .first()
                    .is_some_and(|c| c.starts_with("| id") || *c == "id")
                {
                    continue; // the header row
                }
                out.push(cells.into_iter().map(str::to_string).collect());
            }
        }
    }
    out
}

/// The backtick-quoted spans in a table cell, in order.
fn backticked(cell: &str) -> Vec<String> {
    cell.split('`')
        .skip(1)
        .step_by(2)
        .map(str::to_string)
        .collect()
}

/// Every source file the crate ships, concatenated. Used to ask whether a name is declared public.
fn all_src() -> String {
    fn walk(dir: &std::path::Path, out: &mut String) {
        for entry in std::fs::read_dir(dir).expect("readable").flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(&path, out);
            } else if path.extension().is_some_and(|e| e == "rs") {
                out.push_str(&std::fs::read_to_string(&path).expect("readable"));
                out.push('\n');
            }
        }
    }
    let mut out = String::new();
    walk(&crate_dir().join("src"), &mut out);
    out
}

/// Is `name` declared — or re-exported — as public anywhere in `src/`?
///
/// A textual scan rather than a compile-time reference, because the point is to catch a README row
/// naming an item that does NOT exist: a test that named it in code would fail to compile, which
/// reports the gap as a broken test target rather than as a failing assertion with a list.
fn is_public_item(src: &str, name: &str) -> bool {
    // `A::b` — both halves have to be there. A method on a type that was renamed is exactly as
    // wrong as a missing method.
    if let Some((ty, member)) = name.split_once("::") {
        return is_public_item(src, ty)
            && (is_public_item(src, member) || is_enum_variant(src, ty, member));
    }
    const KINDS: &[&str] = &[
        "struct", "enum", "trait", "type", "fn", "const", "static", "mod", "union",
    ];
    for kind in KINDS {
        let decl = format!("pub {kind} {name}");
        if src.match_indices(&decl).any(|(i, _)| {
            !src[i + decl.len()..].starts_with(|c: char| c.is_alphanumeric() || c == '_')
        }) {
            return true;
        }
    }
    // A re-export counts: `pub use ser::Duration;` makes the name part of the public surface just
    // as much as a declaration does.
    src.lines()
        .map(str::trim)
        .filter(|l| l.starts_with("pub use "))
        .any(|l| {
            l.split(|c: char| !(c.is_alphanumeric() || c == '_'))
                .any(|word| word == name)
        })
}

/// `variant` is declared inside the body of `pub enum ty` — a variant is public exactly when its
/// enum is. Reads each line of the body up to the enum's closing `}` at column zero.
fn is_enum_variant(src: &str, ty: &str, variant: &str) -> bool {
    let decl = format!("pub enum {ty} {{");
    src.match_indices(&decl).any(|(i, _)| {
        src[i + decl.len()..]
            .lines()
            .take_while(|l| !l.starts_with('}'))
            .map(str::trim)
            .any(|l| {
                l.strip_prefix(variant)
                    .is_some_and(|rest| rest.is_empty() || rest.starts_with([' ', '{', '(', ',']))
            })
    })
}

/// Every "Removed" row names a test in `tests/dialect.rs` that asserts the rejection.
///
/// A removal with no test is a claim about the language rather than a property of it. The failure
/// it hides is specific: the construct keeps working, nobody notices, and a policy gets written
/// against something this table says is gone.
#[test]
fn every_removal_row_has_a_rejection_test() {
    let readme = readme();
    let rows = rows_under(&readme, "### Removed");
    assert!(
        rows.len() >= 7,
        "only {} rows found under `### Removed` — the table format changed and this test is now \
         checking nothing",
        rows.len()
    );

    let dialect = include_str!("dialect.rs");
    let mut missing = Vec::new();
    for row in &rows {
        let id = backticked(&row[0]).first().cloned().unwrap_or_default();
        let named = backticked(row.get(2).map(String::as_str).unwrap_or(""));
        match named.first() {
            None => missing.push(format!("  [{id}] names no rejection test")),
            Some(test) => {
                if !dialect.contains(&format!("fn {test}(")) {
                    missing.push(format!(
                        "  [{id}] names `{test}`, which tests/dialect.rs has not"
                    ));
                }
            }
        }
    }
    assert!(
        missing.is_empty(),
        "removal rows without a rejection test:\n{}",
        missing.join("\n")
    );
}

/// Every "Added" row names a public item that exists.
///
/// This is the table that says why this is a crate and not a vendored copy, and it is the one a
/// reader will take on trust — an addition is not visible in the corpus numbers the way a removal
/// is, so nothing else measures it.
///
/// It is RED until the last addition lands, and that is the intent: each row is the contract for
/// one change, written down once rather than re-derived, and the test names precisely which items
/// are still owed.
#[test]
fn every_addition_row_has_public_api() {
    let readme = readme();
    let rows = rows_under(&readme, "### Added");
    assert!(
        rows.len() >= 5,
        "only {} rows found under `### Added` — the table format changed and this test is now \
         checking nothing",
        rows.len()
    );

    let src = all_src();
    let mut missing = Vec::new();
    for row in &rows {
        let id = backticked(&row[0]).first().cloned().unwrap_or_default();
        let items = backticked(row.get(2).map(String::as_str).unwrap_or(""));
        assert!(
            !items.is_empty(),
            "[{id}] names no public item at all — a row nothing can be checked against"
        );
        for item in items {
            if !is_public_item(&src, &item) {
                missing.push(format!("  [{id}] `{item}`"));
            }
        }
    }
    assert!(
        missing.is_empty(),
        "README addition rows naming public items that do not exist yet:\n{}\n\
         Each is one change's contract. When that change lands, this shrinks.",
        missing.join("\n")
    );
}

/// The README's compatibility block matches a live corpus run.
///
/// A hand-maintained compatibility table is a lie with a timestamp, and the README is the document
/// people actually read — so its numbers are generated, committed, and re-derived here. The check
/// is that splicing a fresh block in is the IDENTITY on the committed file, which is "regenerate
/// and diff" without a temporary file.
#[test]
fn the_conformance_summary_is_current() {
    let readme = readme();
    let exclusions =
        Exclusions::load(&conformance_dir().join("EXCLUSIONS.toml")).expect("EXCLUSIONS.toml");
    let live = gen::readme_with_summary(&readme, &exclusions).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(
        live, readme,
        "README.md's conformance summary is stale. Regenerate: cargo run -p typed-cel --features \
         conformance --bin conformance-report -- --write"
    );
}

/// The corpus has NO failing sections, and a new one cannot be written off as already known.
///
/// This test used to hold a `### Known bugs` table in `README.md` to the live failing set, in both
/// directions. That table is gone, because the board reached zero and a section headed "Known
/// bugs" over an empty table reports the opposite of the truth to anyone scanning headings.
///
/// The test survives the table because it never depended on it being non-empty. `rows_under`
/// finds nothing, `documented` is the empty set, and the partition then says exactly one thing:
/// **the corpus must have no failures.** A case that starts failing lands in `undocumented` and
/// this goes red naming it.
///
/// A FAIL is a bug this crate could FIX, as opposed to a construct the dialect declined — which is
/// why it may not quietly become an exclusion. If a future bug is genuinely not worth fixing yet,
/// the honest move is to bring the table back with a row for it AND leave the case failing, not to
/// move it into `EXCLUSIONS.toml`; `exclusions_cite_the_readme` is the other half of that.
#[test]
fn every_failing_section_is_a_known_bug() {
    let readme = readme();
    let documented: BTreeSet<String> = rows_under(&readme, "### Known bugs")
        .iter()
        .flat_map(|row| backticked(row.get(1).map(String::as_str).unwrap_or("")))
        .collect();
    // No row-count floor. The table this reads reached zero and was deleted, so a floor would be
    // asserting the presence of bugs — and while the table existed it would have had to be lowered
    // every time one was fixed, which is a guard edited to stay green. The partition below is the
    // test.

    let exclusions =
        Exclusions::load(&conformance_dir().join("EXCLUSIONS.toml")).expect("EXCLUSIONS.toml");
    let failing: BTreeSet<String> = harness::corpus()
        .cases()
        .filter(|c| {
            matches!(
                gen::outcome_of(c, &exclusions),
                gen::Reported::Ran(harness::run::Outcome::Fail(_))
            )
        })
        .map(|c| format!("{}/{}", c.file, c.section))
        .collect();

    let undocumented: Vec<&String> = failing.difference(&documented).collect();
    let stale: Vec<&String> = documented.difference(&failing).collect();
    assert!(
        undocumented.is_empty() && stale.is_empty(),
        "the Known bugs table and the corpus disagree.\n  \
         failing but undocumented: {undocumented:?}\n  \
         documented but no longer failing: {stale:?}"
    );
}

/// Every reason in `EXCLUSIONS.toml` is a dialect-row id in this README.
///
/// Read from the TOML's text rather than from the parsed rules, so a reason that is present in the
/// file but invisible to the reader — commented out, sitting in a key nothing deserializes — is
/// still held to the README. EXCLUDED is the outcome a tired person reaches for to make a red go
/// away, and this is half of what stops that: excluding a case means editing the document that
/// defines the language.
#[test]
fn every_exclusion_reason_appears_here() {
    let toml = std::fs::read_to_string(conformance_dir().join("EXCLUSIONS.toml"))
        .expect("EXCLUSIONS.toml");
    let reasons: BTreeSet<String> = toml
        .lines()
        .map(str::trim)
        .filter_map(|l| l.strip_prefix("reason"))
        .filter_map(|rest| rest.trim_start().strip_prefix('='))
        .filter_map(|rest| backticked(&rest.replace('"', "`")).into_iter().next())
        .collect();
    assert!(
        reasons.len() >= 8,
        "only {} reasons read out of EXCLUSIONS.toml — the file format changed and this test is \
         now checking nothing",
        reasons.len()
    );

    let readme = readme();
    let ids: BTreeSet<String> = readme
        .lines()
        .filter_map(|l| l.trim().strip_prefix("| `"))
        .filter_map(|rest| rest.split('`').next())
        .map(str::to_string)
        .collect();

    let orphans: Vec<&String> = reasons.iter().filter(|r| !ids.contains(*r)).collect();
    assert!(
        orphans.is_empty(),
        "exclusion reasons that name no README dialect row: {orphans:?}"
    );
}

/// The text between two markers, which must each appear exactly once.
fn block<'t>(text: &'t str, begin: &str, end: &str, whence: &str) -> &'t str {
    assert_eq!(text.matches(begin).count(), 1, "{whence}: `{begin}` once");
    assert_eq!(text.matches(end).count(), 1, "{whence}: `{end}` once");
    let a = text.find(begin).expect("begin") + begin.len();
    let b = text.find(end).expect("end");
    assert!(a <= b, "{whence}: `{end}` before `{begin}`");
    &text[a..b]
}

fn performance() -> String {
    std::fs::read_to_string(crate_dir().join("docs/PERFORMANCE.md")).expect("docs/PERFORMANCE.md")
}

/// The README's ablation block is the measured one, byte for byte.
#[test]
fn the_ablation_block_is_the_measured_one() {
    let (readme, perf) = (readme(), performance());
    let begin = "<!-- ablation:begin -->";
    let end = "<!-- ablation:end -->";
    assert_eq!(
        block(&readme, begin, end, "README.md"),
        block(&perf, begin, end, "docs/PERFORMANCE.md"),
        "the README's ablation block drifted from docs/PERFORMANCE.md"
    );
}

/// Every workload the ablation runs is a row of "Time and allocations", and every row is one it
/// runs.
#[test]
fn every_ablation_workload_is_documented() {
    let bench = std::fs::read_to_string(crate_dir().join("ablation/benches/ablation.rs"))
        .expect("the ablation bench");
    let begin = "const WORKLOADS: &[&str] = &[";
    let start = bench.find(begin).expect("`const WORKLOADS` in the bench") + begin.len();
    let list = &bench[start..start + bench[start..].find("];").expect("the list's end")];
    let workloads: Vec<String> = list
        .split('"')
        .skip(1)
        .step_by(2)
        .map(str::to_string)
        .collect();
    assert!(workloads.len() >= 10, "only {} workloads", workloads.len());
    let perf = performance();
    let table = perf
        .split("### Time and allocations")
        .nth(1)
        .expect("a `### Time and allocations` table");
    let rows: Vec<String> = table
        .lines()
        .skip_while(|l| !l.starts_with('|'))
        .take_while(|l| l.starts_with('|'))
        .filter_map(row_cells)
        .map(|cells| cells[0].trim_matches('`').to_string())
        .filter(|c| c != "workload" && !c.starts_with("---"))
        .collect();
    for w in &workloads {
        assert!(rows.contains(w), "`{w}` has no row in docs/PERFORMANCE.md");
    }
    for r in &rows {
        assert!(
            workloads.contains(r),
            "row `{r}` is not a workload the bench runs"
        );
    }
}

/// The README describes one engine. The one historical paragraph is exempt.
#[test]
fn the_readme_names_no_second_engine() {
    let readme = readme();
    let historical = block(
        &readme,
        "<!-- historical:begin -->",
        "<!-- historical:end -->",
        "README.md",
    );
    let rest = readme.replacen(historical, "", 1);
    let mut leaks = Vec::new();
    for phrase in [
        "tree evaluator",
        "absorbed evaluator",
        "both engines",
        "both runtimes",
        "executable specification",
    ] {
        for line in rest.lines() {
            if line.to_lowercase().contains(phrase) {
                leaks.push(format!("`{phrase}`: {line}"));
            }
        }
    }
    assert!(leaks.is_empty(), "{}", leaks.join("\n"));
}

/// The rule is a language decision, and `README.md` is where this crate states those. Implementing
/// the predicate (`CelTy::requires_narrowing`) without the row leaves it undiscoverable, and the next reader reimplements `any`
/// semantics in the checker because that is what spec CEL does.
#[test]
fn the_dialect_doc_records_the_divergence() {
    let doc = readme();
    assert!(
        doc.contains("`diverges: dyn must be narrowed`"),
        "the Divergences table has no row for the narrowing rule"
    );
    assert!(
        doc.contains("#### `dyn` must be narrowed"),
        "the operator table the checker lifts its rules from is missing"
    );
    // The checker's own tests are specified in the plan and lifted verbatim there; what has to be
    // true HERE is that the rule and its cost are written down where an author will find them.
    for phrase in [
        "No such overload",
        "the result must be `bool`",
        "BUILD ERROR",
    ] {
        assert!(
            doc.contains(phrase),
            "the narrowing block does not say {phrase:?}"
        );
    }
}
