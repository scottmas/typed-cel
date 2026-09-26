//! google/cel-spec's conformance corpus, run against this crate with three honest outcomes.
//!
//! The generated per-case tests live in `conformance/gen/cases.rs` and are included below. The
//! tests in THIS file are the meta-tests: they hold the harness, the exclusion list and the README
//! to each other, so that no one of the three can drift while the other two agree.

#[path = "../conformance/harness/mod.rs"]
mod harness;
#[path = "support/mod.rs"]
mod support;

use harness::case::Case;
use harness::exclusions::Exclusions;
use harness::gen;
use harness::run::{self, Outcome};
use harness::{conformance_dir, corpus};

/// The generated per-case tests. Each one calls [`check`] below.
mod cases {
    include!("../conformance/gen/cases.rs");
}

fn exclusions() -> Exclusions {
    Exclusions::load(&conformance_dir().join("EXCLUSIONS.toml")).expect("EXCLUSIONS.toml")
}

/// Run one corpus case and assert it agreed. Called by every generated test.
///
/// The exclusion check is here as well as in the generator: a stale `gen/cases.rs` — an exclusion
/// added without regenerating — would otherwise keep running a case the dialect has declared it
/// does not implement, and report a bug that is not one.
fn check(file: &str, section: &str, name: &str, ordinal: usize) {
    let case = corpus()
        .cases()
        .find(|c| c.file == file && c.section == section && c.name == name && c.ordinal == ordinal)
        .unwrap_or_else(|| panic!("no such case: {file}/{section}/{name}#{ordinal}"));

    if let Some(reason) = exclusions().reason_for(case) {
        panic!(
            "{}: excluded as `{reason}`, but a generated test still runs it. \
             Regenerate: cargo run -p typed-cel --features conformance --bin \
             conformance-report -- --write",
            case.unique_id()
        );
    }

    match run::run(case) {
        Outcome::Pass | Outcome::PassStatic(_) => {}
        Outcome::Refused(why) => panic!(
            "{}\n  expr: {}\n  the checker refused it, and no exclusion names the dialect row: {why}",
            case.unique_id(),
            case.expr
        ),
        Outcome::Fail(why) => panic!("{}\n  expr: {}\n  {why}", case.unique_id(), case.expr),
    }
}

/// The parser reads every vendored file, and reads the RIGHT number of cases out of each.
///
/// This is the harness's own oracle. A textproto parser that silently drops a field, mis-handles
/// adjacent string concatenation or stops at the first `}` still produces a plausible-looking
/// corpus — just a smaller one — and every downstream number would then be measured against a
/// subset nobody noticed had shrunk. The per-file counts are google/cel-spec v0.25.1's, taken by
/// counting `test {` blocks in the vendored files.
#[test]
fn parses_the_whole_corpus() {
    const EXPECTED: &[(&str, usize)] = &[
        ("basic", 43),
        ("bindings_ext", 5),
        ("block_ext", 37),
        ("comparisons", 406),
        ("conversions", 109),
        ("dynamic", 226),
        ("encoders_ext", 4),
        ("enums", 85),
        ("fields", 60),
        ("fp_math", 30),
        ("integer_math", 64),
        ("lists", 39),
        ("logic", 30),
        ("macros", 44),
        ("macros2", 46),
        ("math_ext", 199),
        ("namespace", 3),
        ("optionals", 70),
        ("parse", 219),
        ("plumbing", 5),
        ("proto2", 108),
        ("proto2_ext", 18),
        ("proto3", 75),
        ("string", 51),
        ("string_ext", 209),
        ("timestamps", 76),
        ("type_deduction", 47),
        ("unknowns", 0),
        ("wrappers", 36),
    ];

    let got: Vec<(String, usize)> = corpus()
        .files
        .iter()
        .map(|f| (f.name.clone(), f.cases.len()))
        .collect();
    let want: Vec<(String, usize)> = EXPECTED
        .iter()
        .map(|(n, c)| ((*n).to_string(), *c))
        .collect();

    assert_eq!(got, want, "corpus shape changed");
    assert_eq!(corpus().len(), 2344, "total case count");
}

/// Every case has the two things that make it addressable and runnable.
#[test]
fn every_case_is_named_and_has_an_expression() {
    let bad: Vec<String> = corpus()
        .cases()
        .filter(|c| c.name.is_empty() || c.expr.is_empty() || c.section.is_empty())
        .map(Case::id)
        .collect();
    assert!(bad.is_empty(), "cases missing a name/section/expr: {bad:?}");
}

/// `file/section/name` is NOT unique upstream, and `unique_id` is what fixes it.
///
/// Four collisions exist in v0.25.1 — three `char_index` tests in one `string_ext` section alone,
/// each asserting something different. Pinning the exact set matters in both directions: a NEW
/// collision means the generated test names would have silently merged two cases into one, and a
/// vanished collision means the corpus moved under us.
#[test]
fn duplicate_case_names_are_known_and_disambiguated() {
    const KNOWN: &[&str] = &[
        "dynamic/float/field_assign_proto2_subnorm",
        "string_ext/index_of/char_index",
        "string_ext/index_of/empty_index",
        "string_ext/index_of/string_index",
    ];

    let mut seen = std::collections::BTreeMap::<String, usize>::new();
    for case in corpus().cases() {
        *seen.entry(case.id()).or_default() += 1;
    }
    let dupes: Vec<&str> = seen
        .iter()
        .filter(|(_, n)| **n > 1)
        .map(|(id, _)| id.as_str())
        .collect();
    assert_eq!(dupes, KNOWN, "the set of duplicated case names changed");

    let unique: std::collections::BTreeSet<String> =
        corpus().cases().map(Case::unique_id).collect();
    assert_eq!(
        unique.len(),
        corpus().len(),
        "unique_id does not separate every case"
    );
}

/// No exclusion rule covers nothing. A rule matching zero cases is a false claim of understanding
/// — a renamed file upstream, or a case name that was guessed rather than read.
#[test]
fn every_exclusion_rule_matches_something() {
    let cases: Vec<&Case> = corpus().cases().collect();
    let dead: Vec<String> = exclusions()
        .dead_rules(&cases)
        .iter()
        .map(|r| format!("{} ({})", r.label(), r.reason))
        .collect();
    assert!(
        dead.is_empty(),
        "exclusion rules matching no case: {dead:?}"
    );
}

/// The partition: every case is EXCLUDED or has exactly one generated test. Nothing is both, and
/// nothing is neither.
///
/// "Neither" is the failure this catches. A case that is not excluded and has no generated test
/// simply is not measured — it contributes to no count, appears in no report, and reads exactly
/// like a case that passed. Re-deriving the expected test set from the corpus and comparing it to
/// what `gen/cases.rs` actually declares is what makes that impossible.
#[test]
fn every_case_resolves_to_exactly_one_outcome() {
    let exclusions = exclusions();
    let expected = gen::test_names(&exclusions);

    let generated = include_str!("../conformance/gen/cases.rs");
    let declared: Vec<String> = generated
        .lines()
        .filter_map(|l| l.strip_prefix("fn ")?.split('(').next())
        .map(str::to_string)
        .collect();

    assert_eq!(
        declared, expected,
        "gen/cases.rs is stale. Regenerate: cargo run -p typed-cel --features conformance \
         --bin conformance-report -- --write"
    );

    let excluded = corpus()
        .cases()
        .filter(|c| exclusions.reason_for(c).is_some())
        .count();
    assert_eq!(
        excluded + declared.len(),
        corpus().len(),
        "{} cases are neither excluded nor generated",
        corpus().len() - excluded - declared.len()
    );
}

/// Every exclusion reason is a dialect-row id in README.md.
///
/// This is what stops EXCLUDED becoming a place to hide failures: excluding a case requires
/// editing the document that describes the language. The ids are matched as whole backtick-quoted
/// spans, so a reason cannot pass by being a substring of a longer row.
#[test]
fn exclusions_cite_the_readme() {
    let readme = std::fs::read_to_string(
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("README.md"),
    )
    .expect("README.md");
    let ids = readme_dialect_ids(&readme);
    assert!(
        ids.len() >= 10,
        "only {} dialect ids found in README.md — the table format changed and this test is now \
         checking nothing",
        ids.len()
    );

    let exclusions = exclusions();
    let unknown: Vec<&str> = exclusions
        .rules
        .iter()
        .map(|r| r.reason.as_str())
        .filter(|reason| !ids.contains(*reason))
        .collect();
    assert!(
        unknown.is_empty(),
        "exclusion reasons that name no README dialect row: {unknown:?}\nknown ids: {ids:?}"
    );
}

/// The reverse direction: no dialect row is a dead letter, and no reason drifts out of the README
/// while the exclusions still cite it. Rows describing constructs whose corpus rows have not been
/// moved yet are listed here explicitly, so the list shrinks as deletions land rather than
/// silently tolerating any mismatch.
#[test]
fn every_readme_dialect_id_is_accounted_for() {
    // Ids that legitimately exclude nothing: no corpus case reaches the divergence, because the
    // corpus has no schemas, no record types and no durations beside timestamps.
    //
    // Every `removed:` id now excludes something. That is the deletions' definition of done: a
    // removal whose corpus rows have not moved has taken the construct out of the API and left it
    // in the implementation.
    const NOT_YET_EXCLUDING: &[&str] = &[
        "diverges: one numeric type",
        "diverges: literal-key record index",
        "diverges: durations without timestamps",
        "diverges: dyn must be narrowed",
    ];

    let readme = std::fs::read_to_string(
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("README.md"),
    )
    .expect("README.md");
    let cited: std::collections::BTreeSet<String> = exclusions()
        .rules
        .iter()
        .map(|r| r.reason.clone())
        .collect();

    let orphans: Vec<String> = readme_dialect_ids(&readme)
        .into_iter()
        .filter(|id| !cited.contains(id) && !NOT_YET_EXCLUDING.contains(&id.as_str()))
        .collect();
    assert!(
        orphans.is_empty(),
        "README dialect rows that exclude nothing and are not listed as pending: {orphans:?}"
    );
}

/// Dialect-row ids, read out of the README's tables. An id is the backtick-quoted content of the
/// first cell of a table row whose id starts with a dialect verb.
fn readme_dialect_ids(readme: &str) -> std::collections::BTreeSet<String> {
    readme
        .lines()
        .filter_map(|l| l.trim().strip_prefix("| `"))
        .filter_map(|rest| rest.split('`').next())
        .filter(|id| {
            id.starts_with("removed: ")
                || id.starts_with("not implemented: ")
                || id.starts_with("diverges: ")
        })
        .map(str::to_string)
        .collect()
}

/// No `#[should_panic]`, anywhere in the generated tests.
///
/// A structural assertion, because the failure mode is one contributor adding one attribute at
/// 6pm. cel-rust's own harness reports `2343 passed; 0 failed` while 1455 of those tests pass BY
/// panicking; that is the exact shape this crate exists not to reproduce.
#[test]
fn no_should_panic_anywhere() {
    // The attribute, spelled so this test's own source does not match the thing it forbids.
    let forbidden = format!("#[{}_panic", "should");
    let mut checked = 0;
    for entry in walk(&conformance_dir()) {
        if entry.extension().is_none_or(|e| e != "rs") {
            continue;
        }
        checked += 1;
        let src = std::fs::read_to_string(&entry).expect("readable");
        assert!(
            !src.contains(&forbidden),
            "{} carries the attribute — the harness has three outcomes and \"passes by failing\" \
             is not among them",
            entry.display()
        );
    }
    assert!(
        checked >= 6,
        "only {checked} harness files scanned — the walk found nothing, so this proves nothing"
    );
}

fn walk(dir: &std::path::Path) -> Vec<std::path::PathBuf> {
    let mut out = Vec::new();
    let Ok(entries) = std::fs::read_dir(dir) else {
        return out;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            out.extend(walk(&path));
        } else {
            out.push(path);
        }
    }
    out
}

/// Running the generator twice produces byte-identical output.
///
/// Generated artifacts are checked in, so any run-to-run instability — a HashMap iteration order,
/// an unsorted directory read — shows up as a spurious diff that trains people to ignore diffs in
/// these files, which is precisely when a real regression slips through.
#[test]
fn the_report_is_reproducible() {
    let exclusions = exclusions();
    for _ in 0..2 {
        assert_eq!(gen::cases_rs(&exclusions), gen::cases_rs(&exclusions));
        assert_eq!(gen::report(&exclusions), gen::report(&exclusions));
        assert_eq!(
            gen::baseline_toml(&exclusions),
            gen::baseline_toml(&exclusions)
        );
    }
}

/// The committed report matches a live run.
///
/// A hand-maintained compatibility table is a lie with a timestamp. Generating it, committing it,
/// and failing the build when it drifts is what makes the number in the README worth reading.
#[test]
fn the_conformance_table_is_current() {
    let live = gen::report(&exclusions());
    let committed =
        std::fs::read_to_string(conformance_dir().join("report.md")).expect("report.md");
    assert_eq!(
        live, committed,
        "conformance/report.md is stale. Regenerate: cargo run -p typed-cel --features \
         conformance --bin conformance-report -- --write"
    );
}

/// The committed per-file counts match a live run, in BOTH directions.
///
/// Without a baseline, "we pass 84%" is a number nobody can regress. With one, a refactor that
/// quietly breaks nine cases is a failing test rather than a slightly smaller number in a report
/// nobody re-reads — and an IMPROVEMENT has to be recorded, so it gets noticed instead of absorbed.
#[test]
fn the_baseline_holds() {
    let live = gen::baseline_toml(&exclusions());
    let committed =
        std::fs::read_to_string(conformance_dir().join("baseline.toml")).expect("baseline.toml");
    assert_eq!(
        live, committed,
        "conformance/baseline.toml is stale. If cases changed outcome, say so in the commit and \
         regenerate: cargo run -p typed-cel --features conformance --bin conformance-report \
         -- --write"
    );
}

/// Every corpus case that NAMES a removed construct is EXCLUDED — not passing, and not failing.
///
/// This is what makes a deletion auditable rather than a claim. There are two ways to get a
/// deletion wrong and this test sees both:
///
///   - the construct still WORKS, so its cases still pass. The API grew a rejection the
///     implementation did not, which is the shape a `#[cfg]` or a removed re-export produces.
///   - the construct is gone but its cases were left FAILING. That is a real regression wearing a
///     deletion's clothes, and the fix is to move the rows in the same commit — if they will not
///     move, the construct is still reachable by a spelling nobody found.
///
/// Matching is TEXTUAL, over the case's own expression and over the values it binds and expects.
/// A `uint` case is one that spells a `u` suffix, calls `uint()`, or binds/expects a uint — the
/// last is the class a syntax-only scan misses, where `x == 1` is a uint case because `x` is bound
/// to one.
#[test]
fn the_corpus_rows_moved() {
    // `removed: protobuf` is deliberately absent: a message literal is not textually identifiable
    // (`TestAllTypes{...}` is an identifier and a brace), and its rows move by whole file, which
    // `every_exclusion_rule_matches_something` already holds.
    const REMOVALS: &[(&str, fn(&Case) -> bool)] = &[
        ("removed: uint", names_uint),
        ("removed: timestamp", names_timestamp),
        ("removed: dyn()", names_dyn),
        ("removed: optional syntax", names_optional),
        ("removed: integer values", names_integer_value),
        ("removed: modulo", names_modulo),
    ];

    let exclusions = exclusions();
    let mut leaked: Vec<String> = Vec::new();
    for (id, names) in REMOVALS {
        let mut matched = 0usize;
        for case in corpus().cases().filter(|c| names(c)) {
            matched += 1;
            if exclusions.reason_for(case).is_some() {
                continue;
            }
            let verdict = match run::run(case) {
                Outcome::Pass | Outcome::PassStatic(_) => {
                    "still PASSES — the construct was not actually removed"
                }
                Outcome::Refused(_) | Outcome::Fail(_) => {
                    "FAILS — the deletion landed but its rows were not moved"
                }
            };
            leaked.push(format!(
                "  [{id}] {}: {verdict}\n    {}",
                case.unique_id(),
                case.expr
            ));
        }
        assert!(
            matched > 0,
            "`{id}` matches no corpus case at all — the predicate is broken, so this test is \
             checking nothing for that removal"
        );
    }

    assert!(
        leaked.is_empty(),
        "{} corpus cases name a removed construct without being excluded:\n{}",
        leaked.len(),
        leaked.join("\n")
    );
}

/// Does the case mention a uint anywhere — in its expression, its bindings, or its expectation?
fn names_uint(case: &Case) -> bool {
    fn value_is_uint(v: &harness::case::CelValue) -> bool {
        use harness::case::CelValue;
        match v {
            CelValue::Uint(_) => true,
            CelValue::List(items) => items.iter().any(value_is_uint),
            CelValue::Map(entries) => entries
                .iter()
                .any(|(k, v)| value_is_uint(k) || value_is_uint(v)),
            CelValue::Type(name) => name == "uint",
            _ => false,
        }
    }
    if case.expr.contains("uint(") || uint_suffix(&case.expr) {
        return true;
    }
    if let harness::case::Expect::Value(v) = &case.expect {
        if value_is_uint(v) {
            return true;
        }
    }
    case.bindings.iter().any(|(_, b)| match b {
        harness::case::Binding::Value(v) => value_is_uint(v),
        harness::case::Binding::Unsupported(_) => false,
    })
}

/// A `u`/`U` suffix on a numeric literal, outside a string.
///
/// Written by hand rather than with a regex because the false positive to avoid is specific: `u`
/// is an ordinary letter, so `'1u'` inside a quoted string and `my_u` in an identifier must not
/// count. Only a `u` that directly follows a digit and is not followed by an identifier character
/// is a uint literal.
fn uint_suffix(expr: &str) -> bool {
    let bytes = expr.as_bytes();
    let mut quote: Option<u8> = None;
    let mut prev_digit = false;
    for (i, &b) in bytes.iter().enumerate() {
        match quote {
            Some(q) => {
                if b == q && bytes.get(i.wrapping_sub(1)) != Some(&b'\\') {
                    quote = None;
                }
                prev_digit = false;
                continue;
            }
            None => {
                if b == b'\'' || b == b'"' {
                    quote = Some(b);
                    prev_digit = false;
                    continue;
                }
            }
        }
        if (b == b'u' || b == b'U') && prev_digit {
            let next = bytes.get(i + 1);
            if !next.is_some_and(|c| c.is_ascii_alphanumeric() || *c == b'_') {
                return true;
            }
        }
        prev_digit = b.is_ascii_hexdigit();
    }
    false
}

/// Does the case EXPECT an integer value? There is no runtime integer, so a case whose answer is
/// `int64_value: 3` asks for a kind the dialect cannot produce — `3.0` is a different corpus
/// expectation, and the harness compares by kind. An integer LITERAL in the expression, or an
/// integer BINDING, is not this: both widen, which is `diverges: one numeric type` rather than the
/// removal.
fn names_integer_value(case: &Case) -> bool {
    fn value_is_int(v: &harness::case::CelValue) -> bool {
        use harness::case::CelValue;
        match v {
            CelValue::Int(_) => true,
            CelValue::List(items) => items.iter().any(value_is_int),
            CelValue::Map(entries) => entries
                .iter()
                .any(|(k, v)| value_is_int(k) || value_is_int(v)),
            _ => false,
        }
    }
    matches!(&case.expect, harness::case::Expect::Value(v) if value_is_int(v))
}

/// A `%` operator, outside a string literal.
fn names_modulo(case: &Case) -> bool {
    let mut quote: Option<char> = None;
    let mut prev = ' ';
    for c in case.expr.chars() {
        match quote {
            Some(q) => {
                if c == q && prev != '\\' {
                    quote = None;
                }
            }
            None if c == '\'' || c == '"' => quote = Some(c),
            None if c == '%' => return true,
            None => {}
        }
        prev = c;
    }
    false
}

fn names_timestamp(case: &Case) -> bool {
    case.expr.contains("timestamp(")
}

fn names_dyn(case: &Case) -> bool {
    case.expr.contains("dyn(")
}

fn names_optional(case: &Case) -> bool {
    let e = &case.expr;
    e.contains("optional.")
        || e.contains("[?")
        || e.contains(".?")
        || e.contains(".orValue(")
        || e.contains(".hasValue(")
        || e.contains(".optMap(")
        || e.contains(".optFlatMap(")
}

/// A rule citing a row the CHECKER enforces covers only cases the checker refuses citing that
/// row. Every case is compiled through the checker first, so for these rows "excluded" must mean
/// "the checker said no, and said why" — a rule over a case the checker admits is a false claim, and
/// the case should be running.
///
/// The rows listed are the ones whose refusals name them (`check.rs` renders the row id in the
/// message). The other rows exclude by construct — a protobuf literal, an extension function, a
/// `uint` suffix — whose cases the checker refuses for whatever the construct first trips over, or
/// that the evaluator cannot answer at all.
#[test]
fn checker_rows_exclude_only_what_the_checker_refuses() {
    const CHECKER_ROWS: &[&str] = &[
        "diverges: duration() takes a string",
        "diverges: equality is homogeneous",
        "diverges: nesting is bounded",
        "diverges: undeclared names are compile errors",
        "not implemented: backtick-quoted field selection",
        "removed: bytes concatenation",
        "removed: dyn values",
        "removed: logic on non-bools",
        "removed: ordering beyond numbers and strings",
        "removed: type conversion functions",
        "removed: type values",
    ];
    let exclusions = exclusions();
    let mut covered = 0usize;
    let mut problems: Vec<String> = Vec::new();
    for case in corpus().cases() {
        let Some(reason) = exclusions.reason_for(case) else {
            continue;
        };
        if !CHECKER_ROWS.contains(&reason) {
            continue;
        }
        covered += 1;
        let cites = format!("`{reason}`");
        match run::run(case) {
            Outcome::Refused(why) | Outcome::PassStatic(why) if why.contains(&cites) => {}
            other => problems.push(format!(
                "  EXCLUDED as `{reason}` but the checker did not refuse it citing that row: {}\n    \
                 {}\n    {other:?}",
                case.unique_id(),
                case.expr.escape_debug()
            )),
        }
    }
    let cited: std::collections::BTreeSet<&str> =
        exclusions.rules.iter().map(|r| r.reason.as_str()).collect();
    let dead: Vec<&&str> = CHECKER_ROWS
        .iter()
        .filter(|r| !cited.contains(**r))
        .collect();
    assert!(dead.is_empty(), "checker rows no rule cites: {dead:?}");
    assert!(covered >= 150, "only {covered} cases under a checker row");
    assert!(
        problems.is_empty(),
        "{} problems:\n{}",
        problems.len(),
        problems.join("\n")
    );
}

/// The lane runs every admitted case on the backend — the one engine — compiled once, never on a
/// second parse through the tree evaluator.
#[test]
fn the_lane_runs_on_the_backend() {
    let text = std::fs::read_to_string(conformance_dir().join("harness/run.rs")).expect("readable");
    let code = support::code_only(&text);
    assert!(
        code.contains("fast_value"),
        "conformance/harness/run.rs does not run a case on the backend"
    );
    for banned in ["Program::compile", ".execute("] {
        assert!(
            !code.contains(banned),
            "conformance/harness/run.rs runs a case on the tree evaluator: it names `{banned}`"
        );
    }
}
