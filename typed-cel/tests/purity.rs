//! The gates that keep this crate a LIBRARY.
//!
//! Three properties, each of which decays silently: the absorbed fork stays private, no concept
//! of the host application (a sandbox policy engine) appears in a file authored for the dialect,
//! and the backend that runs programs (`src/fast/`) names neither the parser nor the checker.
//! None has a compiler to enforce it, so each is a source scan — the only kind of check that
//! catches the fourth leak arriving with the next feature.

#[path = "support/mod.rs"]
mod support;

use std::path::{Path, PathBuf};

use support::code_only;

fn src() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src")
}

/// The absorbed fork, listed EXPLICITLY rather than as a directory glob.
///
/// A glob would silently exempt a new file the day someone adds `src/http_env.rs` to a fork
/// directory. Listing the fork by name means a new file is scanned BY DEFAULT and a new fork file
/// has to be added here deliberately.
const FORK: &[&str] = &[
    "parser",
    "common",
    "objects.rs",
    "context.rs",
    "functions.rs",
    "ser.rs",
    "magic.rs",
    "resolvers.rs",
    "env.rs",
    "json.rs",
    "duration.rs",
    "macros.rs",
];

fn is_fork(rel: &Path) -> bool {
    rel.components()
        .next()
        .map(|c| FORK.contains(&c.as_os_str().to_str().unwrap_or("")))
        .unwrap_or(false)
}

/// Every `.rs` file under `src/` authored for the dialect (not absorbed from the fork).
fn authored() -> Vec<(PathBuf, String)> {
    fn walk(dir: &Path, root: &Path, out: &mut Vec<(PathBuf, String)>) {
        for entry in std::fs::read_dir(dir).expect("src/ is readable") {
            let path = entry.expect("a readable dir entry").path();
            let rel = path.strip_prefix(root).expect("under root").to_path_buf();
            if path.is_dir() {
                if !is_fork(&rel) {
                    walk(&path, root, out);
                }
            } else if path.extension().is_some_and(|e| e == "rs") && !is_fork(&rel) {
                out.push((rel, std::fs::read_to_string(&path).expect("readable")));
            }
        }
    }
    let root = src();
    let mut out = Vec::new();
    walk(&root, &root, &mut out);
    assert!(
        out.len() >= 8,
        "the walk found only {} authored files — the exclusion list has swallowed the crate",
        out.len()
    );
    out
}

/// Words that name a concept of the host application this was built for (a sandbox policy
/// engine). A library file containing one is a library file that has to
/// change when a policy schema changes, which is the exact coupling this crate is supposed to
/// have shed.
const HOST_WORDS: &[&str] = &[
    "metrics",
    "uptime",
    "revoke",
    "grant",
    "sandbox",
    "assertion",
    "policy",
    "broker",
    "guest",
    "http",
    "header",
    "endpoint",
    "session",
    "listener",
];

#[test]
fn the_library_names_no_host_concept() {
    let mut leaks: Vec<String> = Vec::new();
    for (rel, text) in authored() {
        let code = code_only(&text);
        for (n, line) in code.lines().enumerate() {
            let lower = line.to_ascii_lowercase();
            for word in HOST_WORDS {
                if lower.contains(word) {
                    leaks.push(format!(
                        "{}:{}: `{word}` in `{}`",
                        rel.display(),
                        n + 1,
                        line.trim()
                    ));
                }
            }
        }
    }
    assert!(
        leaks.is_empty(),
        "a host-application concept reached the library — move it to the caller that owns the vocabulary:\n{}",
        leaks.join("\n")
    );
}

#[test]
fn the_fork_is_not_public() {
    // `lib.rs` claims the absorbed types stay internal, so the fork's internals remain ours to
    // change without breaking a caller. That claim was FALSE for as long as it stood unchecked —
    // every fork module was `pub` and six fork types were re-exported.
    let lib = include_str!("../src/lib.rs");
    let code = code_only(&lib);
    for name in ["common", "context", "objects", "functions", "parser"] {
        assert!(
            !code.contains(&format!("pub mod {name};")),
            "`pub mod {name};` — the fork is public again"
        );
    }
    for name in [
        "IdedExpr",
        "Context",
        "FunctionContext",
        "ResolveResult",
        "Value",
        "ParseError",
        "ParseErrors",
        "Program",
        "Env",
        "Duration",
    ] {
        for form in [
            format!("pub use common::ast::{name};"),
            format!("pub use context::{name};"),
            format!("pub use objects::{name};"),
            format!("pub use functions::{name};"),
            format!("pub use parser::{name};"),
            format!("pub use ser::{name};"),
            format!("pub use env::{name};"),
        ] {
            assert!(
                !code.contains(&form),
                "`{form}` — a fork type is contract again"
            );
        }
    }

    // The unchecked entry — parse with no checker, run with no roster — is crate-private: a caller
    // gets a program only from `CelEnvironment::compile`. Nor is the function-registration
    // vocabulary a caller could write a custom function with.
    for decl in ["pub struct Program", "pub mod extractors"] {
        assert!(
            !code.lines().any(|l| l.starts_with(decl)),
            "`{decl}` at the crate root — an unchecked entry point is public again"
        );
    }
    assert!(
        code.contains("pub(crate) use program::Program;"),
        "`Program` must be re-exported crate-private, from its private module"
    );

    // The ONE escape hatch, for the crate's own harnesses, and it must stay gated. Ungated it is
    // the same public fork under a different name.
    assert!(
        lib.contains("#[cfg(feature = \"conformance\")]\n#[doc(hidden)]\npub mod fork {"),
        "the `fork` hatch must be declared exactly `#[cfg(feature = \"conformance\")]` then \
         `#[doc(hidden)]` then `pub mod fork {{`. Ungated it is the same public fork under a \
         different name, and `conformance` is the crate's own test signal — nothing a consumer \
         turns on."
    );
}

// ---- the backend that RUNS a program names nothing that COMPILES one ----

/// The first segment of every `crate::` path in `code`, in order of appearance. A brace group
/// (`crate::{a::B, c}`) contributes each of its top-level members' first segments.
fn crate_paths(code: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = code;
    while let Some(ix) = rest.find("crate::") {
        rest = &rest[ix + "crate::".len()..];
        if let Some(group) = rest.strip_prefix('{') {
            let mut depth = 0usize;
            let mut start = 0usize;
            for (i, c) in group.char_indices() {
                match c {
                    '{' => depth += 1,
                    '}' if depth == 0 => {
                        push_first(&group[start..i], &mut out);
                        break;
                    }
                    '}' => depth -= 1,
                    ',' if depth == 0 => {
                        push_first(&group[start..i], &mut out);
                        start = i + 1;
                    }
                    _ => {}
                }
            }
        } else {
            push_first(rest, &mut out);
        }
    }
    out
}

fn push_first(s: &str, out: &mut Vec<String>) {
    let seg: String = s
        .trim_start()
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_')
        .collect();
    if !seg.is_empty() {
        out.push(seg);
    }
}

/// What a file under `src/fast/` may name: the absorbed value model, the lazy seam, and the
/// boundary types a run takes and returns. Never `parser`, `check`, `sigs`, `desugar`, `bounds`,
/// `specialize`, `derive`, `ty` or `unparse` — the backend lowers the tree the checker produced
/// and reads the node kinds the checker recorded, and nothing else of it.
const FAST_MAY_NAME: &[&str] = &[
    // The checked tree lowering reads (`common::ast`), and the roots a run reads.
    "common",
    "bindings",
    "duration",
    // The host functions a program calls: data and closures over boundary values, named here the
    // way `lazy` is — never a forge module.
    "hostfn",
    "lazy",
    // The one value, and its map, key and duration; the one number's representations (`num`).
    "value",
    "num",
    "CelActivation",
    "CelDuration",
    "CelError",
    "CelKey",
    "CelMap",
    "CelMapKey",
    "CelNum",
    "CelProgram",
    "CelValue",
    "ExecutionError",
];

/// Every `.rs` file under `src/fast/`, as (path relative to `src/`, contents).
fn fast_files() -> Vec<(PathBuf, String)> {
    let root = src();
    let mut out = Vec::new();
    for entry in std::fs::read_dir(root.join("fast")).expect("src/fast/ is readable") {
        let path = entry.expect("a readable dir entry").path();
        if path.extension().is_some_and(|e| e == "rs") {
            let rel = path.strip_prefix(&root).expect("under src").to_path_buf();
            out.push((rel, std::fs::read_to_string(&path).expect("readable")));
        }
    }
    out
}

#[test]
fn the_fast_backend_names_neither_the_parser_nor_the_checker() {
    let files = fast_files();
    let names: Vec<String> = files
        .iter()
        .map(|(rel, _)| rel.display().to_string())
        .collect();
    for want in ["mod.rs", "lower.rs", "host.rs", "reg.rs", "matcher.rs"] {
        assert!(
            names.iter().any(|n| n.ends_with(want)),
            "the scan did not find `fast/{want}` (found {names:?})"
        );
    }
    let mut leaks = Vec::new();
    for (rel, text) in files {
        for seg in crate_paths(&code_only(&text)) {
            if !FAST_MAY_NAME.contains(&seg.as_str()) {
                leaks.push(format!("{}: crate::{seg}", rel.display()));
            }
        }
    }
    assert!(
        leaks.is_empty(),
        "the fast backend names a module outside {FAST_MAY_NAME:?}:\n{}",
        leaks.join("\n")
    );
}

#[test]
fn the_path_scanner_sees_a_checker_import() {
    let paths =
        crate_paths("use crate::check::Checker;\nuse crate::{objects::Value, parser::Parser};");
    assert_eq!(paths, ["check", "objects", "parser"]);
}

/// Partial evaluation folds a closed subtree by running it on the backend — the engine that runs
/// the residual — never on the tree evaluator. The positive half (`FastProgram::lower_node`) keeps
/// the scan from passing on a fold that was simply deleted.
#[test]
fn specialize_folds_on_the_backend() {
    let text = std::fs::read_to_string(src().join("specialize.rs")).expect("readable");
    let code = code_only(&text);
    for banned in ["Value::resolve", "resolve_val", ".execute("] {
        assert!(
            !code.contains(banned),
            "src/specialize.rs folds on the tree evaluator: it names `{banned}`"
        );
    }
    assert!(
        code.contains("FastProgram::lower_node"),
        "src/specialize.rs does not lower a closed subtree onto the backend"
    );
}

/// No public entry point runs a program on the tree evaluator, or carries its function table.
#[test]
fn no_public_entry_reaches_the_evaluator() {
    const ALL: &[&str] = &[
        ".execute(",
        "Value::resolve",
        "env::Env",
        "tree_host",
        "with_env",
    ];
    let mut leaks = Vec::new();
    for file in ["activation.rs", "prepared.rs", "lib.rs"] {
        let text = std::fs::read_to_string(src().join(file)).expect("readable");
        let code = code_only(&text);
        for banned in ALL {
            if code.contains(banned) {
                leaks.push(format!("src/{file} names `{banned}`"));
            }
        }
    }
    assert!(leaks.is_empty(), "{}", leaks.join("\n"));
}

/// Every `.rs` file under `dir`, recursively.
fn rs_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for entry in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())) {
        let path = entry.expect("a readable dir entry").path();
        if path.is_dir() {
            out.extend(rs_files(&path));
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
    out
}

/// No test drives a second engine: every program a test runs is compiled through the checker and
/// run on the backend.
#[test]
fn no_test_names_a_second_engine() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    // The scans themselves: they name what they ban, as string data.
    const SCANS: &[&str] = &["tests/purity.rs", "tests/conformance.rs"];
    let mut files = rs_files(&root.join("tests"));
    files.extend(rs_files(&root.join("conformance/harness")));
    for f in ["src/lib.rs"] {
        files.push(root.join(f));
    }
    let mut scanned = 0usize;
    let mut leaks = Vec::new();
    for path in files {
        let rel = path
            .strip_prefix(root)
            .expect("under the crate")
            .display()
            .to_string();
        if SCANS.contains(&rel.as_str()) {
            continue;
        }
        scanned += 1;
        let code = code_only(&std::fs::read_to_string(&path).expect("readable"));
        for banned in [
            "fork::Program",
            "Program::compile",
            ".execute(",
            "test_script(",
        ] {
            if code.contains(banned) {
                leaks.push(format!("{rel} names `{banned}`"));
            }
        }
    }
    assert!(scanned > 40, "only {scanned} files scanned");
    assert!(leaks.is_empty(), "{}", leaks.join("\n"));
}

/// The tree evaluator and its function-call machinery are deleted: the backend is the only engine.
#[test]
fn the_evaluator_is_gone() {
    let root = src();
    for gone in [
        "functions.rs",
        "magic.rs",
        "resolvers.rs",
        "macros.rs",
        "env.rs",
    ] {
        assert!(!root.join(gone).exists(), "src/{gone} still exists");
    }
    let mut leaks = Vec::new();
    for path in rs_files(&root) {
        let code = code_only(&std::fs::read_to_string(&path).expect("readable"));
        for banned in [
            "fn resolve_val",
            "fn resolve_all",
            "Value::resolve",
            "find_overload",
            "FunctionContext",
        ] {
            if code.contains(banned) {
                leaks.push(format!("{} names `{banned}`", path.display()));
            }
        }
    }
    assert!(leaks.is_empty(), "{}", leaks.join("\n"));
}

/// No register or constant carries an ownership bit: a map is indexed one way wherever it lives.
#[test]
fn the_backend_tracks_no_ownership() {
    let mut leaks = Vec::new();
    for (rel, text) in fast_files() {
        let code = code_only(&text);
        for banned in ["Op::Own", "Own {", "fn owned", "fn borrowed", ".steal("] {
            if code.contains(banned) {
                leaks.push(format!("{} names `{banned}`", rel.display()));
            }
        }
    }
    assert!(leaks.is_empty(), "{}", leaks.join("\n"));
}

/// ONE value model: the fork's `Value` and its serde bridges are gone; `CelValue` is the value.
#[test]
fn one_value_model() {
    let root = src();
    for gone in ["objects.rs", "ser.rs", "json.rs"] {
        assert!(!root.join(gone).exists(), "src/{gone} still exists");
    }
    let mut leaks = Vec::new();
    for path in rs_files(&root) {
        let code = code_only(&std::fs::read_to_string(&path).expect("readable"));
        for banned in ["objects::", "Value::Float", "into_value", "from_value"] {
            if names_ident(&code, banned) {
                leaks.push(format!("{} names `{banned}`", path.display()));
            }
        }
    }
    assert!(leaks.is_empty(), "{}", leaks.join("\n"));
}

/// Does `code` name `word` as a whole identifier (or path)? `add_variable_from_value` does not name
/// `from_value`.
fn names_ident(code: &str, word: &str) -> bool {
    let is_ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    code.match_indices(word).any(|(i, _)| {
        let before = code[..i].chars().next_back();
        let after = code[i + word.len()..].chars().next();
        !before.is_some_and(is_ident) && !after.is_some_and(is_ident)
    })
}

/// ONE store: the fork's variable store, value trait and value types are gone; a register borrows a
/// `CelValue` and a run reads its roots from `Bindings`.
#[test]
fn one_store() {
    let root = src();
    for gone in [
        "context.rs",
        "common/value.rs",
        "common/traits.rs",
        "common/types",
    ] {
        assert!(!root.join(gone).exists(), "src/{gone} still exists");
    }
    let mut leaks = Vec::new();
    // The generated ANTLR parser downcasts its own parse-tree contexts, which have nothing to do
    // with values.
    let generated = root.join("parser/gen");
    for path in rs_files(&root)
        .into_iter()
        .filter(|p| !p.starts_with(&generated))
    {
        let code = code_only(&std::fs::read_to_string(&path).expect("readable"));
        for banned in [
            "dyn Val",
            "LazyAdapter",
            "Context",
            "downcast_ref",
            "common::types",
        ] {
            if names_ident(&code, banned) {
                leaks.push(format!("{} names `{banned}`", path.display()));
            }
        }
    }
    assert!(leaks.is_empty(), "{}", leaks.join("\n"));
}
