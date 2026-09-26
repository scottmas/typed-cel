//! Provenance: this crate is a fork, and a fork's licensing is a property that has to be tested.
//!
//! Attribution rots silently. A vendored tree whose provenance decays to "somebody copied this
//! once" is a licensing defect, not an untidy repo, and it decays in exactly the way an untested
//! file decays. So the notices, the fork point and the absence of the upstream dependency are all
//! assertions rather than intentions.

use std::path::{Path, PathBuf};

/// `typed-cel/`.
fn crate_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// The workspace root, which owns the single `Cargo.lock`.
fn workspace_root() -> PathBuf {
    crate_dir()
        .parent()
        .expect("typed-cel/ is one level below the workspace root")
        .to_path_buf()
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The MIT and Apache-2.0 texts are present, and carry the notices each licence requires be
/// retained: MIT wants the copyright line and the permission notice; Apache-2.0 is the corpus's
/// licence and lands here ahead of the corpus itself.
#[test]
fn the_licenses_are_present() {
    let mit = read(&crate_dir().join("LICENSE-MIT"));
    assert!(
        mit.contains("Copyright (c)"),
        "LICENSE-MIT has lost its copyright notice"
    );
    assert!(
        mit.contains("Permission is hereby granted, free of charge"),
        "LICENSE-MIT has lost the MIT permission notice"
    );
    assert!(
        mit.contains("The above copyright notice and this permission notice shall be included"),
        "LICENSE-MIT has lost the retention clause — the one MIT term that binds us"
    );

    let apache = read(&crate_dir().join("LICENSE-APACHE"));
    assert!(
        apache.contains("Apache License") && apache.contains("Version 2.0, January 2004"),
        "LICENSE-APACHE is not the Apache-2.0 text"
    );
}

/// A reader must be able to diff us against the exact tree we took. That needs a commit sha and
/// the repository it belongs to — a version number alone does not identify a tree.
#[test]
fn attribution_names_the_fork_point() {
    let attribution = read(&crate_dir().join("ATTRIBUTION.md"));

    assert!(
        attribution.contains("https://github.com/cel-rust/cel-rust"),
        "ATTRIBUTION.md does not name the upstream repository"
    );
    assert!(
        attribution.contains("0.14.2"),
        "ATTRIBUTION.md does not name the fork version"
    );
    assert!(
        attribution.contains("https://github.com/google/cel-spec")
            || attribution.contains("google/cel-spec"),
        "ATTRIBUTION.md does not name the corpus we vendor under Apache-2.0"
    );

    let shas: Vec<&str> = attribution
        .split(|c: char| !c.is_ascii_hexdigit())
        .filter(|w| w.len() == 40 && w.chars().all(|c| c.is_ascii_hexdigit()))
        .collect();
    assert!(
        !shas.is_empty(),
        "ATTRIBUTION.md carries no 40-character commit sha, so the fork point is not identified"
    );
}

/// The half-finished fork: `typed-cel` exists, and something still pulls the original `cel` in —
/// directly, or transitively through a crate that depends on it. Then the deletions the dialect
/// is FOR become impossible, because two implementations are live at once and either could be the
/// one a caller reached.
///
/// The lock is authoritative for "is this package in the graph at all"; the manifests are checked
/// too, so a dependency added but not yet resolved is caught in the same commit that adds it.
#[test]
fn no_upstream_cel_dependency() {
    let root = workspace_root();

    let lock = read(&root.join("Cargo.lock"));
    let offenders: Vec<usize> = lock
        .lines()
        .enumerate()
        .filter(|(_, l)| l.trim() == r#"name = "cel""#)
        .map(|(i, _)| i + 1)
        .collect();
    assert!(
        offenders.is_empty(),
        "Cargo.lock resolves a package named `cel` at line(s) {offenders:?} — typed-cel is a \
         fork, so upstream must not be in the graph"
    );

    // Every manifest under the workspace, ours excluded: `typed-cel/Cargo.toml` is allowed to
    // mention the word, and does (in prose).
    let ours = crate_dir().join("Cargo.toml");
    let mut checked = 0usize;
    for manifest in manifests(&root) {
        if manifest == ours {
            continue;
        }
        checked += 1;
        for (i, line) in read(&manifest).lines().enumerate() {
            let line = line.trim();
            // `cel = "0.14"`, `cel = { … }`, `cel={…}` — the key up to the first `=`, trimmed.
            if line
                .split_once('=')
                .is_some_and(|(key, _)| key.trim() == "cel")
            {
                panic!(
                    "{}:{} declares a dependency on `cel`: {line}",
                    manifest.display(),
                    i + 1
                );
            }
        }
    }
    // At least the workspace root's own manifest.
    assert!(
        checked >= 1,
        "no manifests scanned — the walk found nothing, so this test proves nothing"
    );
}

/// cel-rust's own unit tests came across with the source and are the first oracle this crate has,
/// before the cel-spec corpus lands. They run as `cargo test -p typed-cel --lib`; what this test
/// guards is that they are still THERE.
///
/// The floor moves DOWN only when a dialect deletion takes a construct's tests with it, and only
/// with a line in ATTRIBUTION.md saying which. A silently shrinking oracle is the failure mode:
/// deleting a construct is supposed to delete its tests, so the count dropping is not by itself
/// suspicious — which is exactly why it has to be stated rather than absorbed.
#[test]
fn the_absorbed_tests_still_pass() {
    let count = count_test_attributes(&crate_dir().join("src"));
    const FLOOR: usize = 81;
    assert!(
        count >= FLOOR,
        "the absorbed source carries {count} #[test] attributes, below the recorded floor of \
         {FLOOR}. If a dialect deletion removed them, lower the floor and say so in \
         ATTRIBUTION.md's change list."
    );
}

fn count_test_attributes(dir: &Path) -> usize {
    let mut n = 0;
    for entry in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())) {
        let path = entry.expect("readable dir entry").path();
        if path.is_dir() {
            n += count_test_attributes(&path);
        } else if path.extension().is_some_and(|e| e == "rs") {
            n += read(&path)
                .lines()
                .filter(|l| l.trim() == "#[test]")
                .count();
        }
    }
    n
}

/// Every `Cargo.toml` under the workspace, skipping `target/` and any vendored registry copy.
fn manifests(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    walk(root, &mut out);
    out
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if path.is_dir() {
            if name == "target" || name == "node_modules" || name.starts_with('.') {
                continue;
            }
            walk(&path, out);
        } else if name == "Cargo.toml" {
            out.push(path);
        }
    }
}
