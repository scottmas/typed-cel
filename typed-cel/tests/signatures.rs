//! The signature table IS the dialect, in executable form.
//!
//! The first two tests hold `README.md` and `src/sigs.rs` to each other in both directions. The
//! rest exercise the table through the checker, because a table nothing consults is a document
//! with a `.rs` extension.

#[path = "support/mod.rs"]
mod support;

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use support::{err, err_mentions, ok};

fn readme() -> String {
    std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("README.md"))
        .expect("README.md")
}

/// The cells of a markdown row, honouring `\|` as an escaped pipe — `_||_` is a real row and its
/// name contains the delimiter.
fn row_cells(line: &str) -> Option<Vec<String>> {
    let line = line.trim();
    let inner = line.strip_prefix('|')?.strip_suffix('|')?;
    if inner.chars().all(|c| matches!(c, '-' | ':' | '|' | ' ')) {
        return None;
    }
    let mut cells = Vec::new();
    let mut cur = String::new();
    let mut chars = inner.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' if chars.peek() == Some(&'|') => {
                chars.next();
                cur.push('|');
            }
            '|' => {
                cells.push(cur.trim().to_string());
                cur = String::new();
            }
            _ => cur.push(c),
        }
    }
    cells.push(cur.trim().to_string());
    Some(cells)
}

/// `` `x`, `y` `` -> `["x", "y"]`.
fn backticked(cell: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = cell;
    while let Some(open) = rest.find('`') {
        let after = &rest[open + 1..];
        let Some(close) = after.find('`') else { break };
        out.push(after[..close].to_string());
        rest = &after[close + 1..];
    }
    out
}

/// The README's `## Signatures` table, as `name -> overloads`.
fn readme_signatures() -> BTreeMap<String, Vec<String>> {
    let readme = readme();
    let mut out = BTreeMap::new();
    let mut inside = false;
    for line in readme.lines() {
        if line.starts_with('#') {
            inside = line.trim_end() == "## Signatures";
            continue;
        }
        if !inside {
            continue;
        }
        let Some(cells) = row_cells(line) else {
            continue;
        };
        if cells.first().map(String::as_str) == Some("function") {
            continue;
        }
        let name = backticked(&cells[0]);
        let Some(name) = name.first() else { continue };
        out.insert(
            name.clone(),
            backticked(cells.get(1).map(String::as_str).unwrap_or("")),
        );
    }
    assert!(
        out.len() >= 20,
        "only {} rows found under `## Signatures` — the table format changed and this test is \
         now checking nothing",
        out.len()
    );
    out
}

fn table_signatures() -> BTreeMap<String, Vec<String>> {
    typed_cel::signature_table()
        .into_iter()
        .map(|(n, o)| (n.to_string(), o))
        .collect()
}

#[test]
fn every_readme_row_has_a_signature() {
    let readme = readme_signatures();
    let table = table_signatures();
    let mut missing = Vec::new();
    for (name, overloads) in &readme {
        match table.get(name) {
            None => missing.push(format!("  `{name}` — documented, not implemented")),
            Some(actual) if actual != overloads => missing.push(format!(
                "  `{name}` — README says {overloads:?}, src/sigs.rs has {actual:?}"
            )),
            Some(_) => {}
        }
    }
    assert!(
        missing.is_empty(),
        "README `## Signatures` rows that src/sigs.rs does not match:\n{}",
        missing.join("\n")
    );
}

#[test]
fn every_signature_has_a_readme_row() {
    let readme: BTreeSet<String> = readme_signatures().into_keys().collect();
    let missing: Vec<String> = table_signatures()
        .into_keys()
        .filter(|n| !readme.contains(n))
        .map(|n| format!("  `{n}`"))
        .collect();
    assert!(
        missing.is_empty(),
        "src/sigs.rs declares functions with no README row — the dialect grew without being \
         written down:\n{}",
        missing.join("\n")
    );
}

#[test]
fn an_undocumented_function_is_rejected() {
    // "unknown function", listing nothing — we register no custom functions — rather than a type
    // error, which would suggest the author could fix it by changing the argument.
    err_mentions(
        "is_owner(body.user_id)",
        ["unknown function", "is_owner"].as_ref(),
    );
    err_mentions(
        "sustained(metrics.cpu.now, 10)",
        ["unknown function"].as_ref(),
    );
    // The numeric aggregate the acceptance battery deliberately does NOT have: `sum` is a `math`
    // extension member, and `removed: extension libraries` shipped none. Registering a custom
    // `sum` is the tempting fix and it is the one thing the Non-Goals forbid.
    err_mentions(
        "body.items.map(x, x.id).sum() == body.amount",
        ["unknown function", "sum"].as_ref(),
    );
    // While the same shape WITHOUT the aggregate is fine, so the refusal is about `sum` and not
    // about comprehensions.
    ok("body.items.map(x, x.id).size() == body.tags.size()");
}

#[test]
fn heterogeneous_equality_is_allowed() {
    // Every number is a double, so an integer literal and a `Num` field are one type.
    ok("body.amount == 100");
    ok("body.amount == 100.5");
    ok("100 == body.amount");
    ok("body.user_id == session.user_id");
}

#[test]
fn ordering_across_incompatible_types_is_rejected() {
    err_mentions("body.amount > session.user_id", [">"].as_ref());
    err_mentions("body.user_id < body.amount", ["<"].as_ref());
    err_mentions("body.items >= body.tags", [">="].as_ref());
}

#[test]
fn equality_across_incompatible_types_is_rejected() {
    // CEL's spec permits heterogeneous equality across NUMERIC types. Comparing a string to a
    // number is a policy bug: the expression can never be true, so the author wrote something
    // they did not mean, and the runtime answering `false` forever hides it.
    err_mentions("body.amount == session.user_id", ["=="].as_ref());
    err_mentions("body.user_id != body.amount", ["!="].as_ref());
}

#[test]
fn in_checks_element_against_container() {
    ok("body.id in session.allowed_ids");
    err("body.amount in session.allowed_ids");
    // The membership spelling the system environment needs: `(K, map(K, _))`.
    ok("'8080' in listeners");
    err("body.amount in listeners");
}

#[test]
fn logical_operators_require_bool() {
    err_mentions("body.user_id && true", ["&&"].as_ref());
    err("true || body.amount");
    err("!body.user_id");
    ok("body.amount > 1 && body.user_id == session.user_id");
}

#[test]
fn the_ternary_branches_must_agree() {
    err("(body.amount > 1 ? body.user_id : body.amount) == 'x'");
    ok("(body.amount > 1 ? body.user_id : body.tenant_id) == 'x'");
    // The condition itself must be a bool.
    err("(body.user_id ? 'a' : 'b') == 'x'");
}

#[test]
fn size_on_a_string_is_rejected() {
    let rendered = err("size(body.name) > 8");
    assert!(
        rendered.contains("size"),
        "the diagnostic must name the function:\n{rendered}"
    );
    err("body.name.size() > 8");
    // Lists and maps keep it, in both spellings.
    ok("size(body.items) == 3");
    ok("body.items.size() == 3");
    ok("size(m) == 3");
    ok("m.size() == 3");
}

#[test]
fn duration_is_its_own_ordering() {
    ok("signals.ready.elapsed > duration('5m')");
    ok("duration('5m') < signals.ready.elapsed");
    // A dropped unit suffix is a BUILD error, not a comparison against nanoseconds.
    err_mentions(
        "signals.ready.elapsed > 300",
        ["duration", "double"].as_ref(),
    );
    err_mentions(
        "300 < signals.ready.elapsed",
        ["duration", "double"].as_ref(),
    );
    // One constructor, and it takes a string.
    err("duration(300) > uptime");
}

#[test]
fn duration_arithmetic_is_closed() {
    ok("signals.ready.elapsed + duration('1s') > duration('2s')");
    ok("signals.ready.elapsed - duration('1s') > duration('2s')");
    // `Duration * Num` is deliberately absent: it is the surface through which the internal unit
    // leaks into a policy's arithmetic.
    err("signals.ready.elapsed * 2 > duration('2s')");
    err("signals.ready.elapsed / 2 > duration('2s')");
    err("signals.ready.elapsed + 1 > duration('2s')");
}
