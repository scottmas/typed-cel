//! The backend's hot types stay small. Every byte of `Reg`, `Op` and the per-call result types is
//! copied on every op or every decision, so a size is a performance contract: each ceiling here is
//! the size the fast-path work brought it down to, and a later change cannot silently
//! grow it back.

use typed_cel::layout_sizes;

/// The ceilings, in bytes.
const CEILINGS: &[(&str, usize)] = &[
    ("Reg", 24),
    ("Op", 24),
    ("ExecutionError", 72),
    ("Option<ExecutionError>", 72),
    ("Result<Reg, Miss>", 24),
    ("Exit", 32),
    ("Flow", 24),
    ("Result<bool, CelError>", 112),
];

#[test]
fn the_hot_types_are_no_larger_than_pinned() {
    let sizes = layout_sizes();
    let mut over = Vec::new();
    for (name, ceiling) in CEILINGS {
        let (_, size) = sizes
            .iter()
            .find(|(n, _)| n == name)
            .unwrap_or_else(|| panic!("layout_sizes() names no `{name}`"));
        if size > ceiling {
            over.push(format!("{name}: {size} B > {ceiling} B"));
        }
    }
    assert_eq!(
        sizes.len(),
        CEILINGS.len(),
        "a probed type has no ceiling: {sizes:?}"
    );
    assert!(over.is_empty(), "hot types grew: {over:?}\nall: {sizes:?}");
}

/// The ops a decision runs most are handled by the dispatch loop itself, not by the out-of-line
/// `slow` function (a nine-argument call into a large function per op). `slow` debug-asserts that
/// it never receives an op this list claims, so the list cannot overstate the loop.
#[test]
fn the_common_ops_are_inline() {
    let inline = typed_cel::inline_ops();
    let missing: Vec<&str> = ["Eq", "Ne", "Absorb", "Match"]
        .into_iter()
        .filter(|op| !inline.contains(op))
        .collect();
    assert!(
        missing.is_empty(),
        "not inline: {missing:?} (inline: {inline:?})"
    );
}
