//! `Parser::parse_with_source_info` — the one behavioural change made on the way in.
//!
//! Upstream attaches the source map to `ParseError`s and drops it when parsing SUCCEEDS, which is
//! fine when parsing is the only phase that can fail. The checker runs afterwards over an
//! `IdedExpr` that carries expression ids and no offsets, so without the map a type error can name
//! the mistake but not point at it. These tests pin that the map survives a successful parse and
//! that its offsets actually address the source text.

use typed_cel::fork::ast::{EntryExpr, Expr, IdedExpr};
use typed_cel::fork::parser::Parser;

/// The text `SourceInfo` addresses for an id.
///
/// The recorded range is INCLUSIVE on both ends — `add_offset` stores an ANTLR `CommonToken`'s
/// `start`/`stop`, and `stop` is the token's last byte, not one past it. Getting that wrong slices
/// a character off every diagnostic, which is the sort of defect nobody notices until it is
/// pointing at the wrong column in a real policy.
fn span<'a>(src: &'a str, info: &typed_cel::fork::ast::SourceInfo, id: u64) -> Option<&'a str> {
    let (start, stop) = info.offset_for(id)?;
    Some(&src[start as usize..=stop as usize])
}

#[test]
fn a_successful_parse_keeps_its_source_map() {
    let src = "files[\"/run/secrets/tls.key\"].closed.elapsed";
    let (expr, info) = Parser::new()
        .parse_with_source_info(src)
        .expect("expression parses");

    assert_eq!(
        info.source, src,
        "the map carries the source it was built from"
    );
    assert!(
        info.offset_for(expr.id).is_some(),
        "the ROOT expression has no offsets — the map was rebuilt empty rather than kept"
    );
}

/// The offsets have to address the real bytes, not merely exist: a diagnostic that points at the
/// wrong column is worse than one that points nowhere.
///
/// What a node is addressed BY is the token that anchors it, not the node's full extent — the
/// operator for a call, the `.` for a select, the token itself for a leaf. That is caret
/// positioning, which is what a `^` under a column needs, and it is a property the checker has to
/// know: a diagnostic about `body.no_such_field` points at the `.`, so it must name the field in
/// its message rather than rely on the span to show which one.
#[test]
fn the_offsets_address_the_anchoring_token() {
    let src = "body.amount > 100";
    let (expr, info) = Parser::new()
        .parse_with_source_info(src)
        .expect("expression parses");

    let Expr::Call(call) = &expr.expr else {
        panic!("expected the comparison at the root, got {:?}", expr.expr);
    };
    assert_eq!(span(src, &info, expr.id), Some(">"), "the call's operator");

    let (lhs, rhs) = (&call.args[0], &call.args[1]);
    assert_eq!(span(src, &info, lhs.id), Some("."), "the select's dot");
    assert_eq!(span(src, &info, rhs.id), Some("100"), "the literal itself");

    let Expr::Select(select) = &lhs.expr else {
        panic!("expected a select on the left, got {:?}", lhs.expr);
    };
    assert_eq!(
        span(src, &info, select.operand.id),
        Some("body"),
        "the identifier itself"
    );
}

/// Every node the parser produced is addressable, not just the ones it happened to record. A map
/// with holes fails a diagnostic exactly where an unusual expression made one.
#[test]
fn every_node_is_addressable() {
    let src = "body.documents.all(d, d.owner_id == session.user_id)";
    let (expr, info) = Parser::new()
        .parse_with_source_info(src)
        .expect("expression parses");

    let mut missing = Vec::new();
    walk(&expr, &mut |node| {
        if info.offset_for(node.id).is_none() {
            missing.push(node.id);
        }
    });
    assert!(
        missing.is_empty(),
        "expression ids {missing:?} have no offsets, so a type error on them cannot name a column"
    );
}

/// `parse` keeps its old shape and its old behaviour — it just throws the map away.
#[test]
fn parse_still_agrees_with_parse_with_source_info() {
    for src in [
        "1 + 1",
        "body.user_id == session.user_id",
        "listeners.exists(p, listeners[p].listen.count > 0)",
    ] {
        let bare = Parser::new().parse(src).expect("parses");
        let (kept, _) = Parser::new()
            .parse_with_source_info(src)
            .expect("parses the same way");
        assert_eq!(
            format!("{bare:?}"),
            format!("{kept:?}"),
            "diverged on {src}"
        );
    }

    // And a parse ERROR still carries the map, which is the path upstream already had.
    let errs = Parser::new()
        .parse_with_source_info("1 +")
        .expect_err("malformed expression");
    assert!(
        errs.errors.iter().any(|e| e.source_info.is_some()),
        "the error path lost the source map it used to carry"
    );
}

/// Visit every `IdedExpr` in the tree, including the ones macros desugared into comprehensions.
fn walk(node: &IdedExpr, f: &mut impl FnMut(&IdedExpr)) {
    f(node);
    match &node.expr {
        Expr::Call(c) => {
            if let Some(t) = &c.target {
                walk(t, f);
            }
            c.args.iter().for_each(|a| walk(a, f));
        }
        Expr::Comprehension(c) => {
            walk(&c.iter_range, f);
            walk(&c.accu_init, f);
            walk(&c.loop_cond, f);
            walk(&c.loop_step, f);
            walk(&c.result, f);
        }
        Expr::List(l) => l.elements.iter().for_each(|e| walk(e, f)),
        Expr::Map(m) => m.entries.iter().for_each(|e| match &e.expr {
            EntryExpr::MapEntry(entry) => {
                walk(&entry.key, f);
                walk(&entry.value, f);
            }
        }),
        Expr::Select(s) => walk(&s.operand, f),
        Expr::Ident(_) | Expr::Literal(_) | Expr::Unspecified => {}
    }
}
