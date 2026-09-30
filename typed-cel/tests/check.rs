//! The checker: a typed fold over `IdedExpr`.
//!
//! Upstream has no checker at all, so `body.no_such_field` is an evaluation-time error in
//! production. Everything here is about moving that to build time, with a message the author can
//! act on.

#[path = "support/mod.rs"]
mod support;

use typed_cel::CompileOpts;
use support::{err, err_mentions, ok};

#[test]
fn a_declared_field_checks() {
    ok("body.user_id == session.user_id");
    ok("body.amount > 100 && session.tenant_id == body.tenant_id");
}

#[test]
fn an_unknown_field_is_an_error() {
    // THE diagnostic this whole crate exists to produce: the field, the record it is missing
    // from, and the roster of what does exist.
    err_mentions(
        "body.no_such_field == session.user_id",
        ["no_such_field", "body", "user_id"].as_ref(),
    );
}

#[test]
fn an_unknown_field_in_a_comprehension_is_an_error() {
    // Proves the iteration variable is bound to the ELEMENT RECORD and not to `Dyn`. Binding it
    // to `Dyn` silently type-checks every field access inside every comprehension body.
    err_mentions(
        "body.documents.all(d, d.no_such_field == session.user_id)",
        ["no_such_field", "owner_id"].as_ref(),
    );
    err_mentions(
        "body.documents.exists(d, d.nope == session.user_id)",
        ["nope"].as_ref(),
    );
    err_mentions(
        "body.documents.filter(d, d.nope == 'x').size() == 1",
        ["nope"].as_ref(),
    );
    ok("body.documents.all(d, d.owner_id == session.user_id)");
    ok("body.documents.exists(d, d.owner_id == session.user_id)");
    ok("body.documents.exists_one(d, d.owner_id == session.user_id)");
    ok("body.documents.filter(d, d.id == 'doc_1').size() == 1");
    ok("body.documents.map(d, d.owner_id).size() == 1");
}

#[test]
fn the_iteration_variable_is_scoped_to_its_comprehension() {
    err_mentions(
        "d.owner_id == session.user_id",
        ["undeclared", "d"].as_ref(),
    );
    err("body.documents.all(d, d.id == 'x') && d.id == 'y'");
    // An inner comprehension's variable shadows an outer one without leaking. `locals` is
    // truncated back to its entry length on the way out, never popped a fixed number of times.
    ok("a.all(x, b.all(x, x.id == 'k')) && a.all(x, x.owner_id == 'k')");
}

#[test]
fn nested_comprehensions_check() {
    ok("a.all(x, b.exists(y, x.id == y.id))");
    err_mentions("a.all(x, b.exists(y, x.nope == y.id))", ["nope"].as_ref());
    err_mentions("a.all(x, b.exists(y, x.id == y.nope))", ["nope"].as_ref());
}

#[test]
fn an_undeclared_variable_is_an_error() {
    let rendered = err_mentions("whatever.x == 1", ["whatever", "undeclared"].as_ref());
    // The declared roster, so the author can see what they meant to type.
    assert!(rendered.contains("session"), "{rendered}");
    assert!(rendered.contains("body"), "{rendered}");
}

#[test]
fn unknown_session_and_context_fields_are_errors() {
    err_mentions("session.does_not_exist == 'x'", ["does_not_exist"].as_ref());
    err_mentions("context.does_not_exist > 1", ["does_not_exist"].as_ref());
    ok("context.risk_score < 0.9");
}

#[test]
fn nested_field_access_checks() {
    ok("body.project.owner.id == session.user_id");
    err_mentions(
        "body.project.owner.nope == session.user_id",
        ["nope"].as_ref(),
    );
    err_mentions("body.project.nope.id == session.user_id", ["nope"].as_ref());
}

#[test]
fn field_access_on_a_scalar_is_an_error() {
    err_mentions(
        "body.user_id.anything == 'x'",
        ["anything", "string"].as_ref(),
    );
    err_mentions("body.amount.anything > 1", ["anything", "double"].as_ref());
}

#[test]
fn field_access_on_a_map_yields_the_value_type() {
    // Maps have no declared field set; records do. `m` is `map(string, double)`.
    ok("has(m.anything) && m.anything > 1");
    err("m.anything == 'x'");
}

#[test]
fn a_dyn_must_be_narrowed() {
    // `Dyn` is `unknown`, not `any` — "the narrowing contract".
    err_mentions("body.blob > 1", ["dyn"].as_ref());
    err_mentions("body.blob.anything == 'x'", ["dyn", "declare"].as_ref());
    err("body.blob + 1 > 2");
    // Existence is the one question a `dyn` still answers (`removed: dyn values`): nullness,
    // membership and equality are all uses of the value.
    ok("has(body.blob)");
    for src in [
        "body.blob == null",
        "body.blob != null",
        "'k' in body.blob",
        "'k' in body.open && body.open['k'] == null",
        "body.open == {}",
        "{} == body.open",
        "body.open.exists(k, k == 'a')",
    ] {
        err_mentions(src, ["dyn", "removed: dyn values"].as_ref());
    }
    // An OPEN object derives `map(string, dyn)`, not a `Dyn`: presence under it still checks, and
    // so does its size, which asks nothing of the values.
    ok("has(body.open.k)");
    ok("size(body.open) > 0");
    err_mentions("'k' in body.open && body.open['k'] > 1", ["dyn"].as_ref());
}

#[test]
fn an_integer_literal_checks_against_a_num_field() {
    // The number-model payoff: one numeric type means both spellings compile with no coercion.
    ok("body.amount > 100");
    ok("100 < body.amount");
    ok("body.amount == 100");
    ok("body.amount > 100.0");
}

#[test]
fn list_and_map_literals_check() {
    ok("body.id in ['a', 'b']");
    ok("{'k': 1}['k'] == 1");
    ok("body.tags == ['a', 'b']");
    err("body.amount in ['a', 'b']");
}

#[test]
fn indexing_a_record_with_a_string_literal_checks_the_field() {
    // `diverges: literal-key record index`. Backtick quoting is a known bug, so a dashed field is
    // reachable only by index — and typing `headers` as a map to make it resolve would discard
    // unknown-key detection for the variables an attacker most influences.
    ok("headers['content-type'] == 'application/json'");
    err_mentions(
        "headers['no-such-header'] == 'x'",
        ["no-such-header", "content-type"].as_ref(),
    );
    // A non-literal index into a record is an error, not a `Dyn`.
    err_mentions(
        "body.documents.all(d, headers[d.id] == 'x')",
        ["computed key"].as_ref(),
    );
}

#[test]
fn a_duration_compares_only_with_a_duration() {
    ok("signals.ready.elapsed > duration('5m')");
    // A dropped unit suffix is a build error rather than a comparison against nanoseconds.
    err_mentions(
        "signals.ready.elapsed > 300",
        ["duration", "double"].as_ref(),
    );
    // And the alias, which is the same expression written the way an author writes it.
    ok("signals.ready.elapsed > 5m");
    ok("uptime > 40s && metrics.cpu.max['40s'] < 0.05");
}

#[test]
fn a_deleted_construct_is_rejected_by_the_checker_too() {
    // Belt and braces over the removals: each fails HERE with a dialect message, even where the
    // spelling reached the AST rather than dying at the parser.
    err_mentions("dyn(body.amount) == 1", ["dyn()"].as_ref());
    err_mentions(
        "timestamp('2026-01-01T00:00:00Z') < uptime",
        ["timestamp"].as_ref(),
    );
    err_mentions("type(body.amount) == 1", ["type values"].as_ref());
    err_mentions("uint(body.amount) == 1", ["uint"].as_ref());
    err_mentions("int(body.amount) == 1", ["int()"].as_ref());
}

#[test]
fn the_checker_terminates_on_a_deep_expression() {
    // A deeply nested expression hits the depth bound rather than overflowing the stack. The
    // parser recurses first, so the bound is on the source — but the checker recurses too, and
    // this asserts the whole pipeline survives.
    let deep = format!("{}body.amount{} > 1", "(".repeat(400), ")".repeat(400));
    let rendered = err(&deep);
    assert!(
        rendered.contains("nests"),
        "expected a depth refusal, got:\n{rendered}"
    );
}

#[test]
fn every_check_error_is_available() {
    // `Checker::run` has always returned a `Vec<CheckError>` and `compile` took `.next()` and
    // dropped the rest. Rendering only the first is right — a cascade is a diagnostic nobody reads
    // — but a policy compiler listing a file's problems wants every one, and dropping them at the
    // boundary meant it could never have them.
    let env = support::env();
    let err = env
        .compile(
            "body.no_such_a == 'x' && session.no_such_b == 'y'",
            &CompileOpts::default(),
        )
        .expect_err("two unknown fields must not compile");

    let all = err.all();
    assert_eq!(all.len(), 2, "{all:#?}");
    assert!(all[0].message.contains("no_such_a"), "{:?}", all[0]);
    assert!(all[1].message.contains("no_such_b"), "{:?}", all[1]);

    // …and `Display` still renders only the first. Counting the diagnostic LINES rather than
    // grepping for the second field name, because the rendering echoes the source — which contains
    // both names — and a naive `!contains` would be asserting nothing about the cascade.
    let rendered = err.to_string();
    assert!(rendered.contains("no_such_a"), "{rendered}");
    assert_eq!(
        rendered.matches("no field `").count(),
        1,
        "the rendering cascaded: {rendered}"
    );

    // Empty for anything that is not a check failure, so a caller can call it unconditionally.
    assert!(env
        .compile("body.user_id ==", &CompileOpts::default())
        .unwrap_err()
        .all()
        .is_empty());
}

#[test]
fn a_removal_message_names_the_dialect_not_the_product() {
    // These are STRINGS: no compiler and no type check will ever find them, and
    // `tests/purity.rs::the_library_names_no_host_concept` cannot tell a rationale from a noun
    // once one is phrased without a banned word. This is the test that does, and it names the
    // specific messages — which means adding a row here whenever a removal is added.
    let env = support::env();
    for (expr, must_say) in [
        ("timestamp('2026-01-01T00:00:00Z') < uptime", "timestamp"),
        ("body.user_id.orValue('x') == 'y'", "optional"),
    ] {
        let rendered = env
            .compile(expr, &CompileOpts::default())
            .expect_err(&format!("`{expr}` must not compile"))
            .to_string();
        assert!(rendered.contains(must_say), "{expr}: {rendered}");
        // It cites the README row a reader can act on…
        assert!(
            rendered.contains("README.md"),
            "`{expr}` does not cite its README row: {rendered}"
        );
        // …and does NOT explain the host application's reasons in library output.
        for product in ["sandbox", "policy", "grant", "guest", "broker"] {
            assert!(
                !rendered.to_ascii_lowercase().contains(product),
                "`{expr}` names the product (`{product}`) instead of the dialect: {rendered}"
            );
        }
    }
}

#[test]
fn a_record_is_built_without_naming_rc() {
    // The struct-literal form needs `Rc`, `BTreeSet` and four fields at every roster site — which
    // is why the same private `record()` helper existed twice already. This file imports neither.
    let mut env = typed_cel::CelEnvironment::new();
    env.declare(
        "sess",
        typed_cel::Record::new("sess", [("user_id", typed_cel::CelTy::Str)]),
    );
    env.declare(
        "opt",
        typed_cel::Record::new(
            "opt",
            [("a", typed_cel::CelTy::Str), ("b", typed_cel::CelTy::Str)],
        )
        .with_optional(["a"]),
    );
    env.declare(
        "hdrs",
        typed_cel::Record::new("hdrs", [("host", typed_cel::CelTy::Str)])
            .with_index(typed_cel::CelTy::Str, typed_cel::CelTy::Str),
    );

    assert!(env
        .compile("sess.user_id == 'u'", &CompileOpts::default())
        .is_ok());
    // An optional field is nameable, but a read of it must be PROVEN present (proven presence):
    // unguarded it is refused, guarded it compiles.
    assert!(env
        .compile("opt.a == opt.b", &CompileOpts::default())
        .is_err());
    assert!(env
        .compile(
            "has(opt.a) && has(opt.b) && opt.a == opt.b",
            &CompileOpts::default()
        )
        .is_ok());
    // The index signature keeps an undeclared key nameable — and, like an optional field, a read
    // of one is proven present first.
    assert!(env
        .compile("hdrs['x-trace-id'] == 'abc'", &CompileOpts::default())
        .is_err());
    assert!(env
        .compile(
            "'x-trace-id' in hdrs && hdrs['x-trace-id'] == 'abc'",
            &CompileOpts::default()
        )
        .is_ok());
    assert!(
        env.compile("sess.nope == 'u'", &CompileOpts::default())
            .is_err(),
        "a builder-made record must still catch an unknown field"
    );
}

/// An empty collection has no element to type it, so it takes the type its USE asks for — the
/// fresh element type variable the cel-spec checker gives `[]` — rather than `dyn`, which nothing
/// accepts. A folded empty known list is spelled `[]`, so this is also what lets such a residual
/// check.
#[test]
fn an_empty_collection_takes_the_type_its_use_asks_for() {
    for expr in [
        "body.name in []",
        "!(body.amount in [])",
        "[] == body.tags",
        "body.tags == []",
        "body.tags != []",
        "size([]) == 0",
        "[].exists(x, x == body.name)",
        "[].all(x, x.startsWith(body.name))",
        "[].filter(x, body.name.startsWith(x)).size() > 0",
        "[].exists_one(x, body.name.startsWith(x))",
        "[].map(x, x + '/') == body.tags",
        "body.name in [].map(x, x + '/')",
        "body.name in [].filter(x, x == body.name)",
        "[].filter(x, x == body.name) == body.tags",
        "body.name in {}",
        "m == {}",
        "{} == m",
        // A literal whose members are all unpinned is itself unpinned, and an unpinned member
        // takes its siblings' type.
        "[[]] != [[]]",
        "[[], body.tags] == [body.tags]",
    ] {
        ok(expr);
    }
}

#[test]
fn a_non_empty_literal_keeps_its_element_type() {
    err_mentions("[1] == ['a']", &["=="]);
    err_mentions("body.name in [1, 2]", &["in"]);
    err_mentions("body.tags == [1]", &["=="]);
}

/// A `dyn` produced anywhere — a heterogeneous literal, an index into an empty one, a derived
/// `unknown` member — is refused where it is used.
#[test]
fn a_dyn_is_refused_wherever_it_is_used() {
    err_mentions(r#"{"s": 1.0, "t": "a"}.o == 'x'"#, &["dyn"]);
    err_mentions("[][0] + 'a' == body.name", &["dyn"]);
    err_mentions("body.blob > 1", &["dyn"]);
    err_mentions("[1] == ['a']", &["=="]);
}

/// The body of a fold over an empty range never runs, but it is still walked for demand.
#[test]
fn a_fold_over_an_empty_range_still_demands_what_its_body_names() {
    let p = support::env()
        .compile(
            "[].exists(x, body.name.startsWith(x))",
            &CompileOpts::default(),
        )
        .expect("checks");
    let rendered = p.demand().to_string();
    assert!(rendered.contains("body ▸ \"name\""), "{rendered}");
}

/// `unsafe_map` (`added: unsafe_map`) differs from `map` ONLY in the presence rules. To every
/// operator it is a map: whatever compiles against a `map` compiles against it, to the same answer.
#[test]
fn an_unsafe_map_is_a_map_to_every_operator() {
    use typed_cel::{CelEnvironment, CelTy};
    let mut env = CelEnvironment::new();
    env.declare("u", CelTy::unsafe_map(CelTy::Str, CelTy::Num));
    env.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    let binding = serde_json::json!({"a": 2});
    let answer = |src: &str| {
        let program = env
            .compile(src, &CompileOpts::default())
            .unwrap_or_else(|e| panic!("`{src}`: {e}"));
        let mut act = env.activation();
        act.bind("u", &binding).unwrap();
        act.bind("m", &binding).unwrap();
        program
            .evaluate(&act)
            .unwrap_or_else(|e| panic!("`{src}`: {e}"))
    };
    // A READ is where the two differ — `m['a']` must be proven present, `u['a']` need not be
    // (`tests/presence.rs`) — so each read form carries the guard a `map` needs; on `u` it is
    // redundant and changes nothing.
    for form in [
        "'a' in X && X['a'] > 1",
        "'a' in X",
        "size(X) > 0",
        "X.all(k, X[k] > 0)",
        "X.exists(k, k == 'a')",
        "has(X.a) && X.a > 1",
        "X == m",
        "X == u",
        "[X, m].size() == 2",
        "(true ? X : m) == m",
    ] {
        let over_u = form.replace('X', "u");
        let over_m = form.replace('X', "m");
        assert_eq!(
            answer(&over_u),
            answer(&over_m),
            "`{over_u}` and `{over_m}` disagree"
        );
    }
}

#[test]
fn unsafe_map_prints_its_name() {
    use typed_cel::{CelEnvironment, CelTy};
    assert_eq!(
        CelTy::unsafe_map(CelTy::Str, CelTy::Num).name(),
        "unsafe_map(string, double)"
    );
    // A diagnostic quoting the type spells it the way the declarer wrote it.
    let mut env = CelEnvironment::new();
    env.declare("u", CelTy::unsafe_map(CelTy::Str, CelTy::Num));
    let e = env
        .compile("u + 1 > 0", &CompileOpts::default())
        .unwrap_err()
        .to_string();
    assert!(e.contains("unsafe_map(string, double)"), "{e}");
}

/// The optional-syntax refusals say what is TRUE: absence is real, and it is proven away with
/// `has()` / `in` — not that every declared path is present, which stopped being the design.
#[test]
fn the_optional_syntax_message_tells_the_truth() {
    use typed_cel::{CelEnvironment, CelTy, Record};
    let mut env = CelEnvironment::new();
    env.declare(
        "body",
        Record::new("body", [("x", CelTy::Num), ("y", CelTy::Num)]).with_optional(["x"]),
    );
    for src in ["optional(1) == 1", "body.y.orValue(0) == 1", "body.?x == 1"] {
        let e = env
            .compile(src, &CompileOpts::default())
            .expect_err("optional syntax is removed")
            .to_string();
        assert!(e.contains("has("), "`{src}`: {e}");
        assert!(e.contains("in m"), "`{src}`: {e}");
        assert!(
            !e.contains("every declared path is present"),
            "`{src}`: {e}"
        );
    }
}
