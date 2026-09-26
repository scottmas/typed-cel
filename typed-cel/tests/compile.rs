//! The public API, and diagnostics that point at the mistake.
//!
//! Owning the parser is what makes the last of these possible: upstream keeps its source map only
//! for parse errors, and a type error arrives later with nothing but expression ids.

#[path = "support/mod.rs"]
mod support;

use support::{env, err, err_raw};
use typed_cel::{CelEnvironment, CelError, CelProgram, CelTy};

#[test]
fn a_parse_error_is_a_compile_error() {
    let rendered = err("body.user_id ==");
    // `ParseErrors` is a COLLECTION, and its `Display` prints every error with its own caret.
    // Taking `.errors[0]` throws away the rest, and the discarded ones are often the informative
    // ones — so the whole rendering comes through.
    assert!(
        rendered.contains("body.user_id =="),
        "the rendering must quote the source:\n{rendered}"
    );
    assert!(
        rendered.contains('^'),
        "the rendering must carry the parser's own caret:\n{rendered}"
    );
    assert!(
        matches!(err_raw("body.user_id =="), CelError::Parse { .. }),
        "a parse failure must stay a parse failure"
    );
}

#[test]
fn a_type_error_is_a_compile_error() {
    let rendered = err("body.amount > session.user_id");
    assert!(rendered.contains("double"), "{rendered}");
    assert!(rendered.contains("string"), "{rendered}");
}

#[test]
fn a_non_boolean_expression_is_rejected() {
    for (expr, ty) in [
        ("body.user_id", "string"),
        ("body.amount", "double"),
        ("body.items", "list"),
        // A `revoke_after` is a DECISION, not a measurement.
        ("files['/a'].closed.elapsed", "duration"),
    ] {
        let rendered = err(expr);
        assert!(
            rendered.contains("bool") && rendered.contains(ty),
            "`{expr}` should be refused as {ty}, got:\n{rendered}"
        );
    }
}

#[test]
fn a_dyn_result_is_rejected() {
    // Uncertainty must not become authorization, and must not become revocation either. The
    // comparison is for EQUALITY with `bool`, never "compatible with bool" — a `dyn` will evaluate
    // to something, and the evaluator would treat a non-bool as a failed condition.
    let rendered = err("body.blob");
    assert!(rendered.contains("dyn"), "{rendered}");
    assert!(rendered.contains("bool"), "{rendered}");
}

#[test]
fn the_diagnostic_names_the_available_fields() {
    let rendered = err("body.documents.all(d, d.owner_id == session.user)");
    assert!(rendered.contains("session"), "{rendered}");
    assert!(rendered.contains("user"), "{rendered}");
    for field in ["user_id", "tenant_id", "roles"] {
        assert!(
            rendered.contains(field),
            "the roster must list `{field}`:\n{rendered}"
        );
    }
    // And structured, so a policy compiler can place it in a file rather than re-parse prose.
    match err_raw("body.documents.all(d, d.owner_id == session.user)") {
        CelError::Check { available, .. } => {
            let available = available.expect("an unknown field carries its roster");
            assert!(available.contains(&"user_id".to_string()), "{available:?}");
        }
        other => panic!("expected a check error, got {other:?}"),
    }
}

#[test]
fn the_diagnostic_points_at_authored_columns() {
    // THE test that proves owning the parser paid for itself: `Parser::parse_with_source_info`
    // keeps the map on the SUCCESS path, and the desugarer's `SpanMap` undoes its own byte shifts.
    let authored = "body.nope == 'x'";
    let span = err_raw(authored).span().expect("a check error has a span");
    assert!(
        span.start <= authored.find("nope").unwrap() && span.end >= authored.find("nope").unwrap(),
        "the caret should sit on `nope`, got {span:?} in {authored:?}"
    );

    // And through a duration rewrite, which grows `30s` by 12 bytes so every later offset shifts.
    let authored = "uptime > 30s && body.nope == 'x'";
    let span = err_raw(authored).span().expect("a check error has a span");
    let nope = authored.find("nope").unwrap();
    assert!(
        span.start <= nope && span.end >= nope,
        "the caret should sit on `nope` at {nope}, got {span:?} in {authored:?}"
    );
    // The rendering quotes what the author typed, never the desugared form.
    let rendered = err(authored);
    assert!(rendered.contains("uptime > 30s"), "{rendered}");
    assert!(!rendered.contains("duration('30s')"), "{rendered}");
}

#[test]
fn one_environment_serves_many_expressions() {
    // Asserted by CONSTRUCTION — `compile` takes `&self` — not by timing.
    let env = env();
    for expr in [
        "body.user_id == session.user_id",
        "body.amount > 100",
        "body.documents.all(d, d.owner_id == session.user_id)",
    ] {
        env.compile(expr).unwrap_or_else(|e| panic!("{expr}: {e}"));
    }
}

#[test]
fn no_custom_functions_are_registered() {
    let rendered = err("is_owner(body.user_id)");
    assert!(rendered.contains("unknown function"), "{rendered}");
    // And the runtime `Context` this crate builds has none either: an activation over an empty
    // environment resolves nothing but the standard library.
    let env = CelEnvironment::new();
    assert!(env.compile("is_owner('x')").is_err());
}

#[test]
fn a_program_is_send_and_sync() {
    // A compiled policy is shared across request-handling threads AND across the poll loop.
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<CelProgram>();
}

#[test]
fn a_schema_translation_failure_is_its_own_error() {
    // A schema whose type cannot be derived must not arrive as a checker error about a field.
    let mut env = CelEnvironment::new();
    env.declare("body", CelTy::Dyn);
    let rendered = err_raw_in(&env, "body.anything == 'x'").to_string();
    assert!(rendered.contains("dyn"), "{rendered}");
}

fn err_raw_in(env: &CelEnvironment, expr: &str) -> CelError {
    match env.compile(expr) {
        Ok(_) => panic!("expected `{expr}` to fail"),
        Err(e) => e,
    }
}

// ---------------------------------------------------------------------------------------------
// Structural queries — enough to lint an expression's SHAPE, not enough to reimplement the checker.
// ---------------------------------------------------------------------------------------------

/// An environment with the shapes the conjunct tests need, built locally so the shared roster can
/// change without silently changing what these assert.
fn shape_env() -> CelEnvironment {
    let mut e = CelEnvironment::new();
    e.declare("up", CelTy::Duration);
    e.declare("flag", CelTy::Bool);
    e.declare("n", CelTy::Num);
    e.declare("other", CelTy::Num);
    e.declare(
        "rec",
        support::record("rec", &[("c", CelTy::Str), ("y", CelTy::Num)]),
    );
    e.declare("gauge", support::record("gauge", &[("x", CelTy::Num)]));
    e
}

fn shapes(expr: &str) -> Vec<(String, Option<String>, Option<String>)> {
    let program = shape_env()
        .compile(expr)
        .unwrap_or_else(|e| panic!("{expr}: {e}"));
    program
        .conjuncts()
        .into_iter()
        .map(|c| {
            let path = c
                .path
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(" ▸ ");
            let lit = c.literal.map(|l| format!("{l:?}"));
            (path, c.operator, lit)
        })
        .collect()
}

#[test]
fn top_level_conjuncts_are_reported() {
    assert_eq!(
        shapes("up > 5s && rec.c == 'x' && flag"),
        vec![
            (
                "up".into(),
                Some(">".into()),
                Some("Duration(\"5s\")".into())
            ),
            (
                "rec ▸ \"c\"".into(),
                Some("==".into()),
                Some("Str(\"x\")".into())
            ),
            ("flag".into(), None, None),
        ],
        "three conjuncts, in SOURCE order"
    );
}

#[test]
fn a_conjunct_carries_its_path_operator_and_literal() {
    // The path uses the same `Segment` vocabulary `DemandSet` does, so a caller matches against
    // ONE thing and not two.
    let one = shapes("up > 40s");
    assert_eq!(
        one,
        vec![(
            "up".into(),
            Some(">".into()),
            Some("Duration(\"40s\")".into())
        )]
    );
}

#[test]
fn a_duration_literal_is_reported_as_the_author_wrote_it() {
    // `40s` desugars to `duration('40s')` BEFORE the parser sees it. A naive reader reports the
    // literal as the string `40s` under a call it did not expect, or reports no literal at all —
    // and a window-guard lint built on that approves the expression it exists to reject.
    assert_eq!(
        shapes("up > 40s"),
        shapes("up > duration('40s')"),
        "the alias and its expansion must report the same conjunct"
    );
}

#[test]
fn a_non_literal_conjunct_is_reported_without_a_literal() {
    // `n > other.…` — nothing constant on the right. The row is still REPORTED, with `literal:
    // None`. A lint that silently skips what it cannot read is a lint that passes the expression
    // it was written to catch.
    assert_eq!(
        shapes("gauge.x > n"),
        vec![("gauge ▸ \"x\"".into(), Some(">".into()), None)]
    );
}

#[test]
fn disjunction_is_not_flattened() {
    // `&&` is the only connective a guard can be proven through. Treating `||` as a conjunct would
    // let `n < 0.05 || up > 40s` pass a guard check it does not satisfy.
    let disjoined = shapes("n < 0.05 || up > 40s");
    assert_eq!(
        disjoined.len(),
        1,
        "`||` is ONE opaque conjunct: {disjoined:?}"
    );
    assert_eq!(disjoined[0].1, None, "an opaque conjunct names no operator");
    assert_eq!(disjoined[0].2, None, "an opaque conjunct names no literal");

    // …and the same expression with `&&` genuinely is two.
    assert_eq!(shapes("n < 0.05 && up > 40s").len(), 2);

    // A disjunction nested under a top-level `&&` stays opaque too — the `&&` splits, the `||`
    // does not.
    let mixed = shapes("flag && (n < 0.05 || up > 40s)");
    assert_eq!(mixed.len(), 2, "{mixed:?}");
    assert_eq!(mixed[1].1, None, "the `||` arm stayed opaque: {mixed:?}");
}

#[test]
fn the_query_does_not_expose_the_ast() {
    // The returned type is OWNED and names no absorbed type, so making the fork private did not
    // have to revisit this API. Compiling this at all is the assertion.
    let program: CelProgram = shape_env().compile("up > 40s && flag").unwrap();
    let conjuncts: Vec<typed_cel::Conjunct> = program.conjuncts();
    let _: &[typed_cel::Segment] = &conjuncts[0].path;
    let _: &Option<String> = &conjuncts[0].operator;
    let _: &Option<typed_cel::Literal> = &conjuncts[0].literal;
    // Owned: it outlives the program.
    drop(program);
    assert_eq!(conjuncts.len(), 2);
}

#[test]
fn a_comprehension_is_one_opaque_conjunct() {
    let mut e = CelEnvironment::new();
    e.declare("flag", CelTy::Bool);
    e.declare(
        "m",
        CelTy::map(CelTy::Str, support::record("entry", &[("n", CelTy::Num)])),
    );
    let program = e.compile("flag && m.exists(k, m[k].n > 0.0)").unwrap();
    let conjuncts = program.conjuncts();
    assert_eq!(conjuncts.len(), 2, "{conjuncts:?}");
    assert_eq!(conjuncts[1].operator, None);
    assert_eq!(conjuncts[1].literal, None);
}
