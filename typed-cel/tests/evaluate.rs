//! Binding, and evaluation as the LIBRARY defines it: `Ok(true)` / `Ok(false)` / `Err`.
//!
//! What a non-`Ok(true)` outcome should CAUSE is not decided here and is not decidable here — it
//! points a different way at every call site. The fail-closed directions belong to the caller.

#[path = "support/mod.rs"]
mod support;

use serde_json::json;
use support::{env, record, record_opt};
use typed_cel::{CelEnvironment, CelTy};

/// A body carrying every required field of the shared environment's `body` record.
fn body(overrides: serde_json::Value) -> serde_json::Value {
    let mut base = json!({
        "user_id": "user_123", "owner_id": "user_123", "tenant_id": "tenant_456",
        "amount": 1.0, "name": "πέντε", "note": "n", "email": "a@example.com",
        "id": "user_123",
        "items": [], "documents": [], "tags": [],
        "project": {"owner": {"id": "user_123"}},
        "blob": null, "open": {},
    });
    let (serde_json::Value::Object(base_map), serde_json::Value::Object(over)) =
        (&mut base, overrides)
    else {
        unreachable!()
    };
    for (k, v) in over {
        base_map.insert(k, v);
    }
    base
}

fn session() -> serde_json::Value {
    json!({
        "user_id": "user_123", "tenant_id": "tenant_456",
        "roles": ["admin"], "allowed_ids": ["user_123", "user_456"],
    })
}

/// Compile against the shared environment and evaluate.
fn assertion(expr: &str, body_json: serde_json::Value) -> Result<bool, String> {
    let env = env();
    let program = env.compile(expr).unwrap_or_else(|e| panic!("{expr}: {e}"));
    let mut activation = env.activation();
    activation
        .bind("body", &body_json)
        .and_then(|a| a.bind("session", &session()))
        .map_err(|e| e.to_string())?;
    program.evaluate(&activation).map_err(|e| e.to_string())
}

#[test]
fn equality_holds_and_fails() {
    assert_eq!(
        assertion("body.user_id == session.user_id", body(json!({}))),
        Ok(true)
    );
    assert_eq!(
        assertion(
            "body.user_id == session.user_id",
            body(json!({"user_id": "user_999"}))
        ),
        Ok(false)
    );
}

#[test]
fn all_over_a_list_of_objects() {
    let conforming = body(json!({"documents": [
        {"id": "doc_1", "owner_id": "user_123"},
        {"id": "doc_2", "owner_id": "user_123"},
    ]}));
    let foreign = body(json!({"documents": [
        {"id": "doc_1", "owner_id": "user_123"},
        {"id": "doc_2", "owner_id": "user_999"},
    ]}));
    let expr = "body.documents.all(d, d.owner_id == session.user_id)";
    assert_eq!(assertion(expr, conforming), Ok(true));
    assert_eq!(assertion(expr, foreign), Ok(false));
}

#[test]
fn an_empty_list_satisfies_all() {
    // "Every document belongs to me" IS satisfied by a response with no documents. Pinned so
    // nobody later "fixes" it into a deny.
    assert_eq!(
        assertion(
            "body.documents.all(d, d.owner_id == session.user_id)",
            body(json!({"documents": []}))
        ),
        Ok(true)
    );
}

#[test]
fn a_missing_optional_field_is_a_deny() {
    // `{"a?": "string"}` declared, `a` absent at runtime. An assertion that CANNOT be evaluated
    // must not become a pass. Filling the hole with `null` would also make `body.a == body.b` true
    // when NEITHER exists.
    let mut env = CelEnvironment::new();
    env.declare(
        "body",
        record_opt("body", &[("a", CelTy::Str), ("b", CelTy::Str)], &["a", "b"]),
    );
    let program = env.compile("body.a == 'x'").unwrap();
    let mut activation = env.activation();
    activation.bind("body", &json!({})).unwrap();
    let outcome = program.evaluate(&activation);
    assert!(
        outcome.is_err(),
        "a missing field must not evaluate: {outcome:?}"
    );

    // And the trap it guards: two absent fields must not compare equal.
    let both = env.compile("body.a == body.b").unwrap();
    assert!(both.evaluate(&activation).is_err());
}

#[test]
fn a_null_field_is_not_true() {
    let mut env = CelEnvironment::new();
    env.declare(
        "body",
        record("body", &[("a", CelTy::Null), ("b", CelTy::Str)]),
    );
    let program = env.compile("body.a == 'x'").unwrap();
    let mut activation = env.activation();
    activation
        .bind("body", &json!({"a": null, "b": "y"}))
        .unwrap();
    assert_eq!(program.evaluate(&activation).ok(), Some(false));
}

#[test]
fn an_evaluation_error_is_an_err() {
    let mut env = CelEnvironment::new();
    env.declare("n", CelTy::Num);
    // `0 / n` with `n == 0` is NaN, and NaN has no order: `>` is an evaluation error. (Division by
    // zero itself is IEEE `inf`, not an error — `removed: integer values`.)
    let program = env.compile("0 / n > 0").unwrap();
    let mut activation = env.activation();
    activation.bind("n", &json!(0.0)).unwrap();
    let outcome = program.evaluate(&activation);
    assert!(
        outcome.is_err(),
        "an unordered comparison must not evaluate: {outcome:?}"
    );
}

#[test]
fn a_non_bool_result_is_an_error_not_a_false() {
    // Two arms, and both matter now that `evaluate` returns a bare `Result`: a caller that reads
    // `Ok(false)` as "safe" must never be handed one for a program that did not produce a bool.
    //
    // The BUILD arm is the reachable one — the checker refuses a non-bool result type outright,
    // and a `dyn` cannot be compared at all, so there is no expression that type-checks as `bool`
    // and evaluates to something else.
    let mut env = CelEnvironment::new();
    env.declare("s", CelTy::Str);
    env.declare("d", CelTy::Dyn);
    assert!(
        env.compile("s").is_err(),
        "a string-typed expression must not compile as an assertion"
    );
    assert!(
        env.compile("d == 1.0").is_err(),
        "`dyn` must not be comparable — that is the hole a non-bool result would come through"
    );

    // The RUNTIME arm is therefore unreachable through the public API, which is exactly why the
    // mapping is written as `Ok(Value::Bool(b)) => Ok(b)` with everything else an `Err` rather
    // than `Ok(v) => Ok(v != Value::Bool(false))`: the second is a silent allow-on-error the day
    // the checker gains a hole, and nothing above would catch it.
}

#[test]
fn the_activation_is_the_declared_variables_only() {
    let env = env();
    let mut activation = env.activation();
    let rendered = activation
        .bind("credential", &json!({"token": "secret"}))
        .err()
        .expect("an undeclared name must be refused, not silently ignored")
        .to_string();
    assert!(rendered.contains("credential"), "{rendered}");
    assert!(rendered.contains("not declared"), "{rendered}");
}

#[test]
fn numbers_bind_exactly() {
    // Every JSON number binds as the one number type, an integer held exactly; and whichever
    // representation it lands in, it compares with the others by value.
    assert_eq!(
        assertion(
            "body.amount == 9007199254740993",
            body(json!({"amount": 9007199254740992i64}))
        ),
        Ok(false),
        "a neighbour above 2^53 is a different number"
    );
    assert_eq!(
        assertion("body.amount == 5.0", body(json!({"amount": 5}))),
        Ok(true)
    );
    assert_eq!(
        assertion("body.amount + 0.5 == 5.5", body(json!({"amount": 5u64}))),
        Ok(true)
    );
    for n in [
        json!(5),
        json!(5.0),
        json!(-0.0),
        json!(1e300),
        json!(9007199254740993i64),
        json!(-17),
    ] {
        let amount = n.clone();
        assert_eq!(
            assertion(
                "body.amount == body.amount",
                body(json!({"amount": amount}))
            ),
            Ok(true),
            "{n} did not bind"
        );
    }
    assert_eq!(
        assertion("body.amount > 100", body(json!({"amount": 1e300}))),
        Ok(true)
    );
    assert_eq!(
        assertion("body.amount > 100", body(json!({"amount": 5}))),
        Ok(false)
    );
}

#[test]
fn values_round_trip_faithfully() {
    assert_eq!(
        assertion("body.name == 'πέντε'", body(json!({"name": "πέντε"}))),
        Ok(true)
    );
    assert_eq!(
        assertion(
            "body.project.owner.id == session.user_id",
            body(json!({"project": {"owner": {"id": "user_123"}}}))
        ),
        Ok(true)
    );
    assert_eq!(
        assertion("body.tags == ['a', 'b']", body(json!({"tags": ["a", "b"]}))),
        Ok(true)
    );
    assert_eq!(
        assertion("body.email.endsWith('@example.com')", body(json!({}))),
        Ok(true)
    );
}

#[test]
fn evaluation_returns_a_bare_result() {
    // `evaluate` takes the activation and NOTHING ELSE. There is no disposition argument, because
    // the library has no opinion about what a failure should cause.
    let mut env = CelEnvironment::new();
    env.declare("n", CelTy::Num);
    let program = env.compile("n > 0").unwrap();
    let mut activation = env.activation();
    activation.bind("n", &json!(1.0)).unwrap();

    let outcome: Result<bool, typed_cel::CelError> = program.evaluate(&activation);
    assert_eq!(outcome.unwrap(), true);

    activation.bind("n", &json!(-1.0)).unwrap();
    assert_eq!(program.evaluate(&activation).unwrap(), false);
}

#[test]
fn an_evaluation_error_says_what_went_wrong_and_not_what_to_do() {
    // The direction used to leak through the ERROR TEXT as well as the type — "the grant is
    // revoked" was rendered by the library. Deleting the enum without rewriting the strings would
    // leave the coupling somewhere a grep for the type cannot find it.
    let mut env = CelEnvironment::new();
    env.declare("rec", record_opt("rec", &[("a", CelTy::Str)], &["a"]));
    let program = env.compile("rec.a == 'x'").unwrap();
    let mut activation = env.activation();
    activation.bind("rec", &json!({})).unwrap();

    let rendered = program.evaluate(&activation).unwrap_err().to_string();
    assert!(rendered.contains("rec.a == 'x'"), "{rendered}");
    assert!(rendered.contains("could not be evaluated"), "{rendered}");
    for word in ["denied", "revoked", "permitted", "grant"] {
        assert!(
            !rendered.contains(word),
            "the library said `{word}`: {rendered}"
        );
    }
}
