//! Bounds, because the fork arrived with none.
//!
//! An expression over attacker-controlled data is bounded by this crate or not at all.

#[path = "support/mod.rs"]
mod support;

use support::{env, err};
use typed_cel::CelLimits;

#[test]
fn a_deeply_nested_expression_is_refused_before_parsing() {
    // 4000 open parens would overflow ANTLR's generated parser, so the refusal has to happen
    // BEFORE `CELParser::start` — measuring depth by walking the parsed AST measures after the
    // hazard.
    let deep = format!("{}body.amount{} > 1", "(".repeat(4000), ")".repeat(4000));
    let rendered = err(&deep);
    assert!(
        rendered.contains("nests") && rendered.contains("limit"),
        "expected a depth refusal naming the limit, got:\n{rendered}"
    );
}

#[test]
fn a_quadratic_comprehension_is_refused_at_build() {
    // Three nested comprehensions is a runtime that is a product of three attacker-controlled
    // lengths. Refused when a human is present to read the error.
    let rendered = err("a.all(x, b.all(y, c.all(z, x.id == z.id)))");
    assert!(
        rendered.contains("cost") && rendered.contains("limit"),
        "the refusal must name the estimate and the limit, got:\n{rendered}"
    );
    // Two levels is legal, so the line is where the plan puts it and not wherever it fell.
    env()
        .compile("a.all(x, b.exists(y, x.id == y.id))")
        .expect("two nested comprehensions must still compile");
}

#[test]
fn an_oversized_list_is_refused_at_activation() {
    // Capping at evaluation time is too late: `execute` cannot be interrupted once it has started,
    // so the cap is a precondition of CONSTRUCTING the activation.
    let env = env();
    // One over the default cap. The elements are never looked at: the length alone refuses.
    let len = CelLimits::default().max_list_len + 1;
    let documents = vec![serde_json::Value::Null; len];
    let body = serde_json::json!({
        "user_id": "u", "owner_id": "u", "tenant_id": "t", "amount": 1.0,
        "name": "n", "note": "n", "email": "e", "id": "i",
        "items": [], "documents": documents, "tags": [],
        "project": {"owner": {"id": "u"}}, "blob": null, "open": {},
    });
    let mut activation = env.activation();
    let err = activation
        .bind("body", &body)
        .err()
        .expect("an oversized list must be refused");
    let rendered = err.to_string();
    assert!(
        rendered.contains(&len.to_string()) && rendered.contains("limit"),
        "the refusal must name the size and the limit, got:\n{rendered}"
    );
}

#[test]
fn a_total_element_budget_is_enforced() {
    // A per-collection cap alone is bypassed by BREADTH: many small arrays that individually pass.
    let limits = CelLimits {
        max_list_len: 100,
        max_total_elements: 250,
        ..CelLimits::default()
    };
    let mut env = typed_cel::CelEnvironment::with_limits(limits);
    env.declare(
        "grid",
        typed_cel::CelTy::list(typed_cel::CelTy::list(typed_cel::CelTy::Num)),
    );
    let grid: Vec<serde_json::Value> = (0..50)
        .map(|_| serde_json::json!([1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]))
        .collect();
    let mut activation = env.activation();
    let rendered = activation
        .bind("grid", &serde_json::Value::Array(grid))
        .err()
        .expect("50 arrays of 10, each under the per-list cap, must exceed the total")
        .to_string();
    assert!(
        rendered.contains("250"),
        "the refusal must name the total limit, got:\n{rendered}"
    );
}

#[test]
fn bounds_are_configurable_with_documented_defaults() {
    let defaults = CelLimits::default();
    let readme = std::fs::read_to_string(
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("README.md"),
    )
    .expect("README.md");
    for (field, value) in [
        ("max_source_len", defaults.max_source_len.to_string()),
        ("max_depth", defaults.max_depth.to_string()),
        ("max_cost", defaults.max_cost.to_string()),
        ("max_list_len", defaults.max_list_len.to_string()),
        (
            "max_total_elements",
            defaults.max_total_elements.to_string(),
        ),
        ("max_unroll", defaults.max_unroll.to_string()),
    ] {
        let line = readme
            .lines()
            .find(|l| l.trim_start().starts_with(&format!("pub {field}:")))
            .unwrap_or_else(|| panic!("README documents no `{field}`"));
        assert!(
            line.contains(&format!("default {value}")),
            "README says `{line}`, the default is {value}"
        );
    }

    // And they are one struct, so a caller changes them together.
    let strict = CelLimits {
        max_source_len: 16,
        ..CelLimits::default()
    };
    let env = typed_cel::CelEnvironment::with_limits(strict);
    assert!(env.compile("1 == 1 && 1 == 1 && 1 == 1").is_err());
}

#[test]
fn a_system_expression_is_bounded_too_but_differently() {
    // The system environment binds no attacker-controlled list, so `max_list_len` is irrelevant
    // there. What matters is that a per-tick evaluation is bounded at BUILD time — an HTTP
    // assertion runs once per request, a system expression runs on every tick, forever.
    let env = env();
    let program = env
        .compile("listeners.exists(p, listeners[p].listen.elapsed > 10s)")
        .expect("the listen(*) shape must compile");

    // 10 000 listeners, evaluated inside a tick budget.
    let mut listeners = serde_json::Map::new();
    for port in 0..10_000u32 {
        listeners.insert(
            port.to_string(),
            serde_json::json!({
                "listen": {"elapsed": "0s", "count": 0.0},
                "accept": {"elapsed": "0s", "count": 0.0},
            }),
        );
    }
    let mut limits = CelLimits::default();
    limits.max_total_elements = 1_000_000;
    let mut wide = typed_cel::CelEnvironment::with_limits(limits);
    wide.declare("listeners", env.types().get("listeners").unwrap().clone());
    let mut activation = wide.activation();
    activation
        .bind("listeners", &serde_json::Value::Object(listeners))
        .expect("the system state is not attacker-bounded, only policy-bounded");

    let start = std::time::Instant::now();
    let fired = program
        .evaluate(&activation)
        .expect("a well-typed system expression evaluates");
    let elapsed = start.elapsed();
    assert!(
        !fired,
        "nothing has listened for 10s in a zero-valued state"
    );
    assert!(
        elapsed < std::time::Duration::from_millis(500),
        "a 10 000-entry state took {elapsed:?}, which does not fit a 1s tick with room for the \
         rest of the policy"
    );
}
