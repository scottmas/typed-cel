//! `CelEnvironment::specialize` unrolls `exists`/`all`/`map` over a KNOWN range into the chain (or
//! list) the loop computes, bounded by `CelLimits::max_unroll`.
//!
//! Every case asserts the exact residual text. Unless a test says otherwise the known root is
//! `p = {"deny": ["/etc", "/proc"], "l": ["a", "b"], "one": ["a"], "e": [], "m": {"b": 1, "a": 2},
//! "a": ["1", "2"], "b": ["x", "y"], "big": ["e0", …, "e99"]}`; `u` is an unknown record.

mod support;

use serde_json::json;
use support::known::fold_text;
use typed_cel::fork::ast::{EntryExpr, Expr, IdedExpr};
use typed_cel::fork::parser::Parser;
use typed_cel::CompileOpts;
use typed_cel::{CelEnvironment, CelLimits, CelTy, Record};

fn env_with(limits: CelLimits) -> CelEnvironment {
    let strs = || CelTy::list(CelTy::Str);
    let mut env = CelEnvironment::with_limits(limits);
    env.declare(
        "p",
        Record::new(
            "p",
            [
                ("deny", strs()),
                ("l", strs()),
                ("one", strs()),
                ("e", strs()),
                ("m", CelTy::map(CelTy::Str, CelTy::Num)),
                ("a", strs()),
                ("b", strs()),
                ("big", strs()),
            ],
        ),
    );
    env.declare(
        "u",
        Record::new(
            "u",
            [
                ("a", CelTy::Num),
                ("b", CelTy::Bool),
                ("s", CelTy::Str),
                ("path", CelTy::Str),
                ("items", strs()),
                ("l", strs()),
            ],
        ),
    );
    env
}

fn env() -> CelEnvironment {
    env_with(CelLimits::default())
}

fn p() -> serde_json::Value {
    let big: Vec<String> = (0..100).map(|i| format!("e{i}")).collect();
    json!({
        "deny": ["/etc", "/proc"],
        "l": ["a", "b"],
        "one": ["a"],
        "e": [],
        "m": {"b": 1, "a": 2},
        "a": ["1", "2"],
        "b": ["x", "y"],
        "big": big,
    })
}

fn folds(cases: &[(&str, &str)]) {
    let env = env();
    for (src, want) in cases {
        assert_eq!(
            &fold_text(&env, &[("p", p())], src),
            want,
            "folding `{src}`"
        );
    }
}

fn parse(src: &str) -> IdedExpr {
    Parser::default()
        .parse(src)
        .unwrap_or_else(|e| panic!("{src}: {e}"))
}

fn strip(e: &IdedExpr) -> IdedExpr {
    let mut out = e.clone();
    zero(&mut out);
    out
}

fn zero(e: &mut IdedExpr) {
    e.id = 0;
    match &mut e.expr {
        Expr::Unspecified | Expr::Ident(_) | Expr::Literal(_) => {}
        Expr::Call(c) => {
            if let Some(t) = c.target.as_mut() {
                zero(t);
            }
            c.args.iter_mut().for_each(zero);
        }
        Expr::Comprehension(c) => {
            zero(&mut c.iter_range);
            zero(&mut c.accu_init);
            zero(&mut c.loop_cond);
            zero(&mut c.loop_step);
            zero(&mut c.result);
        }
        Expr::List(l) => l.elements.iter_mut().for_each(zero),
        Expr::Map(m) => {
            for entry in &mut m.entries {
                entry.id = 0;
                let EntryExpr::MapEntry(me) = &mut entry.expr;
                zero(&mut me.key);
                zero(&mut me.value);
            }
        }
        Expr::Select(s) => zero(&mut s.operand),
    }
}

/// How deep `op` calls nest in `e`, counting only `op` nodes on the path.
fn op_depth(e: &IdedExpr, op: &str) -> usize {
    match &e.expr {
        Expr::Call(c) if c.func_name == op => {
            1 + c.args.iter().map(|a| op_depth(a, op)).max().unwrap_or(0)
        }
        _ => 0,
    }
}

#[test]
fn exists_over_a_known_list_unrolls_to_an_or_chain() {
    folds(&[(
        "p.deny.exists(r, u.path == r || u.path.startsWith(r + \"/\"))",
        "((u.path == \"/etc\") || u.path.startsWith(\"/etc/\")) || ((u.path == \"/proc\") || u.path.startsWith(\"/proc/\"))",
    )]);
}

#[test]
fn all_over_a_known_list_unrolls_to_an_and_chain() {
    folds(&[(
        "p.deny.all(r, u.path != r)",
        "(u.path != \"/etc\") && (u.path != \"/proc\")",
    )]);
}

#[test]
fn an_absorbing_element_decides_the_whole_unroll() {
    folds(&[
        ("p.l.exists(x, x == \"b\" || u.b)", "true"),
        ("p.l.all(x, x == \"a\" && u.b)", "false"),
    ]);
}

#[test]
fn identity_elements_drop_out_of_the_chain() {
    folds(&[
        ("p.l.exists(x, x == \"z\" && u.b)", "false"),
        ("p.l.all(x, x != \"z\" || u.b)", "true"),
        // One element survives, so there is no `||` node at all.
        ("p.l.exists(x, x == \"a\" && (u.a > 1))", "u.a > 1"),
        ("p.l.exists(x, x == \"a\" && u.b)", "u.b"),
    ]);
}

/// The loop computes `false || P` for `exists` and `true && P` for `all`. With one copy left the
/// identity drops out: `P` is a checked bool, so it answers exactly what the loop does.
#[test]
fn a_lone_surviving_term_stands_alone() {
    folds(&[
        ("p.one.exists(x, u.b)", "u.b"),
        ("p.one.all(x, u.b)", "u.b"),
        ("p.one.exists(x, u.a > 1)", "u.a > 1"),
    ]);
}

#[test]
fn an_empty_known_range_unrolls_to_the_fold_identity() {
    folds(&[("p.e.exists(x, u.b)", "false"), ("p.e.all(x, u.b)", "true")]);
}

#[test]
fn the_unrolled_chain_is_balanced() {
    let env = env();
    let original = env
        .compile("p.big.exists(x, u.s == x)", &CompileOpts::default())
        .expect("compiles");
    let mut act = env.activation();
    act.bind("p", &p()).expect("binds");
    let residual = env
        .compile(
            original.source(),
            &CompileOpts {
                known: Some(&act),
                ..Default::default()
            },
        )
        .expect("specializes");
    let r = typed_cel::fork::expression_of(&residual);
    assert_eq!(op_depth(r, "_||_"), 7, "ceil(log2 100)");
    let text = residual.source();
    assert!(!text.contains("p.big"), "{text}");
    assert_eq!(
        strip(&parse(text)),
        strip(r),
        "the rendered chain parses back to the same (balanced) tree"
    );
}

#[test]
fn map_keys_unroll_in_sorted_order() {
    folds(&[(
        "p.m.exists(k, u.s == k)",
        "(u.s == \"a\") || (u.s == \"b\")",
    )]);
}

#[test]
fn map_over_a_known_list_unrolls_to_a_list_literal() {
    folds(&[
        (
            "p.l.map(x, x + u.s) == u.l",
            "[\"a\" + u.s, \"b\" + u.s] == u.l",
        ),
        (
            "p.l.map(x, x + \"!\") == u.l",
            "$k0 == u.l\n// $k0 = [\"a!\", \"b!\"]",
        ),
    ]);
}

#[test]
fn filter_and_exists_one_keep_the_loop_over_a_constant_slot() {
    folds(&[
        (
            "p.l.filter(x, x == u.s).size() == 1",
            "$k0.filter(x, x == u.s).size() == 1\n// $k0 = [\"a\", \"b\"]",
        ),
        (
            "p.l.exists_one(x, x == u.s)",
            "$k0.exists_one(x, x == u.s)\n// $k0 = [\"a\", \"b\"]",
        ),
        (
            "p.l.map(x, x == u.s, x + \"!\") == u.l",
            "$k0.map(x, x == u.s, x + \"!\") == u.l\n// $k0 = [\"a\", \"b\"]",
        ),
        // A `map` over a MAP has no single order to reproduce, so it is not unrolled.
        (
            "p.m.map(k, k + u.s) == u.l",
            "$k0.map(k, k + u.s) == u.l\n// $k0 = {\"a\": 2, \"b\": 1}",
        ),
    ]);
}

#[test]
fn over_the_budget_keeps_the_loop() {
    let known = [(
        "p",
        json!({"l": ["a", "b", "c"], "deny": [], "one": [], "e": [], "m": {}, "a": [], "b": [], "big": []}),
    )];
    let at = |max_unroll: usize| {
        let limits = CelLimits {
            max_unroll,
            ..CelLimits::default()
        };
        fold_text(&env_with(limits), &known, "p.l.exists(r, u.path == r)")
    };
    assert_eq!(
        at(2),
        "$k0.exists(r, u.path == r)\n// $k0 = [\"a\", \"b\", \"c\"]"
    );
    assert_eq!(
        at(3),
        "((u.path == \"a\") || (u.path == \"b\")) || (u.path == \"c\")"
    );
}

#[test]
fn an_element_error_stays_in_its_copy() {
    folds(&[(
        "[0, 5].all(n, [1][n] > 0 || u.b)",
        "($k0[5] > 0) || u.b\n// $k0 = [1]",
    )]);
}

#[test]
fn nested_unrolls_substitute_both_levels() {
    folds(&[(
        "p.a.exists(i, p.b.exists(j, u.s == i + j))",
        "((u.s == \"1x\") || (u.s == \"1y\")) || ((u.s == \"2x\") || (u.s == \"2y\"))",
    )]);
}

#[test]
fn an_inner_loop_variable_shadows_the_unrolled_one() {
    folds(&[(
        "p.l.exists(x, u.items.exists(x, x == u.s))",
        "u.items.exists(x, x == u.s) || u.items.exists(x, x == u.s)",
    )]);
}
