//! `CelEnvironment::specialize` folds the values that are known now out of a checked program.
//!
//! Unless a test says otherwise the known roots are `k = 10.0`, `t = true`, `f = false` and
//! `p = {"fs": {"root": "/ws", "names": ["a", "b"]}}` (`p.fs.nope` is declared optional and absent);
//! `u` is an unknown record. Each case asserts the exact residual text — the folded tree, then one
//! `// $kN = …` line per known composite the residual still reads.

mod support;

use serde_json::json;
use support::known::fold_text;
use typed_cel::fork::ast::{EntryExpr, Expr, IdedExpr};
use typed_cel::fork::parser::Parser;
use typed_cel::CompileOpts;
use typed_cel::{CelEnvironment, CelTy, Record};

fn env() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.declare("k", CelTy::Num);
    env.declare("t", CelTy::Bool);
    env.declare("f", CelTy::Bool);
    env.declare(
        "p",
        Record::new(
            "p",
            [(
                "fs",
                CelTy::from(
                    Record::new(
                        "fs",
                        [
                            ("root", CelTy::Str),
                            ("names", CelTy::list(CelTy::Str)),
                            ("nope", CelTy::Str),
                        ],
                    )
                    .with_optional(["nope"]),
                ),
            )],
        ),
    );
    env.declare(
        "u",
        Record::new(
            "u",
            [
                ("a", CelTy::Num),
                ("n", CelTy::Num),
                ("b", CelTy::Bool),
                ("c", CelTy::Bool),
                ("s", CelTy::Str),
                ("path", CelTy::Str),
                ("items", CelTy::list(CelTy::Num)),
                ("l", CelTy::list(CelTy::Num)),
            ],
        ),
    );
    env
}

fn known() -> Vec<(&'static str, serde_json::Value)> {
    vec![
        ("k", json!(10.0)),
        ("t", json!(true)),
        ("f", json!(false)),
        ("p", json!({"fs": {"root": "/ws", "names": ["a", "b"]}})),
    ]
}

/// Assert each `(authored, residual)` pair against the default known roots.
fn folds(cases: &[(&str, &str)]) {
    let env = env();
    for (src, want) in cases {
        assert_eq!(&fold_text(&env, &known(), src), want, "folding `{src}`");
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

#[test]
fn closed_arithmetic_folds_to_its_number() {
    // A COMPUTED number reifies as the number it is (an integer here); an authored literal keeps
    // its spelling.
    folds(&[("1 + 2 * 3 == u.n", "7 == u.n")]);
}

#[test]
fn known_root_substitutes_as_its_number() {
    folds(&[("k > u.n", "10 > u.n")]);
}

#[test]
fn known_select_chain_folds_to_its_leaf() {
    folds(&[("p.fs.root == u.path", "\"/ws\" == u.path")]);
}

#[test]
fn unknown_root_is_untouched() {
    folds(&[("u.a > 5", "u.a > 5")]);
}

#[test]
fn and_absorbs_false_from_either_side_even_over_an_error() {
    folds(&[
        ("u.b && f", "false"),
        ("f && u.b", "false"),
        ("(duration(\"x\") == duration(\"1s\")) && f", "false"),
        ("u.b && (p.fs.root == \"/x\")", "false"),
    ]);
}

#[test]
fn or_absorbs_true_from_either_side() {
    folds(&[
        ("u.b || t", "true"),
        ("t || u.b", "true"),
        ("(duration(\"x\") == duration(\"1s\")) || t", "true"),
    ]);
}

/// The identity value drops out: every operand of a checked `&&`/`||` is a bool, so `true && x`
/// answers exactly what `x` does — its value, or its error.
#[test]
fn identity_drops_out() {
    folds(&[
        ("(u.a > 1) && t", "u.a > 1"),
        ("t && (u.a > 1)", "u.a > 1"),
        ("(u.a > 1) || f", "u.a > 1"),
        ("f || !u.b", "!u.b"),
        ("t && (u.b && u.c)", "u.b && u.c"),
        ("u.b && u.c", "u.b && u.c"),
        ("u.b && t", "u.b"),
        ("t && u.b", "u.b"),
        ("u.b || f", "u.b"),
        ("f || u.b", "u.b"),
    ]);
}

/// A closed node that errors is never baked into a literal: it stays, with its children folded, and
/// fails at run time in the same place.
#[test]
fn closed_error_stays_in_place() {
    folds(&[(
        "(duration(\"x\") == duration(\"1s\")) && u.b",
        "(duration(\"x\") == duration(\"1s\")) && u.b",
    )]);
}

#[test]
fn nonfinite_not_folded() {
    folds(&[("k / 0.0 < u.n", "(10 / 0.0) < u.n")]);
}

#[test]
fn ternary_picks_on_known_bool() {
    folds(&[
        ("(t ? u.a : u.n) > 1", "u.a > 1"),
        ("(f ? u.a : u.n) > 1", "u.n > 1"),
        ("t ? u.b : (duration(\"x\") == duration(\"1s\"))", "u.b"),
    ]);
}

/// A picked branch whose value no literal can spell is rebuilt from ITS folded children — not
/// left as the whole conditional, which would still read the known roots.
#[test]
fn picked_branch_that_cannot_be_spelled_is_rebuilt() {
    folds(&[("(t ? k / 0.0 : u.a) < u.n", "(10 / 0.0) < u.n")]);
}

#[test]
fn has_on_a_known_operand_folds() {
    folds(&[
        ("has(p.fs.root) && (u.a > 1)", "u.a > 1"),
        ("has(p.fs.nope) || (u.a > 1)", "u.a > 1"),
    ]);
}

/// An absent optional field is a missing key at run time, so the select stays — over the known
/// record, which the residual reads by constant slot.
#[test]
fn an_absent_optional_field_of_a_known_value_is_refused_or_folds_its_guard() {
    let env = env();
    let mut k = env.activation();
    for (name, v) in known() {
        k.bind(name, &v).unwrap();
    }
    let opts = CompileOpts {
        known: Some(&k),
        ..Default::default()
    };
    let e = env
        .compile("p.fs.nope == u.path", &opts)
        .expect_err("the known `p` has no `fs.nope`")
        .to_string();
    assert!(
        e.contains("`p.fs.nope` is absent: the KNOWN value of `p`"),
        "{e}"
    );
    folds(&[
        ("has(p.fs.nope) && p.fs.nope == u.path", "false"),
        ("!has(p.fs.nope) || p.fs.nope == u.path", "true"),
    ]);
}

#[test]
fn member_call_on_a_known_target_folds_the_target() {
    folds(&[("p.fs.root.startsWith(u.path)", "\"/ws\".startsWith(u.path)")]);
}

#[test]
fn in_folds_either_side() {
    folds(&[
        ("u.s in p.fs.names", "u.s in $k0\n// $k0 = [\"a\", \"b\"]"),
        ("\"a\" in p.fs.names && (u.a > 1)", "u.a > 1"),
    ]);
}

#[test]
fn container_literals_fold_element_wise() {
    folds(&[
        ("[k, u.a] == u.l", "[10, u.a] == u.l"),
        ("{\"x\": k}[\"x\"] == u.n", "10 == u.n"),
    ]);
}

#[test]
fn iteration_variable_shadows_a_known_root() {
    folds(&[
        ("u.items.exists(k, k > 1.0)", "u.items.exists(k, k > 1.0)"),
        ("u.items.exists(x, x > k)", "u.items.exists(x, x > 10)"),
    ]);
}

#[test]
fn closed_comprehension_folds_whole() {
    folds(&[
        ("[1, 2, 3].exists(x, x > 2) && (u.a > 1)", "u.a > 1"),
        ("p.fs.names.all(n, n != \"\") || u.b", "true"),
    ]);
}

#[test]
fn kept_comprehension_keeps_its_plumbing() {
    let env = env();
    let src = "u.items.exists(x, x == k || t)";
    let original = env.compile(src, &CompileOpts::default()).expect("compiles");
    let mut act = env.activation();
    for (name, v) in known() {
        act.bind(name, &v).expect("binds");
    }
    let residual = env
        .compile(
            original.source(),
            &CompileOpts {
                known: Some(&act),
                ..Default::default()
            },
        )
        .expect("specializes");
    let (o, r) = (
        typed_cel::fork::expression_of(&original),
        typed_cel::fork::expression_of(&residual),
    );
    let (Expr::Comprehension(o), Expr::Comprehension(r)) = (&o.expr, &r.expr) else {
        panic!("both must be comprehensions: {r:?}");
    };
    assert_eq!(strip(&r.accu_init), strip(&o.accu_init), "accu_init");
    assert_eq!(strip(&r.loop_cond), strip(&o.loop_cond), "loop_cond");
    assert_eq!(strip(&r.result), strip(&o.result), "result");
    assert_eq!(r.iter_var, o.iter_var);
    assert_eq!(r.accu_var, o.accu_var);
    let Expr::Call(step) = &r.loop_step.expr else {
        panic!("the step must stay a call: {:?}", r.loop_step);
    };
    assert_eq!(step.func_name, "_||_", "the expander's operator survives");
    assert_eq!(step.args.len(), 2);
    assert!(
        matches!(&step.args[0].expr, Expr::Ident(n) if n == &r.accu_var),
        "the accumulator read survives: {:?}",
        step.args[0]
    );
    assert_eq!(
        strip(&step.args[1]),
        strip(&parse("true")),
        "the predicate folds"
    );
    assert_eq!(residual.source(), "u.items.exists(x, true)");
}

#[test]
fn no_dotted_function_names_exist() {
    for (name, _) in typed_cel::signature_table() {
        assert!(
            !name.contains('.'),
            "`{name}` is a dotted function name. The evaluator tries `<ident>.<func>` first when a \
             call's target is a bare identifier (objects.rs, the qualified lookup), and the fold \
             substitutes a known root that is a call target — so `Folder::call` must now keep a \
             bare-`Ident` target whose qualified name resolves."
        );
    }
}

#[test]
fn a_call_whose_arguments_all_folded_is_evaluated() {
    // `t || …` folds to `true` only after `!` has been rebuilt around it; the call is then closed.
    folds(&[
        (r#"!(t || u.s == "a")"#, "false"),
        ("!(f && u.b)", "true"),
        (
            r#"u.s.startsWith(p.fs.root + "/")"#,
            r#"u.s.startsWith("/ws/")"#,
        ),
    ]);
}

#[test]
fn and_with_a_folded_false_operand_is_false() {
    folds(&[(r#"u.s == "a" && !(t || u.s == "b")"#, "false")]);
}

#[test]
fn a_conditional_compared_to_one_arm_is_its_condition() {
    folds(&[
        (r#"(u.b ? "eacces" : "allow") == "allow""#, "!u.b"),
        (r#"(u.b ? "eacces" : "allow") == "eacces""#, "u.b"),
        (r#"(u.b ? "eacces" : "allow") != "allow""#, "u.b"),
        (r#"(u.b ? "eacces" : "allow") != "eacces""#, "!u.b"),
        (r#""allow" == (u.b ? "eacces" : "allow")"#, "!u.b"),
        // Arms that are not two distinct literals, or a constant neither arm equals, stay: the
        // condition is a read that can raise, and only rewriting to it keeps that error.
        (r#"(u.b ? "a" : "a") == "a""#, r#"(u.b ? "a" : "a") == "a""#),
        (r#"(u.b ? "a" : "b") == "c""#, r#"(u.b ? "a" : "b") == "c""#),
    ]);
}

#[test]
fn double_negation_of_a_bool_is_the_bool() {
    folds(&[("!!u.b", "u.b"), ("!!(u.b && u.c)", "u.b && u.c")]);
}
