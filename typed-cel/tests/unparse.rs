//! `fork::unparse` renders a desugared tree as CEL text that parses back to the SAME tree.
//!
//! The residual a specializer produces is an `IdedExpr`; its `source()` is this rendering. The
//! property every test here holds is the structural round trip: parse → unparse → parse gives the
//! tree it started from, ids aside.

use typed_cel::fork::ast::{EntryExpr, Expr, IdedExpr, LiteralValue};
use typed_cel::fork::parser::Parser;

fn parse(src: &str) -> IdedExpr {
    Parser::default()
        .parse(src)
        .unwrap_or_else(|e| panic!("{src}: {e}"))
}

/// Ids are parser bookkeeping; two trees are "the same program" when everything else matches.
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

fn round_trip(src: &str) -> String {
    let tree = parse(src);
    let text = typed_cel::fork::unparse(&tree).expect("renders");
    assert_eq!(
        strip(&parse(&text)),
        strip(&tree),
        "{src} rendered as {text}"
    );
    text
}

const NUMERIC_SPELLINGS: &[&str] = &[
    "0",
    "42",
    "-7",
    "9223372036854775807",
    "-9223372036854775808",
    "1.5",
    "7.0",
    "1e21",
    "1e-7",
    "-0.0",
];

#[test]
fn scalars_render_and_round_trip() {
    for src in ["true", "false", "null", "\"a\"", "b\"\\x00\\xff\""] {
        round_trip(src);
    }
    for src in NUMERIC_SPELLINGS {
        round_trip(src);
    }
    assert_eq!(round_trip("7.0"), "7.0");
    assert_eq!(round_trip("42"), "42");
    assert_eq!(round_trip("-7"), "-7");
    assert_eq!(round_trip("b\"\\x00\\xff\""), "b\"\\x00\\xff\"");
}

#[test]
fn double_keeps_decimal_point() {
    // Built by hand, not parsed: the value a fold would place in a residual.
    let seven = IdedExpr {
        id: 0,
        expr: Expr::Literal(LiteralValue::Double(7.0.into())),
    };
    let text = typed_cel::fork::unparse(&seven).expect("renders");
    assert_eq!(text, "7.0");
    match parse(&text).expr {
        Expr::Literal(LiteralValue::Double(d)) => assert_eq!(*d.inner(), 7.0),
        other => panic!("`{text}` re-parsed as {other:?}, not a Double"),
    }
}

#[test]
fn strings_escape_and_round_trip() {
    for src in [
        r#""a\"b""#,
        "'single'",
        r#""back\\slash""#,
        r#""line\nbreak""#,
        r#""tab\t""#,
        r#""\u0001""#,
        "\"πέντε\"",
        "\"emoji 🙂\"",
        r#"r"\d+""#,
        r#""carriage\rreturn""#,
        r#""del\x7f""#,
    ] {
        let text = round_trip(src);
        assert!(
            text.starts_with('"') && text.ends_with('"'),
            "{src} rendered as {text}, not double-quoted"
        );
    }
    assert_eq!(round_trip("'single'"), "\"single\"");
    assert_eq!(round_trip(r#"r"\d+""#), r#""\\d+""#);
}

#[test]
fn operators_round_trip_structurally() {
    for src in [
        "a + b * c",
        "(a + b) * c",
        "a - -b",
        "-(a)",
        "!a",
        "!(a && b)",
        "!!a",
        "-(3)",
        "(-3) + x",
        "a == b",
        "a != b",
        "a < b",
        "a <= b",
        "a > b",
        "a >= b",
        "a % b",
        "a / b",
        "a in [1, 2]",
        "m[\"k\"]",
        "l[0]",
        "l[0][1]",
        "c ? x : y",
        "c ? (d ? x : y) : z",
        "(c ? x : y) ? z : w",
        "a && b || c",
        "a || b || c || d || e",
        "a && b && c && d && e && f",
        "x.y.z",
        "(a + b).c",
        "(a + b)[0]",
        "{\"a\": 1}.a",
        "[1, 2][0]",
    ] {
        round_trip(src);
    }
    // The unary rule: a literal operand is wrapped, so `-_` over `3` never becomes the literal `-3`.
    assert_eq!(round_trip("-(3)"), "-(3)");
    assert_eq!(round_trip("-a"), "-a");
    assert_eq!(round_trip("a - -b"), "a - (-b)");
    // A negative literal is not primary.
    assert_eq!(round_trip("(-3) + x"), "(-3) + x");
    // The parser's balanced run is rendered, not flattened.
    assert_eq!(round_trip("a || b || c || d"), "(a || b) || (c || d)");
}

#[test]
fn calls_round_trip() {
    for src in [
        "size(l)",
        "l.size()",
        "s.startsWith(\"p\")",
        "s.matches(\"^a\")",
        "duration(\"30s\")",
        "mystery(1, x)",
        "x.mystery()",
        "(a + b).mystery(c ? d : e)",
        "f()",
    ] {
        round_trip(src);
    }
    assert_eq!(round_trip("mystery(1, x)"), "mystery(1, x)");
    assert_eq!(round_trip("s.startsWith(\"p\")"), "s.startsWith(\"p\")");
}

#[test]
fn has_round_trips() {
    for src in ["has(x.f)", "has(x.y.f)", "has((a + b).f)", "!has(x.f)"] {
        let text = round_trip(src);
        assert!(text.contains("has("), "{src} rendered as {text}");
    }
    match parse("has(x.f)").expr {
        Expr::Select(s) => assert!(s.test, "`has` is a test Select"),
        other => panic!("has(x.f) parsed as {other:?}"),
    }
    assert_eq!(round_trip("has(x.y.f)"), "has(x.y.f)");
}

#[test]
fn comprehensions_re_macroize() {
    for (src, want) in [
        ("l.exists(v, v > 0)", "l.exists(v, v > 0)"),
        ("l.all(v, v > 0)", "l.all(v, v > 0)"),
        ("l.exists_one(v, v > 0)", "l.exists_one(v, v > 0)"),
        ("l.map(v, v + 1)", "l.map(v, v + 1)"),
        ("l.map(v, v > 0, v + 1)", "l.map(v, v > 0, v + 1)"),
        ("l.filter(v, v > 0)", "l.filter(v, v > 0)"),
        ("m.all(k, m[k] > 0)", "m.all(k, m[k] > 0)"),
        (
            "a.exists(x, b.all(y, x == y))",
            "a.exists(x, b.all(y, x == y))",
        ),
        ("(a + b).exists(x, x)", "(a + b).exists(x, x)"),
        ("[1, 2].map(x, x * 2).size()", "[1, 2].map(x, x * 2).size()"),
    ] {
        assert_eq!(round_trip(src), want);
    }
}

#[test]
fn literals_containers_round_trip() {
    for src in [
        "[]",
        "[1, \"a\", null]",
        "{}",
        "{\"a\": 1, \"b\": [true]}",
        "{1: \"x\", true: \"y\"}",
        "{(a ? b : c): d}",
        "[[1], {\"k\": [2]}]",
    ] {
        round_trip(src);
    }
    assert_eq!(
        round_trip("{\"a\": 1, \"b\": [true]}"),
        "{\"a\": 1, \"b\": [true]}"
    );
}

fn err_of(e: &IdedExpr) -> String {
    match typed_cel::fork::unparse(e) {
        Ok(text) => panic!("{e:?} rendered as {text}, expected a refusal"),
        Err(err) => err.to_string(),
    }
}

#[test]
fn plumbing_is_refused_standalone() {
    // `@not_strictly_false(x)` outside a comprehension: built from `f(x)` by renaming the call.
    let mut nsf = parse("f(x)");
    match &mut nsf.expr {
        Expr::Call(c) => c.func_name = "@not_strictly_false".to_string(),
        other => panic!("{other:?}"),
    }
    let msg = err_of(&nsf);
    assert!(msg.contains("@not_strictly_false"), "{msg}");

    // An unspecified expression.
    let msg = err_of(&IdedExpr::default());
    assert!(msg.contains("unspecified"), "{msg}");

    // A two-variable comprehension.
    let mut two = parse("l.exists(v, v > 0)");
    match &mut two.expr {
        Expr::Comprehension(c) => c.iter_var2 = Some("w".to_string()),
        other => panic!("{other:?}"),
    }
    let msg = err_of(&two);
    assert!(msg.contains("two-variable"), "{msg}");

    // Nested: plumbing buried inside an otherwise renderable tree is still refused, not panicked.
    let mut nested = parse("a && f(x)");
    match &mut nested.expr {
        Expr::Call(c) => match &mut c.args[1].expr {
            Expr::Call(inner) => inner.func_name = "@not_strictly_false".to_string(),
            other => panic!("{other:?}"),
        },
        other => panic!("{other:?}"),
    }
    let msg = err_of(&nested);
    assert!(msg.contains("@not_strictly_false"), "{msg}");
}

#[test]
fn unrecognised_comprehension_shape_is_refused() {
    let mut odd = parse("l.exists(v, v > 0)");
    match &mut odd.expr {
        Expr::Comprehension(c) => {
            c.accu_init = IdedExpr {
                id: 0,
                expr: Expr::Literal(LiteralValue::String("seed".into())),
            }
        }
        other => panic!("{other:?}"),
    }
    let msg = err_of(&odd);
    assert!(msg.contains("comprehension"), "{msg}");
}

#[test]
fn rendered_numbers_survive_desugar() {
    for src in NUMERIC_SPELLINGS {
        let text = round_trip(src);
        let (desugared, _) = typed_cel::desugar(&text).expect("desugars");
        assert_eq!(
            desugared, text,
            "{src} rendered as {text}; desugar rewrote it"
        );
    }
    // In operator position too, where a unit-shaped suffix would be read as a duration.
    for src in ["x > 1e21", "x < (-0.0)", "1e-7 + x"] {
        let text = round_trip(src);
        let (desugared, _) = typed_cel::desugar(&text).expect("desugars");
        assert_eq!(
            desugared, text,
            "{src} rendered as {text}; desugar rewrote it"
        );
    }
}

/// A specialized residual names each known composite it reads by its constant slot, `$kN`, and its
/// `source()` appends one `// $kN = <value>` line per slot, in slot order, so introspection still
/// shows the policy's values. The value is spelled as `fork::unparse` spells its literal: numbers as
/// doubles, map entries sorted by key.
#[test]
fn a_residual_renders_its_slots_by_name_and_appends_a_legend() {
    use typed_cel::{CelEnvironment, CelTy, Record};
    let mut env = CelEnvironment::new();
    env.declare(
        "k",
        Record::new(
            "k",
            [
                ("roots", CelTy::list(CelTy::Str)),
                ("caps", CelTy::map(CelTy::Str, CelTy::Num)),
            ],
        ),
    );
    env.declare("s", CelTy::Str);
    let program = env
        .compile(r#"s in k.caps && k.roots.filter(r, s.startsWith(r)).size() > 0.0"#)
        .expect("compiles");
    let mut known = env.activation();
    known
        .bind(
            "k",
            &serde_json::json!({"roots": ["/a", "/b"], "caps": {"z": 2, "y": 0.5}}),
        )
        .expect("k binds");
    let residual = env.specialize(&program, &known).expect("specializes");
    assert_eq!(
        residual.source(),
        concat!(
            "(s in $k0) && ($k1.filter(r, s.startsWith(r)).size() > 0.0)\n",
            "// $k0 = {\"y\": 0.5, \"z\": 2.0}\n",
            "// $k1 = [\"/a\", \"/b\"]",
        )
    );
    // A slot name is not an identifier the grammar has: the rendering names the pool, and the
    // residual runs from its tree.
    assert!(Parser::default().parse("$k0 == 1").is_err());
}
