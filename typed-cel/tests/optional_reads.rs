//! `added: optional reads` — spec CEL's optional reads, `x.?f.orValue(d)`, `x.?f.hasValue()`,
//! `m[?k].orValue(d)` and `has(x.?a.b)`, rewritten at parse time into the guarded form an author
//! would write by hand, and proven by the presence rules that already exist.
//!
//! There are no optional VALUES: an optional read is legal only as the operand of `.orValue(d)`,
//! `.hasValue()` or `has()`, and every other form is refused. One registered difference from spec
//! CEL: `.orValue(d)`'s default is evaluated only when the value is absent.

use typed_cel::{CelEnvironment, CelTy, CompileOpts, Record};
use serde_json::{json, Value as J};

/// `body: {a: double, o?: double, s?: {z?: string, n: double}, h: {x-t: string, [string]: string},
/// items: list({n: double, note?: string})}`, `m: map(string, double)`, `xs: list(double)`,
/// `d: double`.
fn env() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    let s = Record::new("body.s", [("z", CelTy::Str), ("n", CelTy::Num)]).with_optional(["z"]);
    let h = Record::new("body.h", [("x-t", CelTy::Str)]).with_index(CelTy::Str, CelTy::Str);
    let item = Record::new("body.items[]", [("n", CelTy::Num), ("note", CelTy::Str)])
        .with_optional(["note"]);
    env.declare(
        "body",
        Record::new(
            "body",
            [
                ("a", CelTy::Num),
                ("o", CelTy::Num),
                ("s", s.into()),
                ("h", h.into()),
                ("items", CelTy::list(item.into())),
            ],
        )
        .with_optional(["o", "s"]),
    );
    env.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    env.declare("xs", CelTy::list(CelTy::Num));
    env.declare("d", CelTy::Num);
    env
}

/// Every optional present.
fn present() -> Vec<(&'static str, J)> {
    vec![
        (
            "body",
            json!({"a": 1, "o": 3, "s": {"z": "zz", "n": 2}, "h": {"x-t": "t", "x-other": "o"},
                   "items": [{"n": 1, "note": "x"}]}),
        ),
        ("m", json!({"k": 2})),
        ("xs", json!([5])),
        ("d", json!(7)),
    ]
}

/// Every optional absent.
fn absent() -> Vec<(&'static str, J)> {
    vec![
        (
            "body",
            json!({"a": 1, "h": {"x-t": "t"}, "items": [{"n": 1}]}),
        ),
        ("m", json!({})),
        ("xs", json!([])),
        ("d", json!(7)),
    ]
}

fn run(
    env: &CelEnvironment,
    program: &typed_cel::CelProgram,
    binds: &[(&str, J)],
) -> Result<bool, typed_cel::CelError> {
    let mut act = env.activation();
    for (name, v) in binds {
        act.bind(name, v).unwrap();
    }
    program.evaluate(&act)
}

/// `(row, source, present, absent)`.
const ANSWERS: &[(u32, &str, bool, bool)] = &[
    (1, "body.?o.orValue(0) < 10", true, true),
    (2, "body.?o.orValue(100) < 10", true, false),
    (3, "body.?o.hasValue()", true, false),
    (4, "body.?s.?z.orValue('') == 'zz'", true, false),
    // A plain segment after `.?` is optional too.
    (5, "body.?s.z.orValue('') == 'zz'", true, false),
    // A REQUIRED field after `.?`.
    (6, "body.?s.n.orValue(-1) == 2", true, false),
    (7, "body.h[?'x-other'].orValue('none') == 'o'", true, false),
    // A declared field through `[?]`.
    (8, "body.h[?'x-t'].orValue('none') == 't'", true, true),
    (9, "m[?'k'].orValue(0) == 2", true, false),
    // A non-string key into a literal, present and absent.
    (
        10,
        "{1: 'one'}[?1].orValue('') == 'one' && {1: 'one'}[?2].orValue('') == ''",
        true,
        true,
    ),
    (11, "has(body.?s.z)", true, false),
    (
        12,
        "body.items.all(i, i.?note.orValue('') != 'y')",
        true,
        true,
    ),
    // A non-literal default.
    (
        13,
        "body.?o.orValue(d) + body.?s.?n.orValue(d) > 0",
        true,
        true,
    ),
    // Nested.
    (
        14,
        "body.?o.orValue(body.?s.?n.orValue(0)) >= 0",
        true,
        true,
    ),
    // A literal root.
    (15, "{'a': {'b': 1}}.?a.?b.orValue(0) == 1", true, true),
    (16, "{}.?a.?b.hasValue()", false, false),
];

#[test]
fn the_rewrite_answers_as_spec_cel() {
    let env = env();
    for (row, src, p, a) in ANSWERS {
        let program = env
            .compile(*src, &CompileOpts::default())
            .unwrap_or_else(|e| panic!("row {row} `{src}`: {e}"));
        for (binds, want, which) in [(present(), p, "present"), (absent(), a, "absent")] {
            assert_eq!(
                run(&env, &program, &binds).ok(),
                Some(*want),
                "row {row} `{src}` over the {which} binding"
            );
        }
    }
}

/// `(source, returning, fragments the message contains)`.
const REFUSED: &[(&str, Option<CelTy>, &[&str])] = &[
    ("body.?o == 1", None, &[".orValue(<default>)"]),
    ("body.?o", Some(CelTy::Num), &[".orValue(<default>)"]),
    ("body.?o.value() > 1", None, &["removed: optional values"]),
    (
        "body.?o.or(body.?o).hasValue()",
        None,
        &["removed: optional values"],
    ),
    ("[?body.a]", None, &["removed: optional values"]),
    ("{?'k': body.?o}", None, &["removed: optional values"]),
    // A PLAIN read: `.orValue` has no optional to unwrap.
    ("body.o.orValue(0) > 1", None, &["x.?f.orValue(d)"]),
    // The plain `body.s` BEFORE the first `.?` is an ordinary read, and `s` is optional.
    (
        "body.s.?z.orValue('') == 'zz'",
        None,
        &["`body.s` may be absent"],
    ),
    // The default's type differs. (Its quote style is re-rendered, so it is not pinned.)
    (
        "body.?o.orValue('none') == 'none'",
        None,
        &[".orValue(", "body.?o", "double", "string"],
    ),
    // A LIST: bounds are not presence.
    (
        "xs[?0].orValue(1) == 5",
        None,
        &["optional index on a list", "size(xs) > 0 ? xs[0] : …"],
    ),
];

#[test]
fn optional_reads_that_stay_refused() {
    let env = env();
    for (src, returning, fragments) in REFUSED {
        let opts = CompileOpts {
            returning: returning.as_ref(),
            ..Default::default()
        };
        let text = env.compile(*src, &opts).expect_err(src).to_string();
        for f in *fragments {
            assert!(text.contains(f), "`{src}` should say {f:?}: {text}");
        }
    }
}

/// An optional index on a LIST must never rewrite to `0 in xs`, which is MEMBERSHIP: over
/// `xs = [5]`, `xs[?0].orValue(1) == 5` would answer `false`, silently. It does not compile.
#[test]
fn an_optional_index_on_a_list_is_never_membership() {
    let env = env();
    let refused = env.compile("xs[?0].orValue(1) == 5", &CompileOpts::default());
    assert!(
        refused.is_err(),
        "an optional index on a list compiled: over xs = [5] it answers {:?}",
        run(&env, refused.as_ref().unwrap(), &present())
    );
}

/// `(row, the hand-written guarded form)` for rows of [`ANSWERS`].
const HAND_WRITTEN: &[(u32, &str)] = &[
    (1, "(has(body.o) ? body.o : 0) < 10"),
    (4, "(has(body.s) && has(body.s.z) ? body.s.z : '') == 'zz'"),
    (
        7,
        "('x-other' in body.h ? body.h['x-other'] : 'none') == 'o'",
    ),
    (11, "has(body.s) && has(body.s.z)"),
];

/// The rewrite is an ordinary program: the same roots, the same demand, and — specialized against
/// a known `body` — the same residual as the guarded form an author would write by hand.
#[test]
fn the_rewrite_is_an_ordinary_program() {
    let env = env();
    let mut known = env.activation();
    known.bind("body", &present()[0].1).unwrap();
    for (row, hand) in HAND_WRITTEN {
        let (_, src, _, _) = ANSWERS.iter().find(|(r, ..)| r == row).unwrap();
        assert_eq!(
            env.parse(src).unwrap().roots(),
            env.parse(hand).unwrap().roots(),
            "row {row}: roots"
        );
        let a = env.compile(*src, &CompileOpts::default()).unwrap();
        let b = env.compile(*hand, &CompileOpts::default()).unwrap();
        assert_eq!(
            format!("{:?}", a.demand()),
            format!("{:?}", b.demand()),
            "row {row}: demand"
        );
        let opts = CompileOpts {
            known: Some(&known),
            ..Default::default()
        };
        let a = env.compile(*src, &opts).unwrap();
        let b = env.compile(*hand, &opts).unwrap();
        assert_eq!(a.source(), b.source(), "row {row}: residual");
    }
}

/// Every rewritten node carries a span copied from the authored node it came from, so a diagnostic
/// about one carets what the author typed.
#[test]
fn a_diagnostic_carets_the_authored_text() {
    let env = env();
    let src = "body.s.?z.orValue('') == 'zz'";
    let err = env
        .compile(src, &CompileOpts::default())
        .expect_err("`body.s` is unproven");
    let span = err.span().expect("a span");
    let authored = "body.s.?z.orValue('')";
    assert!(
        span.end <= authored.len() && span.start < span.end,
        "{span:?} lies outside `{authored}` in `{src}`: {err}"
    );
}

/// `diverges: orValue's default is lazy` — the default is evaluated only when the value is
/// absent. Spec CEL evaluates it eagerly, so an erroring default is an error there in both cases.
#[test]
fn lazy_default() {
    let env = env();
    let program = env
        .compile("body.?o.orValue(xs[3]) > 0", &CompileOpts::default())
        .unwrap();
    assert_eq!(run(&env, &program, &present()).ok(), Some(true));
    let err = run(&env, &program, &absent()).expect_err("xs[3] is out of bounds");
    assert!(
        err.to_string().to_lowercase().contains("out of bounds")
            || err.to_string().to_lowercase().contains("index"),
        "{err}"
    );
}
