//! Proven presence — a read that may be absent compiles only when something proves it
//! present.
//!
//! Possibly absent: a record field declared optional (`?`), a key only a record's index signature
//! allows, and any `map` index. A proof is a guard (`has(p)`, `'k' in m`) in a position the rules
//! allow, iteration over the same container, a KNOWN value holding the path, or an `unsafe_map`
//! declaration. Every row of the guard-rules table is a case here, asserted through
//! `fork::presence_report` — the exact list of reads the rules refuse.

#[path = "support/mod.rs"]
mod support;

use typed_cel::fork::presence_report;
use typed_cel::{CelActivation, CelEnvironment, CelTy, CompileOpts, Record};
use serde_json::{json, Value as J};

/// `body: {a: double, o?: double, r?: {c?: double, d: double}, h: {x-t: string, [string]: string},
/// items: list({n: double, note?: string})}`, `m: map(string, double)`,
/// `u: unsafe_map(string, double)`, and `policy: {x?: double, roots: map(string, double)}`.
fn env() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    let r = Record::new("body.r", [("c", CelTy::Num), ("d", CelTy::Num)]).with_optional(["c"]);
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
                ("r", r.into()),
                ("h", h.into()),
                ("items", CelTy::list(item.into())),
            ],
        )
        .with_optional(["o", "r"]),
    );
    env.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    env.declare("u", CelTy::unsafe_map(CelTy::Str, CelTy::Num));
    env.declare(
        "policy",
        Record::new(
            "policy",
            [
                ("x", CelTy::Num),
                ("roots", CelTy::map(CelTy::Str, CelTy::Num)),
            ],
        )
        .with_optional(["x"]),
    );
    env
}

/// The guard-rules table: `(row, source, report)`.
const ROWS: &[(u32, &str, &[(&str, &str)])] = &[
    (1, "body.a > 1", &[]),
    (2, "body.o > 1", &[("body.o", "optional_field")]),
    (3, "has(body.o) && body.o > 1", &[]),
    // Order-insensitive: CEL's `&&` is false whenever either side is, an error absorbed.
    (4, "body.o > 1 && has(body.o)", &[]),
    (5, "!has(body.o) || body.o > 1", &[]),
    (6, "body.o > 1 || !has(body.o)", &[]),
    (7, "has(body.o) ? body.o > 1 : true", &[]),
    (8, "!has(body.o) ? true : body.o > 1", &[]),
    // The wrong branch.
    (
        9,
        "has(body.o) ? true : body.o > 1",
        &[("body.o", "optional_field")],
    ),
    // `||` proves nothing when it is true.
    (
        10,
        "has(body.o) || body.o > 1",
        &[("body.o", "optional_field")],
    ),
    (11, "has(body.r.c)", &[("body.r", "optional_field")]),
    (12, "has(body.r) && has(body.r.c) && body.r.c > 1", &[]),
    // The `has` READS `r`, and a guard never proves the reads inside itself.
    (
        13,
        "has(body.r.c) && body.r.d > 1",
        &[("body.r", "optional_field")],
    ),
    // A declared field of a record with an index signature.
    (14, "body.h[\"x-t\"] == \"a\"", &[]),
    (
        15,
        "body.h[\"x-other\"] == \"a\"",
        &[("body.h[\"x-other\"]", "index_key")],
    ),
    (
        16,
        "\"x-other\" in body.h && body.h[\"x-other\"] == \"a\"",
        &[],
    ),
    (
        17,
        "body.items.all(i, i.note != \"\")",
        &[("i.note", "optional_field")],
    ),
    (18, "body.items.all(i, !has(i.note) || i.note != \"\")", &[]),
    // Shadowed: the inner `i` is a different variable, and nothing proves its `note`.
    (
        19,
        "body.items.all(i, has(i.note) && body.items.all(i, i.note != \"\"))",
        &[("i.note", "optional_field")],
    ),
    // Facts flow into a comprehension body.
    (20, "has(body.o) && [1].all(x, body.o > x)", &[]),
    (21, "m[\"k\"] > 1", &[("m[\"k\"]", "map_key")]),
    (22, "\"k\" in m && m[\"k\"] > 1", &[]),
    // A select and a literal-key index are one segment.
    (23, "has(m.k) && m[\"k\"] > 1", &[]),
    // Iteration.
    (24, "m.all(k, m[k] > 0)", &[]),
    // An `unsafe_map` needs nothing, where a `map` read beside it would. (A COMPUTED key into a
    // rooted `unsafe_map` stays refused by the demand rule: its promise is built from demand, so
    // a key demand cannot name is a key nobody pre-created.)
    (25, "m.all(k, m[k] > u[\"k\"])", &[]),
    (26, "u[\"anything\"] > 1", &[]),
    (27, "\"k\" in m && m[\"j\"] > 1", &[("m[\"j\"]", "map_key")]),
    // No presence path: only a type can prove it.
    (
        28,
        "(true ? body : body).o > 1",
        &[("<expression>.o", "optional_field")],
    ),
];

/// The known-value rows: `policy` known as `{"roots": {"/ws": 1}}`.
const KNOWN_ROWS: &[(u32, &str, &[(&str, &str)])] = &[
    // The known value holds it.
    (29, "policy.roots[\"/ws\"] > 0", &[]),
    (
        30,
        "policy.roots[\"/nope\"] > 0",
        &[("policy.roots[\"/nope\"]", "known_absent")],
    ),
    (31, "policy.x > 1", &[("policy.x", "known_absent")]),
    (32, "has(policy.x) && policy.x > 1", &[]),
];

fn known(env: &CelEnvironment) -> CelActivation {
    let mut k = env.activation();
    k.bind("policy", &json!({"roots": {"/ws": 1}}))
        .expect("binds");
    k
}

fn report(env: &CelEnvironment, src: &str, opts: &CompileOpts<'_>) -> Vec<(String, String)> {
    presence_report(env, src, opts)
        .unwrap_or_else(|e| panic!("`{src}` does not check: {e}"))
        .into_iter()
        .map(|(r, k)| (r, k.to_string()))
        .collect()
}

fn owned(want: &[(&str, &str)]) -> Vec<(String, String)> {
    want.iter()
        .map(|(r, k)| (r.to_string(), k.to_string()))
        .collect()
}

#[test]
fn the_guard_rules_table() {
    let env = env();
    let mut wrong = Vec::new();
    for (row, src, want) in ROWS {
        let got = report(&env, src, &CompileOpts::default());
        if got != owned(want) {
            wrong.push(format!("  row {row} `{src}`: got {got:?}, want {want:?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_known_value_proves_presence() {
    let env = env();
    let k = known(&env);
    let opts = CompileOpts {
        known: Some(&k),
        ..Default::default()
    };
    let mut wrong = Vec::new();
    for (row, src, want) in KNOWN_ROWS {
        let got = report(&env, src, &opts);
        if got != owned(want) {
            wrong.push(format!("  row {row} `{src}`: got {got:?}, want {want:?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    // Row 32: the guard folds against the known value, and the read under it goes with it.
    let residual = env
        .compile("has(policy.x) && policy.x > 1", &opts)
        .expect("compiles");
    assert_eq!(residual.source(), "false");
}

/// A binding with every optional field present, and one with every optional field absent.
fn present() -> Vec<(&'static str, J)> {
    vec![
        (
            "body",
            json!({"a": 2, "o": 3, "r": {"c": 4, "d": 5}, "h": {"x-t": "a", "x-other": "a"},
                   "items": [{"n": 1, "note": "x"}]}),
        ),
        ("m", json!({"k": 2, "j": 3})),
        ("u", json!({"k": 1, "j": 1, "anything": 2})),
    ]
}

fn absent() -> Vec<(&'static str, J)> {
    vec![
        (
            "body",
            json!({"a": 2, "h": {"x-t": "a"}, "items": [{"n": 1}]}),
        ),
        ("m", json!({})),
        ("u", json!({"anything": 2})),
    ]
}

/// What each row answers over [`present`] and [`absent`]: `Some(b)`, or `None` for a run-time
/// `No such key`. The analysis only OBSERVES, so these are the answers the dialect gave before it
/// existed — and the absent column's `None`s are exactly the rows it reports.
const ANSWERS: &[(u32, Option<bool>, Option<bool>)] = &[
    (1, Some(true), Some(true)),
    (2, Some(true), None),
    (3, Some(true), Some(false)),
    (4, Some(true), Some(false)),
    (5, Some(true), Some(true)),
    (6, Some(true), Some(true)),
    (7, Some(true), Some(true)),
    (8, Some(true), Some(true)),
    (9, Some(true), None),
    (10, Some(true), None),
    (11, Some(true), None),
    (12, Some(true), Some(false)),
    (13, Some(true), None),
    (14, Some(true), Some(true)),
    (15, Some(true), None),
    (16, Some(true), Some(false)),
    (17, Some(true), None),
    (18, Some(true), Some(true)),
    (19, Some(true), Some(false)),
    (20, Some(true), Some(false)),
    (21, Some(true), None),
    (22, Some(true), Some(false)),
    (23, Some(true), Some(false)),
    (24, Some(true), Some(true)),
    (25, Some(true), Some(true)),
    (26, Some(true), Some(true)),
    (27, Some(true), Some(false)),
    (28, Some(true), None),
];

fn answer(env: &CelEnvironment, src: &str, binds: &[(&str, J)]) -> Option<bool> {
    let program = typed_cel::fork::compile_unchecked_presence(env, src, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("`{src}`: {e}"));
    let mut act = env.activation();
    for (name, v) in binds {
        act.bind(name, v).expect("binds");
    }
    match program.evaluate(&act) {
        Ok(b) => Some(b),
        Err(e) => {
            assert!(e.to_string().contains("No such key"), "`{src}`: {e}");
            None
        }
    }
}

/// The analysis changes no run-time answer, and it is SOUND on this table: every row it accepts
/// answers without `No such key` over both bindings.
#[test]
fn presence_changes_no_run_time_answer() {
    let env = env();
    let mut wrong = Vec::new();
    for (row, src, want) in ROWS {
        let (_, p, a) = ANSWERS
            .iter()
            .find(|(r, _, _)| r == row)
            .expect("every row has answers");
        let got = (answer(&env, src, &present()), answer(&env, src, &absent()));
        if got != (*p, *a) {
            wrong.push(format!(
                "  row {row} `{src}`: got {got:?}, want {:?}",
                (p, a)
            ));
        }
        if want.is_empty() {
            assert!(
                got.0.is_some() && got.1.is_some(),
                "row {row} `{src}` is accepted yet raises No such key: {got:?}"
            );
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The census, run explicitly: `cargo test -p typed-cel --test presence -- --ignored --nocapture
/// census`. Every generated program, through `presence_report`, one line per read the rules
/// refuse and totals by kind. Every OTHER suite is censused by running it with
/// `--config 'env.CYNCH_CEL_CENSUS="<file>"'`: each compile appends what it would refuse.
#[test]
#[ignore]
fn census() {
    use std::collections::BTreeMap;
    let mut totals: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut programs = 0;
    for (env, batch) in [
        (
            support::gen::roster(),
            support::gen::typed_batch(0x9e37_79b9_7f4a_7c15),
        ),
        (
            support::gen::host_roster(),
            support::gen::host_batch(0x9e37_79b9_7f4a_7c15),
        ),
    ] {
        for (src, _) in batch {
            programs += 1;
            for (read, kind) in presence_report(&env, &src, &CompileOpts::default())
                .unwrap_or_else(|e| panic!("`{src}`: {e}"))
            {
                println!("{kind}\t{read}\t{src}");
                *totals.entry(kind).or_default() += 1;
            }
        }
    }
    println!("{programs} generated programs; unproven reads by kind: {totals:?}");
}

// ---- Story 4: records ----------------------------------------------------------------------

/// Every refused record row is a CHECK error naming the path, both fixes, and the dialect row;
/// a known-absent read names the root that was known.
#[test]
fn unproven_record_reads_are_refused() {
    let env = env();
    let k = known(&env);
    let with_known = CompileOpts {
        known: Some(&k),
        ..Default::default()
    };
    let rows: &[(u32, &str, &[&str])] = &[
        (
            2,
            "body.o > 1",
            &["`body.o`", "has(body.o) && …", "!has(body.o) || …"],
        ),
        (
            9,
            "has(body.o) ? true : body.o > 1",
            &["`body.o`", "has(body.o) && …"],
        ),
        (
            10,
            "has(body.o) || body.o > 1",
            &["`body.o`", "!has(body.o) || …"],
        ),
        (
            11,
            "has(body.r.c)",
            &["`body.r`", "has(body.r) && …", "!has(body.r) || …"],
        ),
        (
            13,
            "has(body.r.c) && body.r.d > 1",
            &["`body.r`", "has(body.r) && …"],
        ),
        (
            15,
            "body.h[\"x-other\"] == \"a\"",
            &[
                "`body.h[\"x-other\"]`",
                "index signature",
                "\"x-other\" in body.h && …",
                "!(\"x-other\" in body.h) || …",
            ],
        ),
        (
            17,
            "body.items.all(i, i.note != \"\")",
            &["`i.note`", "has(i.note) && …"],
        ),
        (
            19,
            "body.items.all(i, has(i.note) && body.items.all(i, i.note != \"\"))",
            &["`i.note`", "!has(i.note) || …"],
        ),
        (
            28,
            "(true ? body : body).o > 1",
            &["`<expression>.o`", "optional"],
        ),
    ];
    for (row, src, fragments) in rows {
        let e = env
            .compile(*src, &CompileOpts::default())
            .expect_err(&format!("row {row} `{src}` must not compile"));
        assert!(
            matches!(e, typed_cel::CelError::Check { .. }),
            "row {row}: {e:?}"
        );
        let text = e.to_string();
        for f in fragments.iter().chain(&["added: proven presence"]) {
            assert!(
                text.contains(f),
                "row {row} `{src}`: {f:?} missing from\n{text}"
            );
        }
    }
    for (row, src, path) in [
        (
            30,
            "policy.roots[\"/nope\"] > 0",
            "`policy.roots[\"/nope\"]`",
        ),
        (31, "policy.x > 1", "`policy.x`"),
    ] {
        let text = env
            .compile(src, &with_known)
            .expect_err(&format!("row {row} `{src}` must not compile"))
            .to_string();
        for f in [path, "KNOWN value of `policy`", "added: proven presence"] {
            assert!(
                text.contains(f),
                "row {row} `{src}`: {f:?} missing from\n{text}"
            );
        }
    }
}

/// Every accepted row that is not about a map compiles through the CHECKED `compile`, and
/// answers what its bindings imply (`ANSWERS`).
#[test]
fn proven_record_reads_compile() {
    let env = env();
    for (row, src, want) in ROWS {
        if !want.is_empty() || (21..=27).contains(row) {
            continue;
        }
        let program = env
            .compile(*src, &CompileOpts::default())
            .unwrap_or_else(|e| panic!("row {row} `{src}`: {e}"));
        let (_, p, a) = ANSWERS.iter().find(|(r, _, _)| r == row).unwrap();
        for (binds, want) in [(present(), p), (absent(), a)] {
            let mut act = env.activation();
            for (name, v) in &binds {
                act.bind(name, v).unwrap();
            }
            assert_eq!(
                program.evaluate(&act).ok(),
                *want,
                "row {row} `{src}` over {binds:?}"
            );
        }
    }
}

/// The soundness claim, measured: 20 000 generated programs that COMPILE, each over 200
/// bindings where every optional field and every map key is independently present or absent,
/// and not one evaluation raises `No such key`.
#[test]
fn a_compiled_program_never_raises_no_such_key() {
    let env = support::gen::roster();
    let mut evaluated = 0usize;
    for seed in 0..20u64 {
        let mut g = support::gen::Gen::new(0x5eed_0000 + seed);
        let acts: Vec<_> = (0..200)
            .map(|_| {
                let mut act = env.activation();
                for (name, v) in support::gen::typed_json(&mut g) {
                    act.bind(name, &v).unwrap();
                }
                act
            })
            .collect();
        for _ in 0..1000 {
            let src = g.typed_bool(4);
            let program = env
                .compile(&src, &CompileOpts::default())
                .unwrap_or_else(|e| panic!("the generator emitted a refused program `{src}`: {e}"));
            for act in &acts {
                if let Err(e) = program.evaluate(act) {
                    let e = e.to_string();
                    assert!(!e.contains("No such key"), "`{src}` raised {e}");
                }
                evaluated += 1;
            }
        }
    }
    assert_eq!(evaluated, 20 * 1000 * 200);
}

/// The residual re-check applies the same rules, with the known values (and a residual's constant
/// slots) in view. For a batch of generated programs compiled with `r` — a record whose optional
/// `o` is present in half the bindings — KNOWN: every one compiles, and the residual answers as the
/// original over the rest.
#[test]
fn residuals_keep_their_proofs() {
    let env = support::gen::roster();
    let mut g = support::gen::Gen::new(0x0e51_d0a1);
    let rest: Vec<Vec<(&str, J)>> = (0..20)
        .map(|_| {
            support::gen::typed_json(&mut g)
                .into_iter()
                .filter(|(n, _)| *n != "r")
                .collect()
        })
        .collect();
    let rs = [json!({"a": 1, "t": "a", "o": 3}), json!({"a": 1, "t": "a"})];
    for i in 0..2000 {
        let src = g.typed_bool(4);
        let original = env
            .compile(&src, &CompileOpts::default())
            .expect("compiles");
        let r = &rs[i % 2];
        let mut k = env.activation();
        k.bind("r", r).unwrap();
        let residual = env
            .compile(
                &src,
                &CompileOpts {
                    known: Some(&k),
                    ..Default::default()
                },
            )
            .unwrap_or_else(|e| panic!("`{src}` with r = {r}: {e}"));
        for binds in &rest {
            let mut full = env.activation();
            let mut part = env.activation();
            for (name, v) in binds {
                full.bind(name, v).unwrap();
                part.bind(name, v).unwrap();
            }
            full.bind("r", r).unwrap();
            assert_eq!(
                format!(
                    "{:?}",
                    original
                        .evaluate(&full)
                        .map_err(|e| e.to_string().replace(original.source(), ""))
                ),
                format!(
                    "{:?}",
                    residual
                        .evaluate(&part)
                        .map_err(|e| e.to_string().replace(residual.source(), ""))
                ),
                "`{src}` with r = {r} -> `{}`",
                residual.source()
            );
        }
    }
}

// ---- Story 5: maps -------------------------------------------------------------------------

#[test]
fn unproven_map_reads_are_refused() {
    let env = env();
    for (row, src, path) in [
        (21, "m[\"k\"] > 1", "`m[\"k\"]`"),
        (27, "\"k\" in m && m[\"j\"] > 1", "`m[\"j\"]`"),
    ] {
        let e = env
            .compile(src, &CompileOpts::default())
            .expect_err(&format!("row {row} `{src}` must not compile"));
        assert!(matches!(e, typed_cel::CelError::Check { .. }), "{e:?}");
        let text = e.to_string();
        for f in [
            path,
            "a map need not hold any key",
            "in m && …",
            "!(",
            "added: proven presence",
        ] {
            assert!(text.contains(f), "row {row}: {f:?} missing from\n{text}");
        }
    }
    // A computed key outside iteration keeps its demand error, which says more.
    let text = env
        .compile(
            "body.h[\"x-t\"] in m && m[body.h[\"x-t\"]] > 1",
            &CompileOpts::default(),
        )
        .expect_err("a computed key")
        .to_string();
    assert!(text.contains("makes the demand set unknowable"), "{text}");
}

#[test]
fn proven_map_reads_compile() {
    let env = env();
    for row in [22, 23, 24, 25, 26] {
        let (_, src, _) = ROWS.iter().find(|(r, _, _)| *r == row).unwrap();
        let program = env
            .compile(*src, &CompileOpts::default())
            .unwrap_or_else(|e| panic!("row {row} `{src}`: {e}"));
        let (_, p, a) = ANSWERS.iter().find(|(r, _, _)| *r == row).unwrap();
        for (m, want) in [(json!({"k": 2, "j": 3}), p), (json!({}), a)] {
            let mut act = env.activation();
            act.bind("m", &m).unwrap();
            act.bind("u", &json!({"k": 1, "anything": 2})).unwrap();
            act.bind("body", &absent()[0].1).unwrap();
            assert_eq!(
                program.evaluate(&act).ok(),
                *want,
                "row {row} `{src}` over m = {m}"
            );
        }
    }
}

/// A map LITERAL whose keys are all string literals is a known value: it proves the keys it was
/// written with, and a key it lacks is refused as known-absent.
#[test]
fn a_map_literal_proves_its_own_keys() {
    let env = CelEnvironment::new();
    let p = env
        .compile("{\"a\": 1}[\"a\"] == 1", &CompileOpts::default())
        .expect("a written key is present");
    assert!(p.evaluate(&env.activation()).unwrap());
    env.compile("{\"a\": 1}.a == 1", &CompileOpts::default())
        .expect("a select is the same segment");
    env.compile(
        "\"b\" in {\"a\": 1} || {\"a\": 1}[\"b\"] == 1",
        &CompileOpts::default(),
    )
    .expect_err("`in` on one literal proves nothing about another");
    let text = env
        .compile("{\"a\": 1}[\"b\"] == 1", &CompileOpts::default())
        .expect_err("an unwritten key")
        .to_string();
    assert!(text.contains("KNOWN value of this map literal"), "{text}");
}
