//! Closed string sets: a string field an environment declares holds one of a fixed list of values.
//!
//! It changes no meaning — the field is still a `string`, compares as one, and a literal outside the
//! list is still just a string that never equals the field. What it changes is REPRESENTATION on
//! the fast backend: `f == "a"`, `f != "a"` and `f == "a" || f == "b"` against listed values
//! compare a small TAG (the value's index in the list) that a [`Facts`] provider may answer
//! directly, instead of comparing string bytes. A provider that answers only `str` still works:
//! the backend looks the string up in the list.

#[path = "support/mod.rs"]
mod support;

use support::gen::Gen;
use typed_cel::CompileOpts;
use typed_cel::{
    emit, CelEnvironment, CelError, CelProgram, CelTy, CelValue, Facts, FastProgram, FastScratch,
    FieldId, Record, ResultKind, Vm,
};

const ACCESS: &[&str] = &["read", "write", "create", "remove", "setmeta", "exec"];

fn env() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.declare(
        "req",
        Record::new(
            "req",
            [
                ("access", CelTy::Str),
                ("other", CelTy::Str),
                ("n", CelTy::Num),
            ],
        ),
    );
    env.declare_enum(&["req", "access"], ACCESS)
        .expect("a declared string field");
    env
}

/// A request read by field, answering the enum field by TAG when `by_tag`, else by string only.
struct Req<'a> {
    access: &'a str,
    other: &'a str,
    by_tag: bool,
    fields: Vec<&'static str>,
}

impl Facts for Req<'_> {
    fn bool(&self, _: FieldId) -> Option<bool> {
        None
    }
    fn num(&self, _: FieldId) -> Option<f64> {
        Some(1.0)
    }
    fn str(&self, f: FieldId) -> Option<&str> {
        match self.fields[f.index()] {
            "access" => Some(self.access),
            "other" => Some(self.other),
            _ => None,
        }
    }
    fn tag(&self, f: FieldId) -> Option<u8> {
        if !self.by_tag || self.fields[f.index()] != "access" {
            return None;
        }
        // A value outside the list has no tag of its own: `OTHER`.
        Some(
            ACCESS
                .iter()
                .position(|a| *a == self.access)
                .map_or(typed_cel::TAG_OTHER, |i| i as u8),
        )
    }
    fn has(&self, _: FieldId) -> bool {
        true
    }
}

fn fields_of(p: &FastProgram) -> Vec<&'static str> {
    p.fields()
        .iter()
        .map(|f| match f.segments().last() {
            Some("access") => "access",
            Some("other") => "other",
            Some("n") => "n",
            other => panic!("reads {other:?}"),
        })
        .collect()
}

#[test]
fn declaring_an_enum_needs_a_declared_string_field() {
    let mut env = env();
    for (path, why) in [
        (&["req", "n"][..], "a double"),
        (&["req", "nope"][..], "undeclared"),
        (&["nope"][..], "undeclared root"),
    ] {
        let got = env.declare_enum(path, &["a"]);
        assert!(
            matches!(got, Err(CelError::Registration { .. })),
            "{path:?} ({why}) must be refused"
        );
    }
    let got = env.declare_enum(&["req", "other"], &["a", "a"]);
    assert!(
        matches!(got, Err(CelError::Registration { .. })),
        "a repeated value is refused"
    );
    let many: Vec<String> = (0..65).map(|i| format!("v{i}")).collect();
    let many: Vec<&str> = many.iter().map(String::as_str).collect();
    let got = env.declare_enum(&["req", "other"], &many);
    assert!(
        matches!(got, Err(CelError::Registration { .. })),
        "more than 64 values is refused"
    );
}

#[test]
fn a_listed_literal_compares_as_a_tag() {
    let env = env();
    let p = env
        .compile(
            r#"req.access == "read" ? "r" : req.access != "write" ? "nw" : "w""#,
            &CompileOpts {
                returning: Some(&CelTy::Str),
                ..Default::default()
            },
        )
        .expect("compiles");
    assert_eq!(p.result_kind(), ResultKind::Str);
    let fast = FastProgram::new(&p).expect("lowers");
    let ops = fast.op_names();
    assert!(
        ops.iter().any(|o| o.contains("Tag")),
        "no tag op:\n{}",
        fast.listing()
    );
    assert!(
        !ops.contains(&"EqK") && !ops.contains(&"CondEqK"),
        "{}",
        fast.listing()
    );
}

#[test]
fn an_unlisted_literal_compares_as_a_string() {
    let env = env();
    // "bogus" is not in the list, so it has no tag: the comparison stays a string comparison, and
    // a value outside the list that happens to BE "bogus" still equals it.
    let p = env
        .compile(r#"req.access == "bogus""#, &CompileOpts::default())
        .expect("compiles");
    let fast = FastProgram::new(&p).expect("lowers");
    assert!(
        !fast.op_names().iter().any(|o| o.contains("Tag")),
        "{}",
        fast.listing()
    );
    let fields = fields_of(&fast);
    for by_tag in [false, true] {
        let req = Req {
            access: "bogus",
            other: "",
            by_tag,
            fields: fields.clone(),
        };
        assert_eq!(
            fast.decide(&req, &mut FastScratch::default())
                .map_err(|e| e.to_string()),
            Ok(true)
        );
    }
}

#[test]
fn an_or_chain_of_listed_values_is_one_tag_test() {
    let env = env();
    let p = env
        .compile(
            r#"req.access == "read" || req.access == "exec" || req.access == "remove""#,
            &CompileOpts::default(),
        )
        .expect("compiles");
    let fast = FastProgram::new(&p).expect("lowers");
    assert_eq!(
        fast.op_names().iter().filter(|o| o.contains("Tag")).count(),
        1,
        "{}",
        fast.listing()
    );
}

/// Every host alike — a JSON binding, a fact binding, and `Facts` with and without a tag-answering
/// provider — over generated tag programs and every listed value plus two outside the list.
#[test]
fn generated_tag_programs_answer_alike_on_every_host() {
    let env = env();
    let mut g = Gen::new(0x7A65);
    let values: Vec<&str> = ACCESS.iter().copied().chain(["bogus", ""]).collect();
    let (mut compared, mut tagged) = (0usize, 0usize);
    let mut mismatches = Vec::new();
    for index in 0..600 {
        let src = gen_tag(&mut g, 3);
        let p: CelProgram = env
            .compile(&src, &CompileOpts::default())
            .unwrap_or_else(|e| panic!("`{src}` does not compile: {e}"));
        let fast = FastProgram::new(&p).expect("lowers");
        let code = emit(&p).expect("emits");
        if fast.op_names().iter().any(|o| o.contains("Tag")) {
            tagged += 1;
        }
        let fields = fields_of(&fast);
        for access in &values {
            for other in ["read", "x"] {
                let mut act = env.activation();
                act.bind(
                    "req",
                    &serde_json::json!({"access": access, "other": other, "n": 1.0}),
                )
                .expect("binds");
                let want = p.evaluate(&act).map_err(|e| e.to_string());
                let mut prepared = env.runtime().activation();
                prepared.bind_fact(
                    "req",
                    CelValue::record([
                        ("access".into(), CelValue::from(*access)),
                        ("other".into(), CelValue::Str(other.into())),
                        ("n".into(), CelValue::Num(1.0)),
                    ]),
                );
                let over_fact = Vm::new().eval(&code, &prepared).map_err(|e| e.to_string());
                for by_tag in [false, true] {
                    let req = Req {
                        access,
                        other,
                        by_tag,
                        fields: fields.clone(),
                    };
                    let got = fast
                        .decide(&req, &mut FastScratch::default())
                        .map_err(|e| e.to_string());
                    compared += 1;
                    if got != want || over_fact != want {
                        mismatches.push(format!(
                            "#{index} `{src}` access={access:?} other={other:?} by_tag={by_tag}: \
                             bound json {want:?}, bound fact {over_fact:?}, facts {got:?}"
                        ));
                    }
                }
            }
        }
    }
    assert!(
        mismatches.is_empty(),
        "{} mismatch(es):\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
    assert!(tagged >= 300, "only {tagged} programs lowered to a tag op");
    assert!(compared >= 10_000, "only {compared} comparisons");
}

/// A `bool` expression comparing `req.access` (and `req.other`, which is NOT an enum) with listed
/// and unlisted literals, in value and branch position, alone and in `||`/`&&` chains.
fn gen_tag(g: &mut Gen, depth: u32) -> String {
    let lit = |g: &mut Gen| g.pick(&["read", "write", "exec", "remove", "bogus", ""]);
    if depth == 0 {
        let field = g.pick(&["req.access", "req.access", "req.other"]);
        let op = g.pick(&["==", "!="]);
        return format!("({field} {op} \"{}\")", lit(g));
    }
    let d = depth - 1;
    match g.below(6) {
        0 => format!("({} || {})", gen_tag(g, d), gen_tag(g, d)),
        1 => format!("({} && {})", gen_tag(g, d), gen_tag(g, d)),
        2 => format!("(!{})", gen_tag(g, d)),
        3 => format!(
            "({} ? {} : {})",
            gen_tag(g, d),
            gen_tag(g, d),
            gen_tag(g, d)
        ),
        4 => format!(
            "(req.access == \"{}\" || req.access == \"{}\")",
            lit(g),
            lit(g)
        ),
        _ => gen_tag(g, 0),
    }
}
