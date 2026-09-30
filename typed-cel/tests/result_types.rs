//! Programs whose result is not `bool`: `compile_returning`, and the result type carried through
//! specialization and onto the fast backend.
//!
//! `compile` stays bool-only — every existing caller (an assertion, a system condition) relies on a
//! non-bool expression being a BUILD error. A decision point with more than two outcomes names the
//! type it must produce instead, and the checker still proves it.

use typed_cel::CompileOpts;
use typed_cel::{
    emit, CelEnvironment, CelError, CelTy, CelValue, Facts, FastProgram, FastScratch, FieldId,
    Record, ResultKind, Vm,
};

fn str_of(v: &CelValue) -> Option<&str> {
    match v {
        CelValue::Str(s) => Some(s),
        _ => None,
    }
}

#[test]
fn compile_is_still_bool_only() {
    match CelEnvironment::new().compile("\"x\"", &CompileOpts::default()) {
        Err(CelError::NotBoolean { actual, .. }) => assert_eq!(actual, "string"),
        other => panic!("want NotBoolean, got {other:?}"),
    }
}

#[test]
fn compile_returning_accepts_its_declared_type() {
    let env = CelEnvironment::new();
    let p = env
        .compile(
            "\"allow\"",
            &CompileOpts {
                returning: Some(&CelTy::Str),
                ..Default::default()
            },
        )
        .expect("a string program compiles as a string program");
    assert_eq!(p.result_kind(), ResultKind::Str);
    let got = Vm::new()
        .eval_result(&emit(&p).expect("emits"), &env.runtime().activation())
        .expect("evaluates");
    assert_eq!(str_of(&got), Some("allow"), "{got:?}");

    // `compile` itself answers `Bool` for the kind.
    assert_eq!(
        env.compile("true", &CompileOpts::default())
            .expect("compiles")
            .result_kind(),
        ResultKind::Bool
    );
}

#[test]
fn compile_returning_refuses_any_other_type() {
    match CelEnvironment::new().compile(
        "true",
        &CompileOpts {
            returning: Some(&CelTy::Str),
            ..Default::default()
        },
    ) {
        Err(CelError::WrongResultType {
            expected, actual, ..
        }) => {
            assert_eq!(expected, "string");
            assert_eq!(actual, "bool");
        }
        other => panic!("want WrongResultType, got {other:?}"),
    }

    // A ternary whose arms disagree is refused by the checker, before the result type is looked at.
    let mut env = CelEnvironment::new();
    env.declare("x", CelTy::Bool);
    match env.compile(
        "x ? \"a\" : 1",
        &CompileOpts {
            returning: Some(&CelTy::Str),
            ..Default::default()
        },
    ) {
        Err(CelError::Check { .. }) => {}
        other => panic!("want a check error, got {other:?}"),
    }
}

#[test]
fn dyn_is_not_a_string() {
    let mut env = CelEnvironment::new();
    env.declare("d", CelTy::Dyn);
    let err = env
        .compile(
            "d",
            &CompileOpts {
                returning: Some(&CelTy::Str),
                ..Default::default()
            },
        )
        .expect_err("uncertainty must not become a tag");
    assert!(
        matches!(
            err,
            CelError::Check { .. } | CelError::WrongResultType { .. }
        ),
        "{err:?}"
    );
}

#[test]
fn an_unsupported_result_type_is_refused() {
    let err = CelEnvironment::new()
        .compile(
            "[1]",
            &CompileOpts {
                returning: Some(&CelTy::list(CelTy::Num)),
                ..Default::default()
            },
        )
        .expect_err("a list is not a result kind");
    assert!(matches!(err, CelError::WrongResultType { .. }), "{err:?}");
}

fn env_ku() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.declare("k", Record::new("k", [("a", CelTy::Str)]));
    env.declare("u", CelTy::Str);
    env
}

#[test]
fn a_specialized_program_keeps_its_result_type() {
    let env = env_ku();
    let p = env
        .compile(
            "k.a == u ? \"allow\" : \"eacces\"",
            &CompileOpts {
                returning: Some(&CelTy::Str),
                ..Default::default()
            },
        )
        .expect("compiles");
    let mut known = env.activation();
    known
        .bind("k", &serde_json::json!({"a": "z"}))
        .expect("binds");
    let residual = env
        .compile(
            p.source(),
            &CompileOpts {
                returning: Some(&CelTy::Str),
                known: Some(&known),
            },
        )
        .expect("a Str residual re-checks");
    assert_eq!(residual.result_kind(), ResultKind::Str);
    let src = residual.source();
    assert!(
        src.contains("\"z\"") && src.contains('u') && !src.contains("k."),
        "{src}"
    );

    let code = emit(&residual).expect("emits");
    for (u, want) in [("z", "allow"), ("y", "eacces")] {
        let mut act = env.runtime().activation();
        act.bind_fact("u", CelValue::Str(u.into()));
        let got = Vm::new().eval_result(&code, &act).expect("evaluates");
        assert_eq!(str_of(&got), Some(want), "u = {u}");
    }
}

#[test]
fn a_program_folded_to_a_constant_string_is_a_literal() {
    let env = env_ku();
    let p = env
        .compile(
            "k.a == u ? \"allow\" : \"eacces\"",
            &CompileOpts {
                returning: Some(&CelTy::Str),
                ..Default::default()
            },
        )
        .expect("compiles");
    let mut known = env.activation();
    known
        .bind("k", &serde_json::json!({"a": "z"}))
        .expect("binds");
    known.bind("u", &serde_json::json!("z")).expect("binds");
    let residual = env
        .compile(
            p.source(),
            &CompileOpts {
                returning: Some(&CelTy::Str),
                known: Some(&known),
            },
        )
        .expect("specializes");
    assert_eq!(residual.source(), "\"allow\"");
    assert_eq!(residual.result_kind(), ResultKind::Str);
}

/// One string field: the facts a tag program reads.
struct One<'a>(&'a str);

impl Facts for One<'_> {
    fn bool(&self, _: FieldId) -> Option<bool> {
        None
    }
    fn num(&self, _: FieldId) -> Option<f64> {
        None
    }
    fn str(&self, _: FieldId) -> Option<&str> {
        Some(self.0)
    }
    fn has(&self, _: FieldId) -> bool {
        true
    }
}

const TAGS: &[&str] = &["allow", "readonly", "eacces"];

#[test]
fn the_fast_backend_answers_a_tag_id() {
    let mut env = CelEnvironment::new();
    env.declare("u", CelTy::Str);
    let p = env
        .compile(
            r#"u == "a" ? "allow" : u == "r" ? "readonly" : u == "?" ? "maybe" : u"#,
            &CompileOpts {
                returning: Some(&CelTy::Str),
                ..Default::default()
            },
        )
        .expect("compiles");
    let fast = FastProgram::new(&p).expect("lowers");
    let mut scratch = FastScratch::default();
    for (u, want) in [
        ("a", Some(0)),
        ("r", Some(1)),
        // A string that is not one of the tags is `None`, never a default.
        ("?", None),
        // A tag computed from the facts is still a tag.
        ("eacces", Some(2)),
        ("x", None),
    ] {
        let got = fast
            .decide_tag(&One(u), &mut scratch, TAGS)
            .expect("decides");
        assert_eq!(got, want, "u = {u}");
        // And the same answer as the value the evaluator computes.
        let mut act = env.activation();
        act.bind("u", &serde_json::json!(u)).expect("binds");
        let value = Vm::new()
            .eval_result(&emit(&p).expect("emits"), &act)
            .expect("evaluates");
        let by_value = str_of(&value).and_then(|s| TAGS.iter().position(|t| *t == s));
        assert_eq!(got, by_value, "u = {u}");
    }
}

#[test]
fn a_tag_from_a_non_string_program_is_an_error() {
    let mut env = CelEnvironment::new();
    env.declare("u", CelTy::Str);
    let p = env
        .compile("u == \"a\"", &CompileOpts::default())
        .expect("compiles");
    let fast = FastProgram::new(&p).expect("lowers");
    let err = fast
        .decide_tag(&One("a"), &mut FastScratch::default(), TAGS)
        .expect_err("a bool is not a tag");
    assert!(err.to_string().contains("rather than a string"), "{err}");
}
