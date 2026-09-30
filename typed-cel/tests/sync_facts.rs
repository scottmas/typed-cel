//! Sync lazy facts: members that do bounded synchronous work when READ.
//!
//! A program that can suspend (a body program) and also reads an impure fact reads it through a
//! `SyncFacts`. Short-circuiting is then the ordering rule: a fact runs only when the program reads
//! it, at most once per value however many times it is read, in the order the program reads it,
//! and never reports "not yet". Ordering is checked under BOTH evaluators, because a VM that
//! pre-fetched both operands of `||` would pass under `evaluate` and fail under `resume`.

#[path = "support/mod.rs"]
mod support;

use std::sync::{Arc, Mutex};

use support::record_opt;
use typed_cel::{
    CelEnvironment, CelError, CelTy, CelValue, FactFn, LazyValue, RunStep, SyncFacts, Vm, VmRun,
};

// ---- 8. compile-time: a SyncFacts can ride a suspended run between threads ----
const _: () = {
    fn send<T: Send>() {}
    fn sync<T: Sync>() {}
    fn takes(_: Arc<dyn LazyValue>) {}
    #[allow(dead_code)]
    fn all() {
        send::<SyncFacts>();
        sync::<SyncFacts>();
        send::<FactFn>();
        sync::<FactFn>();
        takes(Arc::new(SyncFacts::new()));
    }
};

#[test]
fn sync_facts_are_send_sync_static() {
    // The assertion is the `const` block above: it does not compile if `SyncFacts` (or a fact it
    // holds) could borrow, or could not cross threads. This test gives the property a name.
    let _: Arc<dyn LazyValue> = Arc::new(SyncFacts::new());
}

type Log = Arc<Mutex<Vec<&'static str>>>;

/// A fact that logs its own name and answers `out`.
fn fact(log: &Log, name: &'static str, out: Result<CelValue, &'static str>) -> FactFn {
    let log = Arc::clone(log);
    Box::new(move || {
        log.lock().unwrap().push(name);
        out.clone().map_err(str::to_string)
    })
}

fn logged(log: &Log) -> Vec<&'static str> {
    log.lock().unwrap().clone()
}

/// `f` as a record of the given fields, `nope` declared optional (never given to a `SyncFacts`).
fn env(fields: &[(&str, CelTy)]) -> CelEnvironment {
    let mut all: Vec<(&str, CelTy)> = fields.to_vec();
    all.push(("nope", CelTy::Num));
    let mut env = CelEnvironment::new();
    env.declare("f", record_opt("f", &all, &["nope"]));
    env
}

fn activation(env: &CelEnvironment, facts: SyncFacts) -> typed_cel::CelActivation {
    let mut act = env.activation();
    act.bind_lazy("f", CelValue::Lazy(Arc::new(facts))).unwrap();
    act
}

/// `CelProgram::evaluate` of `src` over `facts`.
fn evaluate(env: &CelEnvironment, src: &str, facts: SyncFacts) -> Result<bool, CelError> {
    let program = env.compile(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    program.evaluate(&activation(env, facts))
}

/// The FIRST `Vm::resume` of `src` over `facts`. A `Need` is a failure: a sync fact never waits.
fn resume(env: &CelEnvironment, src: &str, facts: SyncFacts) -> Result<bool, CelError> {
    let program = env.compile(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    let bc = typed_cel::emit(&program).expect("emits");
    let bindings = activation(env, facts).into_bindings();
    let mut run = VmRun::new(Arc::new(bc));
    match Vm::new().resume(&mut run, &bindings) {
        RunStep::Done(r) => r,
        RunStep::Need(h) => panic!("{src}: a sync fact suspended the run (Need({h:?}))"),
    }
}

type Eval = fn(&CelEnvironment, &str, SyncFacts) -> Result<bool, CelError>;
const BOTH: [(&str, Eval); 2] = [("evaluate", evaluate), ("resume", resume)];

fn bools() -> CelEnvironment {
    env(&[("first", CelTy::Bool), ("second", CelTy::Bool)])
}

fn nums() -> CelEnvironment {
    env(&[("first", CelTy::Num), ("broken", CelTy::Num)])
}

// ---- 1 ----
#[test]
fn a_fact_runs_only_when_read() {
    for (which, eval) in BOTH {
        let log = Log::default();
        let facts = SyncFacts::new()
            .with("first", fact(&log, "first", Ok(CelValue::Bool(true))))
            .with("second", fact(&log, "second", Ok(CelValue::Bool(true))));
        assert_eq!(eval(&bools(), "f.first || f.second", facts).unwrap(), true);
        assert_eq!(logged(&log), ["first"], "under {which}");
    }
}

// ---- 2 ----
#[test]
fn facts_run_in_program_order() {
    for (which, eval) in BOTH {
        let log = Log::default();
        // Declared in the OPPOSITE order to the program's reads, so declaration order cannot pass
        // for program order.
        let facts = SyncFacts::new()
            .with("second", fact(&log, "second", Ok(CelValue::Bool(true))))
            .with("first", fact(&log, "first", Ok(CelValue::Bool(false))));
        assert_eq!(eval(&bools(), "f.first || f.second", facts).unwrap(), true);
        assert_eq!(logged(&log), ["first", "second"], "under {which}");
    }
}

// ---- 3 ----
#[test]
fn a_fact_read_twice_runs_once() {
    for (which, eval) in BOTH {
        let log = Log::default();
        let facts = SyncFacts::new().with("first", fact(&log, "first", Ok(CelValue::Num(2.0))));
        // The second comparison is reached only because the first saw 2.0, and is true only if it
        // sees the same 2.0.
        assert_eq!(
            eval(&nums(), "f.first == 1.0 || f.first == 2.0", facts).unwrap(),
            true,
            "under {which}"
        );
        assert_eq!(logged(&log), ["first"], "under {which}");
    }
}

// ---- 4 ----
#[test]
fn a_sync_fact_never_suspends() {
    let programs = [
        "f.first == 2.0",
        "f.first == 1.0 || f.broken == 1.0",
        "f.broken == 1.0",
        "f.broken == 1.0 || true",
        "has(f.first) && f.first > 0.0",
        "has(f.nope)",
        "f.nope == 1.0",
    ];
    for src in programs {
        let log = Log::default();
        let facts = SyncFacts::new()
            .with("first", fact(&log, "first", Ok(CelValue::Num(2.0))))
            .with("broken", fact(&log, "broken", Err("the lookup timed out")));
        // `resume` panics on a `Need`; the verdict itself may be an error.
        let _ = resume(&nums(), src, facts);
    }
}

// ---- 5 ----
#[test]
fn a_failing_fact_is_absorbed_like_any_error() {
    for (which, eval) in BOTH {
        let log = Log::default();
        let facts = SyncFacts::new().with(
            "broken",
            fact(&log, "broken", Err("jwks endpoint refused the dial")),
        );
        assert_eq!(
            eval(&nums(), "f.broken == 1.0 || true", facts).unwrap(),
            true,
            "under {which}"
        );

        let facts = SyncFacts::new().with(
            "broken",
            fact(&log, "broken", Err("jwks endpoint refused the dial")),
        );
        match eval(&nums(), "f.broken == 1.0", facts) {
            Err(CelError::Evaluation { message, .. }) => assert!(
                message.contains("jwks endpoint refused the dial"),
                "under {which}: the fact's own failure text is lost: {message}"
            ),
            other => panic!("under {which}: expected an Evaluation error, got {other:?}"),
        }
    }
}

// ---- 6 ----
#[test]
fn a_failed_fact_is_not_retried() {
    for (which, eval) in BOTH {
        let log = Log::default();
        let facts = SyncFacts::new()
            .with("broken", fact(&log, "broken", Err("flaky")))
            .with("first", fact(&log, "first", Ok(CelValue::Num(1.0))));
        // Both failures are absorbed by a leaf that must be read (a constant `true` would settle
        // the chain before any read).
        assert_eq!(
            eval(
                &nums(),
                "f.broken == 1.0 || f.broken == 2.0 || f.first == 1.0",
                facts
            )
            .unwrap(),
            true,
            "under {which}"
        );
        assert_eq!(logged(&log), ["broken", "first"], "under {which}");
    }
}

// ---- 7 ----
#[test]
fn an_undeclared_fact_is_no_such_member() {
    let facts = SyncFacts::new().with("first", Box::new(|| Ok(CelValue::Num(1.0))));
    assert!(
        matches!(facts.member("nope"), Err(CelError::NoSuchMember { ref key }) if key == "nope"),
        "{:?}",
        facts.member("nope")
    );

    for (which, eval) in BOTH {
        let facts = || SyncFacts::new().with("first", Box::new(|| Ok(CelValue::Num(1.0))));
        assert_eq!(
            eval(&nums(), "has(f.nope)", facts()).unwrap(),
            false,
            "under {which}"
        );
        // The same `no such key` a materialized record gives for an absent optional field.
        match eval(&nums(), "f.nope == 1.0", facts()) {
            Err(CelError::Evaluation { message, .. }) => {
                assert!(message.contains("nope"), "under {which}: {message}")
            }
            other => panic!("under {which}: expected an Evaluation error, got {other:?}"),
        }
    }
}

// ---- 9 ----
#[test]
fn keys_are_the_declared_names() {
    let mut env = CelEnvironment::new();
    env.declare("f", CelTy::map(CelTy::Str, CelTy::Num));
    for (which, eval) in BOTH {
        let log = Log::default();
        let facts = || {
            SyncFacts::new()
                .with("first", fact(&log, "first", Ok(CelValue::Num(1.0))))
                .with("broken", fact(&log, "broken", Err("never asked")))
        };
        assert_eq!(
            eval(&env, r#""first" in f"#, facts()).unwrap(),
            true,
            "under {which}"
        );
        assert_eq!(
            eval(&env, r#""other" in f"#, facts()).unwrap(),
            false,
            "under {which}"
        );
        assert_eq!(
            eval(&env, "has(f.broken)", facts()).unwrap(),
            true,
            "under {which}"
        );
        assert!(
            logged(&log).is_empty(),
            "under {which}: presence ran a fact: {:?}",
            logged(&log)
        );
    }

    // Asked directly, too — not only through the evaluator's keys-first shortcut.
    let log = Log::default();
    let facts = SyncFacts::new().with("first", fact(&log, "first", Ok(CelValue::Num(1.0))));
    assert_eq!(
        facts.poll_has("first").unwrap(),
        typed_cel::Presence::Known(true)
    );
    assert_eq!(
        facts.poll_has("other").unwrap(),
        typed_cel::Presence::Known(false)
    );
    assert!(logged(&log).is_empty());
}

#[test]
fn a_second_declaration_replaces_the_first() {
    let facts = SyncFacts::new()
        .with("first", Box::new(|| Ok(CelValue::Num(1.0))))
        .with("first", Box::new(|| Ok(CelValue::Num(2.0))));
    assert!(matches!(facts.member("first"), Ok(v) if v == CelValue::Int(2)));
    assert_eq!(facts.keys().unwrap().count(), 1);
}
