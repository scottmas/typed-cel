//! A VM that can wait.
//!
//! `Vm::resume` runs a `VmRun` until it finishes or reads a lazy member that is not available yet.
//! A `Need` leaves the program counter and the stack exactly where they were, so the next resume
//! re-executes the same read and nothing before it. Every verdict here is compared with
//! `CelProgram::evaluate` — never with `Vm::eval`, which shares `step` with `resume` and so could
//! not disagree with it.

#[path = "support/mod.rs"]
mod support;

#[path = "support/scripted.rs"]
mod scripted;

use std::sync::Arc;

use scripted::{Scripted, Slot};
use support::gen::{roster, typed_json, Gen, JsonLazy};
use support::record_opt;
use typed_cel::{
    CelActivation, CelBindings, CelEnvironment, CelError, CelTemplate, CelTy, CelValue,
    DemandHandle, RunStep, Vm, VmRun,
};

// ---- 11. compile-time: everything a waiting run holds can ride a flow between threads ----
const _: () = {
    fn send<T: Send>() {}
    fn sync<T: Sync>() {}
    #[allow(dead_code)]
    fn all() {
        send::<VmRun>();
        send::<CelBindings>();
        send::<RunStep>();
        send::<CelTemplate>();
        sync::<CelTemplate>();
    }
};

#[test]
fn runs_bindings_and_templates_are_thread_safe() {
    // The assertion is the `const` block above: it does not compile if any of the types holds a
    // `CelTy`/`TypeEnv` (`Rc`). This test exists so the property has a name in the report.
}

fn env() -> CelEnvironment {
    let mut env = CelEnvironment::new();
    env.declare(
        "v",
        record_opt(
            "v",
            &[
                ("x", CelTy::Num),
                ("y", CelTy::Num),
                ("kind", CelTy::Str),
                ("big", CelTy::Str),
                ("name", CelTy::Str),
                ("missing", CelTy::Num),
                ("field", CelTy::Num),
            ],
            &["missing", "field"],
        ),
    );
    env.declare("m", CelTy::map(CelTy::Str, CelTy::Num));
    env.declare("n", CelTy::Num);
    env
}

fn scripted(slots: &[(&str, Slot)]) -> Arc<Scripted> {
    let s = Arc::new(Scripted::default());
    for (name, slot) in slots {
        s.set(name, slot.clone());
    }
    s
}

fn activation(env: &CelEnvironment, lazies: &[(&str, &Arc<Scripted>)]) -> CelActivation {
    let mut act = env.activation();
    for (name, v) in lazies {
        let v: Arc<dyn typed_cel::LazyValue> = Arc::clone(v) as _;
        act.bind_lazy(name, CelValue::Lazy(v)).unwrap();
    }
    act
}

/// Compile, emit, and start a run with the given lazies bound.
fn start(src: &str, lazies: &[(&str, &Arc<Scripted>)]) -> (VmRun, CelBindings) {
    let env = env();
    let program = env.compile(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    let bc = typed_cel::emit(&program).expect("emits");
    (
        VmRun::new(Arc::new(bc)),
        activation(&env, lazies).into_bindings(),
    )
}

/// `CelProgram::evaluate` of `src` over the given lazies.
fn evaluate(src: &str, lazies: &[(&str, &Arc<Scripted>)]) -> Result<bool, CelError> {
    let env = env();
    let program = env.compile(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    program.evaluate(&activation(&env, lazies))
}

fn done(step: RunStep) -> Result<bool, CelError> {
    match step {
        RunStep::Done(r) => r,
        RunStep::Need(h) => panic!("expected Done, got Need({h:?})"),
    }
}

fn need(step: RunStep) -> DemandHandle {
    match step {
        RunStep::Need(h) => h,
        RunStep::Done(r) => panic!("expected Need, got Done({r:?})"),
    }
}

/// `Ok(b)` exactly; any `Err` matches any `Err`.
fn same(a: &Result<bool, CelError>, b: &Result<bool, CelError>) -> bool {
    match (a, b) {
        (Ok(x), Ok(y)) => x == y,
        (Err(_), Err(_)) => true,
        _ => false,
    }
}

// ---- 1 ----

const HAND_PICKED: &[&str] = &[
    "true",
    "1.0 < 2.0",
    "v.x == 1.0",
    "v.x == 1.0 && v.y == 2.0",
    "v.missing == 1.0 && false",
    "false && v.missing == 1.0",
    "v.missing == 1.0 || true",
    "true || v.missing == 1.0",
    "v.missing == 1.0 || v.x == 1.0",
    "v.x > 0.0 ? v.kind == \"a\" : v.kind == \"b\"",
    "\"a\" in m",
    "\"zz\" in m",
    "has(v.field)",
    "has(v.missing)",
    "[1.0, 2.0, 3.0].exists(i, i == v.x)",
    "[1.0, 2.0, 3.0].all(i, i > v.y)",
    "v.name.startsWith(\"bo\")",
    "v.name.endsWith(\"ob\") && v.name.contains(\"o\")",
    "duration(\"1s\") < duration(\"2s\")",
    "m[\"a\"] == 1.0 && v.missing == 2.0",
];

#[test]
fn resume_equals_evaluate_when_everything_is_ready() {
    let v = scripted(&[
        ("x", Slot::Ready(CelValue::Num(1.0))),
        ("y", Slot::Ready(CelValue::Num(2.0))),
        ("kind", Slot::Ready(CelValue::Str("a".into()))),
        ("big", Slot::Ready(CelValue::Str("z".into()))),
        ("name", Slot::Ready(CelValue::Str("bob".into()))),
        ("field", Slot::Ready(CelValue::Num(4.0))),
    ]);
    let m = scripted(&[("a", Slot::Ready(CelValue::Num(1.0)))]);
    let mut mismatches = Vec::new();
    for src in HAND_PICKED {
        let lazies = [("v", &v), ("m", &m)];
        let want = evaluate(src, &lazies);
        let (mut run, bindings) = start(src, &lazies);
        let got = done(Vm::new().resume(&mut run, &bindings));
        if !same(&want, &got) {
            mismatches.push(format!("{src}: evaluate {want:?}, resume {got:?}"));
        }
    }

    // The typed generator, one program per seed, bound both materialized and (odd seeds) with the
    // record root as a lazy view — so the VM's lazy read arms run on generated programs too.
    let env = roster();
    let mut compared = 0usize;
    for seed in 1..=500u64 {
        let mut g = Gen::new(seed);
        let src = g.typed_bool(4);
        let program = env
            .compile(&src)
            .unwrap_or_else(|e| panic!("seed {seed}: `{src}` does not compile: {e}"));
        let bc = Arc::new(typed_cel::emit(&program).expect("emits"));
        let json = typed_json(&mut g);
        let mut act = env.activation();
        for (name, value) in &json {
            match (seed % 2 == 1, *name, value) {
                (true, "r", serde_json::Value::Object(fields)) => {
                    act.bind_lazy(
                        name,
                        CelValue::Lazy(Arc::new(JsonLazy::new(fields.clone()))),
                    )
                    .unwrap();
                }
                _ => {
                    act.bind(name, value).unwrap();
                }
            }
        }
        let want = program.evaluate(&act);
        let bindings = act.into_bindings();
        let mut run = VmRun::new(bc);
        let got = done(Vm::new().resume(&mut run, &bindings));
        compared += 1;
        if !same(&want, &got) {
            mismatches.push(format!(
                "seed {seed}: `{src}` over {json:?}: evaluate {want:?}, resume {got:?}"
            ));
        }
    }
    assert_eq!(compared, 500);
    assert!(
        mismatches.is_empty(),
        "{} mismatch(es):\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

// ---- 2 ----

#[test]
fn a_pending_select_is_need_and_leaves_pc_and_stack() {
    let v = scripted(&[("x", Slot::Pending(7))]);
    let (mut run, bindings) = start("v.x == 1.0", &[("v", &v)]);
    let vm = Vm::new();
    assert_eq!(need(vm.resume(&mut run, &bindings)), DemandHandle::new(7));
    let (pc, depth) = (run.pc(), run.stack_depth());
    assert!(pc.is_some() && depth.is_some(), "a waiting run has a state");
    assert_eq!(need(vm.resume(&mut run, &bindings)), DemandHandle::new(7));
    assert_eq!(run.pc(), pc, "a pending read moved the program counter");
    assert_eq!(run.stack_depth(), depth, "a pending read changed the stack");
    v.set("x", Slot::Ready(CelValue::Num(1.0)));
    assert!(matches!(
        vm.resume(&mut run, &bindings),
        RunStep::Done(Ok(true))
    ));
}

// ---- 3 ----

#[test]
fn resume_re_executes_only_the_pending_read() {
    let v = scripted(&[
        ("y", Slot::Ready(CelValue::Num(2.0))),
        ("x", Slot::Pending(1)),
    ]);
    let (mut run, bindings) = start("v.y == 2.0 && v.x == 1.0", &[("v", &v)]);
    let vm = Vm::new();
    need(vm.resume(&mut run, &bindings));
    need(vm.resume(&mut run, &bindings));
    v.set("x", Slot::Ready(CelValue::Num(1.0)));
    assert!(done(vm.resume(&mut run, &bindings)).unwrap());
    assert_eq!(v.reads("y"), 1, "a resume restarted the program");
    assert_eq!(v.reads("x"), 3);
}

// ---- 4 ----

#[test]
fn short_circuit_never_polls_the_tail() {
    let v = scripted(&[
        ("kind", Slot::Ready(CelValue::Str("b".into()))),
        ("big", Slot::Pending(9)),
    ]);
    let (mut run, bindings) = start("v.kind == \"a\" && v.big == \"z\"", &[("v", &v)]);
    assert!(matches!(
        Vm::new().resume(&mut run, &bindings),
        RunStep::Done(Ok(false))
    ));
    assert_eq!(v.reads("big"), 0);
}

// ---- 5 ----

#[test]
fn an_erroring_left_then_pending_right_suspends() {
    const SRC: &str = "v.missing == 1.0 && v.x == 2.0";
    let vm = Vm::new();

    let v = scripted(&[("x", Slot::Pending(3))]);
    let (mut run, bindings) = start(SRC, &[("v", &v)]);
    need(vm.resume(&mut run, &bindings));
    v.set("x", Slot::Ready(CelValue::Num(3.0)));
    let got = done(vm.resume(&mut run, &bindings));
    let ready = scripted(&[("x", Slot::Ready(CelValue::Num(3.0)))]);
    let want = evaluate(SRC, &[("v", &ready)]);
    assert!(matches!(got, Ok(false)), "{got:?}");
    assert!(same(&want, &got), "evaluate {want:?}, resume {got:?}");

    let v = scripted(&[("x", Slot::Pending(3))]);
    let (mut run, bindings) = start(SRC, &[("v", &v)]);
    need(vm.resume(&mut run, &bindings));
    v.set("x", Slot::Ready(CelValue::Num(2.0)));
    let got = done(vm.resume(&mut run, &bindings));
    let ready = scripted(&[("x", Slot::Ready(CelValue::Num(2.0)))]);
    let want = evaluate(SRC, &[("v", &ready)]);
    assert!(got.is_err(), "the caught left error was lost: {got:?}");
    assert!(same(&want, &got), "evaluate {want:?}, resume {got:?}");
}

// ---- 6 ----

#[test]
fn need_inside_a_comprehension_resumes_in_place() {
    let v = scripted(&[("name", Slot::Pending(5))]);
    let (mut run, bindings) = start("[\"a\", \"b\"].exists(k, v.name == k)", &[("v", &v)]);
    let vm = Vm::new();
    need(vm.resume(&mut run, &bindings));
    v.set("name", Slot::Ready(CelValue::Str("b".into())));
    assert!(matches!(
        vm.resume(&mut run, &bindings),
        RunStep::Done(Ok(true))
    ));
}

// ---- 7 ----

#[test]
fn has_and_in_suspend_on_pending_presence() {
    let vm = Vm::new();

    let v = scripted(&[("field", Slot::Pending(1))]);
    let (mut run, bindings) = start("has(v.field)", &[("v", &v)]);
    assert_eq!(need(vm.resume(&mut run, &bindings)), DemandHandle::new(1));
    v.set("field", Slot::Missing);
    assert!(matches!(
        vm.resume(&mut run, &bindings),
        RunStep::Done(Ok(false))
    ));

    let m = scripted(&[("a", Slot::Pending(2))]);
    let (mut run, bindings) = start("\"a\" in m", &[("m", &m)]);
    assert_eq!(need(vm.resume(&mut run, &bindings)), DemandHandle::new(2));
    m.set("a", Slot::Missing);
    assert!(matches!(
        vm.resume(&mut run, &bindings),
        RunStep::Done(Ok(false))
    ));
}

// ---- 8 ----

#[test]
fn eval_reads_pending_as_the_tree_walker_does() {
    let env = env();
    let v = scripted(&[("x", Slot::Pending(4))]);
    for (src, want_ok) in [
        ("v.x == 1.0 && false", Some(false)),
        ("v.x == 1.0", None),
        ("false || v.x == 1.0", None),
    ] {
        let program = env.compile(src).unwrap();
        let bc = typed_cel::emit(&program).unwrap();
        let act = activation(&env, &[("v", &v)]);
        let walked = program.evaluate(&act);
        let vm = Vm::new().eval(&bc, &act);
        match want_ok {
            Some(b) => assert!(matches!(vm, Ok(x) if x == b), "{src}: {vm:?}"),
            None => assert!(vm.is_err(), "{src}: {vm:?}"),
        }
        match (&walked, &vm) {
            (Ok(a), Ok(b)) => assert_eq!(a, b, "{src}"),
            (Err(a), Err(b)) => assert_eq!(a.to_string(), b.to_string(), "{src}"),
            _ => panic!("{src}: walker {walked:?}, VM {vm:?}"),
        }
    }
}

// ---- 9 ----

#[test]
fn two_runs_on_one_thread_are_independent() {
    let vm = Vm::new();
    let a = scripted(&[("x", Slot::Pending(1))]);
    let (mut run_a, bindings_a) = start("v.x == 1.0", &[("v", &a)]);
    need(vm.resume(&mut run_a, &bindings_a));

    let b = scripted(&[("kind", Slot::Ready(CelValue::Str("k".into())))]);
    let (mut run_b, bindings_b) = start("v.kind == \"k\" && 1.0 < 2.0", &[("v", &b)]);
    assert!(matches!(
        vm.resume(&mut run_b, &bindings_b),
        RunStep::Done(Ok(true))
    ));

    a.set("x", Slot::Ready(CelValue::Num(2.0)));
    assert!(matches!(
        vm.resume(&mut run_a, &bindings_a),
        RunStep::Done(Ok(false))
    ));
}

// ---- 10 ----

#[test]
fn a_waiting_run_crosses_threads() {
    let v = scripted(&[("x", Slot::Pending(1))]);
    let (tx, rx) = std::sync::mpsc::channel::<(VmRun, CelBindings)>();
    let lazies_v = Arc::clone(&v);
    let a = std::thread::spawn(move || {
        let (mut run, bindings) = start("v.x == 1.0", &[("v", &lazies_v)]);
        need(Vm::new().resume(&mut run, &bindings));
        tx.send((run, bindings)).unwrap();
    });
    a.join().unwrap();
    v.set("x", Slot::Ready(CelValue::Num(1.0)));
    let b = std::thread::spawn(move || {
        let (mut run, bindings) = rx.recv().unwrap();
        done(Vm::new().resume(&mut run, &bindings))
    });
    assert!(matches!(b.join().unwrap(), Ok(true)));
}

// ---- 12 ----

#[test]
fn a_template_instantiates_fresh_bindings() {
    let env = env();
    let program = env.compile("v.x == n").unwrap();
    let bc = Arc::new(typed_cel::emit(&program).unwrap());
    let template = || {
        let mut act = env.activation();
        act.bind("n", &serde_json::json!(3)).unwrap();
        act
    };
    let t = template()
        .into_template(&["v"])
        .expect("v is declared and open");

    let lazy_a = scripted(&[("x", Slot::Ready(CelValue::Num(3.0)))]);
    let lazy_b = scripted(&[("x", Slot::Ready(CelValue::Num(4.0)))]);
    let lazy = |s: &Arc<Scripted>| CelValue::Lazy(Arc::clone(s) as _);
    let vm = Vm::new();
    for (s, want) in [(&lazy_a, true), (&lazy_b, false)] {
        let bindings = t.instantiate(vec![("v", lazy(s))]).expect("instantiates");
        let mut run = VmRun::new(Arc::clone(&bc));
        assert_eq!(done(vm.resume(&mut run, &bindings)).unwrap(), want);
    }
    assert_eq!(lazy_a.reads("x"), 1);
    assert_eq!(lazy_b.reads("x"), 1);

    let bind_err = |r: Result<CelBindings, CelError>, what: &str| match r {
        Err(CelError::Bind { .. }) => {}
        Err(other) => panic!("{what}: expected a bind error, got {other:?}"),
        Ok(_) => panic!("{what}: instantiated"),
    };
    bind_err(t.instantiate(vec![]), "the open root missing");
    bind_err(
        t.instantiate(vec![("v", lazy(&lazy_a)), ("n", CelValue::Num(1.0))]),
        "an extra (already bound) root",
    );
    bind_err(
        t.instantiate(vec![("v", lazy(&lazy_a)), ("zz", CelValue::Num(1.0))]),
        "an undeclared name",
    );
    bind_err(
        t.instantiate(vec![("v", lazy(&lazy_a)), ("v", lazy(&lazy_b))]),
        "the open root twice",
    );

    assert!(matches!(
        template().into_template(&["n"]),
        Err(CelError::Bind { .. })
    ));
    assert!(matches!(
        template().into_template(&["zz"]),
        Err(CelError::Bind { .. })
    ));
}

// ---- 13 ----

#[test]
fn a_finished_run_resumed_again_is_an_error_not_a_panic() {
    let (mut run, bindings) = start("1.0 < 2.0", &[]);
    let vm = Vm::new();
    assert!(matches!(
        vm.resume(&mut run, &bindings),
        RunStep::Done(Ok(true))
    ));
    assert_eq!(run.pc(), None);
    assert!(matches!(
        vm.resume(&mut run, &bindings),
        RunStep::Done(Err(CelError::Bind { .. }))
    ));
}
