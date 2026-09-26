//! A streamed run: a governed value and a suspended VM, fed one event at a time.
//!
//! `StreamedProgram` is built once and shared by every body; `StreamedProgram::begin` makes one
//! `StreamedRun` per body. The run answers `Live` while the program waits, `Dead` at the event that
//! settles a false or erroring verdict, and `Capped` at a cap.

#[path = "support/mod.rs"]
mod support;

use std::sync::Arc;

use serde_json::json;
use support::events::{to_events, Ev};
use support::record_opt;
use typed_cel::{
    emit, CelEnvironment, CelError, CelTy, RunLiveness, StreamedProgram, StreamedRun, Vm,
};

// ---- 13. compile-time: the program is shared across flows, a run rides one between threads ----
const _: () = {
    fn send<T: Send>() {}
    fn sync<T: Sync>() {}
    #[allow(dead_code)]
    fn all() {
        send::<StreamedRun>();
        send::<StreamedProgram>();
        sync::<StreamedProgram>();
    }
};

#[test]
fn the_program_and_run_are_thread_safe() {
    // The assertion is the `const` block above; this names the property.
    let p = program(json_body(&[("x", CelTy::Num)], &[]), "body.x == 1.0");
    let run = p.begin();
    std::thread::spawn(move || drop(run)).join().unwrap();
}

// ------------------------------------------------------------------------------------------
// Helpers
// ------------------------------------------------------------------------------------------

/// The `body` a program reads.
fn json_body(fields: &[(&str, CelTy)], optional: &[&str]) -> Option<CelTy> {
    Some(record_opt("body", fields, optional))
}

/// A program over `body`, declared as `declared`. `n` is declared `Num` and bound to 3.
fn program(declared: Option<CelTy>, src: &str) -> StreamedProgram {
    let mut env = CelEnvironment::new();
    env.declare("n", CelTy::Num);
    env.declare("body", declared.expect("declare `body`"));
    let compiled = env.compile(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    let code = Arc::new(emit(&compiled).expect("the program emits"));
    let mut act = env.activation();
    act.bind("n", &json!(3)).expect("n binds");
    StreamedProgram::new(Arc::new(Vm::new()), &env, &compiled, code, act, "body")
        .expect("the program streams")
}

fn push_all(run: &mut StreamedRun, evs: &[Ev]) -> Vec<RunLiveness> {
    evs.iter().map(|e| run.push(e.as_event())).collect()
}

/// The index of the `EndString` that closes the value of `key` (the first one after its `EndKey`).
fn end_of_value(evs: &[Ev], key: &str) -> usize {
    let k = evs
        .iter()
        .position(|e| *e == Ev::KeyText(key.into()))
        .unwrap_or_else(|| panic!("no key {key}"));
    k + evs[k..].iter().position(|e| *e == Ev::EndString).unwrap()
}

fn end_of_key(evs: &[Ev], key: &str) -> usize {
    let k = evs
        .iter()
        .position(|e| *e == Ev::KeyText(key.into()))
        .unwrap_or_else(|| panic!("no key {key}"));
    k + evs[k..].iter().position(|e| *e == Ev::EndKey).unwrap()
}

fn decided_true(run: &StreamedRun) -> bool {
    matches!(run.decided(), Some(Ok(true)))
}

fn pad(n: usize) -> String {
    "p".repeat(n)
}

// ------------------------------------------------------------------------------------------
// Rows
// ------------------------------------------------------------------------------------------

#[test]
fn a_program_that_reads_no_field_decides_at_begin() {
    let p = program(
        json_body(&[("x", CelTy::Num)], &[]),
        "n == 3.0 || body.x == 1.0",
    );
    let mut run = p.begin();
    assert!(decided_true(&run), "decided at begin: {:?}", run.decided());
    for l in push_all(&mut run, &to_events(r#"{"x":2}"#, 4)) {
        assert_eq!(l, RunLiveness::Live);
    }
    assert!(matches!(run.finish(), Ok(true)));
}

#[test]
fn the_run_is_live_while_the_vm_waits() {
    let p = program(
        json_body(&[("pad", CelTy::Str), ("op", CelTy::Str)], &[]),
        r#"body.op == "read""#,
    );
    let doc = format!(r#"{{"pad":"{}","op":"read"}}"#, pad(256 * 1024));
    let evs = to_events(&doc, 4096);
    let at = end_of_value(&evs, "op");
    let mut run = p.begin();
    for (i, e) in evs.iter().enumerate() {
        let l = run.push(e.as_event());
        assert_eq!(l, RunLiveness::Live, "event {i}");
        if i < at {
            assert!(
                run.decided().is_none(),
                "undecided before `op` settles (event {i})"
            );
        } else {
            assert!(
                decided_true(&run),
                "decided at `op`'s EndString (event {i})"
            );
        }
    }
    assert!(matches!(run.finish(), Ok(true)));
}

#[test]
fn an_early_false_is_dead_at_the_settling_event() {
    let p = program(
        json_body(&[("op", CelTy::Str), ("pad", CelTy::Str)], &[]),
        r#"body.op == "read""#,
    );
    let doc = format!(r#"{{"op":"delete","pad":"{}"}}"#, pad(256 * 1024));
    let evs = to_events(&doc, 4096);
    let at = end_of_value(&evs, "op");
    let got = push_all(&mut p.begin(), &evs);
    assert!(got[..at].iter().all(|l| *l == RunLiveness::Live));
    assert_eq!(
        got[at],
        RunLiveness::Dead,
        "Dead at the settling event itself"
    );
    assert!(
        got[at..].iter().all(|l| *l == RunLiveness::Dead),
        "Dead is final"
    );
}

#[test]
fn an_erroring_verdict_is_dead() {
    let p = program(
        json_body(&[("amount", CelTy::Num)], &[]),
        "body.amount > 1.0",
    );
    let evs = to_events(r#"{"amount":"x"}"#, 4);
    let got = push_all(&mut p.begin(), &evs);
    let begin_string = evs.iter().position(|e| *e == Ev::BeginString).unwrap();
    assert!(got[..begin_string].iter().all(|l| *l == RunLiveness::Live));
    assert_eq!(
        got[begin_string],
        RunLiveness::Dead,
        "the mistyped value fails the read"
    );
}

#[test]
fn short_circuit_never_waits_for_the_tail() {
    let p = program(
        json_body(&[("kind", CelTy::Str), ("big", CelTy::Str)], &[]),
        r#"body.kind == "a" && body.big == "z""#,
    );
    let doc = format!(r#"{{"kind":"b","big":"{}"}}"#, pad(1024 * 1024));
    let evs = to_events(&doc, 4096);
    let at = end_of_value(&evs, "kind");
    let mut run = p.begin();
    for e in &evs[..at] {
        assert_eq!(run.push(e.as_event()), RunLiveness::Live);
    }
    assert_eq!(run.push(evs[at].as_event()), RunLiveness::Dead);
    for e in &evs[at + 1..] {
        run.push(e.as_event());
        assert!(
            run.state_bytes() <= 2048,
            "held {} bytes",
            run.state_bytes()
        );
    }
    assert!(matches!(run.finish(), Ok(false)));
}

#[test]
fn resume_happens_only_when_a_cell_settled() {
    let p = program(
        json_body(&[("name", CelTy::Str)], &[]),
        r#"body.name == "x""#,
    );
    let doc = format!(r#"{{"a":"{}","name":"x"}}"#, pad(10_000));
    let evs = to_events(&doc, 1);
    assert!(evs.len() > 10_000);
    let mut run = p.begin();
    push_all(&mut run, &evs);
    assert!(decided_true(&run));
    // begin; the root object opens; `name`'s key is seen (a presence decision); `name` settles.
    // Ten thousand fragments of an undemanded member move nothing.
    assert_eq!(run.steps(), 4);
    assert!(matches!(run.finish(), Ok(true)));
}

#[test]
fn presence_decides_at_the_key() {
    let ty = || json_body(&[("note", CelTy::Str), ("a", CelTy::Num)], &["note", "a"]);

    let p = program(ty(), "has(body.note)");
    let doc = format!(r#"{{"note":"{}"}}"#, pad(1024 * 1024));
    let evs = to_events(&doc, 4096);
    let at = end_of_key(&evs, "note");
    let mut run = p.begin();
    for e in &evs[..at] {
        run.push(e.as_event());
        assert!(run.decided().is_none());
    }
    run.push(evs[at].as_event());
    assert!(
        decided_true(&run),
        "decided at `note`'s EndKey: {:?}",
        run.decided()
    );
    push_all(&mut run, &evs[at + 1..]);
    assert!(matches!(run.finish(), Ok(true)));

    let p = program(ty(), "!has(body.note)");
    let evs = to_events(r#"{"a":1}"#, 4);
    let close = evs.len() - 1;
    assert_eq!(evs[close], Ev::EndObject);
    let mut run = p.begin();
    for e in &evs[..close] {
        run.push(e.as_event());
        assert!(run.decided().is_none());
    }
    run.push(evs[close].as_event());
    assert!(decided_true(&run), "decided at the root's EndObject");
    assert!(matches!(run.finish(), Ok(true)));
}

#[test]
fn finish_settles_what_the_document_never_closed() {
    let p = program(
        json_body(&[("name", CelTy::Str)], &[]),
        r#"body.name == "xx""#,
    );
    let evs = to_events(r#"{"name":"xx"}"#, 1);
    let cut = evs.iter().position(|e| *e == Ev::Text("x".into())).unwrap() + 1;
    let mut run = p.begin();
    push_all(&mut run, &evs[..cut]);
    assert!(run.decided().is_none(), "still waiting mid-string");
    let got = run.finish();
    assert!(
        matches!(got, Err(_) | Ok(false)),
        "a cut-off document is never accepted: {got:?}"
    );
}

#[test]
fn a_second_run_on_the_same_thread_completes_while_the_first_waits() {
    let p = program(
        json_body(&[("name", CelTy::Str)], &[]),
        r#"body.name == "x""#,
    );
    let a_evs = to_events(r#"{"name":"x"}"#, 4);
    let b_evs = to_events(r#"{"name":"y"}"#, 4);
    let half = end_of_key(&a_evs, "name");

    let mut a = p.begin();
    push_all(&mut a, &a_evs[..half]);
    assert!(a.decided().is_none());

    let mut b = p.begin();
    push_all(&mut b, &b_evs);
    assert!(matches!(b.finish(), Ok(false)));

    push_all(&mut a, &a_evs[half..]);
    assert!(matches!(a.finish(), Ok(true)));
}

#[test]
fn a_run_moves_between_threads() {
    let p = Arc::new(program(
        json_body(&[("pad", CelTy::Str), ("op", CelTy::Str)], &[]),
        r#"body.op == "read""#,
    ));
    let doc = format!(r#"{{"pad":"{}","op":"read"}}"#, pad(8192));
    let evs = to_events(&doc, 64);
    let half = evs.len() / 2;

    let single = {
        let mut run = p.begin();
        push_all(&mut run, &evs);
        run.finish()
    };
    assert!(matches!(single, Ok(true)));

    let (tx, rx) = std::sync::mpsc::channel::<StreamedRun>();
    let first: Vec<Ev> = evs[..half].to_vec();
    let rest: Vec<Ev> = evs[half..].to_vec();
    let pa = Arc::clone(&p);
    let a = std::thread::spawn(move || {
        let mut run = pa.begin();
        push_all(&mut run, &first);
        assert!(run.decided().is_none());
        tx.send(run).unwrap();
    });
    let b = std::thread::spawn(move || {
        let mut run = rx.recv().unwrap();
        push_all(&mut run, &rest);
        run.finish()
    });
    a.join().unwrap();
    let moved = b.join().unwrap();
    assert!(matches!(moved, Ok(true)), "{moved:?}");
}

#[test]
fn a_template_is_instantiated_per_run() {
    let p = program(
        json_body(&[("name", CelTy::Str)], &[]),
        r#"n == 3.0 && body.name == "x""#,
    );
    let x = to_events(r#"{"name":"x"}"#, 1);
    let y = to_events(r#"{"name":"y"}"#, 1);

    let mut a = p.begin();
    let mut b = p.begin();
    // Interleave the two documents event by event: neither run may see the other's cells.
    for (ea, eb) in x.iter().zip(y.iter()) {
        a.push(ea.as_event());
        b.push(eb.as_event());
    }
    assert!(matches!(a.finish(), Ok(true)));
    assert!(matches!(b.finish(), Ok(false)));
}

#[test]
fn an_unstreamable_program_is_refused_when_built() {
    // The shape's refusals surface through `StreamedProgram::new`, not at the first body.
    let mut env = CelEnvironment::new();
    env.declare(
        "body",
        record_opt("body", &[("tags", CelTy::list(CelTy::Str))], &[]),
    );
    let compiled = env.compile(r#"body.tags.size() > 1.0"#).unwrap();
    let code = Arc::new(emit(&compiled).unwrap());
    let got = StreamedProgram::new(
        Arc::new(Vm::new()),
        &env,
        &compiled,
        code,
        env.activation(),
        "body",
    );
    assert!(matches!(got, Err(CelError::Bind { .. })), "{:?}", got.err());
}
