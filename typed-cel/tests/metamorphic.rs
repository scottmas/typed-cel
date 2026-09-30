//! Single-engine laws: two DIFFERENT computations that must answer alike.
//!
//! With one engine there is no second implementation to disagree with, so bug-finding comes from
//! the cel-spec corpus (external answers), the frozen golden (`tests/generated_golden.rs`), and the
//! laws here:
//!
//! - **logic laws** — two different PROGRAMS (`a && b` and `b && a`, De Morgan, …) that must agree;
//! - **literal vs bound** — the same program with its literals spelled in place and bound as
//!   roots, which holds lowering's constant path against its read path;
//! - **every host alike** — ONE program over five ways of supplying its inputs (eager values, lazy
//!   views run straight through and paused-and-resumed, a caller's `Facts`, and a resumed run over
//!   eager values), which share the ops but not the reads.
//!
//! Every test collects EVERY mismatch with a reproduction before failing once, and asserts how many
//! cases RAN and the outcome mix, so a generator change cannot make it vacuous.

#[path = "support/mod.rs"]
mod support;

use typed_cel::CompileOpts;
use std::sync::atomic::Ordering;
use std::sync::Arc;

use serde_json::Value as J;
use support::gen::{
    roster, typed_batch, typed_json, Gen, JsonFacts, JsonLazy, ACTIVATIONS_PER_EXPRESSION, SEEDS,
    TYPED_PER_SEED,
};
use typed_cel::{
    emit, CelActivation, CelBytecode, CelEnvironment, CelError, CelValue, FastScratch, RunStep, Vm,
    VmRun,
};

type Json = Vec<(&'static str, J)>;

fn fail_on(what: &str, mismatches: &[String]) {
    assert!(
        mismatches.is_empty(),
        "{} {what} mismatch(es):\n\n{}",
        mismatches.len(),
        mismatches.join("\n\n")
    );
}

fn render(json: &[(&str, J)]) -> String {
    json.iter()
        .map(|(k, v)| format!("{k}={v}"))
        .collect::<Vec<_>>()
        .join(" ")
}

fn compile(env: &CelEnvironment, src: &str, whence: &str) -> typed_cel::CelProgram {
    env.compile(src, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("{whence}: `{src}` does not compile:\n{e}"))
}

fn bind(env: &CelEnvironment, json: &[(&str, J)]) -> CelActivation {
    let mut act = env.activation();
    for (name, v) in json {
        act.bind(name, v)
            .unwrap_or_else(|e| panic!("binding {name}={v}: {e}"));
    }
    act
}

/// Ok/Err tallies, held to the floor every generated test here holds: at least 10% `Err`, and at
/// least 25% of the `Ok`s each way.
#[derive(Default)]
struct Mix {
    ok_true: usize,
    ok_false: usize,
    err: usize,
}

impl Mix {
    fn add(&mut self, out: &Result<bool, CelError>) {
        match out {
            Ok(true) => self.ok_true += 1,
            Ok(false) => self.ok_false += 1,
            Err(_) => self.err += 1,
        }
    }

    fn total(&self) -> usize {
        self.ok_true + self.ok_false + self.err
    }

    fn assert_not_one_sided(&self, what: &str) {
        let (t, f, e, n) = (self.ok_true, self.ok_false, self.err, self.total());
        eprintln!("{what}: {n} runs — {t} ok true, {f} ok false, {e} err");
        assert!(e * 10 >= n, "{what}: only {e} of {n} runs are errors");
        let ok = t + f;
        assert!(t * 4 >= ok, "{what}: only {t} of {ok} Oks are true");
        assert!(f * 4 >= ok, "{what}: only {f} of {ok} Oks are false");
    }
}

// ---- 1. logic laws -------------------------------------------------------------------------

const PAIRS_PER_SEED: usize = 300;

/// Every law as (left, right) over the two generated operands.
fn laws(a: &str, b: &str) -> Vec<(&'static str, String, String)> {
    vec![
        (
            "&& commutes",
            format!("({a}) && ({b})"),
            format!("({b}) && ({a})"),
        ),
        (
            "|| commutes",
            format!("({a}) || ({b})"),
            format!("({b}) || ({a})"),
        ),
        (
            "De Morgan (&&)",
            format!("!(({a}) && ({b}))"),
            format!("!({a}) || !({b})"),
        ),
        (
            "De Morgan (||)",
            format!("!(({a}) || ({b}))"),
            format!("!({a}) && !({b})"),
        ),
        ("double negation", format!("!!({a})"), format!("({a})")),
        ("&& idempotent", format!("({a}) && ({a})"), format!("({a})")),
        ("|| idempotent", format!("({a}) || ({a})"), format!("({a})")),
        (
            "?: identity",
            format!("({a}) ? true : false"),
            format!("({a})"),
        ),
    ]
}

/// Both `Ok` and equal, or both `Err`. Error IDENTITY is not compared: which of two failing
/// operands reports is a separate, already-pinned rule (`tests/backend_edges.rs`).
fn alike(x: &Result<bool, CelError>, y: &Result<bool, CelError>) -> bool {
    match (x, y) {
        (Ok(a), Ok(b)) => a == b,
        (Err(_), Err(_)) => true,
        _ => false,
    }
}

#[test]
fn logic_laws_hold_on_generated_programs() {
    let env = roster();
    let vm = Vm::new();
    let mut mix = Mix::default();
    let mut ran = 0usize;
    let mut mismatches = Vec::new();
    for seed in SEEDS {
        let mut g = Gen::new(seed ^ 0x1A55);
        for index in 0..PAIRS_PER_SEED {
            let (a, b) = (g.typed_bool(3), g.typed_bool(3));
            let acts: Vec<Json> = (0..ACTIVATIONS_PER_EXPRESSION)
                .map(|_| typed_json(&mut g))
                .collect();
            let whence = format!("seed={seed:#x}, index={index}");
            for (law, lhs, rhs) in laws(&a, &b) {
                let l = emit(&compile(&env, &lhs, &whence)).expect("emits");
                let r = emit(&compile(&env, &rhs, &whence)).expect("emits");
                for json in &acts {
                    let act = bind(&env, json);
                    let (x, y) = (vm.eval(&l, &act), vm.eval(&r, &act));
                    ran += 1;
                    mix.add(&x);
                    if !alike(&x, &y) {
                        mismatches.push(format!(
                            "{whence} [{law}]\n  a = {a}\n  b = {b}\n  with {}\n  {lhs}\n    => {x:?}\n  {rhs}\n    => {y:?}",
                            render(json)
                        ));
                    }
                }
            }
        }
    }
    fail_on("logic-law", &mismatches);
    assert_eq!(
        ran,
        SEEDS.len() * PAIRS_PER_SEED * 8 * ACTIVATIONS_PER_EXPRESSION,
        "every law ran on every pair and activation"
    );
    mix.assert_not_one_sided("logic laws");
}

// ---- 2. literals vs bound roots --------------------------------------------------------------

/// The CEL tokens of `src` — a literal and the root that replaces it are one token each.
fn tokens(src: &str) -> usize {
    let mut n = 0;
    let mut in_word = false;
    for c in src.chars() {
        let word = c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '\'');
        if word {
            if !in_word {
                n += 1;
            }
            in_word = true;
        } else {
            in_word = false;
            if !c.is_whitespace() {
                n += 1;
            }
        }
    }
    n
}

#[test]
fn literals_and_bound_values_answer_alike() {
    let vm = Vm::new();
    let mut mix = Mix::default();
    let (mut ran, mut spelled) = (0usize, 0usize);
    let mut mismatches = Vec::new();
    for seed in SEEDS {
        let plain = typed_batch(seed);
        let mut g = Gen::new(seed);
        g.lits_as_roots = true;
        for (index, (src, acts)) in plain.iter().enumerate() {
            g.lits.clear();
            let bound_src = g.typed_bool(4);
            let lits = std::mem::take(&mut g.lits);
            let bound_acts: Vec<Json> = (0..ACTIVATIONS_PER_EXPRESSION)
                .map(|_| typed_json(&mut g))
                .collect();
            let whence = format!("seed={seed:#x}, index={index}");
            // The same stream, so the same program and the same activations.
            assert_eq!(
                tokens(src),
                tokens(&bound_src),
                "{whence}: the two spellings differ in shape:\n  {src}\n  {bound_src}"
            );
            assert_eq!(*acts, bound_acts, "{whence}: the activations differ");
            spelled += lits.len();

            let env = roster();
            let mut bound_env = roster();
            for (name, ty, _) in &lits {
                bound_env.declare(name.clone(), ty.clone());
            }
            let plain_code = emit(&compile(&env, src, &whence)).expect("emits");
            let bound_code = emit(&compile(&bound_env, &bound_src, &whence)).expect("emits");
            for json in acts {
                let x = vm.eval(&plain_code, &bind(&env, json));
                let mut with_lits: Vec<(&str, J)> =
                    json.iter().map(|(k, v)| (*k, v.clone())).collect();
                with_lits.extend(lits.iter().map(|(n, _, v)| (n.as_str(), v.clone())));
                let y = vm.eval(&bound_code, &bind(&bound_env, &with_lits));
                ran += 1;
                mix.add(&x);
                let message = |r: &Result<bool, CelError>| match r {
                    Ok(b) => Ok(*b),
                    Err(CelError::Evaluation { message, .. }) => Err(message.clone()),
                    Err(other) => panic!("{whence}: failed outside evaluation: {other}"),
                };
                if message(&x) != message(&y) {
                    mismatches.push(format!(
                        "{whence}\n  literal: {src}\n    => {x:?}\n  bound:   {bound_src}\n    => {y:?}\n  with {}",
                        render(&with_lits)
                    ));
                }
            }
        }
    }
    fail_on("literal-vs-bound", &mismatches);
    assert_eq!(
        ran,
        SEEDS.len() * TYPED_PER_SEED * ACTIVATIONS_PER_EXPRESSION
    );
    assert!(
        spelled >= SEEDS.len() * TYPED_PER_SEED,
        "only {spelled} literals were spelled as roots"
    );
    mix.assert_not_one_sided("literals vs bound");
}

// ---- 3. every host alike ---------------------------------------------------------------------

/// A run's verdict and the counters of the lazy `r` and `m` (members, keys calls).
#[derive(Debug, PartialEq)]
struct LazyRun {
    verdict: Result<bool, String>,
    counts: [usize; 4],
}

/// Bind `r` and `m` as `JsonLazy` views and every other root eagerly; `run` gets the activation.
fn lazily(
    env: &CelEnvironment,
    json: &[(&str, J)],
    run: impl FnOnce(CelActivation) -> Result<bool, CelError>,
) -> LazyRun {
    let mut act = env.activation();
    let mut lazy = |name: &str| -> Arc<JsonLazy> {
        let (_, v) = json.iter().find(|(k, _)| *k == name).expect("bound");
        let view = Arc::new(JsonLazy::new(v.as_object().expect("an object").clone()));
        act.bind_lazy(name, CelValue::Lazy(Arc::clone(&view) as _))
            .expect("declared");
        view
    };
    let (r, m) = (lazy("r"), lazy("m"));
    for (name, v) in json.iter().filter(|(k, _)| *k != "r" && *k != "m") {
        act.bind(name, v).expect("binds");
    }
    let verdict = run(act).map_err(|e| e.to_string());
    LazyRun {
        verdict,
        counts: [
            r.members.load(Ordering::SeqCst),
            r.key_calls.load(Ordering::SeqCst),
            m.members.load(Ordering::SeqCst),
            m.key_calls.load(Ordering::SeqCst),
        ],
    }
}

/// A `VmRun` over `act`'s bindings, resumed until it is done.
fn resumed(code: &CelBytecode, act: CelActivation) -> Result<bool, CelError> {
    let vm = Vm::new();
    let bindings = act.into_bindings();
    let mut run = VmRun::new(Arc::new(code.clone()));
    for _ in 0..1000 {
        match vm.resume(&mut run, &bindings) {
            RunStep::Done(out) => return out,
            RunStep::Need(_) => continue,
        }
    }
    panic!("a run over values that never wait did not finish");
}

#[test]
fn every_host_answers_alike() {
    let env = roster();
    let vm = Vm::new();
    let mut mix = Mix::default();
    let (mut ran, mut programs, mut on_facts) = (0usize, 0usize, 0usize);
    let mut scratch = FastScratch::default();
    let mut mismatches = Vec::new();
    for seed in SEEDS {
        for (index, (src, acts)) in typed_batch(seed).iter().enumerate() {
            let whence = format!("seed={seed:#x}, index={index}");
            let code = emit(&compile(&env, src, &whence)).expect("emits");
            programs += 1;
            let mut scalar = true;
            for json in acts {
                let eager = vm.eval(&code, &bind(&env, json));
                mix.add(&eager);
                let eager = eager.map_err(|e| e.to_string());
                let lazy = lazily(&env, json, |act| vm.eval(&code, &act));
                let lazy_resumed = lazily(&env, json, |act| resumed(&code, act));
                let eager_resumed = resumed(&code, bind(&env, json)).map_err(|e| e.to_string());
                let facts = match JsonFacts::new(code.program().fields(), json) {
                    Some(f) => Some(
                        code.program()
                            .decide(&f, &mut scratch)
                            .map_err(|e| e.to_string()),
                    ),
                    None => {
                        scalar = false;
                        None
                    }
                };
                ran += 1;
                let same = lazy.verdict == eager
                    && lazy_resumed == lazy
                    && eager_resumed == eager
                    && facts.as_ref().is_none_or(|f| *f == eager);
                if !same {
                    mismatches.push(format!(
                        "{whence}: {src}\n  with {}\n  eager:          {eager:?}\n  lazy:           {lazy:?}\n  lazy, resumed:  {lazy_resumed:?}\n  eager, resumed: {eager_resumed:?}\n  facts:          {facts:?}",
                        render(json)
                    ));
                }
            }
            on_facts += usize::from(scalar);
        }
    }
    fail_on("host", &mismatches);
    assert_eq!(
        ran,
        SEEDS.len() * TYPED_PER_SEED * ACTIVATIONS_PER_EXPRESSION
    );
    eprintln!("hosts: {on_facts} of {programs} programs read only scalar fields and ran on Facts");
    // Measured: 708 of 3000 programs read only scalar fields (the rest read `xs`, `ss` or `m`
    // whole). The floor sits under that, so a generator change that starves this host fails here.
    assert!(
        on_facts * 5 >= programs,
        "only {on_facts} of {programs} programs ran on Facts"
    );
    mix.assert_not_one_sided("every host");
}
