//! The engine's cost-model cliffs, each pinned by a DETERMINISTIC count — ops dispatched, `slow`
//! entries, host field reads, values built, allocations — against the budget a good lowering needs.
//! Never by time: every count here is the same on every machine and every run.
//!
//! Every test named after a pathology is RED until that cliff is fixed; its failure prints the
//! measured count, the budget, the program, the leg it ran on, and the lowered listing. The
//! `NS_*` constants are what the cliff costs in wall time — measured by `ablation/benches/cliffs.rs`
//! on a Hetzner Cloud cx33 VM (AMD EPYC-Rome, pinned to one core, no `profile` feature) — and are printed,
//! never asserted. A test whose doc comment says GREEN GUARD holds a family that is already fine.
//!
//! The cliffs were found by `tests/perf_harvest.rs` (run it explicitly; see its header). The
//! write-up is `docs/PERFORMANCE.md` "Known cliffs".

#[path = "support/mod.rs"]
mod support;

use typed_cel::CompileOpts;
use std::sync::Arc;

use typed_cel::profile::{self, CountingAlloc, RunProfile};
use typed_cel::{fork, CelEnvironment, CelTy, FastProgram, StreamedProgram, Vm};
use support::perf::{self, Leg, Prepared};

#[global_allocator]
static ALLOC: CountingAlloc = CountingAlloc;

/// One program on one leg at one size, prepared and measured once, warmed.
struct Probe {
    src: String,
    leg: Leg,
    n: usize,
    p: Prepared,
    prof: RunProfile,
}

fn probe(src: &str, leg: Leg, n: usize) -> Probe {
    perf::assert_counting();
    let env = perf::env();
    let p = perf::prepare(&env, src, leg, &perf::policy(n), &perf::req(n))
        .unwrap_or_else(|| panic!("`{src}` does not run on the {} leg", leg.name()));
    let (verdict, prof) = p.measure();
    // A cost measured on a run that failed is the cost of the failure path, not of the program.
    verdict.unwrap_or_else(|e| panic!("`{src}` [{}] n={n} failed: {e}", leg.name()));
    Probe {
        src: src.to_string(),
        leg,
        n,
        p,
        prof,
    }
}

impl Probe {
    /// The failure line: what was measured against what was allowed, and everything needed to
    /// see why — the counts, the residual's source, the listing, and the measured wall time.
    fn over(&self, what: &str, measured: f64, budget: f64, ns: &str) -> String {
        format!(
            "`{}` [{} via {}] n={}: {what} = {measured:.1}, budget {budget:.1}\n  counts: {}\n  runs: {}\n  measured: {ns}\n  listing:\n{}",
            self.src,
            self.leg.name(),
            self.p.how(),
            self.n,
            self.prof.summary(),
            self.p.program.source().lines().next().unwrap_or(""),
            self.p.fast.listing()
        )
    }

    fn reads_of(&self, names: &[&str]) -> u64 {
        self.prof.reads_of(&self.p.fast, names)
    }
}

/// The per-element slope of `q` between `n = 10` and `n = 1000`.
fn per_elem(src: &str, leg: Leg, q: fn(&RunProfile) -> u64) -> (f64, Probe) {
    let small = probe(src, leg, 10);
    let big = probe(src, leg, 1000);
    let slope = (q(&big.prof) as f64 - q(&small.prof) as f64) / 990.0;
    (slope, big)
}

fn fail_on(what: &str, failures: Vec<String>) {
    assert!(
        failures.is_empty(),
        "{} {what}:\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

// ---- 1. a predicate loop is a predicate loop ----

const NS_PREDICATE_LOOP: &str = "31 µs (`names.exists`), 31 µs (`nums.all`), 29 µs \
     (`exists_one`), 100 µs (records) per decision at n=1000, act leg — 29-100 ns/element; \
     hand-written Rust scans 1000 roots in ~2.3 µs";

/// A predicate loop over a bound list costs a handful of ops per element: fetch the next element
/// (1), test it with a compare fused into its branch (1, or 2 for a select then a compare), jump
/// back (1). Six is that plus slack; a record predicate with two tests gets eight.
///
/// `Lower::try_predicate_loop` (`src/fast/lower.rs`) recognizes the three expansions and lowers
/// the predicate as a branch inside `IterNext … Jump`, the literal expansion's accumulator,
/// loop condition and step bookkeeping gone.
#[test]
fn predicate_loop_ops_per_element_is_bounded() {
    let cases: &[(&str, f64)] = &[
        ("policy.names.exists(x, x == req.name)", 6.0),
        ("policy.nums.all(x, x > req.n)", 6.0),
        ("policy.names.exists_one(x, x == req.name)", 6.0),
        (
            "policy.items.exists(i, i.id == req.name && i.qty > req.n)",
            8.0,
        ),
    ];
    let mut failures = Vec::new();
    for (src, budget) in cases {
        let (slope, big) = per_elem(src, Leg::Act, |p| p.ops);
        if slope > *budget {
            failures.push(big.over("ops per element", slope, *budget, NS_PREDICATE_LOOP));
        }
    }
    fail_on(
        "predicate loop(s) over their per-element op budget",
        failures,
    );
}

// ---- 2. the common ops stay in the dispatch loop ----

const NS_OUT_OF_LINE: &str = "with the loop plumbing inline the predicate loops above ran \
     114-202 ns/element (was 126-224); the five-test scalar decision below runs in ~125 ns over \
     Facts (was 134), its reads now the larger cost";

/// The ops a decision runs most stay in `exec`'s inline loop; `slow` is a nine-argument call into
/// a large function. Budget: NO `slow` entry per element of a predicate loop, and none at all for
/// a scalar decision made of presence, negation, numeric comparison and a string prefix test.
///
/// Their common cases are arms of `exec`'s match (`src/fast/mod.rs`, `INLINE`); an uncommon
/// operand falls back to `slow` through `go_slow!`.
#[test]
fn common_ops_stay_in_the_dispatch_loop() {
    let mut failures = Vec::new();
    let (slope, big) = per_elem("policy.names.exists(x, x == req.name)", Leg::Act, |p| {
        p.slow
    });
    if slope > 0.0 {
        failures.push(big.over("slow entries per element", slope, 0.0, NS_OUT_OF_LINE));
    }
    let scalar = probe(
        "has(req.opt) && req.flag && req.n < 10.0 && req.path.startsWith(req.name) == false \
         && !(req.n > 5.0)",
        Leg::Facts,
        1,
    );
    if scalar.prof.slow > 0 {
        failures.push(scalar.over("slow entries", scalar.prof.slow as f64, 0.0, NS_OUT_OF_LINE));
    }
    fail_on("program(s) leaving the dispatch loop", failures);
}

// ---- 3. a loop-invariant read, read once ----

const NS_INVARIANT_READ: &str = "`policy.m.all(k, policy.m[k] > req.n)` runs 219 µs at n=1000 \
     (was 392 µs, one root walk per element), `nums.all(x, x > req.n)` 36 µs (was 145 µs)";

/// A field the loop body reads but no iteration changes is read ONCE per decision. It cannot simply
/// be hoisted above the loop — over an empty range the read never happens, and a missing field must
/// not fail a loop that would not have read it — so the fix reads it on first use and keeps it.
///
/// `Lower::cache_reads` (`src/fast/lower.rs`) gives such a field a register; its reads lower to
/// `ReadCached`, which fills it on first use.
#[test]
fn loop_invariant_field_is_read_once() {
    let cases: &[(&str, Leg, &[&str])] = &[
        (
            "policy.names.exists(x, x == req.name)",
            Leg::Act,
            &["req", "name"],
        ),
        (
            "policy.nums.all(x, x > req.n)",
            Leg::SpecKnown,
            &["req", "n"],
        ),
        (
            "policy.m.all(k, policy.m[k] > req.n)",
            Leg::Act,
            &["policy", "m"],
        ),
    ];
    let mut failures = Vec::new();
    for (src, leg, field) in cases {
        let big = probe(src, *leg, 1000);
        let reads = big.reads_of(field);
        if reads > 1 {
            failures.push(big.over(
                &format!("reads of `{}`", field.join(".")),
                reads as f64,
                1.0,
                NS_INVARIANT_READ,
            ));
        }
    }
    fail_on("loop(s) re-reading an invariant field", failures);
}

// ---- 4. one field, read once per decision ----

const NS_REPEATED_READ: &str = "16-term `req.n < k` chain: 571 ns over Facts (was 686) vs 40 ns \
     for one term; the rest is ops per term (pin 9)";

/// A field a decision reads several times — a chain of comparisons against one field, a nested
/// conditional testing one field arm by arm — is read once: every later read is dominated by the
/// first, so it can reuse the register.
///
/// A field named at two or more sites lowers to `ReadCached` at each (`Lower::cache_reads`); only
/// the first reaches the host.
#[test]
fn a_field_is_read_once_per_decision() {
    let chain = (0..16)
        .map(|i| format!("req.n < {}.0", 1000 + i))
        .collect::<Vec<_>>()
        .join(" && ");
    let mut ternary = String::from("(");
    for i in 0..24 {
        ternary.push_str(&format!(r#"req.name == "k{i}" ? {i}.0 : "#));
    }
    ternary.push_str("-1.0) < 0.0");
    let cases: Vec<(String, &[&str])> = vec![(chain, &["req", "n"]), (ternary, &["req", "name"])];
    let mut failures = Vec::new();
    for (src, field) in &cases {
        let p = probe(src, Leg::Facts, 1);
        let reads = p.reads_of(field);
        if reads > 1 {
            failures.push(p.over(
                &format!("reads of `{}`", field.join(".")),
                reads as f64,
                1.0,
                NS_REPEATED_READ,
            ));
        }
    }
    fail_on("decision(s) re-reading one field", failures);
}

// ---- 5. a concatenation only compared is never built ----

const NS_CONCAT: &str = "`req.path.startsWith(req.name + \"/\")` 57 ns (was 107); the prefix \
     loop `roots.exists(r, req.path.startsWith(r + \"/\"))` 54 µs at n=1000 (was 251 µs, one \
     heap string per element)";

/// A string concatenation whose only consumer is a comparison — `a.startsWith(b + "/")`,
/// `a + b == c`, `(a + b).endsWith(c)` — builds nothing: each test is answerable piecewise
/// (`a.startsWith(b) && a[len(b)..].startsWith("/")`). Budget: no allocation, no stored value.
///
/// `Lower::try_concat` (`src/fast/lower.rs`) lowers each to one `StrOp2` over the two pieces;
/// a chain of three or more pieces still builds all but its last.
#[test]
fn startswith_of_concatenation_allocates_nothing() {
    let mut failures = Vec::new();
    for src in [
        r#"req.path.startsWith(req.name + "/")"#,
        "req.path + req.name == req.other",
        "(req.long + req.name).endsWith(req.name)",
    ] {
        let p = probe(src, Leg::Facts, 1);
        if p.prof.allocs > 0 || p.prof.store > 0 {
            failures.push(p.over("allocations", p.prof.allocs as f64, 0.0, NS_CONCAT));
        }
    }
    // In a loop, on the activation leg: `store` counts only values the run BUILT, so the leg's
    // own scratch allocations (`vm_eval_allocates_nothing_the_program_does_not_build`) do not mask
    // this one.
    let lp = probe(
        r#"policy.roots.exists(r, req.path.startsWith(r + "/"))"#,
        Leg::Act,
        1000,
    );
    if lp.prof.store > 0 {
        failures.push(lp.over("values built", lp.prof.store as f64, 0.0, NS_CONCAT));
    }
    fail_on("concatenation(s) built only to be compared", failures);
}

// ---- 6. map and filter build in linear space ----

const NS_BUILD: &str = "`size(nums.map(x, x * 2.0))`: 5.2 µs at n=100, 46 µs at n=1000 (was 55 µs \
     and 5.8 ms, quadratic); `filter` 48 µs at n=1000 (was 5.9 ms)";

/// `map`/`filter` build their result in linear time and space: one list, grown by appending.
/// Budget at n=1000: 64 bytes per element plus 8 KiB, and a logarithmic number of allocations
/// (amortized growth) — 32 is generous.
///
/// `Lower::try_build_loop` (`src/fast/lower.rs`) lowers the expansion's `@result + [x]` step to
/// an in-place `Append` onto one list sized from the range (`ListNew`), moved into the store
/// uncopied at the end (`ListFreeze`).
#[test]
fn map_and_filter_build_in_linear_space() {
    const N: usize = 1000;
    let budget_bytes = (64 * N + 8192) as f64;
    let mut failures = Vec::new();
    for src in [
        "size(policy.nums.map(x, x * 2.0)) > req.n",
        "size(policy.nums.filter(x, x > req.n)) > req.n",
        "size(policy.nums.map(x, x > req.n, x * 2.0)) > req.n",
        "size(policy.m.map(k, k)) > req.n",
    ] {
        let p = probe(src, Leg::Act, N);
        if p.prof.alloc_bytes as f64 > budget_bytes {
            failures.push(p.over(
                "bytes allocated",
                p.prof.alloc_bytes as f64,
                budget_bytes,
                NS_BUILD,
            ));
        } else if p.prof.allocs > 32 {
            failures.push(p.over("allocations", p.prof.allocs as f64, 32.0, NS_BUILD));
        }
    }
    fail_on("build(s) over the linear budget", failures);
}

// ---- 7. `Vm::eval` reuses one scratch per thread ----

const NS_EVAL_SCRATCH: &str = "`names.exists(x, x == req.name)` at n=1: 348 ns through \
     `Vm::eval` over an activation vs 40 ns specialized over Facts; no allocation remains, the \
     rest is the loop's ops (pins 1 and 2)";

/// A decision through `Vm::eval` / `FastProgram::eval` / `CelProgram::evaluate` over an
/// activation allocates nothing the program does not build, as `decide` with a warmed
/// `FastScratch` already does (`tests/fast_alloc.rs`).
///
/// A program with a comprehension or more than 16 registers runs in a scratch; the activation
/// entry points keep one per thread (`src/fast/mod.rs`, `with_eval_scratch`), so a warm call
/// allocates neither its register file nor its iteration slots.
#[test]
fn vm_eval_allocates_nothing_the_program_does_not_build() {
    const SRC: &str = "policy.names.exists(x, x == req.name)";
    let env = perf::env();
    let program = env.compile(SRC, &CompileOpts::default()).expect("compiles");
    let code = typed_cel::emit(&program).expect("emits");
    let mut act = env.activation();
    act.bind("req", &perf::req(10)).expect("binds");
    act.bind("policy", &perf::policy(10)).expect("binds");
    let fast = FastProgram::new(&program).expect("lowers");
    let vm = Vm::new();
    let entries: [(&str, &dyn Fn() -> Result<bool, typed_cel::CelError>); 3] = [
        ("Vm::eval", &|| vm.eval(&code, &act)),
        ("FastProgram::eval", &|| fast.eval(&act)),
        ("CelProgram::evaluate", &|| program.evaluate(&act)),
    ];
    let mut failures = Vec::new();
    for (name, run) in entries {
        run().expect("decides");
        let (_, prof) = profile::measure(run);
        if prof.allocs > 0 {
            failures.push(format!(
                "`{SRC}` through {name}: {} allocation(s), budget 0 — the program builds nothing \
                 (store={})\n  counts: {}\n  measured: {NS_EVAL_SCRATCH}\n  listing:\n{}",
                prof.allocs,
                prof.store,
                prof.summary(),
                fast.listing()
            ));
        }
    }
    fail_on("activation entry point(s) allocating per call", failures);
}

// ---- 8. a literal list or map of fields is not built to be searched ----

const NS_LITERAL: &str =
    "`req.name in [req.path, req.other]` 63 ns (was 114) vs 77 ns spelled as `==`/`||`; \
     `[a, b, c].exists(..)` 45 ns (was 266); `{\"a\": req.n, \"b\": 2.0}[\"a\"] > 0.0` 40 ns \
     (was 188) vs 41 ns for `req.n > 0.0`";

/// A list or map literal whose elements are fields, used only to be searched or indexed by a
/// constant, is not built: `x in [a, b]` is `x == a || x == b`, `[a, b].exists(v, P)` is `P(a) ||
/// P(b)` (in order, with the same absorption), and `{"k": v, ..}["k"]` is `v`. Budget: nothing
/// built, nothing allocated, and no more ops than the spelled-out form.
///
/// `src/fast/lower.rs`: `try_in_literal`, `unrolled_predicate` (up to `MAX_UNROLLED` elements)
/// and `try_literal_index` — every element still runs first, in order.
#[test]
fn a_literal_collection_of_fields_is_not_built_to_be_searched() {
    let cases = [
        (
            "req.name in [req.path, req.other]",
            "req.name == req.path || req.name == req.other",
        ),
        // A value no field holds: the list reads every element whatever matches, the spelled-out
        // `||` only up to its first match — so the two are compared where both read all three.
        (
            r#"[req.name, req.path, req.other].exists(x, x == "none")"#,
            r#"req.name == "none" || req.path == "none" || req.other == "none""#,
        ),
        (r#"{"a": req.n, "b": 2.0}["a"] > 0.0"#, "req.n > 0.0"),
    ];
    let mut failures = Vec::new();
    for (src, spelled) in cases {
        let p = probe(src, Leg::Facts, 1);
        let twin = probe(spelled, Leg::Facts, 1);
        if p.prof.allocs > 0 || p.prof.store > 0 {
            failures.push(p.over("allocations", p.prof.allocs as f64, 0.0, NS_LITERAL));
        } else if p.prof.ops > twin.prof.ops {
            failures.push(p.over(
                &format!("ops (spelled out `{spelled}`: {})", twin.prof.ops),
                p.prof.ops as f64,
                twin.prof.ops as f64,
                NS_LITERAL,
            ));
        }
    }
    fail_on("literal collection(s) built to be searched", failures);
}

// ---- 9. a chain of comparisons costs two ops a term ----

const NS_CHAIN: &str = "16-term `req.n < k` chain 167 ns over Facts (was 686); `nums.all(x, x > \
     req.n)` specialized at n=256 (an unrolled chain) 1.9 µs (was 10.8); the numeric `==` chain \
     is one `NumIn`";

/// A chain of comparisons of a field against constants — written by hand, or what the partial
/// evaluator unrolls a known list into — costs at most two ops a term: a compare-against-a-constant
/// fused into its branch, and the read (until `a_field_is_read_once_per_decision` removes it).
///
/// `src/fast/lower.rs`: `logic_chain` lowers a maximal `&&`/`||` chain leaf by leaf with one
/// pending-error register for the whole chain, and `try_cmp_branch` fuses a field-vs-constant
/// comparison into its branch (`CondCmpFK`, through the field's cache register).
#[test]
fn comparison_chain_ops_per_term_is_bounded() {
    let chain = |op: &str, cmp: &str| {
        (0..16)
            .map(|i| format!("req.n {cmp} {}.0", 1000 + i))
            .collect::<Vec<_>>()
            .join(op)
    };
    let cases: Vec<(String, Leg, usize, usize)> = vec![
        (chain(" && ", "<"), Leg::Facts, 1, 16),
        (chain(" || ", "=="), Leg::Facts, 1, 16),
        (
            "policy.nums.all(x, x > req.n)".to_string(),
            Leg::SpecKnown,
            100,
            100,
        ),
    ];
    let mut failures = Vec::new();
    for (src, leg, n, terms) in &cases {
        let p = probe(src, *leg, *n);
        let per = p.prof.ops as f64 / *terms as f64;
        if per > 2.0 {
            failures.push(p.over("ops per term", per, 2.0, NS_CHAIN));
        }
    }
    fail_on("comparison chain(s) over two ops a term", failures);
}

// ---- 10. known membership is a lookup at every size ----

const NS_KNOWN_SET: &str = "`m.exists(k, k == req.name)` specialized: 121 ns at 256 keys, 148 ns \
     at 1000 (was 37 µs, a loop); `nums.exists(x, x == req.n)` 68 ns at n=1000 (was 34 µs)";

/// Equality membership in a collection KNOWN at specialization is a lookup at every size, as it
/// already is for a known list of strings (`a_known_string_list_is_one_matcher_at_every_size`).
/// Budget: eight ops, whatever the size.
///
/// `src/fast/lower.rs`: `known_strings` takes a known map's keys into the string matcher, and a
/// known list of numbers is a `NumSet` (`try_numset_exists`, `in`, `num_chain`).
#[test]
fn known_membership_is_a_lookup_at_every_size() {
    let literal = format!(
        "[{}].exists(x, x == req.n)",
        (1..=1000)
            .map(|i| format!("{i}.0"))
            .collect::<Vec<_>>()
            .join(", ")
    );
    let cases: Vec<(String, Leg)> = vec![
        (
            "policy.m.exists(k, k == req.name)".to_string(),
            Leg::SpecKnown,
        ),
        (
            "policy.nums.exists(x, x == req.n)".to_string(),
            Leg::SpecKnown,
        ),
        (literal, Leg::Facts),
    ];
    let mut failures = Vec::new();
    for (src, leg) in &cases {
        let p = probe(src, *leg, 1000);
        if p.prof.ops > 8 {
            failures.push(p.over("ops", p.prof.ops as f64, 8.0, NS_KNOWN_SET));
        }
    }
    fail_on("known membership test(s) that scan", failures);
}

// ---- 11. an invariant inner loop, run once ----

const NS_INNER: &str = "`names.exists(x, x == req.name || nums.exists(y, y < 0.0))` 9.8 µs at \
     n=100 (was 1.17 ms, quadratic)";

/// A comprehension inside a loop body that names neither loop variable computes the same value on
/// every iteration: it runs at most once per decision (on first use, like a loop-invariant read).
/// Budget: linear — 40 ops per outer element, n=100.
///
/// `Lower::invariant_comprehension` (`src/fast/lower.rs`) keeps its result in a pinned register
/// behind a `BrSet`; an erroring one keeps nothing and fails again where it is reached again.
#[test]
fn loop_invariant_inner_comprehension_runs_once() {
    const N: usize = 100;
    let p = probe(
        "policy.names.exists(x, x == req.name || policy.nums.exists(y, y < 0.0))",
        Leg::Act,
        N,
    );
    let budget = (40 * N) as f64;
    fail_on(
        "invariant inner loop(s) re-run per element",
        if p.prof.ops as f64 > budget {
            vec![p.over("ops", p.prof.ops as f64, budget, NS_INNER)]
        } else {
            vec![]
        },
    );
}

// ---- 12. a literal-only subtree is folded at lowering ----

const NS_CONSTANT: &str = "`req.n < 60.0 * 60.0 * 24.0` 42 ns (was 87) vs 42 ns for `req.n < \
     86400.0`; `(true && !false) && req.flag` 26 ns (was 56) vs 31 ns for `req.flag`";

/// A subtree of literals only — `60.0 * 60.0 * 24.0`, `duration("1h") + duration("30m")`,
/// `true && !false` — is computed once, at lowering, in a program that was compiled and never
/// specialized. Budget: no more ops than the program with the value written out.
///
/// `src/fast/lower.rs`: `constant_value` runs a call over constants once (`fold_call`, the
/// backend over no roots, as `specialize` does), keeping it only when it answers; `logic_chain`
/// drops a constant leaf that passes and settles on one that decides.
#[test]
fn a_literal_only_subtree_is_folded_before_it_runs() {
    let cases = [
        ("req.n < 60.0 * 60.0 * 24.0", "req.n < 86400.0"),
        (
            r#"req.d < duration("1h") + duration("30m")"#,
            r#"req.d < duration("90m")"#,
        ),
        ("(true && !false) && req.flag", "req.flag"),
    ];
    let mut failures = Vec::new();
    for (src, folded) in cases {
        let p = probe(src, Leg::Facts, 1);
        let twin = probe(folded, Leg::Facts, 1);
        if p.prof.ops > twin.prof.ops {
            failures.push(p.over(
                &format!("ops (folded `{folded}`: {})", twin.prof.ops),
                p.prof.ops as f64,
                twin.prof.ops as f64,
                NS_CONSTANT,
            ));
        }
    }
    fail_on("literal-only subtree(s) computed per decision", failures);
}

// ---- 13. an error that is discarded allocates nothing ----

const NS_DISCARDED_ERROR: &str = "`items.exists(i, i.tags[5] == req.name || i.qty > 999.0)` \
     specialized at n=1000: 254 µs (was 270), no allocation per element (was ~2)";

/// A comprehension step that fails keeps only its FIRST error, and an absorbing element discards
/// that one too; an error nobody will read costs no allocation. Budget: two allocations per
/// decision (the one error that might be reported), whatever the size.
///
/// `src/fast/mod.rs`: a failure is written into the in-flight box a handler left behind (`fault`,
/// `caught`), and `RaisePending` moves its newest error out rather than copying it.
#[test]
fn a_discarded_loop_error_allocates_nothing() {
    let p = probe(
        "policy.items.exists(i, i.tags[5] == req.name || i.qty > 999.0)",
        Leg::SpecKnown,
        1000,
    );
    fail_on(
        "loop(s) allocating errors they discard",
        if p.prof.allocs > 2 {
            vec![p.over("allocations", p.prof.allocs as f64, 2.0, NS_DISCARDED_ERROR)]
        } else {
            vec![]
        },
    );
}

// ---- the unspecialized loop floor: a loop over a BOUND collection (`Vm::eval`) ----
//
// Budgets count what one more element costs: ops dispatched and `slow` entries, the slope between
// n = 10 and n = 1000 on the activation leg. What those ops cost is `ablation/benches/loops.rs`,
// whose `--check` holds the per-op instruction budget: a release build's count, so not a test here.

/// Fail every case whose per-element slope of `q` is over its budget.
fn per_elem_budgets(
    what: &str,
    ns: &str,
    q: fn(&RunProfile) -> u64,
    cases: &[(&str, f64)],
    failures: &mut Vec<String>,
) {
    for (src, budget) in cases {
        let (slope, big) = per_elem(src, Leg::Act, q);
        if slope > *budget {
            failures.push(big.over(what, slope, *budget, ns));
        }
    }
}

/// Fail every case whose per-element slope of `q` is UNDER its floor.
fn per_elem_floors(
    what: &str,
    ns: &str,
    q: fn(&RunProfile) -> u64,
    cases: &[(&str, f64)],
    failures: &mut Vec<String>,
) {
    for (src, floor) in cases {
        let (slope, big) = per_elem(src, Leg::Act, q);
        if slope < *floor {
            failures.push(big.over(&format!("{what} (a FLOOR)"), slope, *floor, ns));
        }
    }
}

const NS_SCAN: &str =
    "`names.exists(x, x == req.name)` 1.1 ns/element (15 instructions; 11.1 and 96 \
     unscanned), `nums.all(x, x > req.n)` 2.3 (26), `roots.exists(r, req.path.startsWith(r))` 5.7 \
     (47), `m.exists(k, k == req.name)` 1.2 (15), `items.exists(i, i.id == req.name && i.qty > \
     req.n)` 7.9 (97), `names.exists(x, x.matches(\"^zz$\"))` 6.4 (66) — act leg, n=1000, \
     `loops.rs` on a Hetzner cx33; Rust 0.4-4.3";

/// The loops that scan, over bench data none of whose elements decides.
const SCANNED_LOOPS: &[&str] = &[
    "policy.names.exists(x, x == req.name)",
    "policy.nums.exists(x, x < req.n)",
    "policy.nums.all(x, x > req.n)",
    "policy.roots.exists(r, req.path.startsWith(r))",
    "policy.names.all(x, x != req.name)",
    "policy.names.exists_one(x, x == req.name)",
    "policy.m.exists(k, k == req.name)",
    r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#,
    "policy.nums.all(x, x > req.n && x < 1000000.0)",
    "policy.items.exists(i, i.id == req.name && i.qty > req.n)",
    "policy.items.all(i, i.qty > req.n)",
    "policy.m.all(k, policy.m[k] > req.n)",
    r#"policy.names.exists(x, x.matches("^zz$"))"#,
];

/// An element that does not decide its loop dispatches no op: the loop's `IterNext` passes over it
/// natively, testing it as the body's first op would. Budget: 0.05 ops per element (a loop
/// dispatches its `IterNext` and exit once per decision, not per element), NO `slow` entry, and at
/// least 0.95 elements scanned past per element — the floor that says the elements were skipped,
/// not merely that no op counted them.
///
/// `scan::fuse` (`src/fast/scan.rs`) gives the `IterNext` its region; `scan::skip` runs it.
#[test]
fn a_skipped_element_dispatches_no_op() {
    let mut failures = Vec::new();
    let ops: Vec<_> = SCANNED_LOOPS.iter().map(|s| (*s, 0.05)).collect();
    per_elem_budgets("ops per element", NS_SCAN, |p| p.ops, &ops, &mut failures);
    let zero: Vec<_> = SCANNED_LOOPS.iter().map(|s| (*s, 0.0)).collect();
    per_elem_budgets(
        "slow entries per element",
        NS_SCAN,
        |p| p.slow,
        &zero,
        &mut failures,
    );
    let skipped: Vec<_> = SCANNED_LOOPS.iter().map(|s| (*s, 0.95)).collect();
    per_elem_floors(
        "elements scanned past, per element",
        NS_SCAN,
        |p| p.scanned,
        &skipped,
        &mut failures,
    );
    fail_on("scanned loop(s) dispatching per element", failures);
}

/// A scan reads nothing: a loop reads the host exactly as often scanning as not
/// (`with_unfused_loops`), at every size — the first element's field read stays the body's.
#[test]
fn a_scanned_loop_reads_what_its_unfused_twin_reads() {
    let env = perf::env();
    let mut failures = Vec::new();
    for src in SCANNED_LOOPS {
        for n in [0, 1, 10] {
            let (policy, req) = (perf::policy(n), perf::req(n));
            let run = || {
                let p = perf::prepare(&env, src, Leg::Act, &policy, &req).expect("the act leg");
                let (verdict, prof) = p.measure();
                (
                    verdict.map_err(|e| e.to_string()),
                    prof,
                    p.fast.scanned_loops(),
                )
            };
            let (fused, fused_prof, fused_scans) = run();
            let (unfused, unfused_prof, unfused_scans) = typed_cel::with_unfused_loops(run);
            assert!(fused_scans > 0, "`{src}` does not scan");
            assert_eq!(unfused_scans, 0, "`{src}` scans with loops unfused");
            if fused != unfused || fused_prof.reads != unfused_prof.reads {
                failures.push(format!(
                    "`{src}` n={n}: {fused:?} with {} reads, unfused {unfused:?} with {}",
                    fused_prof.reads, unfused_prof.reads
                ));
            }
        }
    }
    fail_on(
        "scanned loop(s) reading unlike their unfused twin",
        failures,
    );
}

const NS_FIELD_TEST: &str =
    "`names.exists(x, x == req.name)` 1.1 ns/element (15 instructions, scanned; \
     was 19.8 and 170, and 31.3 and 228 before), `nums.all(x, x > req.n)` 2.3 (was 19.7), \
     `roots.exists(r, req.path.startsWith(r))` 5.7 (was 25.2), `exists_one` 1.1 (was 20.7) — act \
     leg, n=1000; Rust 0.4-4.3 ns/element";

/// A loop whose test compares the element with a loop-invariant FIELD costs what the same loop
/// against a constant does: fetch the element, and one op that reads the field (cached after the
/// first element), compares and branches — back to the fetch when the loop goes on, out when it
/// is decided. Budget: TWO ops per element; three for `exists_one`, which also counts.
///
/// `CondFR` (`src/fast/mod.rs`) reads the field through its cache register, tests and branches;
/// `Lower::try_field_branch` produces it, and `Lower::try_predicate_loop` makes a non-deciding
/// element's branch land on the loop head itself.
///
/// A predicate loop now scans: its non-deciding elements pass inside its `IterScan`, dispatching no
/// op (`a_skipped_element_dispatches_no_op`), so this budget is a ceiling the loop meets with room.
#[test]
fn a_loop_test_against_a_field_is_one_op() {
    let mut failures = Vec::new();
    per_elem_budgets(
        "ops per element",
        NS_FIELD_TEST,
        |p| p.ops,
        &[
            ("policy.names.exists(x, x == req.name)", 2.0),
            ("policy.nums.exists(x, x < req.n)", 2.0),
            ("policy.nums.all(x, x > req.n)", 2.0),
            ("policy.roots.exists(r, req.path.startsWith(r))", 2.0),
            ("policy.names.all(x, x != req.name)", 2.0),
            ("policy.names.exists_one(x, x == req.name)", 3.0),
        ],
        &mut failures,
    );
    fail_on("loop(s) testing a field in more than one op", failures);
}

const NS_RECORD: &str = "`items.exists(i, i.id == req.name && i.qty > req.n)` 7.9 ns/element \
     (97 instructions, scanned; was 72.8 and 460), `items.all(i, i.qty > req.n)` 9.1 (108; was \
     74.2) — act leg, n=1000; Rust 0.6. The rest is the member lookup: two pointer chases a member";

/// A field of a bound record element is selected in the dispatch loop, from the loop variable in
/// place. Budget: NO `slow` entry per element, and three ops per element for a one-test predicate
/// (fetch, select, fused test) — `items.exists`' first test fails on every element of the data.
///
/// `exec`'s `Op::Select` arm answers a bound map's present member (`src/fast/mod.rs`); the
/// lowering selects from the loop variable in place (`Lower::operand`), and a `&&` chain's
/// per-element `Clear` rides the `IterNext` (`Lower::clear`).
///
/// A predicate loop now scans: its non-deciding elements pass inside its `IterScan`, dispatching no
/// op (`a_skipped_element_dispatches_no_op`), so this budget is a ceiling the loop meets with room.
#[test]
fn a_bound_record_field_is_selected_in_the_loop() {
    let mut failures = Vec::new();
    let cases = &[
        (
            "policy.items.exists(i, i.id == req.name && i.qty > req.n)",
            3.0,
        ),
        ("policy.items.all(i, i.qty > req.n)", 3.0),
    ];
    per_elem_budgets(
        "ops per element",
        NS_RECORD,
        |p| p.ops,
        cases,
        &mut failures,
    );
    let zero: Vec<_> = cases.iter().map(|(s, _)| (*s, 0.0)).collect();
    per_elem_budgets(
        "slow entries per element",
        NS_RECORD,
        |p| p.slow,
        &zero,
        &mut failures,
    );
    fail_on("record loop(s) over budget", failures);
}

const NS_MAP: &str = "`m.exists(k, k == req.name)` 1.2 ns/element (15 instructions, scanned; was \
     21.3), `m.all(k, policy.m[k] > req.n)` 11.5 ns/element (128 instructions; was 29.6 and 251) — \
     act leg, n=1000; Rust 0.4, and 31 through a HashMap";

/// A bound map's keys are iterated, and the map indexed by them, in the dispatch loop; the map
/// the body indexes is the one the loop already read. Budget: NO `slow` entry per element; two
/// ops per element for a key test, three for an index then a test.
///
/// `IterNext` over a bound map's keys is inline, and `m[k]` over the loop's own map and key is
/// `IndexIter`: the iteration's current entry, no lookup and no re-read of `policy.m` — the only
/// computed key the checker admits (`Lower::iter_index`, `src/fast/lower.rs`).
///
/// A predicate loop now scans: its non-deciding elements pass inside its `IterScan`, dispatching no
/// op (`a_skipped_element_dispatches_no_op`), so this budget is a ceiling the loop meets with room.
#[test]
fn a_bound_map_is_iterated_and_indexed_in_the_loop() {
    let mut failures = Vec::new();
    let cases = &[
        ("policy.m.exists(k, k == req.name)", 2.0),
        ("policy.m.all(k, policy.m[k] > req.n)", 3.0),
    ];
    per_elem_budgets("ops per element", NS_MAP, |p| p.ops, cases, &mut failures);
    let zero: Vec<_> = cases.iter().map(|(s, _)| (*s, 0.0)).collect();
    per_elem_budgets(
        "slow entries per element",
        NS_MAP,
        |p| p.slow,
        &zero,
        &mut failures,
    );
    fail_on("map loop(s) over budget", failures);
}

const NS_ARITH: &str = "`size(nums.map(x, x * 2.0))` 15.6 ns/element (130 instructions; was 26.4 \
     and 209) — act leg, n=1000; `req.n * 2.0 + 1.0 < 10.0` enters `slow` no more (was twice)";

/// Numeric arithmetic is an inline op, and a constant operand is not reloaded every element.
/// Budget: NO `slow` entry for `Num (+-*/) Num`, per element of a `map` or in a scalar decision;
/// three ops per element of `map(x, x * 2.0)` (fetch, multiply by the constant, append) plus the
/// jump back.
///
/// `exec` answers `Arith` over two numbers inline (`Arith::num`), and a numeric constant operand
/// is `ArithK`'s, read from the pool (`src/fast/mod.rs`; lowered in `src/fast/lower.rs`).
#[test]
fn numeric_arithmetic_stays_in_the_dispatch_loop() {
    let mut failures = Vec::new();
    let src = "size(policy.nums.map(x, x * 2.0)) > req.n";
    per_elem_budgets(
        "ops per element",
        NS_ARITH,
        |p| p.ops,
        &[(src, 4.0)],
        &mut failures,
    );
    per_elem_budgets(
        "slow entries per element",
        NS_ARITH,
        |p| p.slow,
        &[(src, 0.0)],
        &mut failures,
    );
    let p = probe("req.n * 2.0 + 1.0 < 10.0", Leg::Act, 1);
    if p.prof.slow_of("Arith") > 0 {
        failures.push(p.over(
            "Arith slow entries",
            p.prof.slow_of("Arith") as f64,
            0.0,
            NS_ARITH,
        ));
    }
    fail_on("arithmetic over budget", failures);
}

const NS_STRING_TEST: &str = "`roots.exists(r, req.path == r || req.path.startsWith(r + \"/\"))` \
     20.4 ns/element (188 instructions, scanned; was 36.2 and 308); `names.exists(x, \
     x.matches(\"^zz$\"))` 6.4 (66; was 22.2); `names.exists(x, x.contains(req.name))` 10.8 (137; a \
     prebuilt searcher, where Rust's `str::contains` builds one a call and takes 29.4); `req.name in \
     policy.names` 0.75 (8) — act leg, n=1000; Rust 5.1, 2.8, 29.4 and 0.5";

/// A string test on a loop element — a prefix of a concatenation, a regex match against a constant
/// pattern — is an inline op, its constant operand loaded once. Budget: NO `slow` entry per
/// element; the prefix loop's two tests are three ops per element (fetch, equality fused with the
/// field, prefix-of-concatenation fused with its branch), the match loop's two.
///
/// `StrOp2`, `Matches` and its fused `CondMatches` are inline, a literal pattern never loaded;
/// a field tested against `b + "k"` is one `CondStrOp2F`; and a fallible `&&`/`||` chain keeps no
/// pending-error bookkeeping on the path where no leaf fails (`Lower::split_chain`).
///
/// A predicate loop now scans: its non-deciding elements pass inside its `IterScan`, dispatching no
/// op (`a_skipped_element_dispatches_no_op`), so this budget is a ceiling the loop meets with room.
#[test]
fn string_tests_stay_in_the_dispatch_loop() {
    let mut failures = Vec::new();
    let cases = &[
        (
            r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#,
            3.0,
        ),
        (r#"policy.names.exists(x, x.matches("^zz$"))"#, 2.0),
    ];
    per_elem_budgets(
        "ops per element",
        NS_STRING_TEST,
        |p| p.ops,
        cases,
        &mut failures,
    );
    let zero: Vec<_> = cases.iter().map(|(s, _)| (*s, 0.0)).collect();
    per_elem_budgets(
        "slow entries per element",
        NS_STRING_TEST,
        |p| p.slow,
        &zero,
        &mut failures,
    );
    fail_on("string-test loop(s) over budget", failures);
}

const NS_NESTED: &str = "`items.exists(i, i.tags.exists(t, t == req.name))` 72 ns per outer \
     element (497 instructions, the inner loop scanned; was 239 and 1558), 3 tags each — act leg, \
     n=1000; Rust 16";

/// An inner loop over a field of the outer element starts in the dispatch loop, and its verdict is
/// control flow, not a bool the outer predicate re-tests. Budget: NO `slow` entry per outer
/// element, and eleven ops per outer element of three inner ones: fetch, select, start the inner
/// loop (3); four inner fetches, the last one exiting, and three fused tests (7); the inner exit's
/// `RaisePending`, laid out to fall through into the outer fetch (1).
///
/// `IterInit` is inline and resets the loop's pending error itself; the fetch that ends a loop
/// raises it (`IterNext`'s `pend`); and a predicate loop in branch position is control flow
/// (`Outcome::Branch`, `Lower::try_predicate_loop`).
#[test]
fn an_inner_loop_over_an_element_starts_in_the_loop() {
    let mut failures = Vec::new();
    let src = "policy.items.exists(i, i.tags.exists(t, t == req.name))";
    per_elem_budgets(
        "ops per outer element",
        NS_NESTED,
        |p| p.ops,
        &[(src, 11.0)],
        &mut failures,
    );
    per_elem_budgets(
        "slow entries per outer element",
        NS_NESTED,
        |p| p.slow,
        &[(src, 0.0)],
        &mut failures,
    );
    fail_on("nested loop(s) over budget", failures);
}

const NS_ABSORBED: &str = "`items.all(i, i.tags[5] == req.name || i.qty > 0.0)` 89 ns/element \
     (653 instructions; was 244 and 1745) — act leg, n=1000; Rust 0.9. Specialized, 254 µs a decision";

/// An element whose first test fails and whose second decides it — every element of
/// `items.all(i, i.tags[5] == req.name || i.qty > 0.0)` — costs the failure once: one
/// `slow` entry to raise the out-of-range index (the rare path's cost), the catch inline. Budget:
/// ONE `slow` entry and eight ops per element — fetch, select, index (raises), catch, select,
/// fused test, and the handler's two jumps.
///
/// `Catch` is inline (the error out of the reusable in-flight box); the selects are inline from
/// the element in place (Story 2) and `i.qty > 0.0` is one `CondCmpK`: the one `slow` entry is
/// the out-of-range `Index` raising.
#[test]
fn a_discarded_element_error_is_one_slow_entry() {
    let mut failures = Vec::new();
    let src = "policy.items.all(i, i.tags[5] == req.name || i.qty > 0.0)";
    per_elem_budgets(
        "ops per element",
        NS_ABSORBED,
        |p| p.ops,
        &[(src, 8.0)],
        &mut failures,
    );
    per_elem_budgets(
        "slow entries per element",
        NS_ABSORBED,
        |p| p.slow,
        &[(src, 1.0)],
        &mut failures,
    );
    fail_on("error-absorbing loop(s) over budget", failures);
}

// ---- green guards: families that are already fine ----

/// GREEN GUARD. A known list of strings tested by `==`/`startsWith` (with a literal suffix) is one
/// matcher at every size — the specialized form of the prefix loop runs in 242 ns at n=1000,
/// against 351 µs on the activation leg. Holds `try_match_exists` from regressing into the loop,
/// as a value and as a CONDITION (a branch: the policy shape `ablation`'s `fs_open_1000` runs,
/// where a known list once lowered as a predicate loop over the constant instead).
#[test]
fn a_known_string_list_is_one_matcher_at_every_size() {
    let mut failures = Vec::new();
    for n in [10, 256, 1000] {
        for (src, budget) in [
            (
                r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#,
                4.0,
            ),
            (
                r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/")) ? req.n > 1.0 : req.n < 1.0"#,
                6.0,
            ),
        ] {
            let p = probe(src, Leg::SpecKnown, n);
            // A scanned loop dispatches few ops however long the list: `scanned` is what shows it.
            if p.prof.ops as f64 > budget || p.prof.allocs > 0 || p.prof.scanned > 0 {
                failures.push(p.over("ops", p.prof.ops as f64, budget, "242 ns at n=1000"));
            }
        }
    }
    fail_on(
        "known string list(s) that stopped being a matcher",
        failures,
    );
}

/// GREEN GUARD. A string predicate over a long string costs the same ops, and allocates nothing,
/// whatever the string's length (64 B to 64 KiB).
#[test]
fn long_string_predicates_are_constant_ops_and_allocate_nothing() {
    let mut failures = Vec::new();
    for src in [
        "req.long.startsWith(req.name)",
        r#"req.long.contains("zz")"#,
        r#"req.long.matches("zz")"#,
    ] {
        for n in [1, 1000] {
            let p = probe(src, Leg::Facts, n);
            if p.prof.ops > 4 || p.prof.allocs > 0 {
                failures.push(p.over("ops", p.prof.ops as f64, 4.0, "not measured"));
            }
        }
    }
    fail_on("long-string predicate(s) that grew", failures);
}

/// GREEN GUARD. A path five members deep, read or tested for presence, is one host read and at
/// most three ops.
#[test]
fn a_deep_path_is_one_read() {
    let mut failures = Vec::new();
    for src in [r#"req.a.b.c.d.e == "leaf""#, "has(req.a.b.c.d.e)"] {
        let p = probe(src, Leg::Facts, 1);
        if p.prof.ops > 3 || p.prof.reads != 1 {
            failures.push(p.over("ops", p.prof.ops as f64, 3.0, "not measured"));
        }
    }
    fail_on("deep path(s) that cost more than one read", failures);
}

/// GREEN GUARD. A streamed run over a document whose demanded fields follow a long string costs
/// the same ops, reads and allocations at 64 B and at 64 KiB of padding: the governed value keeps
/// only what the program demands, and the run resumes only on the fields it waits for.
#[test]
fn a_streamed_run_costs_the_same_at_every_document_size() {
    perf::assert_counting();
    let mut env = CelEnvironment::new();
    env.declare("n", CelTy::Num);
    env.declare(
        "body",
        support::record(
            "body",
            &[
                ("pad", CelTy::Str),
                ("tier", CelTy::Str),
                ("amount", CelTy::Num),
            ],
        ),
    );
    let src = r#"body.tier == "gold" && body.amount < 100.0"#;
    let compiled = env.compile(src, &CompileOpts::default()).expect("compiles");
    let code = Arc::new(typed_cel::emit(&compiled).expect("emits"));
    let mut act = env.activation();
    act.bind("n", &serde_json::json!(3)).expect("binds");
    let program = StreamedProgram::new(Arc::new(Vm::new()), &env, &compiled, code, act, "body")
        .expect("streams");
    let run = |n: usize| {
        let doc = format!(
            r#"{{"pad":"{}","tier":"gold","amount":5}}"#,
            "p".repeat(n * 64)
        );
        let evs = support::events::to_events(&doc, 64);
        let (verdict, prof) = profile::measure(|| {
            let mut run = program.begin();
            for e in &evs {
                run.push(e.as_event());
            }
            run.finish()
        });
        assert!(matches!(verdict, Ok(true)), "{verdict:?}");
        prof
    };
    let (small, big) = (run(1), run(1000));
    assert!(
        (small.ops, small.reads, small.allocs) == (big.ops, big.reads, big.allocs),
        "a streamed run's cost grew with the document:\n  64 B:   {}\n  64 KiB: {}",
        small.summary(),
        big.summary()
    );
}

/// GREEN GUARD. What `specialize` leaves is fully folded — no call over literals only survives into
/// a residual — and its own work (allocations) and the residual's size grow linearly in the known
/// collection while it unrolls (n = 10 → 100).
#[test]
fn the_specializer_leaves_no_literal_only_call() {
    let mut failures = Vec::new();
    for src in [
        r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#,
        "policy.nums.all(x, x > req.n)",
        "policy.items.exists(i, i.id == req.name && i.qty > req.n)",
        "req.n < 60.0 * 60.0 * 24.0",
        r#"req.d < duration("1h") + duration("30m") && req.n < policy.nums[0] * 2.0"#,
    ] {
        let (small, big) = (
            probe(src, Leg::SpecKnown, 10),
            probe(src, Leg::SpecKnown, 100),
        );
        let mut left = Vec::new();
        perf::foldable_calls(fork::expression_of(&big.p.program), &mut left);
        if !left.is_empty() {
            failures.push(format!("`{src}`: the residual still computes {left:?}"));
        }
        let (a, b) = (
            small.p.specialize.as_ref().unwrap().allocs as f64,
            big.p.specialize.as_ref().unwrap().allocs as f64,
        );
        let (na, nb) = (
            perf::nodes(fork::expression_of(&small.p.program)) as f64,
            perf::nodes(fork::expression_of(&big.p.program)) as f64,
        );
        if b > 12.0 * a || nb > 12.0 * na {
            failures.push(format!(
                "`{src}`: specialize grew superlinearly from n=10 to n=100: allocations {a} -> \
                 {b}, residual nodes {na} -> {nb}"
            ));
        }
    }
    fail_on("specialization(s) not fully folded or not linear", failures);
}

/// The rig itself: a counter that cannot see the thing it counts would make every pin above
/// vacuous. Known programs, known counts.
#[test]
fn the_counters_see_what_they_count() {
    let p = probe("req.flag", Leg::Facts, 1);
    assert_eq!(
        (p.prof.ops, p.prof.reads, p.prof.allocs),
        (2, 1, 0),
        "{}",
        p.prof.summary()
    );
    // `contains` is not tested piecewise (a match may span the pieces): the `+` is built.
    let concat = probe(r#"(req.path + req.name).contains("x")"#, Leg::Facts, 1);
    // A string `+` is built out of line: one store push, one entry into `slow`.
    assert!(
        concat.prof.store == 1 && concat.prof.allocs >= 1 && concat.prof.slow_of("Arith") == 1,
        "{}",
        concat.prof.summary()
    );
    // Ten elements and the end: the first element fetched (its field read fills the cache), a
    // second `IterScan` scanning past the other nine, then finding none left.
    let lp = probe("policy.names.exists(x, x == req.name)", Leg::Act, 10);
    assert!(
        (lp.prof.op("IterScan"), lp.prof.scanned) == (2, 9),
        "{}",
        lp.prof.summary()
    );
}
