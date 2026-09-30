//! The cliff HARVESTER: sweeps program families and generated corpora, counts what every decision
//! does (`typed_cel::profile`), and flags cost-model outliers. It is a report, not a gate — every
//! test here is `#[ignore]`d and run explicitly:
//!
//! ```text
//! cargo test -p typed-cel --test perf_harvest -- --ignored --nocapture --test-threads=1 harvest
//! cargo test -p typed-cel --release --test perf_harvest -- --ignored --nocapture spot_ns
//! ```
//!
//! What it found is pinned, one red test per cliff, in `tests/perf_cliffs.rs`; the write-up is
//! `docs/PERFORMANCE.md` "Known cliffs". Flags are by COST MODEL, never wall time:
//!
//! - `OPS/ELEM` — a loop body dispatches more than [`OPS_PER_ELEM`] ops per element;
//! - `SUPERLINEAR` — ops, allocations or store pushes grow faster than N over a decade;
//! - `ALLOC` — a program that builds no value its answer needs allocates;
//! - `INVARIANT-READ` — a host field is read once per element, not once per decision;
//! - `SLOW/ELEM` — ops per element go out of line to `slow`;
//! - `FOLDABLE` — a residual still holds a call over literals only;
//! - `COMPILE` — `specialize`'s own work, or the residual's size, grows faster than its input.
//!
//! `spot_ns` times the worst finds (secondary evidence, for the write-up only; nothing asserts it).

#[path = "../conformance/harness/mod.rs"]
mod harness;
#[path = "support/mod.rs"]
mod support;

use typed_cel::CompileOpts;
use std::collections::BTreeMap;

use typed_cel::fork;
use typed_cel::profile::{self, CountingAlloc, RunProfile};
use typed_cel::{CelEnvironment, FastProgram, FastScratch};
use harness::case::Binding;
use harness::exclusions::Exclusions;
use harness::{conformance_dir, corpus};
use support::perf::{self, Leg, Prepared};

#[global_allocator]
static ALLOC: CountingAlloc = CountingAlloc;

/// What a tight lowering needs per element of a predicate loop: fetch the next element, test it
/// (one or two fused compare-and-branch ops), and step (a jump back). Twice that is generous.
const OPS_PER_ELEM: f64 = 8.0;

const SCALE: &[usize] = &[1, 10, 100, 1000];
const DEPTH: &[usize] = &[1, 4, 16, 30];
/// A nested conditional nests two levels per arm; 24 arms is the deepest under the limit of 32.
const TERNARY: &[usize] = &[1, 4, 12, 24];
const FIXED: &[usize] = &[1, 1000];

/// One family: a program shape, parameterized by `n` (a collection's size, a chain's depth or a
/// string's length/64).
struct Fam {
    name: &'static str,
    ns: &'static [usize],
    src: fn(usize) -> String,
    /// Does the ANSWER need a value the program builds (a string, a list)? If not, an allocation is
    /// a cliff.
    builds: bool,
    /// Is `n` a count of elements (or terms) the program visits one by one?
    per_elem: bool,
}

fn s(x: &str) -> String {
    x.to_string()
}

fn chain(n: usize, op: &str, term: impl Fn(usize) -> String) -> String {
    (0..n).map(term).collect::<Vec<_>>().join(op)
}

fn ternary(
    n: usize,
    cond: impl Fn(usize) -> String,
    arm: impl Fn(usize) -> String,
    last: &str,
) -> String {
    let mut out = String::new();
    for i in 0..n {
        out.push_str(&format!("{} ? {} : ", cond(i), arm(i)));
    }
    out.push_str(last);
    out
}

fn families() -> Vec<Fam> {
    macro_rules! fam {
        ($name:expr, $ns:expr, $builds:expr, $per:expr, $src:expr) => {
            Fam {
                name: $name,
                ns: $ns,
                src: $src,
                builds: $builds,
                per_elem: $per,
            }
        };
    }
    vec![
        // ---- comprehension macros over a bound (policy) collection ----
        fam!("exists/str/eq-or-prefix-concat", SCALE, false, true, |_| s(
            r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#
        )),
        fam!("exists/str/eq", SCALE, false, true, |_| s(
            "policy.names.exists(x, x == req.name)"
        )),
        fam!("exists/str/startsWith", SCALE, false, true, |_| s(
            "policy.roots.exists(r, req.path.startsWith(r))"
        )),
        fam!("exists/str/endsWith", SCALE, false, true, |_| s(
            "policy.names.exists(x, req.name.endsWith(x))"
        )),
        fam!("exists/str/contains", SCALE, false, true, |_| s(
            "policy.names.exists(x, req.path.contains(x))"
        )),
        fam!("exists/str/matches", SCALE, false, true, |_| s(
            r#"policy.names.exists(x, x.matches("^zz$"))"#
        )),
        fam!("exists/num/lt", SCALE, false, true, |_| s(
            "policy.nums.exists(x, x < req.n)"
        )),
        fam!("all/num/gt", SCALE, false, true, |_| s(
            "policy.nums.all(x, x > req.n)"
        )),
        fam!("all/str/ne", SCALE, false, true, |_| s(
            "policy.names.all(x, x != req.name)"
        )),
        fam!("exists_one/num", SCALE, false, true, |_| s(
            "policy.nums.exists_one(x, x == req.n)"
        )),
        fam!("exists_one/str", SCALE, false, true, |_| s(
            "policy.names.exists_one(x, x == req.name)"
        )),
        fam!("map/num/size", SCALE, true, true, |_| s(
            "size(policy.nums.map(x, x * 2.0)) > req.n"
        )),
        fam!("map3/num/size", SCALE, true, true, |_| s(
            "size(policy.nums.map(x, x > req.n, x * 2.0)) > req.n"
        )),
        fam!("filter/num/size", SCALE, true, true, |_| s(
            "size(policy.nums.filter(x, x > req.n)) > req.n"
        )),
        fam!("filter/str/size", SCALE, true, true, |_| s(
            "size(policy.names.filter(x, x != req.name)) > req.n"
        )),
        fam!("map/num/exists", SCALE, true, true, |_| s(
            "policy.nums.map(x, x * 2.0).exists(y, y < req.n)"
        )),
        fam!("exists/record", SCALE, false, true, |_| s(
            "policy.items.exists(i, i.id == req.name && i.qty > req.n)"
        )),
        fam!("all/record", SCALE, false, true, |_| s(
            "policy.items.all(i, i.qty > req.n)"
        )),
        fam!("map/record/size", SCALE, true, true, |_| s(
            "size(policy.items.map(i, i.id)) > req.n"
        )),
        fam!("exists/map-key", SCALE, false, true, |_| s(
            "policy.m.exists(k, k == req.name)"
        )),
        fam!("all/map-key-index", SCALE, false, true, |_| s(
            "policy.m.all(k, policy.m[k] > req.n)"
        )),
        fam!("exists_one/map-key", SCALE, false, true, |_| s(
            "policy.m.exists_one(k, k == req.name)"
        )),
        fam!("map/map-key/size", SCALE, true, true, |_| s(
            "size(policy.m.map(k, k)) > req.n"
        )),
        fam!("filter/map-key/size", SCALE, true, true, |_| s(
            "size(policy.m.filter(k, policy.m[k] > req.n)) > req.n"
        )),
        fam!("in/list/str", SCALE, false, true, |_| s(
            "req.name in policy.names"
        )),
        fam!("in/list/num", SCALE, false, true, |_| s(
            "req.n in policy.nums"
        )),
        fam!("in/map", SCALE, false, false, |_| s("req.name in policy.m")),
        fam!("size/list", SCALE, false, false, |_| s(
            "size(policy.names) > req.n"
        )),
        fam!("size/map", SCALE, false, false, |_| s(
            "size(policy.m) > req.n"
        )),
        fam!("nested/exists-in-exists", SCALE, false, true, |_| s(
            "policy.items.exists(i, i.tags.exists(t, t == req.name))"
        )),
        fam!(
            "nested/invariant-inner-loop",
            &[1, 10, 100],
            false,
            true,
            |_| s("policy.names.exists(x, x == req.name || policy.nums.exists(y, y < 0.0))")
        ),
        fam!("error/absorbed-per-element", SCALE, false, true, |_| s(
            "policy.items.exists(i, i.tags[5] == req.name || i.qty < 0.0)"
        )),
        // ---- request-side collections (no Facts spelling: the activation leg only) ----
        fam!("req-list/exists/str", SCALE, false, true, |_| s(
            "req.tags.exists(t, t == req.name)"
        )),
        fam!("req-list/all/num", SCALE, false, true, |_| s(
            "req.nums.all(x, x > req.n)"
        )),
        fam!("req-list/in", SCALE, false, true, |_| s(
            "req.name in req.tags"
        )),
        // ---- strings, n = length / 64 ----
        fam!("string/startsWith-long", SCALE, false, false, |_| s(
            "req.long.startsWith(req.name)"
        )),
        fam!("string/contains-long", SCALE, false, false, |_| s(
            r#"req.long.contains("zz")"#
        )),
        fam!("string/matches-long", SCALE, false, false, |_| s(
            r#"req.long.matches("zz")"#
        )),
        fam!("string/concat-eq", FIXED, false, false, |_| s(
            "req.path + req.name == req.other"
        )),
        fam!("string/startsWith-concat", FIXED, false, false, |_| s(
            r#"req.path.startsWith(req.name + "/")"#
        )),
        fam!("string/concat-long-endsWith", SCALE, false, false, |_| s(
            "(req.long + req.name).endsWith(req.name)"
        )),
        // ---- deep boolean chains and nested conditionals (depth ≤ the 32 limit) ----
        fam!("chain/and-cmp", DEPTH, false, true, |n| chain(
            n,
            " && ",
            |i| format!("req.n < {}.0", 1000 + i)
        )),
        fam!("chain/or-num-eq", DEPTH, false, true, |n| chain(
            n,
            " || ",
            |i| format!("req.n == {}.0", 100 + i)
        )),
        fam!("chain/or-str-eq", DEPTH, false, true, |n| chain(
            n,
            " || ",
            |i| format!(r#"req.name == "a{i}""#)
        )),
        fam!("chain/and-mixed", DEPTH, false, true, |n| chain(
            n,
            " && ",
            |i| match i % 3 {
                0 => s("req.flag"),
                1 => format!(r#"req.name != "x{i}""#),
                _ => format!("req.n < {}.0", 100 + i),
            }
        )),
        fam!("ternary/num-to-str", TERNARY, false, true, |n| format!(
            "({}) == \"z\"",
            ternary(
                n,
                |i| format!("req.n == {}.0", 100 + i),
                |i| format!("\"a{i}\""),
                "\"z\""
            )
        )),
        fam!("ternary/str-to-num", TERNARY, false, true, |n| format!(
            "({}) < 0.0",
            ternary(
                n,
                |i| format!(r#"req.name == "k{i}""#),
                |i| format!("{i}.0"),
                "-1.0"
            )
        )),
        // ---- durations ----
        fam!("duration/cmp", FIXED, false, false, |_| s(
            r#"req.d > duration("5s")"#
        )),
        fam!("duration/arith", FIXED, false, false, |_| s(
            r#"req.d + duration("1s") < duration("1h")"#
        )),
        fam!("duration/vs-bound", FIXED, false, false, |_| s(
            "req.d < policy.limit"
        )),
        fam!("duration/getSeconds", FIXED, false, false, |_| s(
            "req.d.getSeconds() > 10.0"
        )),
        // ---- literals ----
        fam!("literal/list-of-fields-exists", FIXED, false, false, |_| s(
            r#"[req.name, req.path, req.other].exists(x, x == "zz")"#
        )),
        fam!("literal/in-list-of-fields", FIXED, false, false, |_| s(
            "req.name in [req.path, req.other]"
        )),
        fam!("literal/map-index", FIXED, false, false, |_| s(
            r#"{"a": req.n, "b": 2.0}["a"] > 0.0"#
        )),
        fam!("literal/str-list-exists", SCALE, false, true, |n| format!(
            "[{}].exists(x, req.name == x)",
            chain(n, ", ", |i| format!("\"s{i}\""))
        )),
        fam!("literal/num-list-exists", SCALE, false, true, |n| format!(
            "[{}].exists(x, x == req.n)",
            chain(n, ", ", |i| format!("{}.0", i + 1))
        )),
        // ---- presence, depth, arithmetic ----
        fam!("has/opt", FIXED, false, false, |_| s("has(req.opt)")),
        fam!("has/deep", FIXED, false, false, |_| s("has(req.a.b.c.d.e)")),
        fam!("select/deep", FIXED, false, false, |_| s(
            r#"req.a.b.c.d.e == "leaf""#
        )),
        fam!("arith/num", FIXED, false, false, |_| s(
            "req.n * 2.0 + 1.0 < 10.0"
        )),
        fam!("not/bool-and-cmp", FIXED, false, false, |_| s(
            "!req.flag || !(req.n < 0.0)"
        )),
        // ---- literal-only subtrees in a compiled (not specialized) program ----
        fam!("constant/arith-subtree", FIXED, false, false, |_| s(
            "req.n < 60.0 * 60.0 * 24.0"
        )),
        fam!("constant/duration-sum", FIXED, false, false, |_| s(
            r#"req.d < duration("1h") + duration("30m")"#
        )),
        fam!("constant/logic", FIXED, false, false, |_| s(
            "(true && !false) && req.flag"
        )),
    ]
}

struct Row {
    fam: &'static str,
    leg: Leg,
    how: &'static str,
    n: usize,
    ok: bool,
    prof: RunProfile,
    static_ops: usize,
    residual_nodes: Option<usize>,
    spec: Option<RunProfile>,
    foldable: Vec<String>,
    source: String,
    listing: String,
}

fn max_field_reads(p: &RunProfile) -> u64 {
    p.reads_by_field.iter().copied().max().unwrap_or(0)
}

fn slope(a: (usize, u64), b: (usize, u64)) -> f64 {
    (b.1 as f64 - a.1 as f64) / (b.0 as f64 - a.0 as f64)
}

/// Growth faster than N across the last decade of `rows`: `q(n2)/q(n1)` over `n2/n1`, above 1.5
/// once the quantity is past noise.
fn superlinear(pts: &[(usize, u64)]) -> Option<f64> {
    let [.., a, b] = pts else { return None };
    if a.1 < 20 || b.0 <= a.0 {
        return None;
    }
    let growth = (b.1 as f64 / a.1 as f64) / (b.0 as f64 / a.0 as f64);
    (growth > 1.5).then_some(growth)
}

#[test]
#[ignore = "the harvester: run explicitly, with --nocapture"]
fn harvest() {
    perf::assert_counting();
    let env = perf::env();
    let mut rows: Vec<Row> = Vec::new();
    for fam in families() {
        for leg in Leg::ALL {
            for &n in fam.ns {
                let src = (fam.src)(n);
                let (policy, req) = (perf::policy(n), perf::req(n));
                let Some(p): Option<Prepared> = perf::prepare(&env, &src, leg, &policy, &req)
                else {
                    break;
                };
                let (verdict, prof) = p.measure();
                let mut foldable = Vec::new();
                perf::foldable_calls(fork::expression_of(&p.program), &mut foldable);
                rows.push(Row {
                    fam: fam.name,
                    leg,
                    how: p.how(),
                    n,
                    ok: verdict.is_ok(),
                    static_ops: p.fast.op_count(),
                    residual_nodes: p
                        .specialize
                        .as_ref()
                        .map(|_| perf::nodes(fork::expression_of(&p.program))),
                    spec: p.specialize.clone(),
                    foldable,
                    source: p.program.source().chars().take(160).collect(),
                    listing: p.fast.listing(),
                    prof,
                });
            }
        }
    }

    println!("\n==== per-decision counts ====");
    println!(
        "{:<34} {:<12} {:>5} {:>8} {:>7} {:>6} {:>6} {:>6} {:>5} {:>9} {:>6} {:>6}  {}",
        "family",
        "leg",
        "n",
        "ops",
        "slow",
        "reads",
        "store",
        "allocs",
        "sops",
        "sp.allocs",
        "sp.ex",
        "nodes",
        "how"
    );
    for r in &rows {
        println!(
            "{:<34} {:<12} {:>5} {:>8} {:>7} {:>6} {:>6} {:>6} {:>5} {:>9} {:>6} {:>6}  {}{}",
            r.fam,
            r.leg.name(),
            r.n,
            r.prof.ops,
            r.prof.slow,
            r.prof.reads,
            r.prof.store,
            r.prof.allocs,
            r.static_ops,
            r.spec
                .as_ref()
                .map_or(String::new(), |p| p.allocs.to_string()),
            r.spec
                .as_ref()
                .map_or(String::new(), |p| p.execs.to_string()),
            r.residual_nodes.map_or(String::new(), |n| n.to_string()),
            r.how,
            if r.ok { "" } else { "  (ERR)" }
        );
    }

    println!("\n==== flags ====");
    let fams: BTreeMap<&str, Fam> = families().into_iter().map(|f| (f.name, f)).collect();
    let mut flagged = 0usize;
    for fam in fams.values() {
        for leg in Leg::ALL {
            let rs: Vec<&Row> = rows
                .iter()
                .filter(|r| r.fam == fam.name && r.leg == leg)
                .collect();
            if rs.is_empty() {
                continue;
            }
            let mut flags: Vec<String> = Vec::new();
            let pts = |q: fn(&RunProfile) -> u64| -> Vec<(usize, u64)> {
                rs.iter().map(|r| (r.n, q(&r.prof))).collect()
            };
            let (first, last) = (rs[0], rs[rs.len() - 1]);
            if fam.per_elem && rs.len() > 1 {
                let per = slope((first.n, first.prof.ops), (last.n, last.prof.ops));
                if per > OPS_PER_ELEM {
                    let by: Vec<String> = last
                        .prof
                        .by_op
                        .iter()
                        .map(|(k, v)| {
                            let f = first.prof.op(k);
                            (k, (*v as f64 - f as f64) / (last.n - first.n) as f64)
                        })
                        .filter(|(_, d)| *d >= 0.5)
                        .map(|(k, d)| format!("{k}:{d:.1}"))
                        .collect();
                    flags.push(format!(
                        "OPS/ELEM {per:.1} > {OPS_PER_ELEM} [{}]",
                        by.join(" ")
                    ));
                }
                let slow = slope((first.n, first.prof.slow), (last.n, last.prof.slow));
                if slow >= 0.5 {
                    let by: Vec<String> = last
                        .prof
                        .slow_by_op
                        .iter()
                        .map(|(k, v)| {
                            (
                                k,
                                (*v as f64 - first.prof.slow_of(k) as f64)
                                    / (last.n - first.n) as f64,
                            )
                        })
                        .filter(|(_, d)| *d >= 0.5)
                        .map(|(k, d)| format!("{k}:{d:.1}"))
                        .collect();
                    flags.push(format!("SLOW/ELEM {slow:.1} [{}]", by.join(" ")));
                }
                let reads = slope(
                    (first.n, max_field_reads(&first.prof)),
                    (last.n, max_field_reads(&last.prof)),
                );
                if reads >= 0.5 {
                    flags.push(format!(
                        "INVARIANT-READ {reads:.2}/elem (max {} reads of one field at n={})",
                        max_field_reads(&last.prof),
                        last.n
                    ));
                }
            }
            for (what, q) in [
                ("ops", (|p: &RunProfile| p.ops) as fn(&RunProfile) -> u64),
                ("allocs", |p: &RunProfile| p.allocs),
                ("store", |p: &RunProfile| p.store),
                ("alloc_bytes", |p: &RunProfile| p.alloc_bytes),
            ] {
                if let Some(g) = superlinear(&pts(q)) {
                    flags.push(format!(
                        "SUPERLINEAR {what} x{g:.1} per decade ({:?})",
                        pts(q)
                    ));
                }
            }
            if !fam.builds {
                if let Some(r) = rs.iter().rev().find(|r| r.prof.allocs > 0) {
                    flags.push(format!(
                        "ALLOC {} allocs / {} store at n={} (builds nothing the answer needs)",
                        r.prof.allocs, r.prof.store, r.n
                    ));
                }
            }
            if let Some(r) = rs.iter().find(|r| !r.foldable.is_empty()) {
                flags.push(format!("FOLDABLE {:?} at n={}", r.foldable, r.n));
            }
            if rs[0].spec.is_some() && rs.len() > 1 {
                let sp = |q: fn(&RunProfile) -> u64| -> Vec<(usize, u64)> {
                    rs.iter()
                        .map(|r| (r.n, q(r.spec.as_ref().unwrap())))
                        .collect()
                };
                for (what, q) in [
                    (
                        "specialize ops",
                        (|p: &RunProfile| p.ops) as fn(&RunProfile) -> u64,
                    ),
                    ("specialize execs", |p: &RunProfile| p.execs),
                    ("specialize allocs", |p: &RunProfile| p.allocs),
                ] {
                    if let Some(g) = superlinear(&sp(q)) {
                        flags.push(format!("COMPILE {what} x{g:.1} per decade ({:?})", sp(q)));
                    }
                }
                let nodes: Vec<(usize, u64)> = rs
                    .iter()
                    .map(|r| (r.n, r.residual_nodes.unwrap() as u64))
                    .collect();
                if let Some(g) = superlinear(&nodes) {
                    flags.push(format!(
                        "COMPILE residual nodes x{g:.1} per decade ({nodes:?})"
                    ));
                }
                let sops: Vec<(usize, u64)> =
                    rs.iter().map(|r| (r.n, r.static_ops as u64)).collect();
                if let Some(g) = superlinear(&sops) {
                    flags.push(format!(
                        "COMPILE residual ops x{g:.1} per decade ({sops:?})"
                    ));
                }
            }
            if !flags.is_empty() {
                flagged += 1;
                println!(
                    "\n{} [{}] via {}  `{}`",
                    fam.name,
                    leg.name(),
                    last.how,
                    last.source
                );
                for f in &flags {
                    println!("    {f}");
                }
                println!("    at n={}: {}", last.n, last.prof.summary());
                if let Some(sp) = &last.spec {
                    println!(
                        "    specialize at n={}: residual {} nodes, {} ops; {}",
                        last.n,
                        last.residual_nodes.unwrap(),
                        last.static_ops,
                        sp.summary()
                    );
                }
            }
        }
    }
    println!("\n{flagged} (family, leg) pairs flagged");
    let mut listings = String::new();
    for r in &rows {
        listings.push_str(&format!(
            "\n---- {} [{}] n={} via {}\n{}\n{}\n",
            r.fam,
            r.leg.name(),
            r.n,
            r.how,
            r.source,
            r.listing
        ));
    }
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("perf_harvest_listings.txt");
    std::fs::write(&path, listings).expect("writes the listings");
    println!("every program's listing: {}", path.display());
}

/// Outliers of the generated typed corpus and the conformance lane, per program: ops per AST node
/// (static and dispatched), allocations, `slow` share.
#[test]
#[ignore = "the harvester: run explicitly, with --nocapture"]
fn harvest_corpora() {
    perf::assert_counting();
    struct Stat {
        id: String,
        src: String,
        nodes: usize,
        sops: usize,
        prof: RunProfile,
    }
    let mut stats: Vec<Stat> = Vec::new();
    let env = support::gen::roster();
    for (i, (src, acts)) in support::gen::typed_batch(support::gen::SEEDS[0])
        .iter()
        .enumerate()
    {
        let program = env.compile(src, &CompileOpts::default()).expect("compiles");
        let fast = FastProgram::new(&program).expect("lowers");
        let nodes = perf::nodes(fork::expression_of(&program));
        for (j, binds) in acts.iter().enumerate() {
            let mut act = env.activation();
            for (n, v) in binds {
                act.bind(n, v).expect("binds");
            }
            let _ = fast.eval(&act);
            let (_, prof) = profile::measure(|| fast.eval(&act));
            stats.push(Stat {
                id: format!("typed {i}/{j}"),
                src: src.clone(),
                nodes,
                sops: fast.op_count(),
                prof,
            });
        }
    }
    let exclusions = Exclusions::load(&conformance_dir().join("EXCLUSIONS.toml")).expect("loads");
    let mut lane = 0usize;
    for case in corpus().cases() {
        if exclusions.reason_for(case).is_some()
            || harness::run::run(case) != harness::run::Outcome::Pass
        {
            continue;
        }
        let mut env = CelEnvironment::new();
        let mut binds = Vec::new();
        for (name, binding) in &case.bindings {
            let Binding::Value(v) = binding else {
                continue;
            };
            env.declare(name.clone(), harness::run::type_of(v).expect("typed"));
            binds.push((name.clone(), v.clone()));
        }
        let Ok(program) = fork::compile_any(&env, &case.expr) else {
            continue;
        };
        let fast = FastProgram::new(&program).expect("lowers");
        let mut act = env.activation();
        for (n, v) in &binds {
            act.bind_fact(n, harness::run::to_runtime(v).expect("representable"));
        }
        let _ = fork::fast_value(&fast, &act);
        let (_, prof) = profile::measure(|| fork::fast_value(&fast, &act));
        lane += 1;
        stats.push(Stat {
            id: format!("lane {}", case.unique_id()),
            src: case.expr.clone(),
            nodes: perf::nodes(fork::expression_of(&program)),
            sops: fast.op_count(),
            prof,
        });
    }
    println!(
        "\n==== corpora: {} typed runs, {lane} lane programs ====",
        stats.len() - lane
    );
    let show = |title: &str, key: &dyn Fn(&Stat) -> f64, stats: &mut Vec<Stat>| {
        stats.sort_by(|a, b| key(b).partial_cmp(&key(a)).unwrap());
        println!("\n-- top 12 by {title}");
        for s in stats.iter().take(12) {
            println!(
                "{:>8.2}  {:<28} nodes={:<4} sops={:<4} {}\n          `{}`",
                key(s),
                s.id,
                s.nodes,
                s.sops,
                s.prof.summary(),
                s.src.chars().take(200).collect::<String>()
            );
        }
    };
    show(
        "static ops per AST node",
        &|s| s.sops as f64 / s.nodes as f64,
        &mut stats,
    );
    show(
        "dispatched ops per AST node",
        &|s| s.prof.ops as f64 / s.nodes as f64,
        &mut stats,
    );
    show("allocations", &|s| s.prof.allocs as f64, &mut stats);
    show("store pushes", &|s| s.prof.store as f64, &mut stats);
    show(
        "slow share",
        &|s| s.prof.slow as f64 / s.prof.ops.max(1) as f64,
        &mut stats,
    );
    let mut slow_ops: BTreeMap<&str, u64> = BTreeMap::new();
    let mut all_ops: BTreeMap<&str, u64> = BTreeMap::new();
    for s in &stats {
        for (k, v) in &s.prof.slow_by_op {
            *slow_ops.entry(k).or_default() += v;
        }
        for (k, v) in &s.prof.by_op {
            *all_ops.entry(k).or_default() += v;
        }
    }
    println!("\n-- ops dispatched over both corpora (slow entries in parentheses)");
    let mut v: Vec<_> = all_ops.into_iter().collect();
    v.sort_by(|a, b| b.1.cmp(&a.1));
    for (k, n) in v {
        println!("{k:<14} {n:>8} ({})", slow_ops.get(k).copied().unwrap_or(0));
    }
}

/// A streamed run over a document whose demanded fields sit after an `n * 64`-byte string: what
/// the whole run costs (every push), by document size.
#[test]
#[ignore = "the harvester: run explicitly, with --nocapture"]
fn harvest_streamed() {
    use std::sync::Arc;
    perf::assert_counting();
    let mut env = CelEnvironment::new();
    env.declare("n", typed_cel::CelTy::Num);
    env.declare(
        "body",
        support::record(
            "body",
            &[
                ("pad", typed_cel::CelTy::Str),
                ("tier", typed_cel::CelTy::Str),
                ("amount", typed_cel::CelTy::Num),
            ],
        ),
    );
    let src = r#"body.tier == "gold" && body.amount < 100.0"#;
    let compiled = env.compile(src, &CompileOpts::default()).expect("compiles");
    let code = Arc::new(typed_cel::emit(&compiled).expect("emits"));
    let mut act = env.activation();
    act.bind("n", &serde_json::json!(3)).expect("binds");
    let program = typed_cel::StreamedProgram::new(
        Arc::new(typed_cel::Vm::new()),
        &env,
        &compiled,
        code,
        act,
        "body",
    )
    .expect("streams");
    println!("\n==== streamed `{src}` ====");
    for n in SCALE {
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
        println!(
            "n={n:<5} events={:<6} verdict={:?}\n    {}",
            evs.len(),
            verdict.is_ok(),
            prof.summary()
        );
    }
}

/// Median ns per decision for the worst finds, on this machine. Run with `--release` on the VM;
/// the numbers go into `docs/PERFORMANCE.md` and the cliffs' constants, never into an assertion.
#[test]
#[ignore = "timing spot check: run explicitly, --release, on the VM"]
fn spot_ns() {
    let env = perf::env();
    let cases: &[(&str, Leg, usize)] = &[
        // predicate loops (act), and the same shapes' per-element floor at n=10
        ("policy.names.exists(x, x == req.name)", Leg::Act, 1000),
        ("policy.names.exists(x, x == req.name)", Leg::Act, 10),
        ("policy.nums.all(x, x > req.n)", Leg::Act, 1000),
        ("policy.names.exists_one(x, x == req.name)", Leg::Act, 1000),
        ("policy.items.exists(i, i.id == req.name && i.qty > req.n)", Leg::Act, 1000),
        (r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#, Leg::Act, 1000),
        (r#"policy.roots.exists(r, req.path.startsWith(r + "/"))"#, Leg::Act, 1000),
        ("policy.m.all(k, policy.m[k] > req.n)", Leg::Act, 1000),
        // building
        ("size(policy.nums.map(x, x * 2.0)) > req.n", Leg::Act, 1000),
        ("size(policy.nums.filter(x, x > req.n)) > req.n", Leg::Act, 1000),
        ("size(policy.nums.map(x, x * 2.0)) > req.n", Leg::Act, 100),
        // nested, invariant inner loop
        ("policy.names.exists(x, x == req.name || policy.nums.exists(y, y < 0.0))", Leg::Act, 100),
        // errors discarded per element
        ("policy.items.exists(i, i.tags[5] == req.name || i.qty > 999.0)", Leg::SpecKnown, 1000),
        // known collections: past max_unroll, and unrolled
        ("policy.nums.all(x, x > req.n)", Leg::SpecKnown, 1000),
        ("policy.nums.all(x, x > req.n)", Leg::SpecKnown, 256),
        ("policy.nums.exists(x, x == req.n)", Leg::SpecKnown, 1000),
        ("policy.m.exists(k, k == req.name)", Leg::SpecKnown, 1000),
        ("policy.m.exists(k, k == req.name)", Leg::SpecKnown, 256),
        (r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#, Leg::SpecKnown, 1000),
        // scalar decisions over Facts
        (r#"req.path.startsWith(req.name + "/")"#, Leg::Facts, 1),
        ("req.path + req.name == req.other", Leg::Facts, 1),
        ("req.name in [req.path, req.other]", Leg::Facts, 1),
        ("req.name == req.path || req.name == req.other", Leg::Facts, 1),
        (r#"[req.name, req.path, req.other].exists(x, x == "zz")"#, Leg::Facts, 1),
        (r#"{"a": req.n, "b": 2.0}["a"] > 0.0"#, Leg::Facts, 1),
        ("req.n > 0.0", Leg::Facts, 1),
        ("req.n < 60.0 * 60.0 * 24.0", Leg::Facts, 1),
        ("req.n < 86400.0", Leg::Facts, 1),
        ("(true && !false) && req.flag", Leg::Facts, 1),
        ("req.flag", Leg::Facts, 1),
        ("has(req.opt) && req.flag && req.n < 10.0 && req.path.startsWith(req.name) == false && !(req.n > 5.0)", Leg::Facts, 1),
        ("req.n < 1000.0 && req.n < 1001.0 && req.n < 1002.0 && req.n < 1003.0 && req.n < 1004.0 && req.n < 1005.0 && req.n < 1006.0 && req.n < 1007.0 && req.n < 1008.0 && req.n < 1009.0 && req.n < 1010.0 && req.n < 1011.0 && req.n < 1012.0 && req.n < 1013.0 && req.n < 1014.0 && req.n < 1015.0", Leg::Facts, 1),
        ("req.n < 1000.0", Leg::Facts, 1),
    ];
    println!();
    for (src, leg, n) in cases {
        let (policy, req) = (perf::policy(*n), perf::req(*n));
        let p = perf::prepare(&env, src, *leg, &policy, &req).expect("the leg applies");
        let mut scratch = FastScratch::default();
        let mut per = Vec::new();
        for _ in 0..15 {
            let mut iters = 1u64;
            loop {
                let t = std::time::Instant::now();
                for _ in 0..iters {
                    std::hint::black_box(p.run(&mut scratch).ok());
                }
                let el = t.elapsed();
                if el.as_millis() >= 20 {
                    per.push(el.as_nanos() as f64 / iters as f64);
                    break;
                }
                iters *= 2;
            }
        }
        per.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!(
            "{:>12.1} ns  [{}] n={n:<5} {src}",
            per[per.len() / 2],
            leg.name()
        );
    }
}
