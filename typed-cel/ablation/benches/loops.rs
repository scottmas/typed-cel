//! What one more element costs an UNSPECIALIZED loop (`Vm::eval` over an activation), beside the
//! same loop written in Rust over the same data: ns, cycles and instructions per element, as the
//! slope between n = 10 and n = 1000. On a build WITHOUT the `profile` feature.
//!
//! `tests/perf_cliffs.rs` pins what a loop RUNS per element (ops, slow-path entries); this measures
//! what those cost. `--check` is the pin on the cost PER OP, which no debug-build counter sees: it
//! exits non-zero when a family's instructions per element exceed Rust's plus [`INS_PER_OP`] for
//! each op a good lowering runs per element (the budgets `tests/perf_cliffs.rs` holds). It needs
//! the PMU (a Hetzner cx33 has it) and fails loudly without it.
//!
//! ```text
//! cd typed-cel/ablation && cargo bench --bench loops --no-run
//! B=$(ls -t target/release/deps/loops-* | grep -v "\.d$" | head -1)
//! taskset -c 1 $B            # the table
//! taskset -c 1 $B --check    # the per-op instruction budget, red while it is over
//! ```

#[path = "pmu.rs"]
mod pmu;
#[path = "rig.rs"]
#[allow(dead_code)]
mod rig;

use std::collections::HashMap;

use rig::{env, measure, policy, prepare, req, Leg, Row};
use serde_json::Value as J;

/// The policy's collections as Rust holds them, for the baselines.
struct Native {
    roots: Vec<String>,
    names: Vec<String>,
    nums: Vec<f64>,
    items: Vec<(String, f64, Vec<String>)>,
    long: Vec<String>,
    keys: Vec<String>,
    m: HashMap<String, f64>,
    path: String,
    name: String,
    n: f64,
    re: regex::Regex,
}

fn native(n: usize) -> Native {
    let (p, r) = (policy(n), req());
    let strs = |v: &J| -> Vec<String> {
        v.as_array()
            .unwrap()
            .iter()
            .map(|s| s.as_str().unwrap().to_string())
            .collect()
    };
    let m: Vec<(String, f64)> = p["m"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(k, v)| (k.clone(), v.as_f64().unwrap()))
        .collect();
    Native {
        roots: strs(&p["roots"]),
        names: strs(&p["names"]),
        nums: p["nums"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_f64().unwrap())
            .collect(),
        items: p["items"]
            .as_array()
            .unwrap()
            .iter()
            .map(|i| {
                (
                    i["id"].as_str().unwrap().to_string(),
                    i["qty"].as_f64().unwrap(),
                    strs(&i["tags"]),
                )
            })
            .collect(),
        long: strs(&p["long"]),
        keys: m.iter().map(|(k, _)| k.clone()).collect(),
        m: m.into_iter().collect(),
        path: r["path"].as_str().unwrap().to_string(),
        name: r["name"].as_str().unwrap().to_string(),
        n: r["n"].as_f64().unwrap(),
        re: regex::Regex::new("^zz$").unwrap(),
    }
}

type Base = fn(&Native) -> bool;

/// What one dispatched op may cost, in instructions, over the work Rust does: fetch the op, jump to
/// its arm, read its operands out of registers, write or branch. A threaded interpreter with its
/// `pc` and register file in machine registers spends 5-8 on the fetch and jump, and a simple arm a dozen more.
const INS_PER_OP: f64 = 20.0;

/// The families: (label, program, the same decision in Rust, the steps per element a good
/// lowering runs). A predicate loop scans (`src/fast/scan.rs`): a skipped element costs one step
/// per test and per member it reads, as `in` costs one per element it compares. The nested loop is
/// its outer ops per element (4) plus one per inner element scanned (3); the loops that do not scan
/// — every element errors, is mapped, or is kept — count the ops `tests/perf_cliffs.rs` pins.
const FAMILIES: &[(&str, &str, Base, f64)] = &[
    (
        "list/str/eq",
        "policy.names.exists(x, x == req.name)",
        |d| d.names.iter().any(|x| *x == d.name),
        1.0,
    ),
    (
        "list/str/startsWith",
        "policy.roots.exists(r, req.path.startsWith(r))",
        |d| d.roots.iter().any(|r| d.path.starts_with(r.as_str())),
        1.0,
    ),
    (
        "list/num/all",
        "policy.nums.all(x, x > req.n)",
        |d| d.nums.iter().all(|x| *x > d.n),
        1.0,
    ),
    (
        "list/str/exists_one",
        "policy.names.exists_one(x, x == req.name)",
        |d| d.names.iter().filter(|x| **x == d.name).count() == 1,
        1.0,
    ),
    (
        "list/str/eq-or-prefix-concat",
        r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#,
        |d| {
            d.roots.iter().any(|r| {
                d.path == *r
                    || (d.path.starts_with(r.as_str()) && d.path[r.len()..].starts_with('/'))
            })
        },
        2.0,
    ),
    (
        "list/str/matches",
        r#"policy.names.exists(x, x.matches("^zz$"))"#,
        |d| d.names.iter().any(|x| d.re.is_match(x)),
        1.0,
    ),
    (
        "record/and",
        "policy.items.exists(i, i.id == req.name && i.qty > req.n)",
        |d| d.items.iter().any(|(id, q, _)| *id == d.name && *q > d.n),
        2.0,
    ),
    (
        "record/all",
        "policy.items.all(i, i.qty > req.n)",
        |d| d.items.iter().all(|(_, q, _)| *q > d.n),
        2.0,
    ),
    (
        "record/nested-exists",
        "policy.items.exists(i, i.tags.exists(t, t == req.name))",
        |d| {
            d.items
                .iter()
                .any(|(_, _, t)| t.iter().any(|t| *t == d.name))
        },
        7.0,
    ),
    (
        "record/absorbed-error",
        "policy.items.all(i, i.tags[5] == req.name || i.qty > 0.0)",
        |d| {
            d.items
                .iter()
                .all(|(_, q, t)| t.get(5).is_some_and(|t| *t == d.name) || *q > 0.0)
        },
        8.0,
    ),
    (
        "map/key-eq",
        "policy.m.exists(k, k == req.name)",
        |d| d.keys.iter().any(|k| *k == d.name),
        1.0,
    ),
    (
        "map/key-index",
        "policy.m.all(k, policy.m[k] > req.n)",
        |d| d.keys.iter().all(|k| d.m[k] > d.n),
        2.0,
    ),
    (
        "build/map-size",
        "size(policy.nums.map(x, x * 2.0)) > req.n",
        |d| (d.nums.iter().map(|x| x * 2.0).collect::<Vec<_>>().len() as f64) > d.n,
        4.0,
    ),
    (
        "build/filter-size",
        "size(policy.nums.filter(x, x > req.n)) > req.n",
        |d| {
            (d.nums
                .iter()
                .filter(|x| **x > d.n)
                .collect::<Vec<_>>()
                .len() as f64)
                > d.n
        },
        4.0,
    ),
    (
        "list/str/contains-field",
        "policy.names.exists(x, x.contains(req.name))",
        |d| d.names.iter().any(|x| x.contains(d.name.as_str())),
        1.0,
    ),
    (
        "list/str/contains-field-long",
        "policy.long.exists(x, x.contains(req.name))",
        |d| d.long.iter().any(|x| x.contains(d.name.as_str())),
        1.0,
    ),
    (
        "in/list/str",
        "req.name in policy.names",
        |d| d.names.contains(&d.name),
        1.0,
    ),
];

/// `LOOPS_UNFUSED=1`: every row lowered with its loops' scans off (`with_unfused_loops`) — the
/// same binary, for an A/B of what scanning buys each family.
fn act_row(env: &typed_cel::CelEnvironment, src: &str, n: usize) -> Row {
    if std::env::var_os("LOOPS_UNFUSED").is_some() {
        typed_cel::with_unfused_loops(|| prepare(env, src, Leg::Act, n))
    } else {
        prepare(env, src, Leg::Act, n)
    }
}

const LO: usize = 10;
const HI: usize = 1000;

fn native_row(n: usize, f: Base) -> Row {
    let d = native(n);
    Row {
        decide: Box::new(move || f(std::hint::black_box(&d))),
    }
}

fn main() {
    let env = env();
    // `LOOPS_PROFILE=<family>` spins that family's act row at n = 1000 for five seconds, for
    // `perf record` to sample and nothing else; with `LOOPS_PROFILE_NATIVE=1`, its Rust row.
    if let Ok(only) = std::env::var("LOOPS_PROFILE") {
        let (_, src, base, _) = FAMILIES
            .iter()
            .find(|(l, ..)| *l == only)
            .unwrap_or_else(|| panic!("no family {only}"));
        let mut row = if std::env::var_os("LOOPS_PROFILE_NATIVE").is_some() {
            native_row(HI, *base)
        } else {
            act_row(&env, src, HI)
        };
        let t = std::time::Instant::now();
        while t.elapsed().as_secs() < 5 {
            for _ in 0..1000 {
                std::hint::black_box((row.decide)());
            }
        }
        return;
    }
    let check = std::env::args().any(|a| a == "--check");
    let ctr = pmu::Ctr::new();
    if check && ctr.is_none() {
        eprintln!("--check needs the PMU (perf_event_open), and it is not readable here");
        std::process::exit(2);
    }
    let mut over = Vec::new();
    println!(
        "{:<30} {:>8} {:>8} {:>8} {:>8} | {:>7} {:>7} {:>7} | {:>6}",
        "family", "ns@10", "ns@1000", "ns/el", "rust/el", "cyc/el", "ins/el", "r.ins/el", "x rust"
    );
    let slope = |lo: (f64, Option<[f64; 4]>), hi: (f64, Option<[f64; 4]>)| {
        let per = |a: f64, b: f64| (b - a) / (HI - LO) as f64;
        let c = match (lo.1, hi.1) {
            (Some(a), Some(b)) => Some([per(a[0], b[0]), per(a[1], b[1])]),
            _ => None,
        };
        (lo.0, hi.0, per(lo.0, hi.0), c)
    };
    for (label, src, base, good_ops) in FAMILIES {
        let lo = measure(&mut act_row(&env, src, LO), &ctr);
        let hi = measure(&mut act_row(&env, src, HI), &ctr);
        let (a, b, el, c) = slope(lo, hi);
        let rlo = measure(&mut native_row(LO, *base), &ctr);
        let rhi = measure(&mut native_row(HI, *base), &ctr);
        let (_, _, rel, rc) = slope(rlo, rhi);
        let f =
            |x: Option<[f64; 2]>, i: usize| x.map_or("-".to_string(), |c| format!("{:.1}", c[i]));
        println!(
            "{label:<30} {a:>8.0} {b:>8.0} {el:>8.2} {rel:>8.2} | {:>7} {:>7} {:>7} | {:>6.1}",
            f(c, 0),
            f(c, 1),
            f(rc, 1),
            el / rel.max(0.01),
        );
        if let (Some(c), Some(r)) = (c, rc) {
            let budget = r[1] + INS_PER_OP * good_ops;
            if c[1] > budget {
                over.push(format!(
                    "{label}: {:.1} instructions per element, budget {budget:.1} (Rust {:.1} + \
                     {INS_PER_OP} x {good_ops} ops) — `{src}`",
                    c[1], r[1]
                ));
            }
        }
    }
    if check {
        if over.is_empty() {
            println!("\n--check: every family within its per-op instruction budget");
        } else {
            println!(
                "\n--check: {} famil(ies) over the per-op instruction budget:",
                over.len()
            );
            for o in &over {
                println!("  {o}");
            }
            std::process::exit(1);
        }
    }
}
