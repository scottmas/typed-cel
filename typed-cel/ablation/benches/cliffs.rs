//! Wall-clock and cycle spot checks for the cost-model cliffs `tests/perf_cliffs.rs` pins: one row
//! per pinned shape, median ns and cycles per decision, on a build WITHOUT the `profile` feature
//! (this crate is its own workspace, so nothing turns it on).
//!
//! The pins count; this measures what the counts cost. Nothing asserts on it.
//!
//! ```text
//! cd typed-cel/ablation && cargo bench --bench cliffs --no-run
//! B=$(ls -t target/release/deps/cliffs-* | grep -v "\.d$" | head -1)
//! taskset -c 1 $B
//! ```

#[path = "pmu.rs"]
mod pmu;
#[path = "rig.rs"]
mod rig;

use rig::{env, measure, prepare, Leg};

/// The rows: (pinning test, leg, n, program).
const ROWS: &[(&str, Leg, usize, &str)] = &[
    ("predicate_loop_ops_per_element", Leg::Act, 1000, "policy.names.exists(x, x == req.name)"),
    ("predicate_loop_ops_per_element", Leg::Act, 1000, "policy.nums.all(x, x > req.n)"),
    ("predicate_loop_ops_per_element", Leg::Act, 1000, "policy.names.exists_one(x, x == req.name)"),
    ("predicate_loop_ops_per_element", Leg::Act, 1000, "policy.items.exists(i, i.id == req.name && i.qty > req.n)"),
    ("prefix_of_concatenation", Leg::Act, 1000, r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#),
    ("prefix_of_concatenation", Leg::Act, 1000, r#"policy.roots.exists(r, req.path.startsWith(r + "/"))"#),
    ("prefix_of_concatenation", Leg::Facts, 1, r#"req.path.startsWith(req.name + "/")"#),
    ("prefix_of_concatenation", Leg::Facts, 1, "req.path + req.name == req.other"),
    ("loop_invariant_read", Leg::Act, 1000, "policy.m.all(k, policy.m[k] > req.n)"),
    ("map_filter_linear", Leg::Act, 100, "size(policy.nums.map(x, x * 2.0)) > req.n"),
    ("map_filter_linear", Leg::Act, 1000, "size(policy.nums.map(x, x * 2.0)) > req.n"),
    ("map_filter_linear", Leg::Act, 1000, "size(policy.nums.filter(x, x > req.n)) > req.n"),
    ("invariant_inner_loop", Leg::Act, 100, "policy.names.exists(x, x == req.name || policy.nums.exists(y, y < 0.0))"),
    ("discarded_errors", Leg::Spec, 1000, "policy.items.exists(i, i.tags[5] == req.name || i.qty > 999.0)"),
    ("discarded_errors", Leg::Spec, 1000, "policy.items.exists(i, i.qty > 999.0)"),
    ("known_membership", Leg::Spec, 256, "policy.m.exists(k, k == req.name)"),
    ("known_membership", Leg::Spec, 1000, "policy.m.exists(k, k == req.name)"),
    ("known_membership", Leg::Spec, 1000, "policy.nums.exists(x, x == req.n)"),
    ("known_membership", Leg::Spec, 1000, r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#),
    ("comparison_chain", Leg::Spec, 256, "policy.nums.all(x, x > req.n)"),
    ("comparison_chain", Leg::Spec, 1000, "policy.nums.all(x, x > req.n)"),
    ("comparison_chain", Leg::Facts, 1, "req.n < 1000.0 && req.n < 1001.0 && req.n < 1002.0 && req.n < 1003.0 && req.n < 1004.0 && req.n < 1005.0 && req.n < 1006.0 && req.n < 1007.0 && req.n < 1008.0 && req.n < 1009.0 && req.n < 1010.0 && req.n < 1011.0 && req.n < 1012.0 && req.n < 1013.0 && req.n < 1014.0 && req.n < 1015.0"),
    ("comparison_chain", Leg::Facts, 1, "req.n < 1000.0"),
    ("literal_collection", Leg::Facts, 1, "req.name in [req.path, req.other]"),
    ("literal_collection", Leg::Facts, 1, "req.name == req.path || req.name == req.other"),
    ("literal_collection", Leg::Facts, 1, r#"[req.name, req.path, req.other].exists(x, x == "zz")"#),
    ("literal_collection", Leg::Facts, 1, r#"{"a": req.n, "b": 2.0}["a"] > 0.0"#),
    ("literal_collection", Leg::Facts, 1, "req.n > 0.0"),
    ("constant_subtree", Leg::Facts, 1, "req.n < 60.0 * 60.0 * 24.0"),
    ("constant_subtree", Leg::Facts, 1, "req.n < 86400.0"),
    ("constant_subtree", Leg::Facts, 1, "(true && !false) && req.flag"),
    ("constant_subtree", Leg::Facts, 1, "req.flag"),
    ("out_of_line_ops", Leg::Facts, 1, "has(req.opt) && req.flag && req.n < 10.0 && req.path.startsWith(req.name) == false && !(req.n > 5.0)"),
    ("vm_eval_scratch", Leg::Act, 1, "policy.names.exists(x, x == req.name)"),
    ("vm_eval_scratch", Leg::Spec, 1, "policy.names.exists(x, x == req.name)"),
];

fn main() {
    let env = env();
    let ctr = pmu::Ctr::new();
    println!(
        "{:<32} {:<5} {:>5} {:>12} {:>10}  program",
        "pin", "leg", "n", "ns/decision", "cycles"
    );
    for (pin, leg, n, src) in ROWS {
        let mut row = prepare(&env, src, *leg, *n);
        let (ns, counts) = measure(&mut row, &ctr);
        let cycles = counts.map_or("-".to_string(), |c| format!("{:.0}", c[0]));
        let leg = match leg {
            Leg::Act => "act",
            Leg::Facts => "facts",
            Leg::Spec => "spec",
        };
        println!("{pin:<32} {leg:<5} {n:>5} {ns:>12.1} {cycles:>10}  {src}");
    }
}
