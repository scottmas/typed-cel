//! Demand extraction, as public API.
//!
//! The crate's most unusual export, and the one with no analogue in any other CEL implementation.
//! The inherited `Program::references()` is not it: it returns ROOTS only, so it cannot drive
//! demand-based population.

#[path = "support/mod.rs"]
mod support;

use typed_cel::CompileOpts;
use serde_json::json;
use support::env;
use typed_cel::{DemandSet, Segment};

/// `files ▸ "/a" ▸ "closed"` — the rendering the plan and the README both use.
fn render(path: &[Segment]) -> String {
    path.iter()
        .map(|s| match s {
            Segment::Root(r) => r.clone(),
            Segment::Key(k) => format!("{k:?}"),
            Segment::Wild => "*".to_string(),
        })
        .collect::<Vec<_>>()
        .join(" ▸ ")
}

fn paths(expr: &str) -> Vec<String> {
    let env = env();
    let program = env
        .compile(expr, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("{expr}: {e}"));
    program.demand().paths().map(render).collect()
}

fn demand(expr: &str) -> DemandSet {
    env()
        .compile(expr, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("{expr}: {e}"))
        .demand()
        .clone()
}

#[test]
fn a_literal_path_is_harvested() {
    // EXACTLY one path — not the four its spine passes through. A demand set full of prefixes
    // reads as "this policy watches the whole files map", which is the opposite of the claim.
    assert_eq!(
        paths("files[\"/a/b\"].closed.elapsed > 5s"),
        vec![r#"files ▸ "/a/b" ▸ "closed" ▸ "elapsed""#]
    );
    // And the inherited `references()` really is roots-only, which is why this exists at all.
    let program = env()
        .compile(
            "files[\"/a/b\"].closed.elapsed > 5s",
            &CompileOpts::default(),
        )
        .unwrap();
    assert_eq!(
        program.demand().roots().into_iter().collect::<Vec<_>>(),
        vec!["files"]
    );
}

#[test]
fn a_window_key_is_harvested() {
    assert_eq!(
        paths("uptime > 40s && metrics.cpu.max[\"40s\"] < 0.05"),
        vec![
            r#"metrics ▸ "cpu" ▸ "max" ▸ "40s""#.to_string(),
            "uptime".to_string(),
        ]
    );
}

/// A `Map<Str, Record{ avg: Map<Str, Num> }>` under a root named nothing like `metrics`, read
/// through an aggregate named nothing like `max`. The library reports the SHAPE; if it reported
/// only what one environment's vocabulary matched, this read would be invisible. Both maps are
/// `unsafe_map`, as a demand-filled system root is.
fn gauge_env() -> typed_cel::CelEnvironment {
    let mut e = typed_cel::CelEnvironment::new();
    e.declare(
        "gauges",
        typed_cel::CelTy::unsafe_map(
            typed_cel::CelTy::Str,
            support::record(
                "gauge",
                &[(
                    "avg",
                    typed_cel::CelTy::unsafe_map(typed_cel::CelTy::Str, typed_cel::CelTy::Num),
                )],
            ),
        ),
    );
    e
}

#[test]
fn an_aggregate_is_reported_without_naming_its_root() {
    let program = gauge_env()
        .compile(
            "gauges[\"cpu\"].avg[\"40s\"] > 1.0",
            &CompileOpts::default(),
        )
        .unwrap();
    let reads: Vec<(String, String, String, String)> = program
        .demand()
        .keyed_reads()
        .map(|(a, b, c, d)| (a.to_string(), b.to_string(), c.to_string(), d.to_string()))
        .collect();
    assert_eq!(
        reads,
        vec![(
            "gauges".to_string(),
            "cpu".to_string(),
            "avg".to_string(),
            "40s".to_string()
        )]
    );
}

#[test]
fn the_system_windows_are_still_derivable() {
    // What a host asks, expressed as a filter over the general result rather than as a rule
    // baked into the library.
    let set =
        demand("uptime > 40s && metrics.cpu.max[\"40s\"] < 0.05 && metrics.cpu.max[\"10s\"] < 0.9");
    let mut windows: std::collections::BTreeMap<String, Vec<String>> = Default::default();
    for (root, metric, agg, window) in set.keyed_reads() {
        if root == "metrics" && agg == "max" {
            let entry = windows.entry(metric.to_string()).or_default();
            if !entry.iter().any(|w| w == window) {
                entry.push(window.to_string());
            }
        }
    }
    assert_eq!(
        windows.get("cpu").map(Vec::as_slice),
        Some(&["10s".to_string(), "40s".to_string()][..])
    );
}

#[test]
fn a_two_segment_path_is_not_an_aggregate() {
    // A keyed read is `root ▸ key ▸ key ▸ key`. `metrics ▸ "cpu" ▸ "now"` is three segments — and
    // under the very root a host's filter cares about — so a shorter path must not be reported
    // as one, or that filter reads past the end of the path it was handed.
    assert_eq!(
        paths("metrics.cpu.now > 0.5"),
        vec![r#"metrics ▸ "cpu" ▸ "now""#.to_string()]
    );
    assert_eq!(demand("metrics.cpu.now > 0.5").keyed_reads().count(), 0);

    // A LONGER path still matches — a read may descend past an aggregate.
    let deep = demand("files[\"/a\"].closed.elapsed > 5s");
    let reads: Vec<_> = deep
        .keyed_reads()
        .map(|(a, b, c, d)| (a.to_string(), b.to_string(), c.to_string(), d.to_string()))
        .collect();
    assert_eq!(
        reads,
        vec![(
            "files".to_string(),
            "/a".to_string(),
            "closed".to_string(),
            "elapsed".to_string()
        )]
    );
}

#[test]
fn two_expressions_union() {
    let mut set = demand("files[\"/a\"].closed.count > 0");
    set.union(&demand("files[\"/b\"].opened.count > 0"));
    set.union(&demand("files[\"/a\"].closed.count > 0"));
    let rendered: Vec<String> = set.paths().map(render).collect();
    assert_eq!(
        rendered,
        vec![
            r#"files ▸ "/a" ▸ "closed" ▸ "count""#,
            r#"files ▸ "/b" ▸ "opened" ▸ "count""#,
        ]
    );
}

#[test]
fn a_non_literal_key_outside_a_comprehension_is_a_build_error() {
    // The tempting fallback is to widen the root and carry on, which turns ONE unreviewable
    // expression into "populate everything" for the whole policy, silently.
    let env = env();
    let rendered = env
        .compile(
            "body.documents.all(d, files[d.id].closed.count > 0)",
            &CompileOpts::default(),
        )
        .err()
        .expect("a computed key must be refused")
        .to_string();
    assert!(rendered.contains("computed key"), "{rendered}");
    assert!(
        rendered.contains("unknowable") || rendered.contains("write the key out"),
        "the message must say why and how to fix it:\n{rendered}"
    );
}

#[test]
fn a_comprehension_over_a_map_widens_that_root_to_all() {
    // The `listen(*)` case. Widening is legal ONLY where the comprehension proves the iteration is
    // over that same map.
    let set = demand("listeners.exists(p, listeners[p].listen.elapsed > 10s)");
    assert_eq!(
        set.wide_roots().collect::<Vec<_>>(),
        vec!["listeners"],
        "the root the comprehension iterates must be recorded as wide"
    );
}

#[test]
fn the_widened_root_still_records_its_leaf_fields() {
    // A wide root is NOT a licence to materialize whole entries: the leaf fields recorded under it
    // still bound what each entry must carry.
    let set = demand("listeners.exists(p, listeners[p].listen.elapsed > 10s)");
    let rendered: Vec<String> = set.paths().map(render).collect();
    assert_eq!(
        rendered,
        vec![r#"listeners ▸ * ▸ "listen" ▸ "elapsed""#],
        "only `listen.elapsed` is read under each listener"
    );
}

#[test]
fn an_http_demand_set_is_recorded_too() {
    // Harvesting is not system-only. The HTTP set is what the policy artifact stores for
    // auditability — "what does this policy read?" answered without running it.
    assert_eq!(
        paths("body.documents.all(d, d.owner_id == session.user_id)"),
        vec![
            r#"body ▸ "documents""#.to_string(),
            r#"session ▸ "user_id""#.to_string(),
        ]
    );
    assert_eq!(
        paths("headers['content-type'] == 'application/json'"),
        vec![r#"headers ▸ "content-type""#]
    );
}

#[test]
fn the_demand_set_serializes() {
    let set = demand("files[\"/a\"].closed.elapsed > 5s && uptime > 1h");
    let json = serde_json::to_string(&set).expect("a demand set round-trips with the artifact");
    let back: DemandSet = serde_json::from_str(&json).expect("and back");
    assert_eq!(back, set);
}

#[test]
fn the_demand_set_pre_populates_the_activation() {
    // THE test that keeps the system roots total — what their `unsafe_map` type promises. A demanded path exists in the activation
    // from load, zero-valued, so a file that was never touched reads `0` rather than erroring —
    // and a key NOTHING demanded still errors, so a typo cannot silently read as "never happened".
    let env = env();
    let named = env
        .compile("files[\"/a\"].closed.count > 0", &CompileOpts::default())
        .unwrap();
    let unnamed = env
        .compile("files[\"/b\"].closed.count > 0", &CompileOpts::default())
        .unwrap();

    // A host builds this from the union of every expression's demand set. Here: one key.
    let zero_event = json!({"elapsed": "0s", "count": 0.0});
    let state = json!({"/a": {"opened": zero_event, "closed": zero_event}});

    let mut activation = env.activation();
    activation.bind("files", &state).unwrap();

    assert_eq!(
        named.evaluate(&activation).ok(),
        Some(false),
        "a demanded path that never fired must read zero, not error"
    );
    assert!(
        unnamed.evaluate(&activation).is_err(),
        "a key outside the demand set must still error — that is what stops a typo reading as \
         `never happened`"
    );
    // Where that `Err` goes is the caller's.
}

#[test]
fn the_reverse_index_names_which_expressions_read_a_path() {
    // "Which grants does closing /a wake?" — the event-driven wake, so a close that matters
    // re-evaluates two grants rather than fifty.
    let a = demand("files[\"/a\"].closed.count > 0");
    let b = demand("files[\"/b\"].closed.count > 0");
    let c = demand("files[\"/a\"].closed.count > 0 && uptime > 1h");
    let sets = [("grant_a", &a), ("grant_b", &b), ("grant_c", &c)];
    let index = DemandSet::reverse_index(&sets);

    let key: Vec<Segment> = vec![
        Segment::Root("files".into()),
        Segment::Key("/a".into()),
        Segment::Key("closed".into()),
        Segment::Key("count".into()),
    ];
    assert_eq!(
        index.get(key.as_slice()).map(Vec::as_slice),
        Some(&["grant_a", "grant_c"][..])
    );
}

fn labels_env() -> typed_cel::CelEnvironment {
    use typed_cel::{CelTy, Record};
    let mut e = typed_cel::CelEnvironment::new();
    e.declare(
        "body",
        support::record(
            "body",
            &[
                ("labels", CelTy::map(CelTy::Str, CelTy::Str)),
                (
                    "extra",
                    Record::new("body.extra", [("fixed", CelTy::Str)])
                        .with_index(CelTy::Str, CelTy::Str)
                        .into(),
                ),
            ],
        ),
    );
    e.declare("k", CelTy::Str);
    e
}

fn labels_paths(expr: &str) -> (Vec<String>, Vec<String>) {
    let program = labels_env()
        .compile(expr, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("{expr}: {e}"));
    (
        program.demand().paths().map(render).collect(),
        program.demand().wide_roots().map(str::to_string).collect(),
    )
}

#[test]
fn a_presence_key_on_an_open_container_is_demand() {
    // `has(x.k)` on a record commits only the operand — its declared fields bound the question.
    // On a map, or a key only an index signature covers, nothing else names WHICH key is asked.
    for expr in ["has(body.labels.team)", r#""team" in body.labels"#] {
        let (paths, wide) = labels_paths(expr);
        assert_eq!(paths, [r#"body ▸ "labels" ▸ "team""#], "{expr}");
        assert!(wide.is_empty(), "{expr}: {wide:?}");
    }
    let (paths, _) = labels_paths("has(body.extra.k2)");
    assert_eq!(paths, [r#"body ▸ "extra" ▸ "k2""#]);
    // A DECLARED field of an index-signature record stays an operand-only question.
    let (paths, _) = labels_paths("has(body.extra.fixed)");
    assert_eq!(paths, [r#"body ▸ "extra""#]);
    // A key that is not a literal cannot be named at build: the container is demanded whole.
    let (paths, wide) = labels_paths("k in body.labels");
    assert!(
        paths.contains(&r#"body ▸ "labels" ▸ *"#.to_string()),
        "{paths:?}"
    );
    assert_eq!(wide, ["body"]);
}
