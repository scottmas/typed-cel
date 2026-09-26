//! A governed value: the demanded paths of a document that is still arriving.
//!
//! `GovernedShape` is built once from a program's demand, over the root's declared type, and is
//! where every refusal happens. `GovernedDoc` is fed one document's events, settles one cell per
//! demanded node, and is read through `LazyValue::poll_member` / `poll_has`. The reference for
//! every settled answer is `CelActivation::bind` of the whole document followed by a read.

#[path = "support/mod.rs"]
mod support;

use std::sync::Arc;

use support::events::{to_events, Ev};
use support::{record, record_opt};
use typed_cel::Event;
use typed_cel::{
    Access, CelEnvironment, CelError, CelTy, CelValue, GovernedDoc, GovernedShape, LazyValue,
    Presence, Record, GOVERNED_CELL_BYTES,
};

// ---- 21. compile-time: the shape is shared across flows, a doc rides one between threads ----
const _: () = {
    fn send<T: Send>() {}
    fn sync<T: Sync>() {}
    #[allow(dead_code)]
    fn all() {
        send::<GovernedDoc>();
        sync::<GovernedShape>();
        send::<GovernedShape>();
    }
};

// ------------------------------------------------------------------------------------------
// Helpers
// ------------------------------------------------------------------------------------------

fn env_of(body: CelTy) -> CelEnvironment {
    let mut e = CelEnvironment::new();
    e.declare("body", body);
    e
}

fn shape_of(env: &CelEnvironment, src: &str) -> Result<GovernedShape, CelError> {
    let program = env.compile(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    GovernedShape::build("body", env.types().get("body").unwrap(), program.demand())
}

fn doc_of(env: &CelEnvironment, src: &str) -> GovernedDoc {
    GovernedDoc::new(Arc::new(shape_of(env, src).expect("the shape builds")))
}

fn root(doc: &GovernedDoc) -> Arc<dyn LazyValue> {
    match doc.value() {
        CelValue::Lazy(v) => v,
        other => panic!("the root is a view, not {other:?}"),
    }
}

fn feed(doc: &GovernedDoc, evs: &[Ev]) {
    for e in evs {
        doc.push(e.as_event());
    }
}

fn pending(a: Result<Access, CelError>) -> bool {
    matches!(a, Ok(Access::Pending(_)))
}

fn ready_str(a: Result<Access, CelError>) -> String {
    match a {
        Ok(Access::Ready(CelValue::Str(s))) => s.to_string(),
        other => panic!("expected a settled string, got {other:?}"),
    }
}

fn ready_view(a: Result<Access, CelError>) -> Arc<dyn LazyValue> {
    match a {
        Ok(Access::Ready(CelValue::Lazy(v))) => v,
        other => panic!("expected a settled view, got {other:?}"),
    }
}

fn bind_message(a: Result<Access, CelError>) -> String {
    match a {
        Err(CelError::Bind { message }) => message,
        other => panic!("expected a bind error, got {other:?}"),
    }
}

fn build_message(r: Result<GovernedShape, CelError>) -> String {
    match r {
        Err(CelError::Bind { message }) => message,
        other => panic!("expected a build refusal, got {other:?}"),
    }
}

/// The whole-document reference: `bind` refuses with this text.
fn whole_bind_error(env: &CelEnvironment, json: &str) -> String {
    let v: serde_json::Value = serde_json::from_str(json).unwrap();
    match env.activation().bind("body", &v) {
        Err(CelError::Bind { message }) => message,
        Err(other) => panic!("expected a bind error, got {other}"),
        Ok(_) => panic!("{json} binds"),
    }
}

fn name_env() -> CelEnvironment {
    env_of(record_opt(
        "body",
        &[
            ("name", CelTy::Str),
            ("amount", CelTy::Num),
            ("note", CelTy::Str),
        ],
        &["note", "amount"],
    ))
}

// ------------------------------------------------------------------------------------------
// Rows
// ------------------------------------------------------------------------------------------

#[test]
fn a_string_settles_at_its_end_and_not_before() {
    let env = name_env();
    let doc = doc_of(&env, r#"body.name == "ab""#);
    let evs = to_events(r#"{"name":"ab"}"#, 1);
    let first_text = evs.iter().position(|e| *e == Ev::Text("a".into())).unwrap();
    feed(&doc, &evs[..=first_text]);
    let v = root(&doc);
    assert!(pending(v.poll_member("name")), "a prefix never settles");
    let end = evs.iter().position(|e| *e == Ev::EndString).unwrap();
    feed(&doc, &evs[first_text + 1..end]);
    assert!(pending(v.poll_member("name")), "still no EndString");
    feed(&doc, &evs[end..=end]);
    assert_eq!(ready_str(v.poll_member("name")), "ab");
}

#[test]
fn a_number_settles_on_its_token() {
    let env = name_env();
    let doc = doc_of(&env, "body.amount > 1.0");
    let evs = to_events(r#"{"amount":12.5}"#, 1);
    let num = evs.iter().position(|e| matches!(e, Ev::Number(_))).unwrap();
    feed(&doc, &evs[..num]);
    assert!(pending(root(&doc).poll_member("amount")));
    feed(&doc, &evs[num..=num]);
    match root(&doc).poll_member("amount") {
        Ok(Access::Ready(CelValue::Num(n))) => assert_eq!(n, 12.5),
        other => panic!("{other:?}"),
    }
}

#[test]
fn an_absent_optional_is_no_such_member_at_the_objects_close() {
    let env = name_env();
    let doc = doc_of(&env, r#"body.note == "x""#);
    let evs = to_events("{}", 1);
    feed(&doc, &evs[..1]);
    assert!(pending(root(&doc).poll_member("note")));
    feed(&doc, &evs[1..]);
    match root(&doc).poll_member("note") {
        Err(CelError::NoSuchMember { key }) => assert_eq!(key, "note"),
        other => panic!("{other:?}"),
    }
}

#[test]
fn an_absent_required_field_is_the_bind_error() {
    let env = name_env();
    let doc = doc_of(&env, r#"body.name == "x""#);
    let evs = to_events("{}", 1);
    feed(&doc, &evs[..1]);
    assert!(pending(root(&doc).poll_member("name")));
    feed(&doc, &evs[1..]);
    let m = bind_message(root(&doc).poll_member("name"));
    assert!(
        m.contains("required by the schema, absent from the value"),
        "{m}"
    );
    assert!(m.contains("body.name"), "{m}");
    // The whole-document reference words it identically.
    assert_eq!(m, whole_bind_error(&env, "{}"));
}

#[test]
fn a_mismatched_leaf_is_the_bind_error_bind_gives() {
    let env = name_env();
    let doc = doc_of(&env, "body.amount > 1.0");
    let json = r#"{"name":"n","amount":"x"}"#;
    feed(&doc, &to_events(json, 1));
    let streamed = bind_message(root(&doc).poll_member("amount"));
    let whole = whole_bind_error(&env, json);
    let needle = "schema says double, value is a string";
    assert!(streamed.contains(needle), "{streamed}");
    assert!(whole.contains(needle), "{whole}");
    assert_eq!(streamed, whole);
}

#[test]
fn presence_is_known_at_the_key() {
    let env = name_env();
    let doc = doc_of(&env, r#"has(body.note) && body.note == "x""#);
    let big = "n".repeat(64 * 1024);
    let evs = to_events(&format!(r#"{{"note":"{big}"}}"#), 1024);
    let end_key = evs.iter().position(|e| *e == Ev::EndKey).unwrap();
    feed(&doc, &evs[..=end_key]);
    let v = root(&doc);
    assert_eq!(v.poll_has("note").unwrap(), Presence::Known(true));
    assert!(pending(v.poll_member("note")));
    feed(&doc, &evs[end_key + 1..end_key + 4]);
    assert_eq!(v.poll_has("note").unwrap(), Presence::Known(true));
    assert!(pending(v.poll_member("note")));
}

#[test]
fn presence_is_false_at_the_objects_close() {
    let env = name_env();
    let doc = doc_of(&env, r#"body.name == "a" && has(body.note)"#);
    let evs = to_events(r#"{"name":"a"}"#, 1);
    let v = root(&doc);
    for (i, e) in evs.iter().enumerate() {
        if i + 1 < evs.len() {
            doc.push(e.as_event());
            assert!(
                matches!(v.poll_has("note").unwrap(), Presence::Pending(_)),
                "decided before the close, after {e:?}"
            );
        }
    }
    doc.push(evs.last().unwrap().as_event());
    assert_eq!(v.poll_has("note").unwrap(), Presence::Known(false));
    assert_eq!(v.poll_has("name").unwrap(), Presence::Known(true));
    // A field the record does not declare: answered at once, never pending.
    let fresh = doc_of(&env, r#"body.name == "a""#);
    assert_eq!(
        root(&fresh).poll_has("nope").unwrap(),
        Presence::Known(false)
    );
}

#[test]
fn an_undemanded_member_holds_nothing() {
    let env = env_of(record_opt(
        "body",
        &[
            ("big", CelTy::Str),
            ("deep", CelTy::Dyn),
            ("name", CelTy::Str),
        ],
        &["big", "deep"],
    ));
    let big = "b".repeat(1024 * 1024);
    let huge_key = "k".repeat(1024 * 1024);
    for json in [
        format!(r#"{{"big":"{big}","deep":{{"a":[1,[2,{{"b":3}}]]}},"name":"x"}}"#),
        format!(r#"{{"{huge_key}":1,"name":"x"}}"#),
    ] {
        let doc = doc_of(&env, r#"body.name == "x""#);
        let mut most = doc.state_bytes();
        for e in to_events(&json, 1024) {
            doc.push(e.as_event());
            most = most.max(doc.state_bytes());
        }
        assert!(most <= 1024, "held {most} bytes for an undemanded member");
        assert_eq!(ready_str(root(&doc).poll_member("name")), "x");
    }
}

#[test]
fn a_duplicate_key_keeps_the_first_value() {
    let env = name_env();
    let doc = doc_of(&env, r#"body.name == "a""#);
    feed(&doc, &to_events(r#"{"name":"a","name":"b"}"#, 1));
    for _ in 0..3 {
        assert_eq!(ready_str(root(&doc).poll_member("name")), "a");
    }
}

#[test]
fn settled_cells_never_change_and_generation_counts_settles() {
    let env = name_env();
    let doc = doc_of(
        &env,
        r#"body.name == "ab" && body.amount == 3.0 && has(body.note)"#,
    );
    let evs = to_events(r#"{"name":"ab","amount":3,"note":"z"}"#, 8);
    // 0 BeginObject (the root view settles), 3 EndKey name (presence), 6 EndString (name),
    // 9 EndKey amount (presence), 10 Number (amount), 13 EndKey note (presence; `note` itself is
    // not demanded, so its EndString settles nothing), 17 EndObject (the object's presence closes).
    let settling = [0usize, 3, 6, 9, 10, 13, 17];
    assert_eq!(evs.len(), 18, "{evs:?}");
    let v = root(&doc);
    let mut name_seen: Option<String> = None;
    let mut before = doc.generation();
    for (i, e) in evs.iter().enumerate() {
        doc.push(e.as_event());
        let after = doc.generation();
        if settling.contains(&i) {
            assert!(
                after > before,
                "event {i} ({e:?}) settled but generation stayed"
            );
        } else {
            assert_eq!(
                after, before,
                "event {i} ({e:?}) settled nothing but moved generation"
            );
        }
        before = after;
        if let Ok(Access::Ready(CelValue::Str(s))) = v.poll_member("name") {
            let s = s.to_string();
            if let Some(prev) = &name_seen {
                assert_eq!(prev, &s, "a settled cell changed");
            }
            name_seen = Some(s);
        }
    }
    assert_eq!(name_seen.as_deref(), Some("ab"));
    assert_eq!(ready_str(v.poll_member("name")), "ab");
    match v.poll_member("amount") {
        Ok(Access::Ready(CelValue::Num(n))) => assert_eq!(n, 3.0),
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_demanded_string_past_the_cap_is_capped_never_truncated() {
    assert_eq!(GOVERNED_CELL_BYTES, 64 * 1024);
    let env = name_env();
    let program = env.compile(r#"body.name == "x""#).unwrap();
    let shape = GovernedShape::build("body", env.types().get("body").unwrap(), program.demand())
        .unwrap()
        .with_cell_cap(16);
    let doc = GovernedDoc::new(Arc::new(shape));
    let seventeen = "s".repeat(17);
    feed(&doc, &to_events(&format!(r#"{{"name":"{seventeen}"}}"#), 4));
    assert_eq!(doc.capped(), Some("cel.governed_cell_bytes"));
    assert!(
        pending(root(&doc).poll_member("name")),
        "a capped cell never reads as a truncated string"
    );
    // Exactly at the cap is not past it.
    let doc = GovernedDoc::new(Arc::new(
        shape_of(&env, r#"body.name == "x""#)
            .unwrap()
            .with_cell_cap(16),
    ));
    feed(
        &doc,
        &to_events(&format!(r#"{{"name":"{}"}}"#, "s".repeat(16)), 4),
    );
    assert_eq!(doc.capped(), None);
    assert_eq!(ready_str(root(&doc).poll_member("name")).len(), 16);
}

#[test]
fn a_number_too_long_caps() {
    let env = name_env();
    let doc = doc_of(&env, "body.amount > 1.0");
    feed(
        &doc,
        &[
            Ev::BeginObject,
            Ev::BeginKey,
            Ev::KeyText("amount".into()),
            Ev::EndKey,
            Ev::NumberTooLong,
        ],
    );
    assert_eq!(doc.capped(), Some("cel.number_too_long"));
    assert!(pending(root(&doc).poll_member("amount")));
}

#[test]
fn nested_records_settle_through_views() {
    let env = support::env();
    let src = r#"body.project.owner.id == "u1""#;
    let doc = doc_of(&env, src);
    feed(&doc, &to_events(r#"{"project":{"owner":{"id":"u1"}}}"#, 1));
    let project = ready_view(root(&doc).poll_member("project"));
    let owner = ready_view(project.poll_member("owner"));
    assert_eq!(ready_str(owner.poll_member("id")), "u1");

    let doc = doc_of(&env, src);
    feed(&doc, &to_events(r#"{"project":{}}"#, 1));
    let project = ready_view(root(&doc).poll_member("project"));
    let m = bind_message(project.poll_member("owner"));
    assert!(
        m.contains("required by the schema, absent from the value")
            && m.contains("body.project.owner"),
        "{m}"
    );
}

#[test]
fn a_map_key_is_tracked_by_its_literal() {
    let env = env_of(record(
        "body",
        &[("labels", CelTy::map(CelTy::Str, CelTy::Str))],
    ));
    let src = r#"body.labels["team"] == "x""#;
    let doc = doc_of(&env, src);
    feed(&doc, &to_events(r#"{"labels":{"a":"1","team":"x"}}"#, 1));
    let labels = ready_view(root(&doc).poll_member("labels"));
    assert_eq!(ready_str(labels.poll_member("team")), "x");
    assert_eq!(labels.poll_has("team").unwrap(), Presence::Known(true));

    let doc = doc_of(&env, src);
    feed(&doc, &to_events(r#"{"labels":{}}"#, 1));
    let labels = ready_view(root(&doc).poll_member("labels"));
    match labels.poll_member("team") {
        Err(CelError::NoSuchMember { key }) => assert_eq!(key, "team"),
        other => panic!("{other:?}"),
    }
    assert_eq!(labels.poll_has("team").unwrap(), Presence::Known(false));
}

#[test]
fn an_index_signature_field_settles() {
    let extra: CelTy = Record::new("body.extra", [("fixed", CelTy::Str)])
        .with_index(CelTy::Str, CelTy::Str)
        .into();
    let env = env_of(record("body", &[("extra", extra)]));
    let doc = doc_of(&env, r#"body.extra["k"] == "v""#);
    feed(&doc, &to_events(r#"{"extra":{"fixed":"a","k":"v"}}"#, 1));
    let extra = ready_view(root(&doc).poll_member("extra"));
    assert_eq!(ready_str(extra.poll_member("k")), "v");
}

#[test]
fn wide_roots_and_wild_paths_are_refused_at_build() {
    let env = support::env();
    for (src, path) in [
        (r#"body.tags.exists(t, t == "x")"#, "body.tags"),
        (r#"body.items.all(i, i.id != "")"#, "body.items"),
    ] {
        let m = build_message(shape_of(&env, src));
        assert!(m.contains(path), "{src}: {m}");
        assert!(m.contains("settles named paths only"), "{src}: {m}");
    }
    // A comprehension that indexes a map by its own iteration variable: a `Wild` path and a wide
    // root, refused naming the container the iteration covers.
    let env = env_of(record(
        "body",
        &[("labels", CelTy::map(CelTy::Str, CelTy::Str))],
    ));
    let src = r#"body.labels.exists(k, body.labels[k] == "x")"#;
    let program = env.compile(src).unwrap();
    assert!(
        program.demand().wide_roots().any(|r| r == "body"),
        "{}",
        program.demand()
    );
    let m = build_message(shape_of(&env, src));
    assert!(
        m.contains("`body.labels`") && m.contains("settles named paths only"),
        "{m}"
    );
}

#[test]
fn non_settleable_types_are_refused_at_build() {
    let env = env_of(record_opt(
        "body",
        &[
            ("tags", CelTy::list(CelTy::Str)),
            ("raw", CelTy::Bytes),
            ("nothing", CelTy::Null),
            ("blob", CelTy::Dyn),
            ("byNum", CelTy::map(CelTy::Num, CelTy::Str)),
        ],
        &["tags", "raw", "nothing", "blob", "byNum"],
    ));
    // A `dyn` member never reaches a shape: `compile` refuses every use of one but `has()`
    // (`removed: dyn values`).
    assert!(env.compile("body.blob == null").is_err());
    for (src, path, ty) in [
        ("size(body.tags) > 0", "body.tags", "list(string)"),
        (r#"body.raw == b"x""#, "body.raw", "bytes"),
        ("body.nothing == null", "body.nothing", "null_type"),
        (
            r#"body.byNum.x == "a""#,
            "body.byNum",
            "map(double, string)",
        ),
    ] {
        let m = build_message(shape_of(&env, src));
        assert!(m.contains(path) && m.contains(ty), "{src}: {m}");
    }
}

#[test]
fn end_settles_every_open_cell() {
    let env = name_env();
    let doc = doc_of(
        &env,
        r#"body.name == "a" && body.amount > 1.0 && has(body.note)"#,
    );
    feed(
        &doc,
        &[
            Ev::BeginObject,
            Ev::BeginKey,
            Ev::KeyText("name".into()),
            Ev::EndKey,
            Ev::BeginString,
            Ev::Text("a".into()),
        ],
    );
    let v = root(&doc);
    assert!(pending(v.poll_member("name")));
    doc.end();
    for field in ["name", "amount"] {
        let m = bind_message(v.poll_member(field));
        assert!(m.contains("the document ended before"), "{field}: {m}");
    }
    assert_eq!(v.poll_has("note").unwrap(), Presence::Known(false));
    assert_eq!(v.poll_has("name").unwrap(), Presence::Known(true));
    // Nothing moves after the end.
    let g = doc.generation();
    doc.push(Event::EndString);
    doc.push(Event::EndObject);
    assert_eq!(doc.generation(), g);
    assert!(bind_message(v.poll_member("name")).contains("the document ended before"));
}

#[test]
fn a_root_of_the_wrong_shape_fails_every_cell() {
    let env = name_env();
    for json in ["[1]", r#""x""#] {
        let doc = doc_of(&env, r#"body.name == "a" && body.amount > 1.0"#);
        feed(&doc, &to_events(json, 1));
        let whole = whole_bind_error(&env, json);
        assert!(whole.contains("schema says body, value is"), "{whole}");
        let v = root(&doc);
        for field in ["name", "amount"] {
            assert_eq!(bind_message(v.poll_member(field)), whole, "{json} {field}");
        }
        match v.poll_has("name") {
            Err(CelError::Bind { message }) => assert_eq!(message, whole),
            other => panic!("{json}: presence under a failed root is {other:?}"),
        }
    }
}

#[test]
fn other_roots_are_ignored() {
    let mut env = name_env();
    env.declare("n", CelTy::Num);
    let shape = shape_of(&env, r#"body.name == "a" && n > 1.0"#).unwrap();
    let paths: Vec<&str> = shape.paths().collect();
    assert_eq!(paths, ["body", "body.name"]);
}

#[test]
fn shape_and_doc_are_thread_safe() {
    // The assertion is the `const` block at the top of the file. This test names it, and moves a
    // doc across a thread for good measure.
    let env = name_env();
    let doc = doc_of(&env, r#"body.name == "a""#);
    let moved = doc.clone();
    std::thread::spawn(move || feed(&moved, &to_events(r#"{"name":"a"}"#, 1)))
        .join()
        .unwrap();
    assert_eq!(ready_str(root(&doc).poll_member("name")), "a");
}

fn labels_env() -> CelEnvironment {
    let extra: CelTy = Record::new("body.extra", [("fixed", CelTy::Str)])
        .with_index(CelTy::Str, CelTy::Str)
        .into();
    let mut env = env_of(record(
        "body",
        &[
            ("labels", CelTy::map(CelTy::Str, CelTy::Str)),
            ("extra", extra),
        ],
    ));
    env.declare("k", CelTy::Str);
    env
}

#[test]
fn has_on_a_map_key_settles_at_the_key() {
    let env = labels_env();
    for (src, container, key) in [
        ("has(body.labels.team)", "labels", "team"),
        ("has(body.extra.k2)", "extra", "k2"),
    ] {
        let doc = doc_of(&env, src);
        let long = "v".repeat(4096);
        let evs = to_events(
            &format!(r#"{{"{container}":{{"other":"1","{key}":"{long}"}}}}"#),
            512,
        );
        let end_key = evs
            .iter()
            .rposition(|e| *e == Ev::EndKey)
            .expect("the demanded key is the last key");
        feed(&doc, &evs[..end_key]);
        let view = ready_view(root(&doc).poll_member(container));
        assert!(
            matches!(view.poll_has(key).unwrap(), Presence::Pending(_)),
            "{src}: decided before the key"
        );
        feed(&doc, &evs[end_key..=end_key]);
        assert_eq!(view.poll_has(key).unwrap(), Presence::Known(true), "{src}");
        // The key answered before its value arrived.
        assert!(pending(view.poll_member(key)), "{src}");
    }
}

#[test]
fn in_on_a_map_key_settles_at_the_close_when_absent() {
    let env = labels_env();
    let doc = doc_of(&env, r#""team" in body.labels"#);
    let evs = to_events(r#"{"labels":{"a":"1","b":"2"}}"#, 1);
    let close = evs.len() - 2; // the labels object's EndObject
    assert_eq!(evs[close], Ev::EndObject);
    feed(&doc, &evs[..close]);
    let labels = ready_view(root(&doc).poll_member("labels"));
    assert!(matches!(
        labels.poll_has("team").unwrap(),
        Presence::Pending(_)
    ));
    feed(&doc, &evs[close..]);
    assert_eq!(labels.poll_has("team").unwrap(), Presence::Known(false));
    // And agrees with the whole document, bound and evaluated.
    let program = env.compile(r#""team" in body.labels"#).unwrap();
    let mut act = env.activation();
    act.bind(
        "body",
        &serde_json::json!({"labels": {"a": "1", "b": "2"}, "extra": {"fixed": "x"}}),
    )
    .unwrap();
    assert!(!program.evaluate(&act).unwrap());
}

#[test]
fn a_non_literal_key_is_refused_at_shape_build() {
    let env = labels_env();
    let src = "k in body.labels";
    let program = env.compile(src).unwrap();
    assert!(
        program.demand().wide_roots().any(|r| r == "body"),
        "{}",
        program.demand()
    );
    let m = build_message(shape_of(&env, src));
    assert!(
        m.contains("`body.labels`") && m.contains("settles named paths only"),
        "{m}"
    );
}

/// A streamed run's per-event path takes NO lock. The run OWNS its
/// document (`doc: Doc`, by value) and feeds it through `&mut`; the `Mutex` lives only in the
/// shared `GovernedDoc` the evaluator binds as a `LazyValue`, which is not on that path. Two
/// uncontended locks per token (`push` and `generation`) were the whole floor of a sparse body
/// check.
///
/// A source pin: every item on the path — the run, the owned document, the state both feed — is
/// read out of `src/governed.rs` and must not name a lock or the shared document.
#[test]
fn a_governed_push_takes_no_lock() {
    let src = include_str!("../src/governed.rs");
    let code: String = src
        .lines()
        .map(|l| l.split("//").next().unwrap_or(""))
        .collect::<Vec<_>>()
        .join("\n");
    let run = item(&code, "pub struct StreamedRun {");
    assert!(
        run.contains("doc: Doc,"),
        "a streamed run holds its document by value:\n{run}"
    );
    for head in [
        "pub struct StreamedRun {",
        "impl StreamedRun {",
        "struct Doc {",
        "impl Doc {",
        "struct DocState {",
        "impl DocState {",
    ] {
        let body = item(&code, head);
        for banned in ["Mutex", "lock(", "GovernedDoc", "DocInner", "RefCell"] {
            assert!(
                !body.contains(banned),
                "`{head}` names `{banned}`: the per-event path takes a lock\n{body}"
            );
        }
    }
}

/// The text of the item that opens with `head` (at the start of a line), through its matching
/// close brace.
fn item<'s>(code: &'s str, head: &str) -> &'s str {
    let at = code
        .match_indices(head)
        .map(|(i, _)| i)
        .find(|&i| i == 0 || code.as_bytes()[i - 1] == b'\n')
        .unwrap_or_else(|| panic!("`{head}` is not an item of src/governed.rs"));
    let mut depth = 0usize;
    for (i, c) in code[at..].char_indices() {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return &code[at..at + i + 1];
                }
            }
            _ => {}
        }
    }
    panic!("`{head}` never closes")
}

/// A streamed duration settles at the precision `duration()` parses: `1500ns` is 1500
/// nanoseconds, never rounded to whole milliseconds.
#[test]
fn a_streamed_duration_keeps_nanoseconds() {
    let env = env_of(record("body", &[("d", CelTy::Duration)]));
    let doc = doc_of(&env, "body.d > duration('1us')");
    feed(&doc, &to_events(r#"{"d": "1500ns"}"#, 64));
    doc.end();
    match root(&doc).poll_member("d") {
        Ok(Access::Ready(CelValue::Duration(d))) => assert_eq!(d.as_nanos(), Some(1500)),
        other => panic!("expected a settled duration, got {other:?}"),
    }
}
