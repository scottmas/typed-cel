//! `CelTy::admits` — the witness function the soundness law is written against.
//!
//! A derived type is a CLAIM about which values can appear at a position. `admits` is what makes
//! that claim falsifiable: for every value a schema definition ACCEPTS, the type derived from that
//! definition must admit it.

use std::collections::BTreeSet;
use std::rc::Rc;

use serde_json::json;
use typed_cel::{CelTy, Record, Relax};

fn record(fields: Vec<(&str, CelTy)>, optional: &[&str]) -> CelTy {
    CelTy::Record(Rc::new(Record {
        fields: fields
            .into_iter()
            .map(|(name, t)| (name.to_string(), t))
            .collect(),
        optional: optional
            .iter()
            .map(|s| s.to_string())
            .collect::<BTreeSet<_>>(),
        index: None,
        origin: "body".into(),
    }))
}

#[test]
fn scalars_admit_their_own_domain() {
    let pool = [
        json!("a"),
        json!(1),
        json!(true),
        json!(null),
        json!([]),
        json!({}),
    ];
    for (ty, mine) in [
        (CelTy::Str, json!("a")),
        (CelTy::Num, json!(1)),
        (CelTy::Bool, json!(true)),
        (CelTy::Null, json!(null)),
    ] {
        for v in &pool {
            assert_eq!(ty.admits(v), *v == mine, "{}.admits({v})", ty.name());
        }
    }
}

#[test]
fn num_admits_every_json_number() {
    // ONE numeric type: an integer and a float are the same question.
    for v in [json!(0), json!(-1), json!(1.5), json!(1e300), json!(-0.0)] {
        assert!(CelTy::Num.admits(&v), "Num must admit {v}");
    }
}

#[test]
fn dyn_admits_everything() {
    // This test is the reason precision exists: `Dyn` passes soundness for free, so soundness
    // alone can never detect a type that has widened.
    for v in [
        json!(null),
        json!(true),
        json!(0),
        json!("x"),
        json!([1, "a"]),
        json!({"a": {"b": []}}),
    ] {
        assert!(CelTy::Dyn.admits(&v), "Dyn must admit {v}");
    }
}

#[test]
fn a_list_admits_by_element() {
    let t = CelTy::list(CelTy::Str);
    assert!(t.admits(&json!(["a"])));
    // An EMPTY list is admitted by every list type.
    assert!(t.admits(&json!([])));
    assert!(!t.admits(&json!([1])));
    assert!(!t.admits(&json!({})));
}

#[test]
fn a_map_admits_by_value() {
    let t = CelTy::map(CelTy::Str, CelTy::Num);
    assert!(t.admits(&json!({"a": 1})));
    assert!(t.admits(&json!({})));
    assert!(!t.admits(&json!({"a": "x"})));
}

#[test]
fn a_record_admits_when_every_required_field_is_present_and_typed() {
    let t = record(
        vec![("user_id", CelTy::Str), ("roles", CelTy::list(CelTy::Str))],
        &[],
    );
    assert!(t.admits(&json!({"user_id": "u", "roles": []})));
    assert!(!t.admits(&json!({"user_id": 1, "roles": []})));
    assert!(!t.admits(&json!({"roles": []})));
}

#[test]
fn a_record_tolerates_an_absent_optional_field() {
    let t = record(vec![("a", CelTy::Str), ("b", CelTy::Num)], &["b"]);
    assert!(t.admits(&json!({"a": "x"})));
    // Present but wrong type is still a rejection — optionality is about PRESENCE.
    assert!(!t.admits(&json!({"a": "x", "b": "no"})));
    assert!(t.admits(&json!({"a": "x", "b": 1})));
}

#[test]
fn a_record_tolerates_an_undeclared_field() {
    // `admits` answers "could this value appear here", not "does the schema accept it".
    // the schema validator decides the latter and already ran.
    let t = record(vec![("a", CelTy::Str)], &[]);
    assert!(t.admits(&json!({"a": "x", "extra": 9})));
}

#[test]
fn bytes_admits_nothing_json_can_carry() {
    for v in [json!(null), json!("x"), json!(0), json!([]), json!({})] {
        assert!(!CelTy::Bytes.admits(&v), "Bytes must not admit {v}");
    }
}

#[test]
fn duration_admits_nothing_json_can_carry() {
    for v in [json!(null), json!("1s"), json!(0), json!([]), json!({})] {
        assert!(!CelTy::Duration.admits(&v), "Duration must not admit {v}");
    }
}

#[test]
fn an_array_reaches_the_object_arms() {
    // `typeof [] === "object"`, so an arktype-style object domain includes arrays and runs an
    // object's prop and index checks on them. A record or map derived from an object definition
    // therefore does NOT exclude arrays.
    let all_optional = record(vec![("k0", CelTy::Num)], &["k0"]);
    assert!(all_optional.admits(&json!([])));

    let m = CelTy::map(CelTy::Str, CelTy::Str);
    assert!(m.admits(&json!(["s"])));
    assert!(m.admits(&json!([])));
    assert!(!m.admits(&json!([1])));
}

#[test]
fn a_record_reads_an_array_by_stringified_index() {
    let t = record(vec![("0", CelTy::Str)], &[]);
    assert!(t.admits(&json!(["a"])));
    assert!(!t.admits(&json!([1])));
    assert!(!t.admits(&json!([])), "index 0 is required and absent");
}

#[test]
fn relaxing_the_null_narrowing_names_it_and_nothing_else() {
    // `T | null` derives `T` — the lattice has no nullable type — so the `null` the schema
    // accepts is not admitted. `Relax::NULL` is how a soundness harness tells that pinned divergence
    // apart from a real unsoundness. It must not do anything else.
    assert!(!CelTy::Str.admits(&json!(null)));
    assert!(CelTy::Str.admits_relaxed(&json!(null), Relax::NULL));
    let t = record(vec![("a", CelTy::Str)], &[]);
    assert!(!t.admits(&json!({"a": null})));
    assert!(t.admits_relaxed(&json!({"a": null}), Relax::NULL));
    // Not a general widening: a wrong non-null type is still wrong.
    assert!(!t.admits_relaxed(&json!({"a": 1}), Relax::NULL));
    assert!(!CelTy::Str.admits_relaxed(&json!(1), Relax::NULL));
}

#[test]
fn a_poison_admits_nothing_until_that_narrowing_is_relaxed() {
    use std::rc::Rc;
    let poison = CelTy::Unusable(Rc::new(typed_cel::Unusable {
        kind: "Uninhabited",
        message: "body.a: no value can have this type".into(),
    }));
    let t = record(vec![("a", poison.clone())], &[]);
    for v in [json!(null), json!(0), json!("x"), json!([]), json!({})] {
        assert!(
            !poison.admits(&v),
            "the bottom of the lattice admits nothing, got {v}"
        );
    }
    // The data a poisoned position stands for still ARRIVES — a recursive `replies` really does
    // carry comments — so a soundness harness counts this class rather than calling it unsound.
    assert!(!t.admits(&json!({"a": 1})));
    assert!(t.admits_relaxed(&json!({"a": 1}), Relax::UNUSABLE));
    // And relaxing it is not a general widening.
    assert!(!record(vec![("a", CelTy::Str)], &[]).admits_relaxed(&json!({"a": 1}), Relax::UNUSABLE));
}

#[test]
fn a_records_index_constrains_every_undeclared_key() {
    let with_index = CelTy::Record(Rc::new(Record {
        fields: vec![("a".into(), CelTy::Str)],
        optional: BTreeSet::new(),
        index: Some((CelTy::Str, CelTy::Num)),
        origin: "body".into(),
    }));
    assert!(with_index.admits(&json!({"a": "x"})));
    assert!(with_index.admits(&json!({"a": "x", "zz": 1})));
    assert!(!with_index.admits(&json!({"a": "x", "zz": "no"})));
    // A record with NO index still tolerates an undeclared key: `admits` answers "could this value
    // appear", and the schema validator already decided whether it may.
    assert!(record(vec![("a", CelTy::Str)], &[]).admits(&json!({"a": "x", "zz": "no"})));
}
