//! The dialect, in types.
//!
//! `CelTy` is deliberately smaller than spec CEL's type system, and every absence is one of the
//! removals in `README.md`: no `Timestamp`, no `UInt`, no `Int` (one numeric type), no `Optional`,
//! no message. A type that cannot be named is a construct that cannot be written.
//!
//! There is no type registry and no global table. A record IS its fields — structural, declared
//! directly or produced by a schema layer from a JSON schema the caller already has, and carrying
//! the origin it came from so a diagnostic can say which object a missing field is missing from.

use std::borrow::Cow;
use std::collections::BTreeSet;
use std::rc::Rc;

/// The static type of a value an expression can name.
#[derive(Clone, Debug, PartialEq)]
pub enum CelTy {
    Bool,
    /// The ONE numeric type. `number.integer` included — see `README.md`,
    /// `diverges: one numeric type`. Its values are exact integers or doubles (`CelNum`).
    Num,
    Str,
    Bytes,
    Null,
    /// A span, never a wall-clock instant. `elapsed` and `uptime` are these.
    Duration,
    List(Rc<CelTy>),
    Map(Rc<CelTy>, Rc<CelTy>),
    /// A structural record. No name, no registry, no global table.
    Record(Rc<Record>),
    /// No static knowledge.
    ///
    /// `unknown`, not `any` — see [`CelTy::requires_narrowing`]. It is load-bearing that this
    /// stays rare: every producer of it is a hole in the checker.
    Dyn,
    /// A position whose type could not be derived (by a schema layer), carrying WHY.
    ///
    /// NOT `Dyn`. `Dyn` type-checks against everything, so poisoning with it would turn a schema
    /// defect into an unchecked expression — the checker would go quiet exactly where the schema
    /// was broken. `Unusable` type-checks against NOTHING: naming a path that reaches one is a
    /// build error quoting the original reason, and every other field of the schema stays
    /// checkable. That locality is the whole point: a hole under ONE field should not take the
    /// whole schema down with it.
    ///
    /// `Rc` because a record holding many poisoned fields (a whole recursive subtree) should not
    /// hold many copies of one error.
    Unusable(Rc<Unusable>),
}

impl CelTy {
    /// `List(t)`, without the `Rc` at the call site.
    pub fn list(element: CelTy) -> CelTy {
        CelTy::List(Rc::new(element))
    }

    /// `Map(k, v)`, without the `Rc`s at the call site.
    pub fn map(key: CelTy, value: CelTy) -> CelTy {
        CelTy::Map(Rc::new(key), Rc::new(value))
    }

    /// How the type reads in a diagnostic. Spec CEL's names where they exist, because the author
    /// is writing CEL and a name they cannot look up is not a name.
    pub fn name(&self) -> String {
        match self {
            CelTy::Bool => "bool".into(),
            CelTy::Num => "double".into(),
            CelTy::Str => "string".into(),
            CelTy::Bytes => "bytes".into(),
            CelTy::Null => "null_type".into(),
            CelTy::Duration => "duration".into(),
            CelTy::List(t) => format!("list({})", t.name()),
            CelTy::Map(k, v) => format!("map({}, {})", k.name(), v.name()),
            CelTy::Record(r) => r.origin.clone(),
            CelTy::Dyn => "dyn".into(),
            // The reason, not an opaque word: a checker diagnostic quoting a type has to say why
            // the position is unusable, or the author has nothing to act on.
            CelTy::Unusable(why) => format!("unusable({why})"),
        }
    }

    /// Must a value of this type be narrowed before it is used?
    ///
    /// `Dyn` is `unknown`, not `any`: it says "some JSON value", not "stop checking". A schema's
    /// `unknown` is a statement about DATA — the top of the value lattice. CEL's `dyn` is a
    /// statement about VERIFICATION — skip the checker. Mapping the first onto the second leaves a
    /// hole the DIALECT ITSELF forbids an author to spell: `dyn()` is deleted (`README.md`,
    /// `removed: dyn()`; `dyn_is_gone` in `tests/dialect.rs`) precisely because "it exists to
    /// defeat type checking", so the schema must not be able to manufacture one.
    ///
    /// The checker answers ONE question of a `Dyn` — existence, `has(x.k)` — and refuses every
    /// other use of it (`removed: dyn values`). A schema that declares
    /// nothing therefore produces a build error rather than a runtime deny, or, in the system
    /// environment, rather than a REVOCATION nobody wrote down. Revocation is one-way.
    ///
    /// [`CelTy::Unusable`] is deliberately NOT narrowable and must not be folded in here.
    /// Narrowing means "we do not know yet"; a poison means "we know, and it is broken". Merging
    /// them produces a diagnostic telling an author to narrow a field that can never exist.
    ///
    /// The full operator table is `README.md`, `diverges: dyn must be narrowed`. Nothing is
    /// enforced HERE: a schema layer produces types, and refusing an OPERATION is the checker's
    /// job — putting it in the type producer would mean a schema failing to translate because of
    /// an expression nobody has written yet.
    pub fn requires_narrowing(&self) -> bool {
        matches!(self, CelTy::Dyn)
    }

    /// Could `v` appear at a position of this type?
    ///
    /// The witness function a soundness law is written against: for every value a schema ACCEPTS,
    /// the type derived from that schema must admit it. A `false` here for a value the schema
    /// accepted means the checker will reason about data that really arrives using a type that
    /// says it cannot.
    ///
    /// It is deliberately PERMISSIVE about undeclared keys. This answers "could this value
    /// appear", not "does the schema accept it" — the second question is the schema validator's,
    /// it already ran, and duplicating it here would make every open object report its own
    /// payloads impossible.
    pub fn admits(&self, v: &serde_json::Value) -> bool {
        self.admits_relaxed(v, Relax::NONE)
    }

    /// [`CelTy::admits`], with the lattice's DELIBERATE narrowings relaxed.
    ///
    /// This exists to NAME divergences rather than to hide them. Two positions in the lattice
    /// admit less than the schema they came from, on purpose:
    ///
    /// - `T | null` translates to `T`, because there is no nullable type to put it in and widening
    ///   to `Dyn` would make every nullable field unusable. So a `null` the schema accepts is not
    ///   admitted.
    /// - a poisoned position ([`CelTy::Unusable`]) admits nothing, but the data it stands for can
    ///   still arrive — a recursive `replies` really does carry comments.
    ///
    /// A soundness harness uses this to partition violations: one that disappears under a
    /// relaxation is that known divergence; one that survives every relaxation is a failure.
    pub fn admits_relaxed(&self, v: &serde_json::Value, relax: Relax) -> bool {
        self.admits_inner(v, relax)
    }

    fn admits_inner(&self, v: &serde_json::Value, relax: Relax) -> bool {
        use serde_json::Value as J;
        if relax.null && matches!(v, J::Null) {
            return true;
        }
        match (self, v) {
            (CelTy::Dyn, _) => true,
            (CelTy::Unusable(_), _) => relax.unusable,
            (CelTy::Bool, J::Bool(_)) => true,
            (CelTy::Num, J::Number(_)) => true,
            (CelTy::Str, J::String(_)) => true,
            (CelTy::Null, J::Null) => true,
            (CelTy::List(e), J::Array(items)) => items.iter().all(|i| e.admits_inner(i, relax)),
            // An ARRAY reaches the object arms too. `typeof [] === "object"` in JavaScript, so an
            // arktype-style schema's object domain INCLUDES arrays and runs an object's prop and
            // index checks on them. A record or a map derived from an object definition therefore
            // does not exclude arrays. The keys an array offers are its stringified indices, which
            // is exactly what such a schema checks against.
            (CelTy::Map(k, val), J::Object(_) | J::Array(_)) => {
                // A JSON object's keys are always strings, so a `Map` whose key type could not
                // admit a string is a type no JSON value can inhabit. One line, deliberately —
                // not a special case a later reader deletes as dead.
                k.admits(&J::String(String::new()))
                    && object_values(v).all(|i| val.admits_inner(i, relax))
            }
            (CelTy::Record(r), J::Object(_) | J::Array(_)) => {
                let declared = r.fields.iter().all(|(name, t)| match object_get(v, name) {
                    Some(field) => t.admits_inner(&field, relax),
                    None => r.is_optional(name),
                });
                // The index constrains every key the record does NOT declare. Without this the
                // soundness law fires on every payload that uses one — 31% of object definitions.
                declared
                    && match &r.index {
                        None => true,
                        Some((_, value)) => object_entries(v)
                            .filter(|(k, _)| r.get(k).is_none())
                            .all(|(_, i)| value.admits_inner(i, relax)),
                    }
            }
            // `Bytes` and `Duration` have no JSON witness, and every other pair is a genuine
            // mismatch. No `_ => true` anywhere: a wildcard here would make the soundness law
            // pass by construction, which is the one failure mode this function must not have.
            _ => false,
        }
    }
}

/// Which of the lattice's deliberate narrowings [`CelTy::admits_relaxed`] should look past.
///
/// A struct rather than positional bools: a harness classifies a violation by asking with ONE
/// relaxation at a time, and `admits_relaxed(v, true, false)` says nothing at the call site about
/// which narrowing is being forgiven.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Relax {
    /// `T | null` derives `T`.
    pub null: bool,
    /// A poisoned position admits nothing.
    pub unusable: bool,
}

impl Relax {
    /// What [`CelTy::admits`] itself uses: nothing relaxed.
    pub const NONE: Relax = Relax {
        null: false,
        unusable: false,
    };
    pub const NULL: Relax = Relax {
        null: true,
        unusable: false,
    };
    pub const UNUSABLE: Relax = Relax {
        null: false,
        unusable: true,
    };
    pub const ALL: Relax = Relax {
        null: true,
        unusable: true,
    };
}

/// The OWN property at `key`, reading an array the way JavaScript does.
///
/// Mirrors JavaScript's own-property read, because a schema layer with JavaScript semantics and
/// this function have to agree about which keys a value offers or the soundness law fires on the
/// difference: numeric keys index elements, `length` is a real own property holding the element
/// count, and a non-canonical index (`arr["01"]`) is `undefined`. No prototype chain.
fn object_get<'a>(v: &'a serde_json::Value, key: &str) -> Option<Cow<'a, serde_json::Value>> {
    match v {
        serde_json::Value::Object(m) => m.get(key).map(Cow::Borrowed),
        serde_json::Value::Array(items) => {
            if key == "length" {
                // Computed, not stored, so there is nothing to borrow.
                return Some(Cow::Owned(serde_json::Value::from(items.len())));
            }
            if key.len() > 1 && key.starts_with('0') {
                return None;
            }
            key.parse::<usize>()
                .ok()
                .and_then(|i| items.get(i))
                .map(Cow::Borrowed)
        }
        _ => None,
    }
}

/// Every own value of an object-domain value, arrays included.
fn object_values(v: &serde_json::Value) -> Box<dyn Iterator<Item = &serde_json::Value> + '_> {
    Box::new(object_entries(v).map(|(_, v)| v))
}

/// Every own enumerable `(key, value)` of an object-domain value.
///
/// An array's own enumerable keys are its stringified indices — `length` is NOT among them, which
/// is why this is not `object_get`'s inverse.
fn object_entries(
    v: &serde_json::Value,
) -> Box<dyn Iterator<Item = (std::borrow::Cow<'_, str>, &serde_json::Value)> + '_> {
    match v {
        serde_json::Value::Object(m) => {
            Box::new(m.iter().map(|(k, v)| (Cow::Borrowed(k.as_str()), v)))
        }
        serde_json::Value::Array(items) => Box::new(
            items
                .iter()
                .enumerate()
                .map(|(i, v)| (Cow::Owned(i.to_string()), v)),
        ),
        _ => Box::new(std::iter::empty()),
    }
}

/// A record's fields, in the order they were declared.
#[derive(Debug, PartialEq)]
pub struct Record {
    /// Required props first, then optional, each in declaration order — which for a definition
    /// written as a JSON object is sorted, because `serde_json::Map` is. Asserted rather than
    /// left to chance: this is the order a diagnostic's "available: …" roster reads out, and a
    /// roster that reorders between runs is a diff nobody can review.
    pub fields: Vec<(String, CelTy)>,
    /// The subset of `fields` a schema declared with `?`. Carried, never erased: naming an
    /// optional field type-checks, and it is the RUNTIME that treats a missing one as an error.
    pub optional: BTreeSet<String>,
    /// The index signature, when the schema declared one alongside its props.
    ///
    /// Real schemas often declare both, and dropping it made a schema that says "every string key maps to number" reject `headers['x-trace-id']` at build —
    /// invisibly, since the result was neither an error nor a `Dyn`.
    ///
    /// The KEY pattern is not reproduced. A schema layer should record a pattern index like
    /// `{"[/^f/]": "number"}` as `(Str, Dyn)`: the key stays nameable, and the VALUE is only the
    /// index's where the index constrains every key a value can carry. A second matcher here would
    /// be a second dialect to keep in step, and claiming `number` for a key the pattern never
    /// covered is a soundness violation.
    pub index: Option<(CelTy, CelTy)>,
    /// Where this record came from — `session`, `body.project.owner`, `body.documents[]`. For
    /// diagnostics only; nothing dispatches on it.
    pub origin: String,
}

/// Why a position has no type. Whoever built the type — a translation from a schema — says what
/// kind of refusal it was and how to say it; the checker and the binder only ever say it.
#[derive(Clone, Debug, PartialEq)]
pub struct Unusable {
    /// A short, stable name for the refusal, for whoever counts them (`"Uninhabited"`, …).
    pub kind: &'static str,
    /// The diagnostic, as a policy author reads it.
    pub message: String,
}

impl std::fmt::Display for Unusable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl Record {
    /// A record from an origin and its fields.
    ///
    /// The struct-literal form needs `Rc`, `BTreeSet` and all four fields at every roster site,
    /// and the duplication was already real: the same private `record()` helper existed in the
    /// embedding application AND in this crate's own test support. Two copies is the signal;
    /// a third is somebody's bug.
    ///
    /// Returns a `Record` rather than a `CelTy` so the builders below chain. `impl From<Record> for
    /// CelTy` means a caller still writes `env.declare("session", Record::new(..))` with no
    /// conversion in sight.
    pub fn new(
        origin: &str,
        fields: impl IntoIterator<Item = (impl Into<String>, CelTy)>,
    ) -> Record {
        Record {
            fields: fields.into_iter().map(|(n, t)| (n.into(), t)).collect(),
            optional: BTreeSet::new(),
            index: None,
            origin: origin.to_string(),
        }
    }

    /// The subset of fields a schema declared with `?`.
    pub fn with_optional(
        mut self,
        optional: impl IntoIterator<Item = impl Into<String>>,
    ) -> Record {
        self.optional = optional.into_iter().map(Into::into).collect();
        self
    }

    /// The index signature a schema declared alongside its props.
    pub fn with_index(mut self, key: CelTy, value: CelTy) -> Record {
        self.index = Some((key, value));
        self
    }

    pub fn get(&self, field: &str) -> Option<&CelTy> {
        self.fields
            .iter()
            .find(|(name, _)| name == field)
            .map(|(_, t)| t)
    }

    /// Powers "available: …" in a diagnostic.
    pub fn names(&self) -> Vec<&str> {
        self.fields.iter().map(|(name, _)| name.as_str()).collect()
    }

    pub fn is_optional(&self, field: &str) -> bool {
        self.optional.contains(field)
    }

    /// A declared field, or the index's value type, or nothing.
    ///
    /// The lookup ORDER is the semantics: a declared prop is more specific than the index. A schema
    /// layer should refuse a definition whose declared REQUIRED key contradicts its index, so the
    /// two never disagree here.
    pub fn field_or_index(&self, field: &str) -> Option<&CelTy> {
        self.get(field)
            .or_else(|| self.index.as_ref().map(|(_, value)| value))
    }
}

/// So a roster site writes `env.declare("session", Record::new(..))` and never names `Rc`.
impl From<Record> for CelTy {
    fn from(r: Record) -> CelTy {
        CelTy::Record(Rc::new(r))
    }
}
