//! The checker: a typed fold over `IdedExpr`.
//!
//! The centre of what this fork added to cel-rust. One recursive function over the AST with a scope
//! stack; the signature table (`sigs.rs`) feeds it and demand extraction (`demand.rs`) falls out
//! of it. Upstream has no checker at all, so `body.no_such_field` is an evaluation-time error in
//! production — a request denied, or a permission revoked, for a reason nobody wrote down.
//!
//! Two rules constrain every arm, and neither is negotiable here:
//!
//! - [`CelTy::Dyn`] is `unknown`, NOT `any`, and a program that checks holds no `dyn` VALUE
//!   (`removed: dyn values`): `body.blob > 1`, `body.blob == null` and `[1.0, "a"]` are build
//!   errors. Only `has(x.k)` — and `size()` of a collection of them — asks nothing of one.
//! - [`CelTy::Unusable`] is a position whose type could not be derived. It carries its reason and
//!   type-checks against NOTHING, so naming a path that reaches one is a build error quoting why.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use crate::bindings::Bindings;
use crate::common::ast::{
    operators, CallExpr, ComprehensionExpr, EntryExpr, Expr, IdedExpr, LiteralValue, SelectExpr,
};
use crate::demand::{DemandSet, Segment};
use crate::sigs::{self, Lookup};
use crate::ty::{CelTy, Record};
use crate::CelValue;

/// The variables an expression may name and their field structure.
///
/// Built OUTSIDE this crate — by whatever application embeds it — because the crate is
/// deliberately environment-agnostic. It knows about types; it knows
/// nothing about what a `body` or a `listener` is.
#[derive(Clone, Debug, Default)]
pub struct TypeEnv {
    vars: BTreeMap<String, CelTy>,
    /// The host functions the environment registered, by name.
    hosts: BTreeMap<String, HostSig>,
}

/// A host function's signature, beside the variables — so a `CelTy` never enters a `Send` value.
/// `params` includes the receiver for a member.
#[derive(Clone, Debug)]
pub(crate) struct HostSig {
    pub(crate) params: Vec<CelTy>,
    pub(crate) ret: CelTy,
    pub(crate) member: bool,
}

impl HostSig {
    /// `(double) -> double`, or `string.f(double) -> bool`, as the signature table renders one.
    fn render(&self, name: &str) -> String {
        let names = |ts: &[CelTy]| ts.iter().map(CelTy::name).collect::<Vec<_>>().join(", ");
        if self.member {
            format!(
                "{}.{name}({}) -> {}",
                self.params[0].name(),
                names(&self.params[1..]),
                self.ret.name()
            )
        } else {
            format!("({}) -> {}", names(&self.params), self.ret.name())
        }
    }
}

/// Is `name` one the dialect owns: a signature, a removal, a type denotation, or a macro? A host
/// function never takes one.
pub(crate) fn is_dialect_name(name: &str) -> bool {
    sigs::is_builtin(name)
        || DELETED_FUNCTIONS.iter().any(|(n, _)| *n == name)
        || DELETED_IDENTIFIERS.iter().any(|(n, _)| *n == name)
        || [
            operators::HAS,
            operators::ALL,
            operators::EXISTS,
            operators::EXISTS_ONE,
            "existsOne",
            operators::MAP,
            operators::FILTER,
        ]
        .contains(&name)
}

impl TypeEnv {
    pub fn new() -> TypeEnv {
        TypeEnv::default()
    }

    pub fn declare(&mut self, name: impl Into<String>, ty: CelTy) -> &mut TypeEnv {
        self.vars.insert(name.into(), ty);
        self
    }

    pub fn get(&self, name: &str) -> Option<&CelTy> {
        self.vars.get(name)
    }

    /// The declared roster, for a diagnostic's "available: …".
    pub fn roster(&self) -> Vec<String> {
        self.vars.keys().cloned().collect()
    }

    pub(crate) fn declare_host(&mut self, name: &str, sig: HostSig) {
        self.hosts.insert(name.to_string(), sig);
    }

    pub(crate) fn host(&self, name: &str) -> Option<&HostSig> {
        self.hosts.get(name)
    }
}

/// One thing the checker refused, addressed by the expression id it was found at.
///
/// The id — not a span. The compile layer owns the `SourceInfo` and the desugarer's `SpanMap`, and
/// it is the only place that can turn an id into a column the AUTHOR typed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckError {
    pub id: u64,
    pub message: String,
    /// The roster to print under "available: …", when there is one.
    pub available: Option<Vec<String>>,
}

impl CheckError {
    fn at(id: u64, message: impl Into<String>) -> CheckError {
        CheckError {
            id,
            message: message.into(),
            available: None,
        }
    }

    fn with_roster(id: u64, message: impl Into<String>, available: Vec<String>) -> CheckError {
        CheckError {
            id,
            message: message.into(),
            available: Some(available),
        }
    }
}

impl std::fmt::Display for CheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)?;
        if let Some(available) = &self.available {
            write!(f, "; available: {}", available.join(", "))?;
        }
        Ok(())
    }
}

/// Names the dialect DELETED, and what to say instead of "unknown function".
///
/// A removal the author can still type deserves a message naming the removal, not a generic
/// lookup failure. Each message says what the DIALECT does and cites the `README.md` row id; the
/// rationale lives in the README, which is where a reader can act on it — and where it can name
/// the embedding application's reasons without putting its vocabulary in library output. `tests/purity.rs` is what
/// keeps that true, and `tests/readme.rs::a_removal_message_names_the_dialect_not_the_product`
/// pins the specific strings, because a scan cannot tell a rationale from a noun.
const DELETED_FUNCTIONS: &[(&str, &str)] = &[
    ("dyn", "`dyn()` is removed: it exists to defeat type checking, and this dialect has a real checker"),
    ("timestamp", "`timestamp` is removed: durations are the only temporal type in this dialect. See `removed: timestamp` in README.md"),
    ("getFullYear", "`timestamp` is removed, and with it every wall-clock accessor"),
    ("getDayOfYear", "`timestamp` is removed, and with it every wall-clock accessor"),
    ("getHours", "`timestamp` is removed, and with it every wall-clock accessor"),
    ("getMinutes", "`timestamp` is removed, and with it every wall-clock accessor"),
    ("uint", "`uint` is removed: this dialect has one number type, and a large integer is written without a `u`"),
    ("int", "`int()` is removed: this dialect has one number type, which holds integers exactly. See `removed: type conversion functions` in README.md"),
    ("bool", "`bool()` is removed: a string is not a truth value in this dialect. See `removed: type conversion functions` in README.md"),
    ("string", "`string()` is removed: it is lossy on bytes and redundant elsewhere. See `removed: type conversion functions` in README.md"),
    ("double", "`double()` is removed: every number in this dialect is already of its one number type. See `removed: type conversion functions` in README.md"),
    ("type", "there are no type values in this dialect. See `removed: type values` in README.md"),
    ("list", "there are no type values in this dialect. See `removed: type values` in README.md"),
    ("map", "there are no type values in this dialect. See `removed: type values` in README.md"),
    ("bytes", "`bytes()` is removed: a string literal's bytes are written `b'…'`. See `removed: type conversion functions` in README.md"),
    ("null_type", "there are no type values in this dialect. See `removed: type values` in README.md"),
    ("optional", "optional syntax is removed: a read that may be absent is proven present with `has(x.f)` or `'k' in m` — guard it where you read it. See `removed: optional syntax` in README.md"),
    ("orValue", "optional syntax is removed: a read that may be absent is proven present with `has(x.f)` or `'k' in m` — guard it where you read it. See `removed: optional syntax` in README.md"),
    ("_%_", "`%` is removed: this dialect has one number type, and no program needs its remainder. See `removed: modulo` in README.md"),
];

/// The type DENOTATIONS, which are bare identifiers rather than calls.
///
/// A separate table because it is reached from a separate place. `DELETED_FUNCTIONS` is consulted
/// on the unknown-FUNCTION path, and `bool` on its own never gets there — it is an identifier, so
/// it takes the undeclared-VARIABLE path and would otherwise report a typo. Declaring these as
/// variables instead would be worse than the typo: it would make them WRITABLE.
const DELETED_IDENTIFIERS: &[(&str, &str)] = &[
    ("int", TYPE_VALUES_REMOVED),
    ("string", TYPE_VALUES_REMOVED),
    ("list", TYPE_VALUES_REMOVED),
    ("map", TYPE_VALUES_REMOVED),
    ("bool", TYPE_VALUES_REMOVED),
    ("double", TYPE_VALUES_REMOVED),
    ("bytes", TYPE_VALUES_REMOVED),
    ("null_type", TYPE_VALUES_REMOVED),
    ("type", TYPE_VALUES_REMOVED),
];

const TYPE_VALUES_REMOVED: &str =
    "there are no type values in this dialect. See `removed: type values` in README.md";

/// What checking one node produced.
///
/// `path` is the literal path this node NAMES, when it names one — `files ▸ "/a" ▸ "closed"`.
/// Demand harvesting is a byproduct of the fold rather than a second walk, because a harvester
/// that re-derived which selects are field accesses would silently disagree the first time the two
/// drifted.
struct Checked {
    ty: CelTy,
    path: Option<Vec<Segment>>,
    /// The expression's PRESENCE path, when it has one: a root followed by literal keys. What a
    /// guard (`has`, `in`) proves present, and what a read must find proven.
    pres: Option<PresPath>,
}

impl Checked {
    fn bare(ty: CelTy) -> Checked {
        Checked {
            ty,
            path: None,
            pres: None,
        }
    }
}

/// A comprehension variable in scope, with the path its range names.
struct Local {
    name: String,
    ty: CelTy,
    /// The demand path of the map this variable iterates, when it iterates one. A computed key is
    /// legal ONLY where this proves the iteration is over that same map.
    range_path: Option<Vec<Segment>>,
    /// A fresh id per comprehension: the presence root of this variable. An inner `i` shadowing an
    /// outer `i` is a different root, so a fact about one proves nothing about the other.
    scope: u32,
    /// The presence path of the container iterated: `m[k]`, `k` this variable, is present exactly
    /// when the container indexed is this one.
    range_pres: Option<PresPath>,
}

/// Where a presence path starts: a declared root, ONE comprehension's iteration variable —
/// identified by the scope that bound it, never by its name — or a residual's constant slot, whose
/// value is known.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum PresRoot {
    Var(String),
    Local(u32),
    Slot(String),
    /// A map LITERAL whose keys are all scalar literals, by its expression id: a known value, whose
    /// keys are exactly the ones written.
    Literal(u64),
}

/// A root followed by literal keys. A field select and a literal-key index produce the SAME
/// segment, so `has(m.k)` proves `m["k"]`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct PresPath {
    root: PresRoot,
    keys: Vec<String>,
}

impl PresPath {
    fn root(root: PresRoot) -> PresPath {
        PresPath {
            root,
            keys: Vec::new(),
        }
    }

    fn child(&self, key: &str) -> PresPath {
        let mut keys = self.keys.clone();
        keys.push(key.to_string());
        PresPath {
            root: self.root.clone(),
            keys,
        }
    }

    /// `self` and every proper prefix that has at least one key: proving `a.b.c` present proves
    /// `a.b` present too.
    fn with_prefixes(&self) -> impl Iterator<Item = PresPath> + '_ {
        (1..=self.keys.len()).map(|n| PresPath {
            root: self.root.clone(),
            keys: self.keys[..n].to_vec(),
        })
    }
}

/// Why a read may find nothing there.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AbsentKind {
    /// A record field its schema declared optional (`?`).
    OptionalField,
    /// A record key only the record's index signature allows.
    IndexKey,
    /// Any key of a `map`.
    MapKey,
    /// A key a KNOWN value does not hold.
    KnownAbsent,
}

#[cfg_attr(not(feature = "conformance"), allow(dead_code))]
impl AbsentKind {
    pub(crate) fn name(self) -> &'static str {
        match self {
            AbsentKind::OptionalField => "optional_field",
            AbsentKind::IndexKey => "index_key",
            AbsentKind::MapKey => "map_key",
            AbsentKind::KnownAbsent => "known_absent",
        }
    }
}

/// A read the presence rules refuse: nothing in view proves it present.
#[derive(Clone, Debug)]
#[cfg_attr(not(feature = "conformance"), allow(dead_code))]
pub(crate) struct Unproven {
    pub(crate) id: u64,
    /// The read as the author wrote it: `body.discount`, `m["k"]`, `i.note`.
    pub(crate) rendered: String,
    pub(crate) kind: AbsentKind,
}

/// The one recursive walk. Everything else in the crate feeds it or consumes its output.
pub struct Checker<'a> {
    env: &'a TypeEnv,
    /// Comprehension iteration variables, innermost last. Truncated back to the entry length on
    /// the way out, which is what keeps `d` undefined outside its `all(...)`.
    locals: Vec<Local>,
    demand: DemandSet,
    errors: Vec<CheckError>,
    depth: u32,
    max_depth: u32,
    /// A residual's constant slots and their DECLARED types ([`Checker::with_consts`]). A slot is
    /// typed like a variable but names no demand: nothing the host supplies stands behind it.
    consts: &'a [(String, CelTy)],
    /// The type of every node checked, by expression id, when [`Checker::run_presence`] asked for it.
    types: Option<HashMap<u64, CelTy>>,
    /// Presence facts in force at the node being checked: pushed on the way into a subtree the
    /// facts hold for, truncated on the way out.
    proven: Vec<PresPath>,
    next_scope: u32,
    /// The KNOWN roots and their values (`CompileOpts::known`): a read under one is present iff
    /// the value holds it.
    known: Option<(&'a Bindings, &'a BTreeSet<String>)>,
    /// A residual's constant slots' values, on the re-check: known exactly as the roots they came
    /// from were.
    slot_values: &'a [(Arc<str>, CelValue)],
    /// What the presence rules refuse, in the order the walk met them.
    unproven: Vec<Unproven>,
    /// The keys each string-keyed map literal checked so far was written with, by expression id.
    literal_keys: HashMap<u64, BTreeSet<String>>,
    /// Whether an unproven read is a CHECK ERROR. Off only for the report and the unchecked test
    /// door, which observe the rules instead of applying them.
    enforce_presence: bool,
}

impl<'a> Checker<'a> {
    pub fn new(env: &'a TypeEnv, max_depth: u32) -> Checker<'a> {
        Checker {
            env,
            locals: Vec::new(),
            demand: DemandSet::default(),
            errors: Vec::new(),
            depth: 0,
            max_depth,
            consts: &[],
            types: None,
            proven: Vec::new(),
            next_scope: 0,
            known: None,
            slot_values: &[],
            unproven: Vec::new(),
            literal_keys: HashMap::new(),
            enforce_presence: true,
        }
    }

    /// Collect unproven reads without refusing them — `fork::presence_report` and the unchecked
    /// test door.
    pub(crate) fn observing_presence(self) -> Checker<'a> {
        Checker {
            enforce_presence: false,
            ..self
        }
    }

    /// Hand the checker the values known now: a read under a known root is present exactly when
    /// the value holds it.
    pub(crate) fn with_known(
        self,
        bindings: &'a Bindings,
        roots: &'a BTreeSet<String>,
    ) -> Checker<'a> {
        Checker {
            known: Some((bindings, roots)),
            ..self
        }
    }

    /// A residual's constant slots' values, so a read of `$k0["k"]` is proven by the slot's value
    /// exactly as `policy.x["k"]` was by the known binding.
    pub(crate) fn with_slot_values(self, values: &'a [(Arc<str>, CelValue)]) -> Checker<'a> {
        Checker {
            slot_values: values,
            ..self
        }
    }

    /// Declare a residual's constant slots. A slot reads as its declared type and contributes no
    /// demand path.
    pub(crate) fn with_consts(self, consts: &'a [(String, CelTy)]) -> Checker<'a> {
        Checker { consts, ..self }
    }

    /// Check a whole expression. Returns its type, what it reads, and the type of every node, by
    /// expression id — the specializer types a known composite from this table (the type the
    /// ORIGINAL was checked at, never one inferred from the value), and the fast backend lowers by
    /// it.
    ///
    /// Also hands back every read the presence rules refuse, in the order the walk met them.
    #[allow(clippy::type_complexity)]
    pub(crate) fn run_presence(
        mut self,
        e: &IdedExpr,
    ) -> (
        Result<(CelTy, DemandSet, HashMap<u64, CelTy>), Vec<CheckError>>,
        Vec<Unproven>,
    ) {
        self.types = Some(HashMap::new());
        let checked = self.check(e);
        if let Some(c) = &checked {
            self.commit(c.path.clone());
        }
        let unproven = std::mem::take(&mut self.unproven);
        if !self.errors.is_empty() {
            return (Err(self.errors), unproven);
        }
        let result = match checked {
            Some(c) => {
                self.demand.finish();
                Ok((c.ty, self.demand, self.types.unwrap_or_default()))
            }
            // `check` returning `None` with no error recorded is a checker bug, not a policy one.
            None => Err(vec![CheckError::at(e.id, "expression has no type")]),
        };
        (result, unproven)
    }

    fn error(&mut self, e: CheckError) -> Option<Checked> {
        self.errors.push(e);
        None
    }

    /// Record a path that nothing above will extend.
    fn commit(&mut self, path: Option<Vec<Segment>>) {
        if let Some(p) = path {
            self.demand.record(p);
        }
    }

    fn check(&mut self, e: &IdedExpr) -> Option<Checked> {
        self.depth += 1;
        if self.depth > self.max_depth {
            self.depth -= 1;
            return self.error(CheckError::at(
                e.id,
                format!(
                    "expression nests deeper than the limit of {}. See `diverges: nesting is \
                     bounded` in README.md",
                    self.max_depth
                ),
            ));
        }
        let out = match &e.expr {
            Expr::Literal(v) => Some(Checked::bare(literal_ty(v))),
            Expr::Ident(name) => self.ident(name, e.id),
            Expr::Select(s) => self.select(s, e.id),
            Expr::Call(c) => self.call(c, e.id),
            Expr::List(l) => self.list(&l.elements, e.id),
            Expr::Map(m) => self.map_literal(&m.entries, e.id),
            Expr::Comprehension(c) => self.comprehension(c, e.id),
            // `Expr::Struct` is `removed: protobuf` — it is not in the enum, so the exhaustive
            // match IS the rejection and there is no runtime check to keep in step.
            Expr::Unspecified => self.error(CheckError::at(
                e.id,
                "unsupported expression: this construct is not in the typed-CEL dialect",
            )),
        };
        self.depth -= 1;
        if let (Some(types), Some(c)) = (self.types.as_mut(), &out) {
            types.insert(e.id, c.ty.clone());
        }
        out
    }

    /// Locals shadow globals — innermost first.
    fn ident(&mut self, name: &str, id: u64) -> Option<Checked> {
        if let Some(local) = self.locals.iter().rev().find(|l| l.name == name) {
            return Some(Checked {
                ty: local.ty.clone(),
                path: None,
                pres: Some(PresPath::root(PresRoot::Local(local.scope))),
            });
        }
        if let Some((_, t)) = self.consts.iter().find(|(n, _)| n == name) {
            return Some(Checked {
                pres: Some(PresPath::root(PresRoot::Slot(name.to_string()))),
                ..Checked::bare(t.clone())
            });
        }
        match self.env.get(name) {
            Some(t) => Some(Checked {
                ty: t.clone(),
                path: Some(vec![Segment::Root(name.to_string())]),
                pres: Some(PresPath::root(PresRoot::Var(name.to_string()))),
            }),
            None => match DELETED_IDENTIFIERS.iter().find(|(n, _)| *n == name) {
                Some((_, why)) => self.error(CheckError::at(id, why.to_string())),
                None => self.error(CheckError::with_roster(
                    id,
                    format!("undeclared variable `{name}`. {UNDECLARED}"),
                    self.env.roster(),
                )),
            },
        }
    }

    fn select(&mut self, s: &SelectExpr, id: u64) -> Option<Checked> {
        // A backtick-quoted field arrives here with its delimiters still attached, which is the
        // only reason the checker can see the construct at all — and the only reason it must. Left
        // alone the select is a lookup for a key nothing has, so it fails at EVALUATION with
        // `No such key`, which reads as missing data rather than as a construct that is not here.
        if let Some(bare) = s.field.strip_prefix('`').and_then(|f| f.strip_suffix('`')) {
            return self.error(CheckError::at(
                id,
                format!(
                    "backtick-quoted field selection is not in this dialect; write \
                     `['{bare}']` instead. See `not implemented: backtick-quoted field selection` \
                     in README.md"
                ),
            ));
        }
        let operand = self.check(&s.operand)?;
        // `has(x.k)` desugars to a select with `test` set. It is an EXISTENCE question, answerable
        // without narrowing a `Dyn` — but on a record whose fields are declared, a field that
        // cannot exist is still a typo, and reporting it is the whole point of the crate.
        if s.test {
            if let CelTy::Record(r) = &operand.ty {
                if r.field_or_index(&s.field).is_none() {
                    return self.unknown_field(&s.field, r, id);
                }
            }
            // On an open container the key is demand: nothing else says WHICH key's presence the
            // expression asks about, and a streamed value cannot answer for a key it never tracked.
            let path = if names_an_open_key(&operand.ty, &s.field) {
                operand.path.map(|mut p| {
                    p.push(Segment::Key(s.field.clone()));
                    p
                })
            } else {
                operand.path
            };
            self.commit(path);
            return Some(Checked::bare(CelTy::Bool));
        }
        let path = operand.path.map(|mut p| {
            p.push(Segment::Key(s.field.clone()));
            p
        });
        let pres = operand.pres.as_ref().map(|p| p.child(&s.field));
        match &operand.ty {
            CelTy::Record(r) => match r.field_or_index(&s.field) {
                // THE diagnostic this whole crate exists to produce.
                None => self.unknown_field(&s.field, r, id),
                Some(t) => {
                    let ty = t.clone();
                    self.require_present(id, &operand.ty, operand.pres.as_ref(), &s.field, || {
                        Read::select(&s.operand, &s.field)
                    });
                    Some(Checked { ty, path, pres })
                }
            },
            // A map has no declared field set, so a select is the value type.
            m if m.is_map() => {
                self.require_present(id, m, operand.pres.as_ref(), &s.field, || {
                    Read::select(&s.operand, &s.field)
                });
                Some(Checked {
                    ty: m.map_parts().expect("a map").1.clone(),
                    path,
                    pres,
                })
            }
            // `Dyn` is `unknown`, not `any`: a select on one is an error, not a `Dyn`.
            CelTy::Dyn => self.error(CheckError::at(
                id,
                format!(
                    "cannot read `.{}` on a value of type dyn; declare the field in the schema so \
                     it has a type",
                    s.field
                ),
            )),
            CelTy::Unusable(why) => self.error(CheckError::at(
                id,
                format!("cannot read `.{}`: {why}", s.field),
            )),
            other => self.error(CheckError::at(
                id,
                format!(
                    "cannot read `.{}` on a value of type {}",
                    s.field,
                    other.name()
                ),
            )),
        }
    }

    fn unknown_field(&mut self, field: &str, r: &Record, id: u64) -> Option<Checked> {
        self.error(CheckError::with_roster(
            id,
            format!("no field `{field}` on `{}`", r.origin),
            r.names().into_iter().map(str::to_string).collect(),
        ))
    }

    fn call(&mut self, c: &CallExpr, id: u64) -> Option<Checked> {
        if c.func_name == operators::INDEX {
            return self.index(c, id);
        }

        let member = c.target.is_some();
        let mut args = Vec::with_capacity(c.args.len() + 1);
        // Every argument is checked, THEN the failure is propagated. `args.push(self.check(a)?)`
        // abandoned every sibling arm the moment one failed, so
        // `body.no_such_a == 'x' && session.no_such_b == 'y'` reported one error and the author
        // fixed it only to meet the second — and `CelError::all` could never have had both.
        //
        // Only CALLS recover, and only across their own arguments: those are independent
        // subexpressions. A `Select` still short-circuits, because `.c` on an operand whose type is
        // unknown has nothing to say and would cascade.
        let mut failed = false;
        if let Some(target) = &c.target {
            match self.check(target) {
                Some(checked) => args.push(checked),
                None => failed = true,
            }
        }
        // `&&`, `||` and `?:` check each argument with the presence facts its SIBLINGS prove.
        let facts = self.arg_facts(c);
        for (i, a) in c.args.iter().enumerate() {
            let mark = self.proven.len();
            if let Some(f) = facts.get(i) {
                self.proven.extend(f.iter().cloned());
            }
            let checked = self.check(a);
            self.proven.truncate(mark);
            match checked {
                Some(checked) => args.push(checked),
                None => failed = true,
            }
        }
        if failed {
            return None;
        }
        let exprs: Vec<&IdedExpr> = c.target.as_deref().into_iter().chain(&c.args).collect();
        adopt_empty(&c.func_name, &exprs, &mut args);
        // An empty literal's type is the one it ADOPTED from its use, and that is the type a
        // specializer must hold its value at.
        if let Some(types) = self.types.as_mut() {
            for (x, a) in exprs.iter().zip(&args) {
                if is_empty_collection(x) {
                    types.insert(x.id, a.ty.clone());
                }
            }
        }

        // `removed: dyn values`: an argument that holds a `dyn` is a use of one, and a program that
        // checks has none. `size()` is the one call that asks nothing of the elements, so a
        // derived heterogeneous tuple (`list(dyn)`) still has a length. An EMPTY literal's `dyn`
        // is not a value at all — it is the element type nothing has pinned yet.
        if c.func_name != "size" {
            if let Some(i) =
                (0..args.len()).find(|&i| holds_dyn(&args[i].ty) && !unpinned(exprs[i]))
            {
                let message = format!(
                    "`{}` has no meaning on a value of type {} (argument {}); a dyn value must be \
                     narrowed — declare it in the schema so it has a type, or ask `has()`. \
                     {DYN_VALUES_REMOVED}",
                    spell(&c.func_name),
                    args[i].ty.name(),
                    i + 1
                );
                // The paths still count: a fold over an empty range discards this refusal and
                // keeps what its body names.
                for a in args {
                    self.commit(a.path);
                }
                return self.error(CheckError::at(id, message));
            }
        }

        // Nullness is answerable without a type.
        if matches!(
            c.func_name.as_str(),
            operators::EQUALS | operators::NOT_EQUALS
        ) && args.iter().any(|a| a.ty == CelTy::Null)
        {
            for a in args {
                self.commit(a.path);
            }
            return Some(Checked::bare(CelTy::Bool));
        }
        // `k in x` on an open container is a presence question, and its key is demand exactly as
        // `has(x.k)`'s is. A key that is not a literal cannot be named at build, so the container
        // is demanded WHOLE: a `Wild` segment, and its root widened.
        if c.func_name == operators::IN && args.len() == 2 {
            let literal = match &exprs[0].expr {
                Expr::Literal(LiteralValue::String(k)) => Some(k.inner().to_string()),
                _ => None,
            };
            let open = match &literal {
                Some(k) => names_an_open_key(&args[1].ty, k),
                None => {
                    args[1].ty.is_map()
                        || matches!(&args[1].ty, CelTy::Record(r) if r.index.is_some())
                }
            };
            if open {
                if let Some(p) = args[1].path.as_mut() {
                    match literal {
                        Some(k) => p.push(Segment::Key(k)),
                        None => {
                            p.push(Segment::Wild);
                            if let Some(Segment::Root(root)) = p.first() {
                                self.demand.widen(root.clone());
                            }
                        }
                    }
                }
            }
        }

        let tys: Vec<CelTy> = args.iter().map(|a| a.ty.clone()).collect();
        for a in args {
            self.commit(a.path);
        }

        // `"k" in rec` asks what `has(rec.k)` asks — and it is the ONLY guard for a key no
        // selector can spell (`'x-other' in body.h`). The backend already answers it as a presence
        // question. As with `has`, a literal key the record can never hold is a typo.
        if c.func_name == operators::IN && tys.len() == 2 && tys[0] == CelTy::Str {
            if let CelTy::Record(r) = &tys[1] {
                if let Expr::Literal(LiteralValue::String(k)) = &exprs[0].expr {
                    if r.field_or_index(k.inner()).is_none() {
                        let r = r.clone();
                        return self.unknown_field(k.inner(), &r, id);
                    }
                }
                return Some(Checked::bare(CelTy::Bool));
            }
        }

        match sigs::resolve(&c.func_name, &tys, member) {
            Lookup::Ok(ty) => Some(Checked::bare(ty)),
            Lookup::UnknownFunction => {
                // An EMBEDDING's function: exactly its declared types, never one that needs
                // narrowing — a host function is no way around `removed: dyn values`.
                if let Some(sig) = self.env.host(&c.func_name) {
                    if sig.member == member
                        && sig.params.len() == tys.len()
                        && sig
                            .params
                            .iter()
                            .zip(&tys)
                            .all(|(p, a)| p.same_shape(a) && !a.requires_narrowing())
                    {
                        return Some(Checked::bare(sig.ret.clone()));
                    }
                    let got = tys.iter().map(CelTy::name).collect::<Vec<_>>().join(", ");
                    return self.error(CheckError::at(
                        id,
                        format!(
                            "`{}` accepts {}, not ({got}){}",
                            c.func_name,
                            sig.render(&c.func_name),
                            if sig.member == member {
                                ""
                            } else if sig.member {
                                "; it is called as a method"
                            } else {
                                "; it is not called as a method"
                            }
                        ),
                    ));
                }
                let msg = DELETED_FUNCTIONS
                    .iter()
                    .find(|(n, _)| *n == c.func_name)
                    .map(|(_, why)| why.to_string())
                    .unwrap_or_else(|| {
                        let mut msg = format!(
                            "unknown function `{}`; this dialect registers no custom functions. \
                             {UNDECLARED}",
                            c.func_name
                        );
                        if !self.env.hosts.is_empty() {
                            let names: Vec<&str> =
                                self.env.hosts.keys().map(String::as_str).collect();
                            msg.push_str(&format!(
                                "; registered host functions: {}",
                                names.join(", ")
                            ));
                        }
                        msg
                    });
                self.error(CheckError::at(id, msg))
            }
            Lookup::NoOverload => {
                // A `Dyn` operand is the interesting case: say what to do about it rather than
                // reporting a missing overload the author cannot add.
                if let Some(i) = tys.iter().position(|t| t.requires_narrowing()) {
                    return self.error(CheckError::at(
                        id,
                        format!(
                            "`{}` has no meaning on a value of type dyn (argument {}); declare it \
                             in the schema so it has a type. {DYN_VALUES_REMOVED}",
                            spell(&c.func_name),
                            i + 1
                        ),
                    ));
                }
                // A conditional whose branches differ would produce a value of no one type.
                if c.func_name == operators::CONDITIONAL
                    && tys.len() == 3
                    && !tys[1].same_shape(&tys[2])
                {
                    return self.error(CheckError::at(
                        id,
                        format!(
                            "the branches of `?:` have different types ({} and {}); a value of no \
                             one type is a dyn. {DYN_VALUES_REMOVED}",
                            tys[1].name(),
                            tys[2].name()
                        ),
                    ));
                }
                if let Some(why) = tys.iter().find_map(|t| match t {
                    CelTy::Unusable(why) => Some(why.clone()),
                    _ => None,
                }) {
                    return self.error(CheckError::at(id, format!("{why}")));
                }
                let spelled: Vec<String> = tys.iter().map(CelTy::name).collect();
                let row = removed_row(&c.func_name, &tys)
                    .map(|row| format!(". See `{row}` in README.md"))
                    .unwrap_or_default();
                self.error(CheckError::at(
                    id,
                    format!(
                        "`{}` does not accept ({}){row}",
                        spell(&c.func_name),
                        spelled.join(", ")
                    ),
                ))
            }
        }
    }

    /// `_[_]`. There is no optional form: an index that may miss must be PROVEN present — by a
    /// guard, by iterating the same container, by a known value, or by an `unsafe_map` declaration
    /// (the proofs are listed at `require_present`).
    fn index(&mut self, c: &CallExpr, id: u64) -> Option<Checked> {
        if c.args.len() != 2 {
            return self.error(CheckError::at(id, "malformed index expression"));
        }
        let target = self.check(&c.args[0])?;
        let key_expr = &c.args[1];

        // A literal string key into a RECORD is a FIELD ACCESS wearing different syntax, and it
        // has to stay one: `headers['content-type']` is reachable only by index (backtick quoting
        // is a known bug), and typing `headers` as a map to make it resolve would discard
        // unknown-key detection for the three variables an attacker most influences.
        if let CelTy::Record(r) = &target.ty {
            return match &key_expr.expr {
                Expr::Literal(LiteralValue::String(k)) => {
                    let r = r.clone();
                    match r.field_or_index(k.inner()) {
                        Some(t) => {
                            let ty = t.clone();
                            self.require_present(
                                id,
                                &target.ty,
                                target.pres.as_ref(),
                                k.inner(),
                                || Read::index(&c.args[0], k.inner()),
                            );
                            let path = target.path.map(|mut p| {
                                p.push(Segment::Key(k.inner().to_string()));
                                p
                            });
                            let pres = target.pres.as_ref().map(|p| p.child(k.inner()));
                            Some(Checked { ty, path, pres })
                        }
                        None => self.unknown_field(k.inner(), &r, id),
                    }
                }
                // A computed key into a record cannot be checked, and must not silently pass.
                _ => self.error(CheckError::at(
                    id,
                    format!(
                        "`{}` is indexed with a computed key; a record's keys must be string \
                         literals so they can be checked",
                        r.origin
                    ),
                )),
            };
        }

        let key = self.check(key_expr)?;
        // The presence of the key read: a literal key extends the operand's presence path; a
        // computed one is proven only by iterating the same container.
        let mut pres = None;
        if target.ty.is_map() {
            match &key_expr.expr {
                Expr::Literal(LiteralValue::String(k)) => {
                    self.require_present(id, &target.ty, target.pres.as_ref(), k.inner(), || {
                        Read::index(&c.args[0], k.inner())
                    });
                    pres = target.pres.as_ref().map(|p| p.child(k.inner()));
                }
                Expr::Ident(name) if self.iterated_key(name, target.pres.as_ref()) => {}
                // A non-string literal key into a map LITERAL: present iff it was written.
                Expr::Literal(lit)
                    if matches!(
                        target.pres.as_ref().map(|p| (&p.root, p.keys.len())),
                        Some((PresRoot::Literal(_), 0))
                    ) =>
                {
                    let Some(PresRoot::Literal(lit_id)) = target.pres.as_ref().map(|p| &p.root)
                    else {
                        unreachable!()
                    };
                    let written = literal_key(lit).is_some_and(|k| {
                        self.literal_keys
                            .get(lit_id)
                            .is_some_and(|w| w.contains(&k))
                    });
                    if !written {
                        let read = Read {
                            rendered: format!("{}[{}]", render(&c.args[0]), render(key_expr)),
                            container: render(&c.args[0]),
                            key: None,
                            select: false,
                        };
                        self.unproven(
                            id,
                            read,
                            AbsentKind::KnownAbsent,
                            Some("this map literal".to_string()),
                        );
                    }
                }
                // Outside iteration, a computed key into a rooted map is already refused below
                // for its demand, with the better message.
                _ if target.path.is_some() => {}
                _ => {
                    if matches!(target.ty, CelTy::Map(..)) {
                        let read = Read {
                            rendered: format!("{}[{}]", render(&c.args[0]), render(key_expr)),
                            container: render(&c.args[0]),
                            key: None,
                            select: false,
                        };
                        self.unproven(id, read, AbsentKind::MapKey, None);
                    }
                }
            }
        }
        let path = match &key_expr.expr {
            // A literal key is demand information even where it is not a type question — the
            // runtime needs it to know WHICH file to track.
            Expr::Literal(LiteralValue::String(k)) => target.path.clone().map(|mut p| {
                p.push(Segment::Key(k.inner().to_string()));
                p
            }),
            // A computed key is legal ONLY inside a comprehension over the same container, where
            // the iteration itself proves the range. Anywhere else, widening one unreviewable
            // expression would silently turn the whole policy into "populate everything".
            Expr::Ident(name) if self.iterates(name, target.path.as_deref()) => {
                target.path.clone().map(|mut p| {
                    p.push(Segment::Wild);
                    p
                })
            }
            _ if target.path.is_some() && target.ty.is_map() => {
                let named = describe(key_expr);
                self.error(CheckError::at(
                    id,
                    format!(
                        "computed key {named} makes the demand set unknowable; write the key out, \
                         or index inside a comprehension over the same collection"
                    ),
                ));
                None
            }
            _ => None,
        };
        if let Some(p) = &path {
            if p.last() == Some(&Segment::Wild) {
                if let Some(Segment::Root(root)) = p.first() {
                    self.demand.widen(root.clone());
                }
            }
        }

        let tys = [target.ty.clone(), key.ty.clone()];
        self.commit(key.path);
        match sigs::resolve(operators::INDEX, &tys, false) {
            Lookup::Ok(ty) => Some(Checked { ty, path, pres }),
            _ => {
                if target.ty.requires_narrowing() {
                    return self.error(CheckError::at(
                        id,
                        "cannot index a value of type dyn; declare its shape in the schema",
                    ));
                }
                if let CelTy::Unusable(why) = &target.ty {
                    return self.error(CheckError::at(id, format!("{why}")));
                }
                self.error(CheckError::at(
                    id,
                    format!(
                        "cannot index a value of type {} with {}",
                        target.ty.name(),
                        key.ty.name()
                    ),
                ))
            }
        }
    }

    /// Is `name` an iteration variable whose range is exactly the container at `path`?
    fn iterates(&self, name: &str, path: Option<&[Segment]>) -> bool {
        let Some(path) = path else { return false };
        self.locals
            .iter()
            .rev()
            .find(|l| l.name == name)
            .and_then(|l| l.range_path.as_deref())
            .is_some_and(|range| range == path)
    }

    fn list(&mut self, elements: &[IdedExpr], id: u64) -> Option<Checked> {
        let mut element = Element::default();
        for e in elements {
            let c = self.check(e)?;
            self.commit(c.path);
            if let Err(message) = element.admit(e, c.ty, "list", "elements") {
                return self.error(CheckError::at(id, message));
            }
        }
        let ty = match element.finish(&mut self.types) {
            Ok(ty) => ty,
            Err(message) => return self.error(CheckError::at(id, message)),
        };
        Some(Checked::bare(CelTy::list(ty)))
    }

    fn map_literal(
        &mut self,
        entries: &[crate::common::ast::IdedEntryExpr],
        id: u64,
    ) -> Option<Checked> {
        let mut keys = Element::default();
        let mut values = Element::default();
        for entry in entries {
            let EntryExpr::MapEntry(e) = &entry.expr;
            let k = self.check(&e.key)?;
            let v = self.check(&e.value)?;
            self.commit(k.path);
            self.commit(v.path);
            let admitted = keys
                .admit(&e.key, k.ty, "map", "keys")
                .and_then(|_| values.admit(&e.value, v.ty, "map", "values"));
            if let Err(message) = admitted {
                return self.error(CheckError::at(id, message));
            }
        }
        let key_ty = keys.finish(&mut self.types);
        let val_ty = values.finish(&mut self.types);
        // A literal whose keys are all string literals is KNOWN: it holds exactly those keys.
        let pres = literal_keys(entries).map(|written| {
            self.literal_keys.insert(id, written);
            PresPath::root(PresRoot::Literal(id))
        });
        match (key_ty, val_ty) {
            (Ok(k), Ok(v)) => Some(Checked {
                pres,
                ..Checked::bare(CelTy::map(k, v))
            }),
            (Err(message), _) | (_, Err(message)) => self.error(CheckError::at(id, message)),
        }
    }

    /// The desugared macro.
    ///
    /// `all`/`exists`/`exists_one`/`map`/`filter` are expanded by the parser into a fold
    /// (`parser/macros.rs`), so the checker never sees `all` as a call. It types the fold by its
    /// SHAPE rather than by walking the synthesized `@result` plumbing: the accumulator, the
    /// `@not_strictly_false` guard and the `_+_` append are the expander's, not the author's, and
    /// checking them would mean giving internal names public signatures.
    fn comprehension(&mut self, c: &ComprehensionExpr, id: u64) -> Option<Checked> {
        let entry = self.locals.len();
        let range = self.check(&c.iter_range)?;
        // A range that holds a `dyn` would bind one (or, over a map, iterate a container whose
        // values have no type). An empty literal's `dyn` is only its unpinned element type.
        if holds_dyn(&range.ty) && !unpinned(&c.iter_range) {
            let message = format!(
                "cannot iterate a value of type {}; a dyn value must be narrowed. \
                 {DYN_VALUES_REMOVED}",
                range.ty.name()
            );
            self.commit(range.path);
            return self.error(CheckError::at(id, message));
        }
        let (key_ty, elem_ty) = match &range.ty {
            CelTy::List(el) => (CelTy::Num, (**el).clone()),
            m if m.is_map() => {
                let (k, v) = m.map_parts().expect("a map");
                (k.clone(), v.clone())
            }
            // No `Dyn` arm: a range whose type is unknown is not iterable until it is narrowed.
            // Binding the iteration variable to `Dyn` here would silently type-check every field
            // access inside every comprehension body.
            other => {
                return self.error(CheckError::at(
                    id,
                    format!("cannot iterate a value of type {}", other.name()),
                ))
            }
        };
        // One-variable form binds the ELEMENT of a list and the KEY of a map. Getting this
        // backwards types every comprehension body wrong and nothing else notices.
        let bound = if range.ty.is_map() { key_ty } else { elem_ty };
        let range_path = range.path.clone();
        self.commit(range.path);
        let scope = self.next_scope;
        self.next_scope += 1;
        self.locals.push(Local {
            name: c.iter_var.clone(),
            ty: bound,
            range_path,
            scope,
            range_pres: range.pres,
        });
        if let Some(v2) = &c.iter_var2 {
            // `not implemented: two-variable comprehension macros` — the parser does not produce
            // one today, so reaching here means the expander changed and this arm is the bookmark.
            self.locals.truncate(entry);
            return self.error(CheckError::at(
                id,
                format!("two-variable comprehensions are not implemented (`{v2}`)"),
            ));
        }

        if is_empty_collection(&c.iter_range) {
            let result = self.empty_range_fold(c, id);
            self.locals.truncate(entry);
            return result;
        }

        let result = match classify(c) {
            Some(Fold::Predicate) => {
                let body = second_arg(&c.loop_step)?;
                let b = self.check(body)?;
                self.commit(b.path);
                self.expect(&b.ty, &CelTy::Bool, body.id, "comprehension body");
                Some(Checked::bare(CelTy::Bool))
            }
            Some(Fold::CountingPredicate) => {
                let body = first_arg(&c.loop_step)?;
                let b = self.check(body)?;
                self.commit(b.path);
                self.expect(&b.ty, &CelTy::Bool, body.id, "comprehension body");
                Some(Checked::bare(CelTy::Bool))
            }
            Some(Fold::Build) => {
                let (pred, appended) = build_parts(&c.loop_step)?;
                if let Some(p) = pred {
                    let pc = self.check(p)?;
                    self.commit(pc.path);
                    self.expect(&pc.ty, &CelTy::Bool, p.id, "comprehension predicate");
                }
                let e = self.check(appended)?;
                self.commit(e.path);
                if holds_dyn(&e.ty) && !unpinned(appended) {
                    self.locals.truncate(entry);
                    return self.error(CheckError::at(
                        appended.id,
                        format!(
                            "a `map` step of type {} builds a list of dyn values. \
                             {DYN_VALUES_REMOVED}",
                            e.ty.name()
                        ),
                    ));
                }
                Some(Checked::bare(CelTy::list(e.ty)))
            }
            None => {
                self.locals.truncate(entry);
                return self.error(CheckError::at(
                    id,
                    "unrecognised comprehension shape: the macro expander and the checker disagree",
                ));
            }
        };
        self.locals.truncate(entry);
        result
    }

    /// A fold over an EMPTY literal range: its body never runs, so the iteration variable is
    /// `dyn` and whatever the body's checking reports is discarded — the evaluator never reaches
    /// it either. The body is still walked, so the paths it names stay in the demand set. The
    /// result is the fold's type with no element to constrain it: `bool` for a predicate, and for
    /// `map`/`filter` an empty list, which [`adopt_empty`] then types from where it is used.
    fn empty_range_fold(&mut self, c: &ComprehensionExpr, id: u64) -> Option<Checked> {
        let Some(fold) = classify(c) else {
            return self.error(CheckError::at(
                id,
                "unrecognised comprehension shape: the macro expander and the checker disagree",
            ));
        };
        if let Some(l) = self.locals.last_mut() {
            l.ty = CelTy::Dyn;
        }
        let mark = self.errors.len();
        let unproven_mark = self.unproven.len();
        let parts: Vec<&IdedExpr> = match fold {
            Fold::Predicate => second_arg(&c.loop_step).into_iter().collect(),
            Fold::CountingPredicate => first_arg(&c.loop_step).into_iter().collect(),
            Fold::Build => match build_parts(&c.loop_step) {
                Some((pred, appended)) => pred.into_iter().chain([appended]).collect(),
                None => Vec::new(),
            },
        };
        for part in parts {
            if let Some(checked) = self.check(part) {
                self.commit(checked.path);
            }
        }
        self.errors.truncate(mark);
        self.unproven.truncate(unproven_mark);
        Some(Checked::bare(match fold {
            Fold::Predicate | Fold::CountingPredicate => CelTy::Bool,
            Fold::Build => CelTy::list(CelTy::Dyn),
        }))
    }

    /// Is `name` an iteration variable whose range is exactly the container at `container`? Then
    /// `container[name]` is present: the iteration only ever names keys the container holds.
    fn iterated_key(&self, name: &str, container: Option<&PresPath>) -> bool {
        let Some(container) = container else {
            return false;
        };
        self.locals
            .iter()
            .rev()
            .find(|l| l.name == name)
            .and_then(|l| l.range_pres.as_ref())
            .is_some_and(|range| range == container)
    }

    /// A read of key `key` on a container of type `container`, whose presence path is `pres`.
    /// Required record fields and `unsafe_map` keys need nothing; everything else must be proven
    /// present by a guard in force, by a known value, or by iterating the same container.
    fn require_present(
        &mut self,
        id: u64,
        container: &CelTy,
        pres: Option<&PresPath>,
        key: &str,
        read: impl Fn() -> Read,
    ) {
        let kind = match container {
            CelTy::Record(r) if r.is_optional(key) => AbsentKind::OptionalField,
            CelTy::Record(r) if r.get(key).is_none() && r.index.is_some() => AbsentKind::IndexKey,
            CelTy::Map(..) => AbsentKind::MapKey,
            // A required field, an `unsafe_map`'s key, anything else: nothing to prove.
            _ => return,
        };
        let Some(container) = pres else {
            return self.unproven(id, read(), kind, None);
        };
        let p = container.child(key);
        if self.proven.contains(&p) {
            return;
        }
        match self.known_presence(&p) {
            Some(true) => return,
            Some(false) => {
                let root = match &p.root {
                    PresRoot::Var(n) | PresRoot::Slot(n) => Some(format!("`{n}`")),
                    PresRoot::Literal(_) => Some("this map literal".to_string()),
                    PresRoot::Local(_) => None,
                };
                return self.unproven(id, read(), AbsentKind::KnownAbsent, root);
            }
            None => {}
        }
        self.unproven(id, read(), kind, None)
    }

    /// Record a read nothing proves present — and, when the rules are enforced, refuse it.
    /// `known_root` names the root whose KNOWN value lacks the key.
    fn unproven(&mut self, id: u64, read: Read, kind: AbsentKind, known_root: Option<String>) {
        if self.enforce_presence && refused(kind) {
            self.errors.push(CheckError::at(
                id,
                unproven_message(&read, kind, known_root.as_deref()),
            ));
        }
        self.unproven.push(Unproven {
            id,
            rendered: read.rendered,
            kind,
        });
    }

    /// Does the known value at `p`'s root hold `p`? `None` when the root is not known, or is a
    /// view served on access (it proves nothing).
    fn known_presence(&self, p: &PresPath) -> Option<bool> {
        let mut v = match &p.root {
            PresRoot::Var(name) => {
                let (bindings, roots) = self.known?;
                if !roots.contains(name) {
                    return None;
                }
                bindings.get(name)?
            }
            PresRoot::Slot(name) => self
                .slot_values
                .iter()
                .find(|(n, _)| &**n == name.as_str())
                .map(|(_, v)| v)?,
            PresRoot::Literal(id) => {
                // One level: a literal's own keys. A nested literal's keys are its own root.
                let written = self.literal_keys.get(id)?;
                return match p.keys.as_slice() {
                    [k] => Some(written.contains(&format!("s{k}"))),
                    _ => None,
                };
            }
            PresRoot::Local(_) => return None,
        };
        for k in &p.keys {
            match v {
                CelValue::Map(m) => match m.get(k) {
                    Some(next) => v = next,
                    None => return Some(false),
                },
                _ => return None,
            }
        }
        Some(true)
    }

    /// The presence path `e` names, resolved through the CURRENT locals, without checking it —
    /// facts are read off a subtree before that subtree is checked.
    fn pres_of(&self, e: &IdedExpr) -> Option<PresPath> {
        match &e.expr {
            Expr::Ident(name) => {
                if let Some(l) = self.locals.iter().rev().find(|l| l.name == *name) {
                    return Some(PresPath::root(PresRoot::Local(l.scope)));
                }
                if self.consts.iter().any(|(n, _)| n == name) {
                    return Some(PresPath::root(PresRoot::Slot(name.clone())));
                }
                self.env
                    .get(name)
                    .map(|_| PresPath::root(PresRoot::Var(name.clone())))
            }
            Expr::Map(m) => {
                literal_keys(&m.entries).map(|_| PresPath::root(PresRoot::Literal(e.id)))
            }
            Expr::Select(s) if !s.test => self.pres_of(&s.operand).map(|p| p.child(&s.field)),
            Expr::Call(c) if c.func_name == operators::INDEX && c.args.len() == 2 => {
                match &c.args[1].expr {
                    Expr::Literal(LiteralValue::String(k)) => {
                        self.pres_of(&c.args[0]).map(|p| p.child(k.inner()))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// `P(e)` when `when` is true, `N(e)` when false: the paths `e` proves present when it has
    /// that value. `has(p)` and `"k" in x` prove their path and every prefix; `!` swaps the two;
    /// `&&` unions its sides' `P`, `||` their `N`; nothing else proves anything.
    fn facts(&self, e: &IdedExpr, when: bool, out: &mut Vec<PresPath>) {
        match &e.expr {
            Expr::Select(s) if s.test && when => {
                if let Some(p) = self.pres_of(&s.operand).map(|p| p.child(&s.field)) {
                    out.extend(p.with_prefixes());
                }
            }
            Expr::Call(c) => match (c.func_name.as_str(), c.args.as_slice()) {
                (operators::LOGICAL_NOT, [a]) => self.facts(a, !when, out),
                (operators::LOGICAL_AND, [a, b]) if when => {
                    self.facts(a, true, out);
                    self.facts(b, true, out);
                }
                (operators::LOGICAL_OR, [a, b]) if !when => {
                    self.facts(a, false, out);
                    self.facts(b, false, out);
                }
                (operators::IN, [k, x]) if when => {
                    if let (Expr::Literal(LiteralValue::String(k)), Some(p)) =
                        (&k.expr, self.pres_of(x))
                    {
                        out.extend(p.child(k.inner()).with_prefixes());
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }

    /// The facts each argument of a call is checked under — the facts its SIBLINGS prove, never
    /// its own (a guard cannot prove the reads inside itself: `has(a.b)` reads `a`).
    ///
    /// `a && b` is `false` whenever either side is `false`, an error on the other side absorbed,
    /// so each side is checked with what the OTHER proves when true — order-insensitive. `a || b`
    /// likewise with what the other proves when false. `c ? t : f` checks `t` with `P(c)` and `f`
    /// with `N(c)`, and `c` with nothing: a conditional does not absorb an error in its condition.
    fn arg_facts(&self, c: &CallExpr) -> Vec<Vec<PresPath>> {
        let facts = |e: &IdedExpr, when: bool| {
            let mut out = Vec::new();
            self.facts(e, when, &mut out);
            out
        };
        match (c.func_name.as_str(), c.args.as_slice()) {
            (operators::LOGICAL_AND, [a, b]) => vec![facts(b, true), facts(a, true)],
            (operators::LOGICAL_OR, [a, b]) => vec![facts(b, false), facts(a, false)],
            (operators::CONDITIONAL, [cond, _, _]) => {
                vec![Vec::new(), facts(cond, true), facts(cond, false)]
            }
            _ => Vec::new(),
        }
    }

    fn expect(&mut self, actual: &CelTy, want: &CelTy, id: u64, what: &str) {
        if actual != want {
            self.errors.push(CheckError::at(
                id,
                format!(
                    "{what} must be {}, this one is {}",
                    want.name(),
                    actual.name()
                ),
            ));
        }
    }
}

/// Which fold the parser's macro expander produced.
pub(crate) enum Fold {
    /// `all` / `exists`: `loop_step` is `_&&_`/`_||_`(@result, PREDICATE).
    Predicate,
    /// `exists_one`: `loop_step` is `_?_:_`(PREDICATE, @result + 1, @result).
    CountingPredicate,
    /// `map` / `filter`: `loop_step` appends to a list, optionally under a filter.
    Build,
}

pub(crate) fn classify(c: &ComprehensionExpr) -> Option<Fold> {
    match &c.accu_init.expr {
        Expr::Literal(LiteralValue::Boolean(_)) => Some(Fold::Predicate),
        Expr::Literal(LiteralValue::Int(_)) => Some(Fold::CountingPredicate),
        Expr::List(l) if l.elements.is_empty() => Some(Fold::Build),
        _ => None,
    }
}

pub(crate) fn first_arg(e: &IdedExpr) -> Option<&IdedExpr> {
    match &e.expr {
        Expr::Call(c) => c.args.first(),
        _ => None,
    }
}

pub(crate) fn second_arg(e: &IdedExpr) -> Option<&IdedExpr> {
    match &e.expr {
        Expr::Call(c) => c.args.get(1),
        _ => None,
    }
}

/// `(filter?, appended)` from a `map`/`filter` fold's step.
///
/// `filter(x, p)` and the three-argument `map(x, p, e)` both wrap the append in a conditional;
/// two-argument `map` does not.
pub(crate) fn build_parts(step: &IdedExpr) -> Option<(Option<&IdedExpr>, &IdedExpr)> {
    let (pred, add) = match &step.expr {
        Expr::Call(c) if c.func_name == operators::CONDITIONAL && c.args.len() == 3 => {
            (Some(&c.args[0]), &c.args[1])
        }
        _ => (None, step),
    };
    let appended = match &add.expr {
        Expr::Call(c) if c.func_name == operators::ADD && c.args.len() == 2 => {
            match &c.args[1].expr {
                Expr::List(l) if l.elements.len() == 1 => &l.elements[0],
                _ => return None,
            }
        }
        _ => return None,
    };
    Some((pred, appended))
}

fn literal_ty(v: &LiteralValue) -> CelTy {
    match v {
        LiteralValue::Boolean(_) => CelTy::Bool,
        LiteralValue::Bytes(_) => CelTy::Bytes,
        // ONE numeric type. An integer literal is a `Num` (held exactly as an integer), which is
        // what makes `body.amount > 100` and `100 < body.amount` both compile against a `Num` field.
        LiteralValue::Double(_) | LiteralValue::Int(_) | LiteralValue::UInt(_) => CelTy::Num,
        LiteralValue::Null => CelTy::Null,
        LiteralValue::String(_) => CelTy::Str,
    }
}

/// Is `e` a collection that is empty whatever its context: `[]`, `{}`, or a `map`/`filter` over one.
///
/// Such a value has no element to type it, so the checker gives it the element type its use asks
/// for — the fresh type variable the cel-spec checker would give it — rather than `dyn`, which
/// nothing accepts. Only these: a non-empty literal keeps its joined element type.
fn is_empty_collection(e: &IdedExpr) -> bool {
    match &e.expr {
        Expr::List(l) => l.elements.is_empty(),
        Expr::Map(m) => m.entries.is_empty(),
        Expr::Comprehension(c) => {
            matches!(classify(c), Some(Fold::Build)) && is_empty_collection(&c.iter_range)
        }
        _ => false,
    }
}

/// Is `e` a collection literal none of whose element types is pinned — `[]`, `{}`, `[[]]`,
/// `{"k": []}`, a `map`/`filter` over one?
///
/// Its `dyn` is an element type nothing has fixed yet, not a value: no element of it can be read,
/// because there is none. `removed: dyn values` refuses a `dyn` VALUE, so these are exempt from
/// it, and a literal member that is one takes its siblings' type.
fn unpinned(e: &IdedExpr) -> bool {
    match &e.expr {
        Expr::List(l) => l.elements.iter().all(unpinned),
        Expr::Map(m) => m.entries.iter().all(|entry| {
            let EntryExpr::MapEntry(me) = &entry.expr;
            unpinned(&me.value)
        }),
        Expr::Comprehension(c) => {
            matches!(classify(c), Some(Fold::Build)) && is_empty_collection(&c.iter_range)
        }
        _ => false,
    }
}

/// Type each empty-collection argument of a call from its use: the element type of `x in []` is
/// `x`'s type, and otherwise an empty argument takes the type of a sibling argument of the same
/// container kind (`[] == body.tags`). An empty argument with nothing to take a type from keeps
/// `list(dyn)`/`map(dyn, dyn)`, which a generic signature (`size`) still accepts.
fn adopt_empty(func: &str, exprs: &[&IdedExpr], args: &mut [Checked]) {
    if exprs.len() != args.len() {
        return;
    }
    for i in 0..args.len() {
        if !is_empty_collection(exprs[i]) {
            continue;
        }
        let adopted = if func == operators::IN && i == 1 {
            match &args[1].ty {
                CelTy::List(_) => Some(CelTy::list(args[0].ty.clone())),
                m if m.is_map() => Some(CelTy::map(args[0].ty.clone(), CelTy::Dyn)),
                _ => None,
            }
        } else {
            (0..args.len())
                .filter(|&j| j != i && !is_empty_collection(exprs[j]))
                .map(|j| &args[j].ty)
                .find(|t| {
                    matches!((&args[i].ty, t), (CelTy::List(_), CelTy::List(_)))
                        || (args[i].ty.is_map() && t.is_map())
                })
                .cloned()
        };
        if let Some(ty) = adopted {
            args[i].ty = ty;
        }
    }
}

/// The README "Removed" or "Divergences" row a missing overload IS, when it is one: an operator
/// the dialect keeps, applied to a kind it deliberately does not extend to. `None` for an ordinary type error
/// (`'a' < 1`), which is a mistake rather than a construct.
fn removed_row(func: &str, tys: &[CelTy]) -> Option<&'static str> {
    let orderable = |t: &CelTy| matches!(t, CelTy::Num | CelTy::Str | CelTy::Duration);
    match func {
        operators::EQUALS | operators::NOT_EQUALS => Some("diverges: equality is homogeneous"),
        "duration" => Some("diverges: duration() takes a string"),
        operators::LESS
        | operators::LESS_EQUALS
        | operators::GREATER
        | operators::GREATER_EQUALS
            if tys.iter().any(|t| !orderable(t)) =>
        {
            Some("removed: ordering beyond numbers and strings")
        }
        operators::LOGICAL_AND | operators::LOGICAL_OR | operators::LOGICAL_NOT
            if tys.iter().any(|t| *t != CelTy::Bool) =>
        {
            Some("removed: logic on non-bools")
        }
        operators::ADD if tys.iter().all(|t| *t == CelTy::Bytes) => {
            Some("removed: bytes concatenation")
        }
        _ => None,
    }
}

/// Where an undeclared variable or unknown function points: spec CEL defers both to evaluation.
const UNDECLARED: &str = "See `diverges: undeclared names are compile errors` in README.md";

/// Where every `removed: dyn values` refusal points.
const DYN_VALUES_REMOVED: &str = "See `removed: dyn values` in README.md";

/// Does a value of this type hand out a `dyn` to whatever uses it?
///
/// Through lists and maps — a `list(dyn)` yields `dyn` elements — but NOT into a record. A
/// record's members are typed one by one, and a member declared `unknown` is refused where it is
/// SELECTED and used; refusing every use of the record around it would make a whole body
/// unusable for one member nobody reads.
fn holds_dyn(t: &CelTy) -> bool {
    match t {
        CelTy::Dyn => true,
        CelTy::List(e) => holds_dyn(e),
        m if m.is_map() => {
            let (k, v) = m.map_parts().expect("a map");
            holds_dyn(k) || holds_dyn(v)
        }
        _ => false,
    }
}

/// The element (or key, or value) type of a collection literal, built one member at a time.
///
/// Every member must have ONE type (`removed: dyn values`): there is no least-upper-bound to widen
/// to, because the only one is `dyn`. An EMPTY member (`[]`, `{}`) has no element type of its own,
/// so it takes the type of its siblings of the same kind.
#[derive(Default)]
struct Element {
    ty: Option<CelTy>,
    /// Empty collection members, by id, with the placeholder type they checked at.
    empty: Vec<(u64, CelTy)>,
    kind: (&'static str, &'static str),
}

impl Element {
    fn admit(
        &mut self,
        e: &IdedExpr,
        ty: CelTy,
        literal: &'static str,
        members: &'static str,
    ) -> Result<(), String> {
        self.kind = (literal, members);
        if unpinned(e) {
            self.empty.push((e.id, ty));
            return Ok(());
        }
        if holds_dyn(&ty) {
            return Err(format!(
                "a {literal} literal's {members} cannot be of type {}; a dyn value must be \
                 narrowed. {DYN_VALUES_REMOVED}",
                ty.name()
            ));
        }
        // A `map` and an `unsafe_map` of the same parts are one shape; their join is the `map`.
        match self.ty.as_ref().map(|prev| (prev.join_shape(&ty), prev)) {
            None => self.ty = Some(ty),
            Some((Some(joined), _)) => self.ty = Some(joined),
            Some((None, prev)) => return Err(heterogeneous(literal, members, prev, &ty)),
        }
        Ok(())
    }

    /// The one member type. An empty member adopts it, and its adopted type is what a specializer
    /// holds its value at.
    fn finish(self, types: &mut Option<HashMap<u64, CelTy>>) -> Result<CelTy, String> {
        let (literal, members) = self.kind;
        let Some(ty) = self.ty else {
            // Nothing but empty members (or nothing at all): the placeholder stands, to be pinned
            // by the use, as for a lone `[]`.
            return Ok(self
                .empty
                .into_iter()
                .next()
                .map(|(_, t)| t)
                .unwrap_or(CelTy::Dyn));
        };
        for (id, placeholder) in self.empty {
            let same_kind = matches!((&placeholder, &ty), (CelTy::List(_), CelTy::List(_)))
                || (placeholder.is_map() && ty.is_map());
            if !same_kind {
                return Err(heterogeneous(literal, members, &ty, &placeholder));
            }
            if let Some(types) = types.as_mut() {
                types.insert(id, ty.clone());
            }
        }
        Ok(ty)
    }
}

fn heterogeneous(literal: &str, members: &str, a: &CelTy, b: &CelTy) -> String {
    format!(
        "heterogeneous {literal} literal: {members} of type {} and {}; a {literal}'s {members} \
         must share one type. {DYN_VALUES_REMOVED}",
        a.name(),
        b.name()
    )
}

/// A function name as an author would read it. `_>_` is `>`; `@in` is `in`.
fn spell(name: &str) -> String {
    if let Some(op) = name.strip_prefix('@') {
        return op.to_string();
    }
    let trimmed = name.trim_matches('_');
    if trimmed.is_empty() || trimmed == name {
        name.to_string()
    } else {
        trimmed.to_string()
    }
}

fn describe(e: &IdedExpr) -> String {
    match &e.expr {
        Expr::Ident(n) => format!("`{n}`"),
        _ => "here".to_string(),
    }
}

/// Does a presence question for `key` on a value of type `ty` name a key the type does not
/// declare — any key of a map, or a key only a record's index signature covers?
fn names_an_open_key(ty: &CelTy, key: &str) -> bool {
    match ty {
        m if m.is_map() => true,
        CelTy::Record(r) => r.index.is_some() && r.get(key).is_none(),
        _ => false,
    }
}

/// A read's operand as the author wrote it — a root, fields, literal keys — or `<expression>` for
/// anything else (a conditional, a call's result): the operand of a read that only a TYPE can
/// prove present.
fn render(e: &IdedExpr) -> String {
    match &e.expr {
        Expr::Ident(name) => name.clone(),
        Expr::Select(s) if !s.test => format!("{}.{}", render(&s.operand), s.field),
        Expr::Call(c) if c.func_name == operators::INDEX && c.args.len() == 2 => {
            match &c.args[1].expr {
                Expr::Literal(LiteralValue::String(k)) => {
                    format!("{}[{:?}]", render(&c.args[0]), k.inner())
                }
                _ => format!("{}[{}]", render(&c.args[0]), render(&c.args[1])),
            }
        }
        Expr::Literal(LiteralValue::Int(i)) => i.to_string(),
        Expr::Literal(LiteralValue::UInt(u)) => format!("{u}u"),
        Expr::Literal(LiteralValue::Double(d)) => format!("{:?}", d.inner()),
        Expr::Literal(LiteralValue::Boolean(b)) => b.inner().to_string(),
        Expr::Literal(LiteralValue::Null) => "null".to_string(),
        Expr::Map(_) => "{…}".to_string(),
        _ => "<expression>".to_string(),
    }
}

/// A read, as the author wrote it — what a presence diagnostic quotes and how its fix is spelled.
pub(crate) struct Read {
    /// `body.discount`, `m["k"]`.
    rendered: String,
    /// The operand read FROM: `body`, `m`.
    container: String,
    /// The key read, when it is a literal.
    key: Option<String>,
    /// A field select (`x.k`, fixed with `has(x.k)`) rather than an index (`x["k"]`, fixed with
    /// `'k' in x`).
    select: bool,
}

impl Read {
    fn select(operand: &IdedExpr, field: &str) -> Read {
        let container = render(operand);
        Read {
            rendered: format!("{container}.{field}"),
            container,
            key: Some(field.to_string()),
            select: true,
        }
    }

    fn index(operand: &IdedExpr, key: &str) -> Read {
        let container = render(operand);
        Read {
            rendered: format!("{container}[{key:?}]"),
            container,
            key: Some(key.to_string()),
            select: false,
        }
    }

    /// The two guards that prove this read: `(when present, when absent)`.
    fn fixes(&self) -> (String, String) {
        match &self.key {
            Some(_) if self.select => (
                format!("has({}) && …", self.rendered),
                format!("!has({}) || …", self.rendered),
            ),
            Some(k) => (
                format!("{k:?} in {} && …", self.container),
                format!("!({k:?} in {}) || …", self.container),
            ),
            None => (
                format!(
                    "iterate `{}` and index it with the iteration variable",
                    self.container
                ),
                format!("write the key out and guard it with `in`"),
            ),
        }
    }
}

/// Which kinds are refused at compile time: every one.
fn refused(_: AbsentKind) -> bool {
    true
}

/// The keys of a map literal, canonical ([`literal_key`]), when every one is a literal a map key
/// can be.
fn literal_keys(entries: &[crate::common::ast::IdedEntryExpr]) -> Option<BTreeSet<String>> {
    entries
        .iter()
        .map(|entry| {
            let EntryExpr::MapEntry(e) = &entry.expr;
            match &e.key.expr {
                Expr::Literal(v) => literal_key(v),
                _ => None,
            }
        })
        .collect()
}

/// A literal as the map key the runtime makes of it, spelled so two literals naming ONE key spell
/// alike: there is one number type, so `1`, `1u` and `1.0` are the same key, and `1.5` is none.
/// `None` for a literal no map key can be.
fn literal_key(v: &LiteralValue) -> Option<String> {
    match v {
        LiteralValue::String(s) => Some(format!("s{}", s.inner())),
        LiteralValue::Boolean(b) => Some(format!("b{}", b.inner())),
        LiteralValue::Int(i) => Some(format!("n{i}")),
        LiteralValue::UInt(u) => i64::try_from(*u).ok().map(|i| format!("n{i}")),
        LiteralValue::Double(d) => {
            let d: f64 = *d.inner();
            (d.fract() == 0.0 && d.abs() < 9.2e18).then(|| format!("n{}", d as i64))
        }
        _ => None,
    }
}

/// Where every presence refusal points.
const PROVEN_PRESENCE: &str = "See `added: proven presence` in README.md";

fn unproven_message(read: &Read, kind: AbsentKind, known_root: Option<&str>) -> String {
    let r = &read.rendered;
    let (present, absent) = read.fixes();
    let why = match kind {
        AbsentKind::OptionalField => "its schema declares it optional".to_string(),
        AbsentKind::IndexKey => format!(
            "`{}` declares no such field; only its index signature allows the key",
            read.container
        ),
        AbsentKind::MapKey => "a map need not hold any key".to_string(),
        AbsentKind::KnownAbsent => {
            return format!(
                "`{r}` is absent: the KNOWN value of {} has no such key. Guard it (`{present}`) \
                 or fix the key. {PROVEN_PRESENCE}",
                known_root.unwrap_or("its root")
            )
        }
    };
    format!(
        "`{r}` may be absent ({why}) and nothing here proves it present; write `{present}` or \
         `{absent}`. {PROVEN_PRESENCE}"
    )
}
