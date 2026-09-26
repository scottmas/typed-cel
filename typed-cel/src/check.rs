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

use std::collections::{BTreeMap, HashMap};

use crate::common::ast::{
    operators, CallExpr, ComprehensionExpr, EntryExpr, Expr, IdedExpr, LiteralValue, SelectExpr,
};
use crate::demand::{DemandSet, Segment};
use crate::sigs::{self, Lookup};
use crate::ty::{CelTy, Record};

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
    ("uint", "`uint` is removed: every number in this dialect is a double"),
    ("int", "`int()` is removed: every number in this dialect is a double. See `removed: type conversion functions` in README.md"),
    ("bool", "`bool()` is removed: a string is not a truth value in this dialect. See `removed: type conversion functions` in README.md"),
    ("string", "`string()` is removed: it is lossy on bytes and redundant elsewhere. See `removed: type conversion functions` in README.md"),
    ("double", "`double()` is removed: every number in this dialect is already a double. See `removed: type conversion functions` in README.md"),
    ("type", "there are no type values in this dialect. See `removed: type values` in README.md"),
    ("list", "there are no type values in this dialect. See `removed: type values` in README.md"),
    ("map", "there are no type values in this dialect. See `removed: type values` in README.md"),
    ("bytes", "`bytes()` is removed: a string literal's bytes are written `b'…'`. See `removed: type conversion functions` in README.md"),
    ("null_type", "there are no type values in this dialect. See `removed: type values` in README.md"),
    ("optional", "optional syntax is removed: every declared path is present in the activation. See `removed: optional syntax` in README.md"),
    ("orValue", "optional syntax is removed: every declared path is present in the activation. See `removed: optional syntax` in README.md"),
    ("_%_", "`%` is removed: every number in this dialect is a double, and no program needs a floating-point remainder. See `removed: modulo` in README.md"),
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
}

impl Checked {
    fn bare(ty: CelTy) -> Checked {
        Checked { ty, path: None }
    }
}

/// A comprehension variable in scope, with the path its range names.
struct Local {
    name: String,
    ty: CelTy,
    /// The demand path of the map this variable iterates, when it iterates one. A computed key is
    /// legal ONLY where this proves the iteration is over that same map.
    range_path: Option<Vec<Segment>>,
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
    /// The type of every node checked, by expression id, when [`Checker::run_typed`] asked for it.
    types: Option<HashMap<u64, CelTy>>,
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
    pub(crate) fn run_typed(
        mut self,
        e: &IdedExpr,
    ) -> Result<(CelTy, DemandSet, HashMap<u64, CelTy>), Vec<CheckError>> {
        self.types = Some(HashMap::new());
        self.run_inner(e)
            .map(|(ty, demand, types)| (ty, demand, types.unwrap_or_default()))
    }

    #[allow(clippy::type_complexity)]
    fn run_inner(
        mut self,
        e: &IdedExpr,
    ) -> Result<(CelTy, DemandSet, Option<HashMap<u64, CelTy>>), Vec<CheckError>> {
        let checked = self.check(e);
        if let Some(c) = &checked {
            self.commit(c.path.clone());
        }
        if !self.errors.is_empty() {
            return Err(self.errors);
        }
        match checked {
            Some(c) => {
                self.demand.finish();
                Ok((c.ty, self.demand, self.types))
            }
            // `check` returning `None` with no error recorded is a checker bug, not a policy one.
            None => Err(vec![CheckError::at(e.id, "expression has no type")]),
        }
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
            });
        }
        if let Some((_, t)) = self.consts.iter().find(|(n, _)| n == name) {
            return Some(Checked::bare(t.clone()));
        }
        match self.env.get(name) {
            Some(t) => Some(Checked {
                ty: t.clone(),
                path: Some(vec![Segment::Root(name.to_string())]),
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
        match &operand.ty {
            CelTy::Record(r) => match r.field_or_index(&s.field) {
                // THE diagnostic this whole crate exists to produce.
                None => self.unknown_field(&s.field, r, id),
                Some(t) => Some(Checked {
                    ty: t.clone(),
                    path,
                }),
            },
            // A map has no declared field set, so a select is the value type.
            CelTy::Map(_, v) => Some(Checked {
                ty: (**v).clone(),
                path,
            }),
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
        let mut checked_arg =
            |this: &mut Self, e: &IdedExpr, args: &mut Vec<Checked>| match this.check(e) {
                Some(c) => args.push(c),
                None => failed = true,
            };
        if let Some(target) = &c.target {
            checked_arg(self, target, &mut args);
        }
        for a in &c.args {
            checked_arg(self, a, &mut args);
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
                    matches!(&args[1].ty, CelTy::Map(..))
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
                            .all(|(p, a)| p == a && !a.requires_narrowing())
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
                if c.func_name == operators::CONDITIONAL && tys.len() == 3 && tys[1] != tys[2] {
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

    /// `_[_]`. There is no optional form — every path an expression may name is present in the
    /// activation, so an index that misses is a policy error, not a runtime case.
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
                            let path = target.path.map(|mut p| {
                                p.push(Segment::Key(k.inner().to_string()));
                                p
                            });
                            Some(Checked { ty, path })
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
            _ if target.path.is_some() && matches!(target.ty, CelTy::Map(..)) => {
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
            Lookup::Ok(ty) => Some(Checked { ty, path }),
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
        match (key_ty, val_ty) {
            (Ok(k), Ok(v)) => Some(Checked::bare(CelTy::map(k, v))),
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
            CelTy::Map(k, v) => ((**k).clone(), (**v).clone()),
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
        let bound = if matches!(range.ty, CelTy::Map(..)) {
            key_ty
        } else {
            elem_ty
        };
        let range_path = range.path.clone();
        self.commit(range.path);
        self.locals.push(Local {
            name: c.iter_var.clone(),
            ty: bound,
            range_path,
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
        Some(Checked::bare(match fold {
            Fold::Predicate | Fold::CountingPredicate => CelTy::Bool,
            Fold::Build => CelTy::list(CelTy::Dyn),
        }))
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
        // ONE numeric type. An integer literal is a double, which is what makes `body.amount > 100`
        // and `100 < body.amount` both compile against a `Num` field.
        LiteralValue::Double(_) | LiteralValue::Int(_) => CelTy::Num,
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
                CelTy::Map(..) => Some(CelTy::map(args[0].ty.clone(), CelTy::Dyn)),
                _ => None,
            }
        } else {
            (0..args.len())
                .filter(|&j| j != i && !is_empty_collection(exprs[j]))
                .map(|j| &args[j].ty)
                .find(|t| {
                    matches!(
                        (&args[i].ty, t),
                        (CelTy::List(_), CelTy::List(_)) | (CelTy::Map(..), CelTy::Map(..))
                    )
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
        CelTy::Map(k, v) => holds_dyn(k) || holds_dyn(v),
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
        match &self.ty {
            None => self.ty = Some(ty),
            Some(prev) if *prev == ty => {}
            Some(prev) => return Err(heterogeneous(literal, members, prev, &ty)),
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
            let same_kind = matches!(
                (&placeholder, &ty),
                (CelTy::List(_), CelTy::List(_)) | (CelTy::Map(..), CelTy::Map(..))
            );
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
        CelTy::Map(..) => true,
        CelTy::Record(r) => r.index.is_some() && r.get(key).is_none(),
        _ => false,
    }
}
