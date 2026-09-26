//! The signature table: the dialect, enforced.
//!
//! What `_==_`, `_>_`, `duration`, `endsWith` and friends accept and return. The table IS the
//! `README.md` "Signatures" section in executable form, and `tests/signatures.rs` compares the two
//! in BOTH directions — a hand-maintained doc beside a hand-maintained table drifts within a
//! month.
//!
//! Making it a CLOSED enumeration is what turns "outside the dialect" into a structural error
//! rather than a thing someone remembers. There is no `_ => Dyn` arm for an unrecognised name:
//! an unknown function is an error, because the alternative makes `is_owner(body.user_id)`
//! silently valid and the policy then enforces something nobody implemented.
//!
//! `size()` over a string is absent HERE, which is where `removed: size() on strings` is actually
//! enforced — the arm is shared with lists and maps in the evaluator, so the rejection has to come
//! from the checker or not at all.

use crate::ty::CelTy;

/// A scalar in a signature. Deliberately NOT [`CelTy`]: the table is a `static`, and `CelTy`
/// carries `Rc`s, so it is neither `Sync` nor promotable to `'static`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Prim {
    Bool,
    Num,
    Str,
    Duration,
}

impl Prim {
    fn ty(self) -> CelTy {
        match self {
            Prim::Bool => CelTy::Bool,
            Prim::Num => CelTy::Num,
            Prim::Str => CelTy::Str,
            Prim::Duration => CelTy::Duration,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Prim::Bool => "bool",
            Prim::Num => "double",
            Prim::Str => "string",
            Prim::Duration => "duration",
        }
    }
}

/// One position in a signature.
///
/// `Var` is a type VARIABLE, not a wildcard: every `T` in one signature unifies to the same type,
/// which is what makes `(T, T) -> bool` reject `body.amount == session.user_id` instead of
/// accepting everything.
#[derive(Debug)]
pub(crate) enum P {
    Prim(Prim),
    Var(char),
    List(&'static P),
    Map(&'static P, &'static P),
}

impl P {
    /// How the position reads in the README table. The test parses these back.
    pub(crate) fn render(&self) -> String {
        match self {
            P::Prim(p) => p.name().to_string(),
            P::Var(c) => c.to_string(),
            P::List(e) => format!("list({})", e.render()),
            P::Map(k, v) => format!("map({}, {})", k.render(), v.render()),
        }
    }

    /// Unify this position against an actual type, extending `binds`.
    fn unify(&self, actual: &CelTy, binds: &mut Vec<(char, CelTy)>) -> bool {
        match self {
            P::Prim(p) => *actual == p.ty(),
            P::Var(c) => match binds.iter().find(|(n, _)| n == c) {
                Some((_, bound)) => bound == actual,
                None => {
                    binds.push((*c, actual.clone()));
                    true
                }
            },
            P::List(e) => match actual {
                CelTy::List(el) => e.unify(el, binds),
                _ => false,
            },
            P::Map(k, v) => match actual {
                CelTy::Map(ak, av) => k.unify(ak, binds) && v.unify(av, binds),
                _ => false,
            },
        }
    }

    /// The concrete type this position denotes once `binds` is known.
    fn instantiate(&self, binds: &[(char, CelTy)]) -> Option<CelTy> {
        Some(match self {
            P::Prim(p) => p.ty(),
            P::Var(c) => binds.iter().find(|(n, _)| n == c)?.1.clone(),
            P::List(e) => CelTy::list(e.instantiate(binds)?),
            P::Map(k, v) => CelTy::map(k.instantiate(binds)?, v.instantiate(binds)?),
        })
    }
}

/// One overload.
///
/// For a MEMBER overload `params[0]` is the target, so `string.endsWith(string) -> bool` is
/// `params: [Str, Str], member: true`. Uniform params keep unification in one place; only the
/// rendering distinguishes the two spellings.
#[derive(Debug)]
pub(crate) struct Sig {
    pub params: &'static [P],
    pub ret: &'static P,
    pub member: bool,
}

impl Sig {
    /// `(double, double) -> bool`, or `string.endsWith(string) -> bool`.
    pub(crate) fn render(&self, name: &str) -> String {
        if self.member {
            let args: Vec<String> = self.params[1..].iter().map(P::render).collect();
            format!(
                "{}.{name}({}) -> {}",
                self.params[0].render(),
                args.join(", "),
                self.ret.render()
            )
        } else {
            let args: Vec<String> = self.params.iter().map(P::render).collect();
            format!("({}) -> {}", args.join(", "), self.ret.render())
        }
    }
}

const T: P = P::Var('T');
const K: P = P::Var('K');
const V: P = P::Var('V');
const BOOL: P = P::Prim(Prim::Bool);
const NUM: P = P::Prim(Prim::Num);
const STR: P = P::Prim(Prim::Str);
const DUR: P = P::Prim(Prim::Duration);
const LIST_T: P = P::List(&P::Var('T'));
const MAP_KV: P = P::Map(&P::Var('K'), &P::Var('V'));

/// `(T, T) -> bool`. Equality is homogeneous because every number is one type, so there is no
/// int/double/uint split to reconcile.
static EQ: &[Sig] = &[Sig {
    params: &[T, T],
    ret: &BOOL,
    member: false,
}];

/// Ordering: numbers, strings, durations. A `Duration` is its own ordering — collapsing it into
/// `Num` would make `elapsed > 300` check and mean 300 of whatever unit the evaluator carries.
static ORD: &[Sig] = &[
    Sig {
        params: &[NUM, NUM],
        ret: &BOOL,
        member: false,
    },
    Sig {
        params: &[STR, STR],
        ret: &BOOL,
        member: false,
    },
    Sig {
        params: &[DUR, DUR],
        ret: &BOOL,
        member: false,
    },
];

static LOGICAL: &[Sig] = &[Sig {
    params: &[BOOL, BOOL],
    ret: &BOOL,
    member: false,
}];

static NUM_NUM: &[Sig] = &[Sig {
    params: &[NUM, NUM],
    ret: &NUM,
    member: false,
}];

static STR_PRED: &[Sig] = &[Sig {
    params: &[STR, STR],
    ret: &BOOL,
    member: true,
}];

/// Every function name the dialect knows, and nothing else.
///
/// Names beginning with `@` are produced by macro desugaring; `@in` is the one an author writes
/// (`x in y`). The other synthesized nodes — `@not_strictly_false`, the `@result` accumulator —
/// never reach the table, because the checker types a comprehension by its FOLD SHAPE rather than
/// by walking the plumbing the expander emitted.
pub(crate) static SIGNATURES: &[(&str, &[Sig])] = &[
    ("_==_", EQ),
    ("_!=_", EQ),
    ("_<_", ORD),
    ("_<=_", ORD),
    ("_>_", ORD),
    ("_>=_", ORD),
    ("_&&_", LOGICAL),
    ("_||_", LOGICAL),
    (
        "!_",
        &[Sig {
            params: &[BOOL],
            ret: &BOOL,
            member: false,
        }],
    ),
    (
        "-_",
        &[Sig {
            params: &[NUM],
            ret: &NUM,
            member: false,
        }],
    ),
    (
        "_?_:_",
        &[Sig {
            params: &[BOOL, T, T],
            ret: &T,
            member: false,
        }],
    ),
    // Addition is the widest operator in the dialect and it is still four rows: numbers, strings,
    // list concatenation, and duration spans.
    (
        "_+_",
        &[
            Sig {
                params: &[NUM, NUM],
                ret: &NUM,
                member: false,
            },
            Sig {
                params: &[STR, STR],
                ret: &STR,
                member: false,
            },
            Sig {
                params: &[LIST_T, LIST_T],
                ret: &LIST_T,
                member: false,
            },
            Sig {
                params: &[DUR, DUR],
                ret: &DUR,
                member: false,
            },
        ],
    ),
    // `Duration * Num` is deliberately absent: every such addition widens a surface where the
    // internal unit (nanoseconds, via `chrono::TimeDelta`) can leak into a policy's arithmetic.
    // Durations are compared and added.
    (
        "_-_",
        &[
            Sig {
                params: &[NUM, NUM],
                ret: &NUM,
                member: false,
            },
            Sig {
                params: &[DUR, DUR],
                ret: &DUR,
                member: false,
            },
        ],
    ),
    ("_*_", NUM_NUM),
    ("_/_", NUM_NUM),
    // A literal-key index into a RECORD is checked field access and never reaches the table —
    // `removed: optional syntax` means there is no `_[?_]` either.
    (
        "_[_]",
        &[
            Sig {
                params: &[LIST_T, NUM],
                ret: &T,
                member: false,
            },
            Sig {
                params: &[MAP_KV, K],
                ret: &V,
                member: false,
            },
        ],
    ),
    (
        "@in",
        &[
            Sig {
                params: &[T, LIST_T],
                ret: &BOOL,
                member: false,
            },
            Sig {
                params: &[K, MAP_KV],
                ret: &BOOL,
                member: false,
            },
        ],
    ),
    // One constructor, and `timestamp` is ABSENT — its absence is structural, not an omission.
    (
        "duration",
        &[Sig {
            params: &[STR],
            ret: &DUR,
            member: false,
        }],
    ),
    (
        "getSeconds",
        &[Sig {
            params: &[DUR],
            ret: &NUM,
            member: true,
        }],
    ),
    (
        "getMilliseconds",
        &[Sig {
            params: &[DUR],
            ret: &NUM,
            member: true,
        }],
    ),
    // Over a LIST or MAP only. The string arm is `removed: size() on strings`.
    (
        "size",
        &[
            Sig {
                params: &[LIST_T],
                ret: &NUM,
                member: false,
            },
            Sig {
                params: &[MAP_KV],
                ret: &NUM,
                member: false,
            },
            Sig {
                params: &[LIST_T],
                ret: &NUM,
                member: true,
            },
            Sig {
                params: &[MAP_KV],
                ret: &NUM,
                member: true,
            },
        ],
    ),
    ("startsWith", STR_PRED),
    ("endsWith", STR_PRED),
    ("contains", STR_PRED),
    ("matches", STR_PRED),
];

/// Is `name` in the table? The one list of the dialect's function names — a host function is
/// refused any of them, and never by a second copy of the list.
pub(crate) fn is_builtin(name: &str) -> bool {
    SIGNATURES.iter().any(|(n, _)| *n == name)
}

/// The outcome of looking a call up in the table.
pub(crate) enum Lookup {
    /// One overload matched; this is what it returns.
    Ok(CelTy),
    /// The name is in the table and no overload accepts these argument types.
    NoOverload,
    /// The name is not in the table at all. A DIFFERENT diagnostic: the author wrote a function
    /// this dialect does not have, rather than the wrong arguments to one it does.
    UnknownFunction,
}

/// Resolve `name` against `args`. For a member call `args[0]` is the target.
pub(crate) fn resolve(name: &str, args: &[CelTy], member: bool) -> Lookup {
    let Some((_, sigs)) = SIGNATURES.iter().find(|(n, _)| *n == name) else {
        return Lookup::UnknownFunction;
    };
    for sig in *sigs {
        if let Some(ty) = sig.accepts(args, member) {
            return Lookup::Ok(ty);
        }
    }
    Lookup::NoOverload
}

impl Sig {
    /// This overload's result for `args`, when it accepts them.
    fn accepts(&self, args: &[CelTy], member: bool) -> Option<CelTy> {
        if self.member != member || self.params.len() != args.len() {
            return None;
        }
        let mut binds = Vec::new();
        if self
            .params
            .iter()
            .zip(args)
            .all(|(p, a)| p.unify(a, &mut binds))
        {
            self.ret.instantiate(&binds)
        } else {
            None
        }
    }
}

/// Every `(name, rendered overload)` pair, for the README cross-check.
pub(crate) fn rendered() -> Vec<(&'static str, Vec<String>)> {
    SIGNATURES
        .iter()
        .map(|(name, sigs)| (*name, sigs.iter().map(|s| s.render(name)).collect()))
        .collect()
}
