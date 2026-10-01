//! The ablation. Prints tables; asserts EQUAL VERDICTS across every leg before timing anything, and
//! nothing about time. Methodology and results: ../../docs/PERFORMANCE.md.
//!
//!     ablation --bench                      one run: raw `@` rows, then the rendered tables
//!     ablation --combine a.txt b.txt c.txt  the median of several runs' medians, rendered
//!     ablation --combine … --historical h1.txt h2.txt h3.txt
//!                                           …with the headline's column (2) from older runs
//!
//! Columns:
//!   Rust                hand-written Rust over the same typed request struct — the floor
//!   (1) upstream        cel-rust 0.14.2 from crates.io, `Program::execute` over a bound `Context`
//!   (2) typed tree      this crate's tree evaluator on the typed dialect — deleted; its numbers
//!                       are the historical ones in PERFORMANCE.md
//!   (3a) bytecode, act. `Vm::eval` over the same bound `CelActivation`
//!   (3b) bytecode, facts`FastProgram::decide` reading the request by field (`Facts`)
//!   (4) + partial eval. the policy folded in at compile time, the residual on `decide`

#[path = "../../tests/support/events.rs"] // the JSON → typed_cel::Event tokenizer the tests use
#[allow(dead_code)]
mod events;

mod count;
#[path = "floor.rs"]
mod floor;
#[path = "pmu.rs"]
mod pmu;

use std::collections::BTreeMap;
use std::hint::black_box;
use std::sync::Arc;
use std::time::{Duration, Instant};

use typed_cel::{
    emit, CelActivation, CelBytecode, CelEnvironment, CelLimits, CelProgram, CelTy, CompileOpts,
    Facts, FastProgram, FastScratch, FieldId, Record, RunLiveness, StreamedProgram, Vm,
};

#[global_allocator]
static GLOBAL: count::Counting = count::Counting;

/// The rows of every table, in order.
const WORKLOADS: &[&str] = &[
    "prefix_1",
    "prefix_13",
    "prefix_1000",
    "fs_open_allow_all",
    "fs_open_13",
    "fs_open_1000",
    "method_in_literal",
    "method_in_policy",
    "user_eq",
    "nested_fields",
    "short_circuit_first",
    "short_circuit_last",
    "all_items",
    "exists_items",
    "durations",
    "optional_sum",
    "required_sum",
    "streamed_body_early",
    "streamed_body_late",
    "policy_residual",
];

/// The rows of the headline block (PERFORMANCE.md, and the README's copy of it).
const HEADLINE: &[&str] = &[
    "fs_open_allow_all",
    "fs_open_13",
    "fs_open_1000",
    "prefix_13",
    "nested_fields",
    "all_items",
    "policy_residual",
];

/// The live columns. Column (2) measured `CelProgram::evaluate` while it ran the typed tree
/// evaluator, which is deleted; its numbers are historical (`--historical`, and
/// `docs/PERFORMANCE.md`).
const COLS: &[(&str, &str)] = &[
    ("rust", "Rust"),
    ("upstream", "(1) upstream"),
    ("bytecode_act", "(3a) bytecode, activation"),
    ("bytecode_facts", "(3b) bytecode, facts"),
    ("specialized", "(4) + partial evaluation"),
];

// ------------------------------------------------------------------------------------------
// The data every leg reads
// ------------------------------------------------------------------------------------------

#[derive(serde::Serialize, Clone)]
struct Item {
    qty: f64,
    price: f64,
}
#[derive(serde::Serialize, Clone)]
struct Account {
    owner_id: String,
    tier: String,
}
#[derive(serde::Serialize, Clone)]
struct Body {
    account: Account,
    items: Vec<Item>,
    amount: f64,
}
/// Four fields declared OPTIONAL (`req.opt`), read through `.orValue(0)`.
#[derive(serde::Serialize, Clone, Default)]
struct Opt {
    #[serde(skip_serializing_if = "Option::is_none")]
    a: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    b: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    c: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    d: Option<f64>,
}
/// The same four fields declared REQUIRED (`req.sum`): the floor a guarded read can reach.
#[derive(serde::Serialize, Clone, Default)]
struct Sum {
    a: f64,
    b: f64,
    c: f64,
    d: f64,
}
#[derive(serde::Serialize, Clone, Default)]
struct Flags {
    f0: bool,
    f1: bool,
    f2: bool,
    f3: bool,
    f4: bool,
    f5: bool,
    f6: bool,
    f7: bool,
}
#[derive(serde::Serialize, Clone)]
struct Req {
    path: String,
    method: String,
    user: String,
    tenant: String,
    // the fs.open shape (tests/fast_alloc.rs)
    path_utf8: bool,
    path_text: String,
    access: String,
    target: String,
    subject: String,
    body: Body,
    flags: Flags,
    opt: Opt,
    sum: Sum,
    /// Bound as durations, per leg (upstream: `chrono::Duration`; the dialect: a `"<n>ms"` string).
    #[serde(skip)]
    uptime_ms: i64,
    #[serde(skip)]
    idle_ms: i64,
}
#[derive(serde::Serialize, Clone, Default)]
struct Policy {
    roots: Vec<String>,
    methods: Vec<String>,
    owner: String,
    tenant: String,
    mode: String,
    fs: FsPolicy,
}
#[derive(serde::Serialize, Clone, Default)]
struct FsPolicy {
    default: String,
    deny_other_process_proc: bool,
    writable_roots: Vec<String>,
    readonly_roots: Vec<String>,
    deny_roots: Vec<String>,
}

fn base_req() -> Req {
    Req {
        path: "/w/d0000/x".into(),
        method: "GET".into(),
        user: "u1".into(),
        tenant: "t1".into(),
        path_utf8: true,
        path_text: "/ws/a/b.txt".into(),
        access: "read".into(),
        target: "file".into(),
        subject: "own".into(),
        body: Body {
            account: Account {
                owner_id: "u1".into(),
                tier: "gold".into(),
            },
            items: (0..16)
                .map(|i| Item {
                    qty: 1.0 + i as f64,
                    price: 10.0 + i as f64,
                })
                .collect(),
            amount: 50.0,
        },
        flags: Flags::default(),
        opt: Opt::default(),
        sum: Sum::default(),
        uptime_ms: 45_000,
        idle_ms: 1_000,
    }
}

fn rec(origin: &str, fields: &[(&str, CelTy)]) -> CelTy {
    Record::new(origin, fields.iter().map(|(n, t)| (*n, t.clone()))).into()
}

/// `req` and `policy`, declared exactly as the structs above.
fn env() -> CelEnvironment {
    let mut e = CelEnvironment::with_limits(CelLimits::default());
    let item = rec("item", &[("qty", CelTy::Num), ("price", CelTy::Num)]);
    let flags: Vec<(String, CelTy)> = (0..8).map(|i| (format!("f{i}"), CelTy::Bool)).collect();
    e.declare(
        "req",
        rec(
            "req",
            &[
                ("path", CelTy::Str),
                ("method", CelTy::Str),
                ("user", CelTy::Str),
                ("tenant", CelTy::Str),
                ("path_utf8", CelTy::Bool),
                ("path_text", CelTy::Str),
                ("access", CelTy::Str),
                ("target", CelTy::Str),
                ("subject", CelTy::Str),
                (
                    "body",
                    rec(
                        "req.body",
                        &[
                            (
                                "account",
                                rec(
                                    "req.body.account",
                                    &[("owner_id", CelTy::Str), ("tier", CelTy::Str)],
                                ),
                            ),
                            ("items", CelTy::list(item)),
                            ("amount", CelTy::Num),
                        ],
                    ),
                ),
                (
                    "flags",
                    Record::new(
                        "req.flags",
                        flags.iter().map(|(n, t)| (n.as_str(), t.clone())),
                    )
                    .into(),
                ),
                (
                    "opt",
                    Record::new("req.opt", ["a", "b", "c", "d"].map(|n| (n, CelTy::Num)))
                        .with_optional(["a", "b", "c", "d"])
                        .into(),
                ),
                (
                    "sum",
                    rec(
                        "req.sum",
                        &[
                            ("a", CelTy::Num),
                            ("b", CelTy::Num),
                            ("c", CelTy::Num),
                            ("d", CelTy::Num),
                        ],
                    ),
                ),
                ("uptime", CelTy::Duration),
                ("idle", CelTy::Duration),
            ],
        ),
    );
    e.declare(
        "policy",
        rec(
            "policy",
            &[
                ("roots", CelTy::list(CelTy::Str)),
                ("methods", CelTy::list(CelTy::Str)),
                ("owner", CelTy::Str),
                ("tenant", CelTy::Str),
                ("mode", CelTy::Str),
                (
                    "fs",
                    rec(
                        "policy.fs",
                        &[
                            ("default", CelTy::Str),
                            ("deny_other_process_proc", CelTy::Bool),
                            ("writable_roots", CelTy::list(CelTy::Str)),
                            ("readonly_roots", CelTy::list(CelTy::Str)),
                            ("deny_roots", CelTy::list(CelTy::Str)),
                        ],
                    ),
                ),
            ],
        ),
    );
    e
}

fn req_json(r: &Req) -> serde_json::Value {
    let mut v = serde_json::to_value(r).expect("req serializes");
    let m = v.as_object_mut().expect("an object");
    m.insert("uptime".into(), format!("{}ms", r.uptime_ms).into());
    m.insert("idle".into(), format!("{}ms", r.idle_ms).into());
    v
}

fn upstream_req(r: &Req) -> cel::Value {
    let cel::Value::Map(m) = cel::to_value(r).expect("req converts") else {
        panic!("req is a map")
    };
    let mut map = (*m.map).clone();
    for (k, ms) in [("uptime", r.uptime_ms), ("idle", r.idle_ms)] {
        map.insert(
            cel::objects::Key::String(Arc::new(k.to_string())),
            cel::Value::Duration(chrono::Duration::milliseconds(ms)),
        );
    }
    cel::Value::Map(cel::objects::Map { map: Arc::new(map) })
}

// ------------------------------------------------------------------------------------------
// Facts: the request read by field
// ------------------------------------------------------------------------------------------

enum Scalar {
    /// An optional field that is not there.
    Absent,
    Bool(bool),
    Num(f64),
    Str(String),
    Dur(i64),
}

/// Every field a program reads, resolved against (policy, request) ONCE, answered by index.
struct ReqFacts {
    vals: Vec<Scalar>,
}

impl Facts for ReqFacts {
    fn bool(&self, f: FieldId) -> Option<bool> {
        match &self.vals[f.index()] {
            Scalar::Bool(b) => Some(*b),
            _ => None,
        }
    }
    fn num(&self, f: FieldId) -> Option<f64> {
        match &self.vals[f.index()] {
            Scalar::Num(n) => Some(*n),
            _ => None,
        }
    }
    fn str(&self, f: FieldId) -> Option<&str> {
        match &self.vals[f.index()] {
            Scalar::Str(s) => Some(s),
            _ => None,
        }
    }
    fn duration_ms(&self, f: FieldId) -> Option<i64> {
        match &self.vals[f.index()] {
            Scalar::Dur(d) => Some(*d),
            _ => None,
        }
    }
    fn has(&self, f: FieldId) -> bool {
        !matches!(self.vals[f.index()], Scalar::Absent)
    }
}

/// The scalar a field path names, or `Err(path)` for a composite read (a list or a record read
/// whole), which `Facts` does not serve.
fn scalar(p: &Policy, r: &Req, names: &[&str]) -> Result<Scalar, String> {
    use Scalar::*;
    let s = |v: &String| Str(v.clone());
    Ok(match names {
        ["req", "path"] => s(&r.path),
        ["req", "method"] => s(&r.method),
        ["req", "user"] => s(&r.user),
        ["req", "tenant"] => s(&r.tenant),
        ["req", "path_utf8"] => Bool(r.path_utf8),
        ["req", "path_text"] => s(&r.path_text),
        ["req", "access"] => s(&r.access),
        ["req", "target"] => s(&r.target),
        ["req", "subject"] => s(&r.subject),
        ["req", "body", "account", "owner_id"] => s(&r.body.account.owner_id),
        ["req", "body", "account", "tier"] => s(&r.body.account.tier),
        ["req", "body", "amount"] => Num(r.body.amount),
        ["req", "flags", f] => Bool(match *f {
            "f0" => r.flags.f0,
            "f1" => r.flags.f1,
            "f2" => r.flags.f2,
            "f3" => r.flags.f3,
            "f4" => r.flags.f4,
            "f5" => r.flags.f5,
            "f6" => r.flags.f6,
            "f7" => r.flags.f7,
            other => panic!("no flag {other}"),
        }),
        ["req", "opt", f] => match *f {
            "a" => r.opt.a,
            "b" => r.opt.b,
            "c" => r.opt.c,
            "d" => r.opt.d,
            other => panic!("no optional field {other}"),
        }
        .map_or(Absent, Num),
        ["req", "sum", f] => Num(match *f {
            "a" => r.sum.a,
            "b" => r.sum.b,
            "c" => r.sum.c,
            "d" => r.sum.d,
            other => panic!("no field {other}"),
        }),
        ["req", "uptime"] => Dur(r.uptime_ms),
        ["req", "idle"] => Dur(r.idle_ms),
        ["policy", "owner"] => s(&p.owner),
        ["policy", "tenant"] => s(&p.tenant),
        ["policy", "mode"] => s(&p.mode),
        ["policy", "fs", "default"] => s(&p.fs.default),
        ["policy", "fs", "deny_other_process_proc"] => Bool(p.fs.deny_other_process_proc),
        other => return Err(other.join(".")),
    })
}

fn facts_for(code: &FastProgram, p: &Policy, reqs: &[Req]) -> Result<Vec<ReqFacts>, String> {
    reqs.iter()
        .map(|r| {
            let vals = code
                .fields()
                .iter()
                .map(|f| {
                    let names: Vec<&str> = std::iter::once(f.root()).chain(f.segments()).collect();
                    scalar(p, r, &names)
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(ReqFacts { vals })
        })
        .collect()
}

// ------------------------------------------------------------------------------------------
// The workloads
// ------------------------------------------------------------------------------------------

struct Workload {
    id: &'static str,
    dialect: String,
    upstream: String,
    rust: fn(&Policy, &Req) -> bool,
    policy: Policy,
    requests: Vec<Req>,
}

/// N distinct roots, some prefixes of others (the same generator for every column).
fn roots(prefix: &str, n: usize) -> Vec<String> {
    (0..n)
        .map(|i| {
            if i % 3 == 0 {
                format!("/{prefix}/d{i:04}")
            } else {
                format!("/{prefix}/d{:04}/sub{i}", i - i % 3)
            }
        })
        .collect()
}

fn under(t: &str, roots: &[String]) -> bool {
    roots
        .iter()
        .any(|x| t == x || (t.starts_with(x.as_str()) && t.as_bytes().get(x.len()) == Some(&b'/')))
}

const PREFIX: &str = r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#;

fn prefix(id: &'static str, n: usize) -> Workload {
    let rs = roots("w", n);
    let paths = [
        rs[0].clone(),
        format!("{}/x", rs[n / 2]),
        format!("{}/a/b", rs[n - 1]),
        rs[n - 1].clone(),
        "/w/d9999".to_string(),
        format!("{}x", rs[0]),
        "/other/p".to_string(),
        "/w".to_string(),
    ];
    Workload {
        id,
        dialect: PREFIX.into(),
        upstream: PREFIX.into(),
        rust: |p, r| under(&r.path, &p.roots),
        policy: Policy {
            roots: rs,
            ..Policy::default()
        },
        requests: paths
            .iter()
            .map(|path| Req {
                path: path.clone(),
                ..base_req()
            })
            .collect(),
    }
}

/// The `fs.open` decision's shape (tests/fast_alloc.rs), verbatim.
const OPEN: &str = r#"(!req.path_utf8 ? "eacces"
 : (req.subject == "other_process" && policy.fs.deny_other_process_proc) ? "eacces"
 : (req.target == "device" && !(policy.fs.default == "allow"
     || policy.fs.writable_roots.exists(r, req.path_text == r)
     || policy.fs.readonly_roots.exists(r, req.path_text == r))) ? "eacces"
 : policy.fs.deny_roots.exists(r, req.path_text == r || req.path_text.startsWith(r + "/")) ? "eacces"
 : policy.fs.writable_roots.exists(r, req.path_text == r || req.path_text.startsWith(r + "/")) ? "allow"
 : (policy.fs.readonly_roots.exists(r, req.path_text == r || req.path_text.startsWith(r + "/"))
     || policy.fs.default == "readonly")
     ? ((req.access == "read" || req.access == "exec") ? "allow"
        : req.access == "write" ? "readonly" : "erofs")
 : policy.fs.default == "allow" ? "allow" : "eacces") == "allow""#;

fn open_rust(p: &Policy, r: &Req) -> bool {
    let fs = &p.fs;
    let t = r.path_text.as_str();
    let exact = |roots: &[String]| roots.iter().any(|x| t == x);
    let ruling = if !r.path_utf8 {
        "eacces"
    } else if r.subject == "other_process" && fs.deny_other_process_proc {
        "eacces"
    } else if r.target == "device"
        && !(fs.default == "allow" || exact(&fs.writable_roots) || exact(&fs.readonly_roots))
    {
        "eacces"
    } else if under(t, &fs.deny_roots) {
        "eacces"
    } else if under(t, &fs.writable_roots) {
        "allow"
    } else if under(t, &fs.readonly_roots) || fs.default == "readonly" {
        if r.access == "read" || r.access == "exec" {
            "allow"
        } else if r.access == "write" {
            "readonly"
        } else {
            "erofs"
        }
    } else if fs.default == "allow" {
        "allow"
    } else {
        "eacces"
    };
    ruling == "allow"
}

fn fs_open(id: &'static str, fs: FsPolicy, paths: &[String]) -> Workload {
    let mut requests = Vec::new();
    for p in paths {
        for access in ["read", "write"] {
            requests.push(Req {
                path_text: p.clone(),
                access: access.into(),
                ..base_req()
            });
        }
    }
    // Not UTF-8: refused whatever the roots say, so an allow-all policy still has a `false`.
    for p in paths.iter().take(2) {
        requests.push(Req {
            path_utf8: false,
            path_text: p.clone(),
            ..base_req()
        });
    }
    Workload {
        id,
        dialect: OPEN.into(),
        upstream: OPEN.into(),
        rust: open_rust,
        policy: Policy {
            fs,
            ..Policy::default()
        },
        requests,
    }
}

fn strs(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| s.to_string()).collect()
}

fn workloads() -> Vec<Workload> {
    let mut out = vec![
        prefix("prefix_1", 1),
        prefix("prefix_13", 13),
        prefix("prefix_1000", 1000),
    ];

    out.push(fs_open(
        "fs_open_allow_all",
        FsPolicy {
            default: "allow".into(),
            ..FsPolicy::default()
        },
        &strs(&["/ws/a/b.txt", "/usr/lib/x.so", "/secret/k", "/etc/passwd"]),
    ));
    out.push(fs_open(
        "fs_open_13",
        FsPolicy {
            default: "deny".into(),
            deny_other_process_proc: false,
            writable_roots: strs(&["/ws", "/tmp", "/home/u", "/var/tmp", "/run/user"]),
            readonly_roots: strs(&["/usr", "/lib", "/etc", "/opt", "/bin"]),
            deny_roots: strs(&["/secret", "/root", "/etc/shadow"]),
        },
        &strs(&["/ws/a/b.txt", "/usr/lib/x.so", "/secret/k", "/nowhere/p"]),
    ));
    let (w, r, d) = (roots("w", 400), roots("r", 300), roots("d", 300));
    let paths = vec![
        format!("{}/f", w[399]),
        format!("{}/f", r[150]),
        format!("{}/f", d[299]),
        "/nowhere/f".to_string(),
    ];
    out.push(fs_open(
        "fs_open_1000",
        FsPolicy {
            default: "deny".into(),
            deny_other_process_proc: false,
            writable_roots: w,
            readonly_roots: r,
            deny_roots: d,
        },
        &paths,
    ));

    let methods = [
        "GET", "POST", "HEAD", "DELETE", "OPTIONS", "PUT", "PATCH", "TRACE",
    ];
    let by_method = |m: &&str| Req {
        method: m.to_string(),
        ..base_req()
    };
    out.push(Workload {
        id: "method_in_literal",
        dialect: r#"req.method in ["GET", "HEAD", "OPTIONS"]"#.into(),
        upstream: r#"req.method in ["GET", "HEAD", "OPTIONS"]"#.into(),
        rust: |_, r| matches!(r.method.as_str(), "GET" | "HEAD" | "OPTIONS"),
        policy: Policy::default(),
        requests: methods.iter().map(by_method).collect(),
    });
    out.push(Workload {
        id: "method_in_policy",
        dialect: "req.method in policy.methods".into(),
        upstream: "req.method in policy.methods".into(),
        rust: |p, r| p.methods.iter().any(|m| *m == r.method),
        policy: Policy {
            methods: strs(&["GET", "HEAD", "OPTIONS"]),
            ..Policy::default()
        },
        requests: methods.iter().map(by_method).collect(),
    });
    out.push(Workload {
        id: "user_eq",
        dialect: "req.user == policy.owner".into(),
        upstream: "req.user == policy.owner".into(),
        rust: |p, r| r.user == p.owner,
        policy: Policy {
            owner: "u1".into(),
            ..Policy::default()
        },
        requests: ["u1", "u2", "u1", "u3", "u10", "u1", "", "u11"]
            .iter()
            .map(|u| Req {
                user: u.to_string(),
                ..base_req()
            })
            .collect(),
    });
    let mut nested = Vec::new();
    for owner in ["u1", "u2"] {
        for tier in ["gold", "silver"] {
            for user in ["u1", "u2"] {
                let mut r = base_req();
                r.user = user.into();
                r.body.account.owner_id = owner.into();
                r.body.account.tier = tier.into();
                nested.push(r);
            }
        }
    }
    out.push(Workload {
        id: "nested_fields",
        dialect: r#"req.body.account.owner_id == req.user && req.body.account.tier == "gold""#
            .into(),
        upstream: r#"req.body.account.owner_id == req.user && req.body.account.tier == "gold""#
            .into(),
        rust: |_, r| r.body.account.owner_id == r.user && r.body.account.tier == "gold",
        policy: Policy::default(),
        requests: nested,
    });

    let flags = "req.flags.f0 || req.flags.f1 || req.flags.f2 || req.flags.f3 || req.flags.f4 || req.flags.f5 || req.flags.f6 || req.flags.f7";
    let flag_rust: fn(&Policy, &Req) -> bool = |_, r| {
        let f = &r.flags;
        f.f0 || f.f1 || f.f2 || f.f3 || f.f4 || f.f5 || f.f6 || f.f7
    };
    // Half the requests decide on the named flag; the other half set none and run every operand.
    let flag_reqs = |first: bool| -> Vec<Req> {
        (0..8)
            .map(|i| {
                let mut r = base_req();
                if i % 2 == 0 {
                    if first {
                        r.flags.f0 = true;
                    } else {
                        r.flags.f7 = true;
                    }
                }
                r
            })
            .collect()
    };
    out.push(Workload {
        id: "short_circuit_first",
        dialect: flags.into(),
        upstream: flags.into(),
        rust: flag_rust,
        policy: Policy::default(),
        requests: flag_reqs(true),
    });
    out.push(Workload {
        id: "short_circuit_last",
        dialect: flags.into(),
        upstream: flags.into(),
        rust: flag_rust,
        policy: Policy::default(),
        requests: flag_reqs(false),
    });

    let items = |f: &dyn Fn(usize, &mut Item)| -> Req {
        let mut r = base_req();
        for (i, it) in r.body.items.iter_mut().enumerate() {
            f(i, it);
        }
        r
    };
    let item_reqs: Vec<Req> = vec![
        items(&|_, _| {}),
        items(&|i, it| {
            if i == 15 {
                it.qty = 0.0
            }
        }),
        items(&|_, _| {}),
        items(&|i, it| {
            if i == 0 {
                it.price = 1000.0
            }
        }),
        items(&|i, it| {
            if i == 15 {
                it.price = 1000.0
            }
        }),
        items(&|_, _| {}),
        items(&|i, it| {
            if i == 8 {
                it.price = 1200.0
            }
        }),
        items(&|_, it| it.price = 5.0),
    ];
    out.push(Workload {
        id: "all_items",
        dialect: "req.body.items.all(i, i.qty > 0 && i.price < 1000)".into(),
        upstream: "req.body.items.all(i, i.qty > 0 && i.price < 1000)".into(),
        rust: |_, r| r.body.items.iter().all(|i| i.qty > 0.0 && i.price < 1000.0),
        policy: Policy::default(),
        requests: item_reqs.clone(),
    });
    out.push(Workload {
        id: "exists_items",
        dialect: "req.body.items.exists(i, i.price > 999)".into(),
        upstream: "req.body.items.exists(i, i.price > 999)".into(),
        rust: |_, r| r.body.items.iter().any(|i| i.price > 999.0),
        policy: Policy::default(),
        requests: item_reqs,
    });

    let mut dur = Vec::new();
    for up in [45_000, 30_000, 40_001, 40_000] {
        for idle in [1_000, 600_000] {
            dur.push(Req {
                uptime_ms: up,
                idle_ms: idle,
                ..base_req()
            });
        }
    }
    out.push(Workload {
        id: "durations",
        dialect: "req.uptime > 40s && req.idle < 5m".into(),
        upstream: "req.uptime > duration('40s') && req.idle < duration('5m')".into(),
        rust: |_, r| r.uptime_ms > 40_000 && r.idle_ms < 300_000,
        policy: Policy::default(),
        requests: dur,
    });

    // Two of the four optional fields present in every request, a different two each time.
    let pairs = [
        (0, 1),
        (2, 3),
        (0, 2),
        (1, 3),
        (0, 3),
        (1, 2),
        (0, 1),
        (2, 3),
    ];
    let opt_reqs: Vec<Req> = pairs
        .iter()
        .enumerate()
        .map(|(i, (x, y))| {
            // Every other request sums past 100: both answers, so neither is a short circuit.
            let big = if i % 2 == 0 { 0.0 } else { 50.0 };
            let mut v = [None; 4];
            v[*x] = Some(10.0 + big + i as f64);
            v[*y] = Some(20.0 + big + i as f64);
            let mut r = base_req();
            r.opt = Opt {
                a: v[0],
                b: v[1],
                c: v[2],
                d: v[3],
            };
            let n = |o: Option<f64>| o.unwrap_or(0.0);
            r.sum = Sum {
                a: n(v[0]),
                b: n(v[1]),
                c: n(v[2]),
                d: n(v[3]),
            };
            r
        })
        .collect();
    out.push(Workload {
        id: "optional_sum",
        dialect: "req.opt.?a.orValue(0) + req.opt.?b.orValue(0) + req.opt.?c.orValue(0) \
                  + req.opt.?d.orValue(0) < 100"
            .into(),
        upstream: "(has(req.opt.a) ? req.opt.a : 0.0) + (has(req.opt.b) ? req.opt.b : 0.0) \
                   + (has(req.opt.c) ? req.opt.c : 0.0) + (has(req.opt.d) ? req.opt.d : 0.0) \
                   < 100.0"
            .into(),
        rust: |_, r| {
            let o = &r.opt;
            o.a.unwrap_or(0.0) + o.b.unwrap_or(0.0) + o.c.unwrap_or(0.0) + o.d.unwrap_or(0.0)
                < 100.0
        },
        policy: Policy::default(),
        requests: opt_reqs.clone(),
    });
    out.push(Workload {
        id: "required_sum",
        dialect: "req.sum.a + req.sum.b + req.sum.c + req.sum.d < 100".into(),
        upstream: "req.sum.a + req.sum.b + req.sum.c + req.sum.d < 100.0".into(),
        rust: |_, r| r.sum.a + r.sum.b + r.sum.c + r.sum.d < 100.0,
        policy: Policy::default(),
        requests: opt_reqs,
    });

    let residual_roots = roots("w", 13);
    let mut res_reqs = Vec::new();
    for (path, method, tenant, user) in [
        (format!("{}/x", residual_roots[12]), "GET", "t1", "u1"),
        (format!("{}/x", residual_roots[0]), "HEAD", "t1", "u2"),
        (format!("{}/x", residual_roots[6]), "POST", "t1", "u1"),
        ("/other/x".to_string(), "GET", "t1", "u1"),
        (format!("{}/x", residual_roots[3]), "GET", "t2", "u1"),
        (format!("{}/x", residual_roots[3]), "GET", "t1", ""),
        (format!("{}/y", residual_roots[9]), "OPTIONS", "t1", "u3"),
        (residual_roots[2].clone(), "GET", "t1", "u1"),
    ] {
        res_reqs.push(Req {
            path,
            method: method.into(),
            tenant: tenant.into(),
            user: user.into(),
            ..base_req()
        });
    }
    let residual = r#"req.method in policy.methods && policy.roots.exists(r, req.path.startsWith(r + "/")) && req.tenant == policy.tenant && (policy.mode == "enforce" ? req.user != "" : true)"#;
    out.push(Workload {
        id: "policy_residual",
        dialect: residual.into(),
        upstream: residual.into(),
        rust: |p, r| {
            p.methods.iter().any(|m| *m == r.method)
                && p.roots.iter().any(|x| {
                    r.path.starts_with(x.as_str()) && r.path.as_bytes().get(x.len()) == Some(&b'/')
                })
                && r.tenant == p.tenant
                && (if p.mode == "enforce" {
                    !r.user.is_empty()
                } else {
                    true
                })
        },
        policy: Policy {
            roots: residual_roots,
            methods: strs(&["GET", "HEAD", "OPTIONS"]),
            tenant: "t1".into(),
            mode: "enforce".into(),
            ..Policy::default()
        },
        requests: res_reqs,
    });
    out
}

// ------------------------------------------------------------------------------------------
// Measuring
// ------------------------------------------------------------------------------------------

const WARMUP: usize = 10_000;
const ROUNDS: usize = 15;
const ROUND_MIN: Duration = Duration::from_millis(20);
const ALLOC_EVALS: usize = 10_000;

/// (median, min) ns per call over `ROUNDS` rounds, each at least `ROUND_MIN` long.
fn time<F: FnMut(usize) -> bool>(n: usize, f: &mut F) -> (f64, f64) {
    for i in 0..WARMUP {
        black_box(f(black_box(i % n)));
    }
    let mut batch = 64usize;
    loop {
        let t = Instant::now();
        for i in 0..batch {
            black_box(f(black_box(i % n)));
        }
        let e = t.elapsed();
        if e >= ROUND_MIN {
            break;
        }
        let scale = ROUND_MIN.as_nanos() as f64 * 1.25 / (e.as_nanos().max(1) as f64);
        batch = ((batch as f64 * scale).ceil() as usize).max(batch * 2);
    }
    let mut per: Vec<f64> = (0..ROUNDS)
        .map(|_| {
            let t = Instant::now();
            for i in 0..batch {
                black_box(f(black_box(i % n)));
            }
            t.elapsed().as_nanos() as f64 / batch as f64
        })
        .collect();
    per.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (per[ROUNDS / 2], per[0])
}

fn measure<F: FnMut(usize) -> bool>(out: &mut String, id: &str, col: &str, n: usize, mut f: F) {
    let (median, min) = time(n, &mut f);
    let allocs = count::allocs_per(ALLOC_EVALS, |i| {
        black_box(f(i % n));
    });
    raw(
        out,
        format!("@time\t{id}\t{col}\t{median}\t{min}\t{allocs}"),
    );
}

fn na(out: &mut String, id: &str, col: &str, why: &str) {
    raw(out, format!("@time\t{id}\t{col}\tna\t{why}"));
}

fn raw(out: &mut String, line: String) {
    println!("{line}");
    out.push_str(&line);
    out.push('\n');
}

fn median_us<T, F: FnMut() -> T>(mut f: F) -> f64 {
    black_box(f());
    let mut v: Vec<f64> = (0..50)
        .map(|_| {
            let t = Instant::now();
            black_box(f());
            t.elapsed().as_nanos() as f64 / 1000.0
        })
        .collect();
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[25]
}

fn verdict_of(v: Result<cel::Value, cel::ExecutionError>) -> Result<bool, String> {
    match v {
        Ok(cel::Value::Bool(b)) => Ok(b),
        Ok(other) => Err(format!("not a bool: {other:?}")),
        Err(e) => Err(e.to_string()),
    }
}

/// What the dialect columns run, built once per workload: the checked program, its bytecode, the
/// requests as `Facts` for (3b), and the specialized residual with its `Facts` for (4).
struct Prepared {
    program: CelProgram,
    bytecode: CelBytecode,
    facts: Result<Vec<ReqFacts>, String>,
    specialized: Option<(CelProgram, FastProgram, Vec<ReqFacts>)>,
}

fn prepared(env: &CelEnvironment, w: &Workload) -> Prepared {
    let id = w.id;
    let policy_json = serde_json::to_value(&w.policy).expect("policy serializes");
    let program = env
        .compile(&w.dialect, &CompileOpts::default())
        .unwrap_or_else(|e| panic!("{id}: {e}"));
    let bytecode = emit(&program).unwrap_or_else(|e| panic!("{id}: {e}"));
    let facts = facts_for(bytecode.program(), &w.policy, &w.requests);
    let specialized = if w.dialect.contains("policy.") {
        let mut known = env.activation();
        known.bind("policy", &policy_json).expect("policy binds");
        let residual = env
            .compile(
                &w.dialect,
                &CompileOpts {
                    known: Some(&known),
                    ..Default::default()
                },
            )
            .unwrap_or_else(|e| panic!("{id}: {e}"));
        let fast = FastProgram::new(&residual).unwrap_or_else(|e| panic!("{id}: {e}"));
        let f = facts_for(&fast, &w.policy, &w.requests).unwrap_or_else(|p| {
            panic!(
                "{id}: the residual reads a composite {p}: {}",
                residual.source()
            )
        });
        Some((residual, fast, f))
    } else {
        None
    };
    Prepared {
        program,
        bytecode,
        facts,
        specialized,
    }
}

fn run_workload(env: &CelEnvironment, w: &Workload, out: &mut String) {
    let id = w.id;
    let n = w.requests.len();
    assert!(n >= 8, "{id}: {n} requests");
    let reads_policy = w.dialect.contains("policy.");
    let policy_json = serde_json::to_value(&w.policy).expect("policy serializes");

    // (1) upstream
    let up_prog = cel::Program::compile(&w.upstream).unwrap_or_else(|e| panic!("{id}: {e:?}"));
    let up_policy = cel::to_value(&w.policy).expect("policy converts");
    let up_ctx: Vec<cel::Context<'static>> = w
        .requests
        .iter()
        .map(|r| {
            let mut c = cel::Context::default();
            c.add_variable_from_value("policy", up_policy.clone());
            c.add_variable_from_value("req", upstream_req(r));
            c
        })
        .collect();

    // (2) / (3a), (3b), (4)
    let Prepared {
        program: _,
        bytecode,
        facts,
        specialized,
    } = prepared(env, w);
    let acts: Vec<CelActivation> = w
        .requests
        .iter()
        .map(|r| {
            let mut a = env.activation();
            a.bind("policy", &policy_json).expect("policy binds");
            a.bind("req", &req_json(r)).expect("req binds");
            a
        })
        .collect();
    let vm = Vm::new();
    let code = bytecode.program();

    // The vacuity guard: every leg answers every request, and alike.
    let mut verdicts = Vec::new();
    let mut scratch = FastScratch::default();
    for (i, r) in w.requests.iter().enumerate() {
        let mut answers: Vec<(&str, Result<bool, String>)> = vec![
            ("rust", Ok((w.rust)(&w.policy, r))),
            ("upstream", verdict_of(up_prog.execute(&up_ctx[i]))),
            (
                "bytecode_act",
                vm.eval(&bytecode, &acts[i]).map_err(|e| e.to_string()),
            ),
        ];
        if let Ok(f) = &facts {
            answers.push((
                "bytecode_facts",
                code.decide(&f[i], &mut scratch).map_err(|e| e.to_string()),
            ));
        }
        if let Some((_, fast, f)) = &specialized {
            answers.push((
                "specialized",
                fast.decide(&f[i], &mut scratch).map_err(|e| e.to_string()),
            ));
        }
        let want = &answers[0].1;
        if answers.iter().any(|(_, a)| a != want || a.is_err()) {
            panic!("{id}: request {i} — the legs disagree: {answers:?}");
        }
        verdicts.push(*want.as_ref().unwrap());
    }
    assert!(
        verdicts.contains(&true) && verdicts.contains(&false),
        "{id}: a one-sided request set measures a short circuit, not a program: {verdicts:?}"
    );

    let reqs = &w.requests;
    let pol = &w.policy;
    measure(out, id, "rust", n, |i| {
        (w.rust)(black_box(pol), black_box(&reqs[i]))
    });
    measure(out, id, "upstream", n, |i| {
        verdict_of(up_prog.execute(&up_ctx[i])).unwrap()
    });
    measure(out, id, "bytecode_act", n, |i| {
        vm.eval(&bytecode, &acts[i]).unwrap()
    });
    match &facts {
        Ok(f) => {
            let mut s = FastScratch::default();
            measure(out, id, "bytecode_facts", n, |i| {
                code.decide(&f[i], &mut s).unwrap()
            });
        }
        Err(p) => na(
            out,
            id,
            "bytecode_facts",
            &format!("n/a (composite root: `{p}`)"),
        ),
    }
    match &specialized {
        Some((_, fast, f)) => {
            let mut s = FastScratch::default();
            measure(out, id, "specialized", n, |i| {
                fast.decide(&f[i], &mut s).unwrap()
            });
        }
        None => na(out, id, "specialized", "— (reads no policy)"),
    }

    // Compile time.
    let up_us = median_us(|| cel::Program::compile(&w.upstream).unwrap());
    let typed_us = median_us(|| env.compile(&w.dialect, &CompileOpts::default()).unwrap());
    let bc_us = median_us(|| {
        let p = env.compile(&w.dialect, &CompileOpts::default()).unwrap();
        emit(&p).unwrap()
    });
    // (4) is parse / compile with known / lower: the text is parsed once, outside the timing, the
    // way a caller that compiles one program against many policies keeps it.
    let (spec_us, lower_us) = if reads_policy {
        let parsed = env.parse(&w.dialect).unwrap();
        let s = median_us(|| {
            let mut known = env.activation();
            known.bind("policy", &policy_json).unwrap();
            env.compile(
                &parsed,
                &CompileOpts {
                    known: Some(&known),
                    ..Default::default()
                },
            )
            .unwrap()
        });
        let residual = &specialized.as_ref().unwrap().0;
        let l = median_us(|| FastProgram::new(residual).unwrap());
        (format!("{s}"), format!("{l}"))
    } else {
        ("-".into(), "-".into())
    };
    raw(
        out,
        format!("@compile\t{id}\t{up_us}\t{typed_us}\t{bc_us}\t{spec_us}\t{lower_us}"),
    );

    // Retained memory. Each build runs once unmeasured first, so a lazily built global is not
    // charged to the program.
    let mem_up = {
        let f = || cel::Program::compile(&w.upstream).unwrap();
        black_box(f());
        count::retained(f)
    };
    let mem_prog = {
        let f = || env.compile(&w.dialect, &CompileOpts::default()).unwrap();
        black_box(f());
        count::retained(f)
    };
    let mem_bc = {
        let f = || {
            let p = env.compile(&w.dialect, &CompileOpts::default()).unwrap();
            let b = emit(&p).unwrap();
            (p, b)
        };
        black_box(f());
        count::retained(f)
    };
    let mem_spec = if reads_policy {
        let f = || {
            let p = env.parse(&w.dialect).unwrap();
            let mut known = env.activation();
            known.bind("policy", &policy_json).unwrap();
            let residual = env
                .compile(
                    &p,
                    &CompileOpts {
                        known: Some(&known),
                        ..Default::default()
                    },
                )
                .unwrap();
            let fast = FastProgram::new(&residual).unwrap();
            drop(known);
            drop(p);
            (residual, fast)
        };
        black_box(f());
        format!("{}", count::retained(f))
    } else {
        "-".into()
    };
    raw(
        out,
        format!("@mem\t{id}\t{mem_up}\t{mem_prog}\t{mem_bc}\t{mem_spec}"),
    );
}

// ------------------------------------------------------------------------------------------
// The streamed body
// ------------------------------------------------------------------------------------------

const PADS: usize = 40;

fn body_env() -> CelEnvironment {
    let mut e = CelEnvironment::with_limits(CelLimits::default());
    let item = rec("item", &[("qty", CelTy::Num), ("price", CelTy::Num)]);
    let mut fields: Vec<(String, CelTy)> = vec![
        (
            "account".into(),
            rec(
                "body.account",
                &[("owner_id", CelTy::Str), ("tier", CelTy::Str)],
            ),
        ),
        ("amount".into(), CelTy::Num),
        ("items".into(), CelTy::list(item)),
    ];
    for i in 0..PADS {
        fields.push((format!("pad{i:02}"), CelTy::Str));
    }
    e.declare(
        "body",
        Record::new("body", fields.iter().map(|(n, t)| (n.as_str(), t.clone()))),
    );
    e
}

/// A ~4 KiB document with the demanded fields near its START (`early`) or its END.
fn body_doc(early: bool, tier: &str, amount: f64) -> String {
    let head =
        format!(r#""account": {{"owner_id": "u1", "tier": "{tier}"}}, "amount": {amount:?}"#);
    let items: Vec<String> = (0..8)
        .map(|i| format!(r#"{{"qty": {}.0, "price": {}.5}}"#, i + 1, 10 + i))
        .collect();
    let items = format!(r#""items": [{}]"#, items.join(", "));
    let pads: Vec<String> = (0..PADS)
        .map(|i| format!(r#""pad{i:02}": "{}""#, "p".repeat(80)))
        .collect();
    let pads = pads.join(", ");
    if early {
        format!("{{{head}, {items}, {pads}}}")
    } else {
        format!("{{{pads}, {items}, {head}}}")
    }
}

const BODY: &str = r#"body.account.tier == "gold" && body.amount < 100"#;

fn run_streamed(id: &str, early: bool, out: &mut String) {
    let env = body_env();
    let docs: Vec<String> = [
        ("gold", 50.0),
        ("silver", 50.0),
        ("gold", 150.0),
        ("gold", 99.5),
    ]
    .iter()
    .flat_map(|(t, a)| [body_doc(early, t, *a), body_doc(early, t, a + 0.25)])
    .collect();
    let n = docs.len();

    let up_prog = cel::Program::compile(BODY).unwrap();
    let up_base = cel::Context::default();
    let up = |text: &str| -> Result<bool, String> {
        let v: serde_json::Value = serde_json::from_str(text).unwrap();
        let mut c = up_base.new_inner_scope();
        c.add_variable("body", v).unwrap();
        verdict_of(up_prog.execute(&c))
    };

    let program = env.compile(BODY, &CompileOpts::default()).unwrap();
    let bytecode = emit(&program).unwrap();
    let vm = Vm::new();
    let act = |text: &str| -> Result<bool, String> {
        let v: serde_json::Value = serde_json::from_str(text).unwrap();
        let mut a = env.activation();
        a.bind("body", &v).map_err(|e| e.to_string())?;
        vm.eval(&bytecode, &a).map_err(|e| e.to_string())
    };

    let sp = StreamedProgram::new(
        Arc::new(Vm::new()),
        &env,
        &program,
        Arc::new(emit(&program).unwrap()),
        env.activation(),
        "body",
    )
    .unwrap();
    // Tokenized ONCE, untimed: the producer is not this crate's.
    let evs: Vec<Vec<events::Ev>> = docs.iter().map(|d| events::to_events(d, 64)).collect();
    let mut state = 0usize;
    let mut streamed = |i: usize| -> Result<bool, String> {
        let mut run = sp.begin();
        for e in &evs[i] {
            if run.push(e.as_event()) != RunLiveness::Live {
                break;
            }
        }
        state = state.max(run.state_bytes());
        run.finish().map_err(|e| e.to_string())
    };

    let mut verdicts = Vec::new();
    for (i, d) in docs.iter().enumerate() {
        let answers = [
            ("upstream", up(d)),
            ("bytecode_act", act(d)),
            ("streamed", streamed(i)),
        ];
        let want = &answers[0].1;
        if answers.iter().any(|(_, a)| a != want || a.is_err()) {
            panic!("{id}: document {i} — the legs disagree: {answers:?}");
        }
        verdicts.push(*want.as_ref().unwrap());
    }
    assert!(
        verdicts.contains(&true) && verdicts.contains(&false),
        "{id}: {verdicts:?}"
    );

    na(out, id, "rust", "— (streamed row)");
    measure(out, id, "upstream", n, |i| up(&docs[i]).unwrap());
    measure(out, id, "bytecode_act", n, |i| act(&docs[i]).unwrap());
    measure(out, id, "bytecode_facts", n, |i| streamed(i).unwrap());
    na(out, id, "specialized", "— (streamed row)");
    raw(out, format!("@state\t{id}\t{}\t{state}", docs[0].len()));

    let up_us = median_us(|| cel::Program::compile(BODY).unwrap());
    let typed_us = median_us(|| env.compile(BODY, &CompileOpts::default()).unwrap());
    let bc_us = median_us(|| emit(&env.compile(BODY, &CompileOpts::default()).unwrap()).unwrap());
    raw(
        out,
        format!("@compile\t{id}\t{up_us}\t{typed_us}\t{bc_us}\t-\t-"),
    );
    let mem_up = count::retained(|| cel::Program::compile(BODY).unwrap());
    let mem_prog = count::retained(|| env.compile(BODY, &CompileOpts::default()).unwrap());
    let mem_bc = count::retained(|| {
        let p = env.compile(BODY, &CompileOpts::default()).unwrap();
        let b = emit(&p).unwrap();
        (p, b)
    });
    raw(
        out,
        format!("@mem\t{id}\t{mem_up}\t{mem_prog}\t{mem_bc}\t-"),
    );
}

// ------------------------------------------------------------------------------------------
// Rendering (one run, or the median of several)
// ------------------------------------------------------------------------------------------

#[derive(Default)]
struct Runs {
    /// (workload, col) → per run: (median, min, allocs) or the n/a text
    time: BTreeMap<(String, String), Vec<Result<(f64, f64, f64), String>>>,
    /// workload → per run: [up, typed, bytecode, spec, lower] (µs; NaN = none)
    compile: BTreeMap<String, Vec<[f64; 5]>>,
    /// workload → per run: [up, prog, prog+bc, residual+fast] bytes (NaN = none)
    mem: BTreeMap<String, Vec<[f64; 4]>>,
    /// workload → per run: (document bytes, state bytes)
    state: BTreeMap<String, Vec<(f64, f64)>>,
    runs: usize,
}

fn num(s: &str) -> f64 {
    if s == "-" {
        f64::NAN
    } else {
        s.parse().unwrap_or_else(|_| panic!("not a number: {s}"))
    }
}

impl Runs {
    fn add(&mut self, text: &str) {
        self.runs += 1;
        for line in text.lines() {
            let f: Vec<&str> = line.split('\t').collect();
            match f[0] {
                "@time" => {
                    let v = if f[3] == "na" {
                        Err(f[4].to_string())
                    } else {
                        Ok((num(f[3]), num(f[4]), num(f[5])))
                    };
                    self.time
                        .entry((f[1].into(), f[2].into()))
                        .or_default()
                        .push(v);
                }
                "@compile" => self.compile.entry(f[1].into()).or_default().push([
                    num(f[2]),
                    num(f[3]),
                    num(f[4]),
                    num(f[5]),
                    num(f[6]),
                ]),
                "@mem" => self.mem.entry(f[1].into()).or_default().push([
                    num(f[2]),
                    num(f[3]),
                    num(f[4]),
                    num(f[5]),
                ]),
                "@state" => self
                    .state
                    .entry(f[1].into())
                    .or_default()
                    .push((num(f[2]), num(f[3]))),
                _ => {}
            }
        }
    }
}

fn med(mut v: Vec<f64>) -> f64 {
    v.sort_by(f64::total_cmp);
    v[v.len() / 2]
}

/// The spread of several runs' values, relative to their median.
fn spread(v: &[f64]) -> f64 {
    let m = med(v.to_vec());
    let (lo, hi) = v
        .iter()
        .fold((f64::MAX, f64::MIN), |(l, h), x| (l.min(*x), h.max(*x)));
    if m == 0.0 {
        0.0
    } else {
        (hi - lo) / m
    }
}

fn ns(v: f64) -> String {
    if v >= 1_000_000.0 {
        format!("{:.2} ms", v / 1_000_000.0)
    } else if v >= 10_000.0 {
        format!("{:.1} µs", v / 1000.0)
    } else if v >= 100.0 {
        format!("{v:.0} ns")
    } else {
        format!("{v:.1} ns")
    }
}

fn count_fmt(v: f64) -> String {
    if (v - v.round()).abs() < 0.05 {
        format!("{}", v.round() as i64)
    } else {
        format!("{v:.1}")
    }
}

fn us(v: f64) -> String {
    if v.is_nan() {
        "—".into()
    } else if v >= 1000.0 {
        format!("{:.2} ms", v / 1000.0)
    } else {
        format!("{v:.1} µs")
    }
}

fn bytes(v: f64) -> String {
    if v.is_nan() {
        "—".into()
    } else if v >= 1_048_576.0 {
        format!("{:.2} MiB", v / 1_048_576.0)
    } else if v >= 10_240.0 {
        format!("{:.1} KiB", v / 1024.0)
    } else {
        format!("{} B", v as i64)
    }
}

/// The columns of a time table, each with the runs it is read from.
fn time_table(r: &Runs, hist: Option<&Runs>, rows: &[&str], wide: &mut Vec<String>) -> String {
    let mut cols: Vec<(&str, String, &Runs)> =
        COLS.iter().map(|(c, h)| (*c, h.to_string(), r)).collect();
    if let Some(h) = hist {
        cols.insert(2, ("typed_tree", "(2) typed tree †".to_string(), h));
    }
    let mut s = String::from("| workload |");
    for (_, h, _) in &cols {
        s += &format!(" {h} |");
    }
    s += "\n|---|";
    for _ in &cols {
        s += "---:|";
    }
    s += "\n";
    for id in rows {
        s += &format!("| `{id}` |");
        for (col, _, r) in &cols {
            let Some(cells) = r.time.get(&(id.to_string(), col.to_string())) else {
                s += " — |";
                continue;
            };
            match &cells[0] {
                Err(why) => s += &format!(" {why} |"),
                Ok(_) => {
                    let ok: Vec<(f64, f64, f64)> =
                        cells.iter().map(|c| *c.as_ref().unwrap()).collect();
                    let medians: Vec<f64> = ok.iter().map(|c| c.0).collect();
                    let m = med(medians.clone());
                    let a = med(ok.iter().map(|c| c.2).collect());
                    let mark = if spread(&medians) > 0.10 {
                        wide.push(format!("{id} / {col}: {:.0}%", spread(&medians) * 100.0));
                        "†"
                    } else {
                        ""
                    };
                    s += &format!(" {}{mark} ({}) |", ns(m), count_fmt(a));
                }
            }
        }
        s += "\n";
    }
    s
}

fn render(r: &Runs, hist: Option<&Runs>) -> String {
    let mut wide = Vec::new();
    let mut s = String::new();
    s += &format!(
        "Runs combined: {} (each cell: the median of the runs' median ns/eval; allocations/eval in parentheses)\n\n",
        r.runs
    );
    s += "### Headline\n\n<!-- ablation:begin -->\n";
    s += &time_table(r, hist, HEADLINE, &mut Vec::new());
    if hist.is_some() {
        s += "\n† Column (2) is historical: measured on the typed dialect's first engine, since deleted \
              (docs/PERFORMANCE.md, \"Historical\"). Every other column is this run.\n";
    }
    s += "<!-- ablation:end -->\n\n### Time and allocations\n\n";
    s += &time_table(r, None, WORKLOADS, &mut wide);
    s += "\n### Compile and memory\n\n";
    s += "| workload | (1) compile | checked compile | (3) compile + emit | (4) parse / compile with known / lower | (1) `Program` | `CelProgram` | (3) + `CelBytecode` | (4) residual + `FastProgram` |\n";
    s += "|---|---:|---:|---:|---:|---:|---:|---:|---:|\n";
    for id in WORKLOADS {
        let (Some(c), Some(m)) = (r.compile.get(*id), r.mem.get(*id)) else {
            continue;
        };
        let c: Vec<f64> = (0..5)
            .map(|k| med(c.iter().map(|x| x[k]).collect()))
            .collect();
        let mm: Vec<f64> = (0..4)
            .map(|k| {
                let v: Vec<f64> = m.iter().map(|x| x[k]).collect();
                if v[0].is_nan() {
                    f64::NAN
                } else {
                    med(v)
                }
            })
            .collect();
        let spec = if c[3].is_nan() {
            "—".to_string()
        } else {
            format!("{} / {} / {}", us(c[1]), us(c[3]), us(c[4]))
        };
        s += &format!(
            "| `{id}` | {} | {} | {} | {spec} | {} | {} | {} | {} |\n",
            us(c[0]),
            us(c[1]),
            us(c[2]),
            bytes(mm[0]),
            bytes(mm[1]),
            bytes(mm[2]),
            bytes(mm[3])
        );
    }
    s += "\n### Streamed body: document and run state\n\n| workload | document | streamed run state (max over the set) |\n|---|---:|---:|\n";
    for (id, v) in &r.state {
        s += &format!(
            "| `{id}` | {} | {} |\n",
            bytes(med(v.iter().map(|x| x.0).collect())),
            bytes(med(v.iter().map(|x| x.1).collect()))
        );
    }
    if !wide.is_empty() {
        s += &format!(
            "\n† the runs' medians spread more than 10%: {}\n",
            wide.join("; ")
        );
    }
    s
}

fn sh(cmd: &str, args: &[&str]) -> String {
    std::process::Command::new(cmd)
        .args(args)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".into())
}

fn header() {
    let cpu = std::fs::read_to_string("/proc/cpuinfo")
        .ok()
        .and_then(|t| {
            t.lines()
                .find(|l| l.starts_with("model name"))
                .and_then(|l| l.split(':').nth(1))
                .map(|s| s.trim().to_string())
        })
        .unwrap_or_else(|| "unknown".into());
    println!("# cpu: {cpu}");
    // Every CPU the machine has, not the ones this process is pinned to.
    let cores = std::fs::read_to_string("/proc/cpuinfo")
        .map(|t| t.lines().filter(|l| l.starts_with("processor")).count())
        .unwrap_or(0);
    println!("# cores: {cores}");
    println!("# kernel: {}", sh("uname", &["-r"]));
    let home_rustc = format!(
        "{}/.cargo/bin/rustc",
        std::env::var("HOME").unwrap_or_default()
    );
    let rustc = match sh("rustc", &["-V"]) {
        v if v != "unknown" => v,
        _ => sh(&home_rustc, &["-V"]),
    };
    println!("# rustc: {rustc}");
    println!("# git: {}", sh("git", &["rev-parse", "HEAD"]));
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.first().map(String::as_str) == Some("--combine") {
        let read =
            |path: &String| std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
        let split = args.iter().position(|a| a == "--historical");
        let (live, older) = match split {
            Some(i) => (&args[1..i], &args[i + 1..]),
            None => (&args[1..], &args[args.len()..]),
        };
        let mut r = Runs::default();
        for path in live {
            r.add(&read(path));
        }
        let mut h = Runs::default();
        for path in older {
            h.add(&read(path));
        }
        print!("{}", render(&r, split.map(|_| &h)));
        return;
    }
    match args.first().map(String::as_str) {
        Some("--listing") => return listing(&args[1..]),
        Some("--cycles") => return cycles(&args[1..]),
        Some("--cycles-median") => return cycles_median(&args[1..]),
        Some("--trace") => return trace(&args[1..]),
        _ => {}
    }
    header();
    let env = env();
    let mut out = String::new();
    let all = workloads();
    for id in WORKLOADS {
        match *id {
            "streamed_body_early" => run_streamed(id, true, &mut out),
            "streamed_body_late" => run_streamed(id, false, &mut out),
            _ => {
                let w = all
                    .iter()
                    .find(|w| w.id == *id)
                    .unwrap_or_else(|| panic!("no workload {id}"));
                run_workload(&env, w, &mut out);
            }
        }
    }
    let mut r = Runs::default();
    r.add(&out);
    println!();
    print!("{}", render(&r, None));
}

// ------------------------------------------------------------------------------------------
// Cycles: hardware counters per decision
// ------------------------------------------------------------------------------------------

/// Calls per counted run: long enough that the two counter reads are noise.
const CYCLE_ITERS: usize = 5_000_000;

/// The columns whose cycles the `--against` gate holds: the ones `decide` runs.
const GATED: &[&str] = &["bytecode_facts", "specialized"];

fn cycles_row<F: FnMut(usize) -> bool>(
    out: &mut String,
    id: &str,
    col: &str,
    n: usize,
    ctr: &Option<pmu::Ctr>,
    mut f: F,
) {
    // `time` warms and then times; the counted run comes after it, equally warm.
    let (median, _min) = time(n, &mut f);
    let line = match ctr
        .as_ref()
        .map(|c| pmu::per_call(c, n, CYCLE_ITERS, &mut f))
    {
        Some([cyc, ins, br, miss]) => {
            format!("@cycles\t{id}\t{col}\t{median:.1}\t{cyc:.1}\t{ins:.1}\t{br:.1}\t{miss:.2}")
        }
        None => format!("@cycles\t{id}\t{col}\t{median:.1}\tna\tna\tna\tna"),
    };
    raw(out, line);
}

/// `nested_fields`'s three field reads, in the order the floor spikes hardcode.
const NESTED_FIELDS: [&[&str]; 3] = [
    &["req", "body", "account", "owner_id"],
    &["req", "user"],
    &["req", "body", "account", "tier"],
];

fn cycles(args: &[String]) {
    let mut against = None;
    let mut filters = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--against" {
            against = Some(it.next().expect("--against <file>").clone());
        } else {
            filters.push(a.clone());
        }
    }
    let ctr = pmu::Ctr::new();
    if ctr.is_none() {
        if against.is_some() {
            eprintln!("cycles need the PMU; run on a Linux x86_64 host that exposes it");
            std::process::exit(2);
        }
        println!("# pmu: unavailable — ns only");
    }
    let wanted = |id: &str| filters.is_empty() || filters.iter().any(|f| f == id);
    let env = env();
    let all = workloads();
    let mut out = String::new();
    for id in WORKLOADS
        .iter()
        .filter(|id| !id.starts_with("streamed_") && wanted(id))
    {
        let w = all.iter().find(|w| w.id == *id).expect("workload");
        let p = prepared(&env, w);
        let n = w.requests.len();
        let (reqs, pol) = (&w.requests, &w.policy);
        cycles_row(&mut out, id, "rust", n, &ctr, |i| {
            (w.rust)(black_box(pol), black_box(&reqs[i]))
        });
        if let Ok(f) = &p.facts {
            let code = p.bytecode.program();
            let mut s = FastScratch::default();
            cycles_row(&mut out, id, "bytecode_facts", n, &ctr, |i| {
                code.decide(&f[i], &mut s).unwrap()
            });
            if *id == "nested_fields" {
                floor_rows(&mut out, w, code, f, &ctr);
            }
        }
        if let Some((_, fast, f)) = &p.specialized {
            let mut s = FastScratch::default();
            cycles_row(&mut out, id, "specialized", n, &ctr, |i| {
                fast.decide(&f[i], &mut s).unwrap()
            });
        }
    }
    if wanted("constant_true") {
        // The program `true`: every cycle it costs is the fixed per-call path.
        let fast = FastProgram::new(
            &env.compile("true", &CompileOpts::default())
                .expect("`true` compiles"),
        )
        .expect("`true` lowers");
        let facts: Vec<ReqFacts> = (0..8).map(|_| ReqFacts { vals: Vec::new() }).collect();
        let mut s = FastScratch::default();
        cycles_row(&mut out, "constant_true", "bytecode_facts", 8, &ctr, |i| {
            fast.decide(&facts[i], &mut s).unwrap()
        });
    }
    println!();
    print!("{}", cycles_table(&parse_cycles(&out)));
    if let Some(path) = against {
        let base = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        std::process::exit(gate(&parse_cycles(&base), &parse_cycles(&out)));
    }
}

/// The floor spikes beside `nested_fields`, each held to the Rust column's answers first.
fn floor_rows(
    out: &mut String,
    w: &Workload,
    code: &FastProgram,
    f: &[ReqFacts],
    ctr: &Option<pmu::Ctr>,
) {
    let fields = code.fields();
    assert!(
        fields.len() == 3 && NESTED_FIELDS.iter().zip(fields).all(|(n, p)| p.is(n)),
        "the floor spikes hardcode nested_fields's field order; the program reads {:?}",
        fields
            .iter()
            .map(|p| std::iter::once(p.root())
                .chain(p.segments())
                .collect::<Vec<_>>()
                .join("."))
            .collect::<Vec<_>>()
    );
    let (ops, k) = floor::nested();
    let (fops, fk) = floor::nested_fused();
    let tree = floor::closures::nested();
    for (i, r) in w.requests.iter().enumerate() {
        let want = (w.rust)(&w.policy, r);
        let got = [
            floor::run(&ops, &k, &f[i]).ok(),
            floor::run_fused(&fops, &fk, &f[i]).ok(),
            tree(&f[i]).ok(),
        ];
        assert!(
            got.iter().all(|g| *g == Some(want)),
            "nested_fields request {i}: a floor spike disagrees with Rust ({want}): {got:?}"
        );
    }
    let n = w.requests.len();
    cycles_row(out, w.id, "floor_lean", n, ctr, |i| {
        floor::run(&ops, &k, &f[i]).ok().unwrap()
    });
    cycles_row(out, w.id, "floor_fused", n, ctr, |i| {
        floor::run_fused(&fops, &fk, &f[i]).ok().unwrap()
    });
    cycles_row(out, w.id, "floor_closures", n, ctr, |i| {
        tree(&f[i]).unwrap()
    });
}

/// One `@cycles` row: (id, col) → [ns, cycles, instructions, branches, branch misses].
type CycleRows = BTreeMap<(String, String), [Option<f64>; 5]>;

fn parse_cycles(text: &str) -> CycleRows {
    let mut rows = CycleRows::new();
    for line in text.lines().filter(|l| l.starts_with("@cycles\t")) {
        let c: Vec<&str> = line.split('\t').collect();
        let mut v = [None; 5];
        for (k, cell) in c[3..8].iter().enumerate() {
            v[k] = cell.parse().ok();
        }
        rows.insert((c[1].to_string(), c[2].to_string()), v);
    }
    rows
}

fn cycles_table(rows: &CycleRows) -> String {
    let mut s =
        String::from("| workload | column | ns | cycles | instructions | IPC | branch misses |\n");
    s += "|---|---|---:|---:|---:|---:|---:|\n";
    let f = |v: Option<f64>, d: usize| v.map_or("na".to_string(), |x| format!("{x:.d$}"));
    for ((id, col), v) in rows {
        let ipc = match (v[1], v[2]) {
            (Some(c), Some(i)) if c > 0.0 => Some(i / c),
            _ => None,
        };
        s += &format!(
            "| `{id}` | {col} | {} | {} | {} | {} | {} |\n",
            f(v[0], 1),
            f(v[1], 0),
            f(v[2], 0),
            f(ipc, 2),
            f(v[4], 2)
        );
    }
    s
}

/// The 5% gate: exit status 1 when any gated `decide` cell's cycles rose by more than 5% AND its
/// instruction count rose. Cycles alone swing ±7% run to run on the small cells (measured: the
/// program `true` over five runs, 94–109 cycles at a fixed 240 instructions), so a cycle rise with
/// no more instructions executed is layout or noise, not a regression the story introduced.
fn gate(base: &CycleRows, now: &CycleRows) -> i32 {
    let mut worst = Vec::new();
    println!("\n# cycles against the baseline (now / base)");
    for ((id, col), v) in now {
        if !GATED.contains(&col.as_str()) {
            continue;
        }
        let Some(base_v) = base.get(&(id.clone(), col.clone())) else {
            continue;
        };
        let (Some(b), Some(c), Some(bi), Some(ci)) = (base_v[1], v[1], base_v[2], v[2]) else {
            continue;
        };
        let ratio = c / b;
        println!("{id}\t{col}\t{b:.1} -> {c:.1}\t{ratio:.3}\tinstructions {bi:.0} -> {ci:.0}");
        if ratio > 1.05 && ci > bi {
            worst.push(format!(
                "{id} {col}: {b:.1} -> {c:.1} ({ratio:.3}), instructions {bi:.0} -> {ci:.0}"
            ));
        }
    }
    if worst.is_empty() {
        println!("# gate: no gated cell regressed (cycles > +5% with more instructions)");
        0
    } else {
        eprintln!("# gate: REGRESSED more than 5%:\n{}", worst.join("\n"));
        1
    }
}

/// `--cycles-median a b c`: the per-cell median of several `--cycles` runs, as `@cycles` rows.
fn cycles_median(paths: &[String]) {
    let runs: Vec<CycleRows> = paths
        .iter()
        .map(|p| parse_cycles(&std::fs::read_to_string(p).unwrap_or_else(|e| panic!("{p}: {e}"))))
        .collect();
    let first = runs.first().expect("--cycles-median <run>...");
    for (key, _) in first {
        let mut cells = [None; 5];
        for (k, cell) in cells.iter_mut().enumerate() {
            let v: Vec<f64> = runs
                .iter()
                .filter_map(|r| r.get(key).and_then(|v| v[k]))
                .collect();
            if v.len() == runs.len() {
                *cell = Some(med(v));
            }
        }
        let f = |v: Option<f64>, d: usize| v.map_or("na".to_string(), |x| format!("{x:.d$}"));
        println!(
            "@cycles\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            key.0,
            key.1,
            f(cells[0], 1),
            f(cells[1], 1),
            f(cells[2], 1),
            f(cells[3], 1),
            f(cells[4], 2)
        );
    }
}

/// `--listing [workload…]`: each program's lowered ops, and the hot types' sizes.
fn listing(filters: &[String]) {
    let env = env();
    for w in workloads()
        .iter()
        .filter(|w| filters.is_empty() || filters.iter().any(|f| f == w.id))
    {
        let p = prepared(&env, w);
        let code = p.bytecode.program();
        println!(
            "## {} (3b): {} ops\n{}\n{}",
            w.id,
            code.op_count(),
            p.program.source(),
            code.listing()
        );
        if let Some((residual, fast, _)) = &p.specialized {
            println!(
                "## {} (4): {} ops\n{}\n{}",
                w.id,
                fast.op_count(),
                residual.source(),
                fast.listing()
            );
        }
    }
    println!("## layout");
    for (name, size) in typed_cel::layout_sizes() {
        println!("{name}\t{size}");
    }
}

/// `--trace <workload> <request> <column>`: warm the column, then run it ONCE between two `int3`
/// markers for `tools/steptrace.py` to single-step.
fn trace(args: &[String]) {
    let [id, req, col] = args else {
        panic!("--trace <workload> <request> <column>")
    };
    let req: usize = req.parse().expect("request index");
    let env = env();
    if id == "constant_true" {
        // The fixed per-call path alone.
        let fast = FastProgram::new(
            &env.compile("true", &CompileOpts::default())
                .expect("`true` compiles"),
        )
        .expect("`true` lowers");
        let facts = ReqFacts { vals: Vec::new() };
        let mut s = FastScratch::default();
        for _ in 0..1000 {
            black_box(fast.decide(&facts, &mut s).unwrap());
        }
        marker();
        black_box(fast.decide(black_box(&facts), &mut s).unwrap());
        marker();
        return;
    }
    let all = workloads();
    let w = all.iter().find(|w| w.id == id.as_str()).expect("workload");
    let p = prepared(&env, w);
    let mut s = FastScratch::default();
    let (fast, f): (&FastProgram, &Vec<ReqFacts>) = match col.as_str() {
        "bytecode_facts" => (
            p.bytecode.program(),
            p.facts.as_ref().expect("scalar reads"),
        ),
        "specialized" => {
            let (_, fast, f) = p.specialized.as_ref().expect("reads the policy");
            (fast, f)
        }
        other => panic!("--trace runs bytecode_facts or specialized, not {other}"),
    };
    for _ in 0..1000 {
        black_box(fast.decide(&f[req], &mut s).unwrap());
    }
    marker();
    black_box(fast.decide(black_box(&f[req]), &mut s).unwrap());
    marker();
}

#[cfg(target_arch = "x86_64")]
fn marker() {
    // SAFETY: a breakpoint trap; under the stepper it stops the tracee, alone it kills it — the
    // mode exists only for the stepper.
    unsafe { std::arch::asm!("int3") }
}

#[cfg(not(target_arch = "x86_64"))]
fn marker() {
    panic!("--trace is x86_64 only");
}
