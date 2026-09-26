//! `CelEnvironment::specialize`: fold the roots an activation bound with `bind` out of a compiled
//! program, leaving a residual `CelProgram` that reads only the rest.
//!
//! The residual is a first-class program: it evaluates, it emits, its `source()` is the rendered
//! residual, and its `demand()` names no folded root.

#[path = "support/mod.rs"]
mod support;

use std::collections::BTreeSet;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use serde_json::{json, Value as J};
use support::record;
use typed_cel::fork::ast::{EntryExpr, Expr, IdedExpr};
use typed_cel::{
    emit, CelActivation, CelEnvironment, CelError, CelLimits, CelProgram, CelTy, CelValue,
    LazyValue, Segment, Vm,
};

fn env_with(limits: CelLimits) -> CelEnvironment {
    let mut e = CelEnvironment::with_limits(limits);
    e.declare(
        "policy",
        record(
            "policy",
            &[
                (
                    "fs",
                    record(
                        "policy.fs",
                        &[
                            ("open", CelTy::Bool),
                            ("root", CelTy::Str),
                            ("deny_roots", CelTy::list(CelTy::Str)),
                        ],
                    ),
                ),
                ("limit", CelTy::Num),
            ],
        ),
    );
    e.declare(
        "req",
        record(
            "req",
            &[
                ("path", CelTy::Str),
                ("size", CelTy::Num),
                ("flag", CelTy::Bool),
            ],
        ),
    );
    e.declare("live", record("live", &[("flag", CelTy::Bool)]));
    e
}

fn env() -> CelEnvironment {
    env_with(CelLimits::default())
}

/// The known root; `open` is a boolean that, when true, decides the whole of `OPEN`.
fn policy(open: bool) -> J {
    json!({"fs": {"open": open, "root": "/ws", "deny_roots": ["/etc", "/proc"]}, "limit": 7})
}

fn known(env: &CelEnvironment, p: &J) -> CelActivation {
    let mut a = env.activation();
    a.bind("policy", p).expect("policy binds");
    a
}

fn req(path: &str, size: f64, flag: bool) -> J {
    json!({"path": path, "size": size, "flag": flag})
}

/// An activation binding `req` and nothing else.
fn rest(env: &CelEnvironment, r: &J) -> CelActivation {
    let mut a = env.activation();
    a.bind("req", r).expect("req binds");
    a
}

/// An activation binding both roots.
fn full(env: &CelEnvironment, p: &J, r: &J) -> CelActivation {
    let mut a = known(env, p);
    a.bind("req", r).expect("req binds");
    a
}

fn compile(env: &CelEnvironment, src: &str) -> CelProgram {
    env.compile(src)
        .unwrap_or_else(|e| panic!("`{src}` compiles: {e}"))
}

fn spec(env: &CelEnvironment, src: &str, p: &J) -> (CelProgram, CelProgram) {
    let original = compile(env, src);
    let residual = env
        .specialize(&original, &known(env, p))
        .unwrap_or_else(|e| panic!("`{src}` specializes: {e}"));
    (original, residual)
}

fn paths(p: &CelProgram) -> BTreeSet<Vec<Segment>> {
    p.demand().paths().map(<[Segment]>::to_vec).collect()
}

fn wide(p: &CelProgram) -> BTreeSet<String> {
    p.demand().wide_roots().map(str::to_string).collect()
}

fn outcome(r: Result<bool, CelError>) -> Result<bool, String> {
    r.map_err(|e| e.to_string())
}

const DENY: &str =
    r#"policy.fs.deny_roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#;
const OPEN: &str = "policy.fs.open || req.path.startsWith(policy.fs.root)";
const LIMIT: &str = "req.size > policy.limit + 1.0";

/// Every (program, known policy) this file specializes, for the whole-file properties.
fn cases() -> Vec<(&'static str, J)> {
    vec![
        (DENY, policy(false)),
        (OPEN, policy(true)),
        (OPEN, policy(false)),
        (LIMIT, policy(false)),
        ("policy.limit == 7.0 && req.flag", policy(false)),
    ]
}

/// Well-formed `req` values for the whole-file properties.
fn reqs() -> Vec<J> {
    [
        "/etc",
        "/etc/passwd",
        "/etcetera",
        "/proc/1/mem",
        "/home",
        "/ws/a",
    ]
    .iter()
    .flat_map(|p| [req(p, 7.5, true), req(p, 9.0, false)])
    .collect()
}

#[test]
fn worked_example_deny_roots() {
    let env = env();
    let p = policy(false);
    let (original, residual) = spec(&env, DENY, &p);
    assert_eq!(
        residual.source(),
        r#"((req.path == "/etc") || req.path.startsWith("/etc/")) || ((req.path == "/proc") || req.path.startsWith("/proc/"))"#
    );
    assert_eq!(
        paths(&residual),
        BTreeSet::from([vec![
            Segment::Root("req".to_string()),
            Segment::Key("path".to_string())
        ]])
    );
    for path in ["/etc", "/etc/passwd", "/etcetera", "/proc/1/mem", "/home"] {
        let r = req(path, 1.0, false);
        assert_eq!(
            outcome(residual.evaluate(&rest(&env, &r))),
            outcome(original.evaluate(&full(&env, &p, &r))),
            "req.path = {path}"
        );
    }
}

#[test]
fn a_known_that_decides_the_whole_expression_folds_to_a_constant() {
    let env = env();
    let (_, open) = spec(&env, OPEN, &policy(true));
    assert_eq!(open.source(), "true");
    assert_eq!(open.demand().paths().count(), 0);
    assert_eq!(open.demand().wide_roots().count(), 0);

    // `false ||` drops out: the program is checked, so `x` is a bool and `false || x` is `x`.
    let (_, closed) = spec(&env, OPEN, &policy(false));
    assert_eq!(closed.source(), r#"req.path.startsWith("/ws")"#);
}

#[test]
fn bound_numbers_stay_doubles_in_the_residual() {
    let env = env();
    let p = policy(false);
    let (original, residual) = spec(&env, LIMIT, &p);
    assert_eq!(residual.source(), "req.size > 8.0");
    for (size, want) in [(7.5, false), (9.0, true)] {
        let r = req("/x", size, false);
        assert_eq!(residual.evaluate(&rest(&env, &r)).expect("evaluates"), want);
        assert_eq!(
            outcome(residual.evaluate(&rest(&env, &r))),
            outcome(original.evaluate(&full(&env, &p, &r))),
            "req.size = {size}"
        );
    }
}

#[test]
fn residual_demand_is_the_original_minus_known_roots() {
    let env = env();
    for (src, p) in cases() {
        let (original, residual) = spec(&env, src, &p);
        let (o, r) = (paths(&original), paths(&residual));
        assert!(r.is_subset(&o), "`{src}`: {r:?} is not a subset of {o:?}");
        assert!(
            !r.iter()
                .any(|p| p.first() == Some(&Segment::Root("policy".to_string()))),
            "`{src}`: residual demand still names `policy`: {r:?}"
        );
        let (ow, rw) = (wide(&original), wide(&residual));
        assert!(rw.is_subset(&ow), "`{src}`: wide {rw:?} ⊄ {ow:?}");
        assert!(!rw.contains("policy"), "`{src}`: wide roots name `policy`");
    }
}

#[test]
fn residual_runs_without_the_known_root_bound() {
    let env = env();
    for (src, p) in cases() {
        let (_, residual) = spec(&env, src, &p);
        for r in reqs() {
            assert!(
                residual.evaluate(&rest(&env, &r)).is_ok(),
                "`{}` (from `{src}`) on {r}: {:?}",
                residual.source(),
                residual.evaluate(&rest(&env, &r))
            );
        }
    }
}

/// A record-shaped view counting every member resolution.
#[derive(Debug)]
struct Counting {
    field: &'static str,
    value: CelValue,
    reads: Arc<AtomicUsize>,
}

impl LazyValue for Counting {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        self.reads.fetch_add(1, Ordering::SeqCst);
        if name == self.field {
            Ok(self.value.clone())
        } else {
            Err(CelError::NoSuchMember {
                key: name.to_string(),
            })
        }
    }
}

fn counting(field: &'static str, value: CelValue) -> (CelValue, Arc<AtomicUsize>) {
    let reads = Arc::new(AtomicUsize::new(0));
    let view = Counting {
        field,
        value,
        reads: reads.clone(),
    };
    (CelValue::Lazy(Arc::new(view)), reads)
}

#[test]
fn a_lazily_bound_root_is_unknown_and_never_read() {
    let env = env();
    let (view, reads) = counting("flag", CelValue::Bool(true));
    let mut k = known(&env, &policy(false));
    k.bind_lazy("live", view).expect("live binds");
    let original = compile(&env, "policy.limit == 7.0 && live.flag");
    let residual = env.specialize(&original, &k).expect("specializes");
    // `true &&` drops out: `live.flag` is declared `bool`, so `true && x` is `x`.
    assert_eq!(residual.source(), "live.flag");
    assert_eq!(
        reads.load(Ordering::SeqCst),
        0,
        "specialize read the lazy view"
    );
    assert!(paths(&residual).contains(&vec![
        Segment::Root("live".to_string()),
        Segment::Key("flag".to_string())
    ]));
}

#[test]
fn bind_lazy_after_bind_makes_the_root_unknown() {
    let env = env();
    let (view, reads) = counting("limit", CelValue::Num(7.0));
    let mut k = known(&env, &policy(false));
    k.bind_lazy("policy", view).expect("policy rebinds lazily");
    let original = compile(&env, "policy.limit == 7.0 && req.flag");
    let residual = env
        .specialize(&original, &k)
        .expect("a lazily bound root is not a known root");
    assert_eq!(residual.source(), "(policy.limit == 7.0) && req.flag");
    assert_eq!(
        reads.load(Ordering::SeqCst),
        0,
        "specialize read the lazy view"
    );
}

/// The read check a residual passes before it is handed back: a tree that still reads a known root
/// — here a loop over `z`, as a fold leaves one over a range no literal can spell — is refused,
/// naming the root.
#[test]
fn surviving_known_read_is_refused() {
    let roots: BTreeSet<String> = ["z".to_string()].into();
    let residual = typed_cel::fork::parser::Parser::default()
        .parse("z.exists(x, x > u.n)")
        .expect("parses");
    let err = typed_cel::fork::check_no_known_read(&residual, &roots)
        .expect_err("the residual still reads `z`");
    assert!(err.contains('z'), "the refusal names `z`: {err}");
    assert_eq!(
        typed_cel::fork::check_no_known_read(&residual, &BTreeSet::new()),
        Ok(())
    );
}

#[test]
fn a_comprehension_variable_shadows_a_known_root_in_the_read_check() {
    let e = typed_cel::fork::parser::Parser::default()
        .parse("u.exists(z, z > 1) && z.a.b > 1")
        .expect("parses");
    let roots: BTreeSet<String> = ["z".to_string()].into();
    assert_eq!(
        typed_cel::fork::check_no_known_read(&e, &roots),
        Err("z.a.b".to_string()),
        "the shadowed `z` is not a read; the free one is, named by its whole path"
    );
    let shadowed = typed_cel::fork::parser::Parser::default()
        .parse("u.exists(z, z > 1)")
        .expect("parses");
    assert_eq!(
        typed_cel::fork::check_no_known_read(&shadowed, &roots),
        Ok(())
    );
}

#[test]
fn specialize_is_deterministic() {
    let env = env();
    for (src, p) in cases() {
        let (_, a) = spec(&env, src, &p);
        let (_, b) = spec(&env, src, &p);
        assert_eq!(a.source(), b.source(), "`{src}`");
        let lowered = |p| typed_cel::FastProgram::new(p).expect("lowers").listing();
        assert_eq!(lowered(&a), lowered(&b), "`{src}`");
    }
}

fn ids(e: &IdedExpr, out: &mut Vec<u64>) {
    out.push(e.id);
    match &e.expr {
        Expr::Unspecified | Expr::Ident(_) | Expr::Literal(_) => {}
        Expr::Select(s) => ids(&s.operand, out),
        Expr::Call(c) => {
            if let Some(t) = &c.target {
                ids(t, out);
            }
            c.args.iter().for_each(|a| ids(a, out));
        }
        Expr::List(l) => l.elements.iter().for_each(|x| ids(x, out)),
        Expr::Map(m) => {
            for entry in &m.entries {
                out.push(entry.id);
                let EntryExpr::MapEntry(me) = &entry.expr;
                ids(&me.key, out);
                ids(&me.value, out);
            }
        }
        Expr::Comprehension(c) => {
            for part in [
                &c.iter_range,
                &c.accu_init,
                &c.loop_cond,
                &c.loop_step,
                &c.result,
            ] {
                ids(part, out);
            }
        }
    }
}

#[test]
fn residual_ids_are_unique() {
    let env = env();
    let p =
        json!({"fs": {"open": false, "root": "/ws", "deny_roots": ["/a", "/b", "/c"]}, "limit": 7});
    let (_, residual) = spec(&env, DENY, &p);
    let mut all = Vec::new();
    ids(typed_cel::fork::expression_of(&residual), &mut all);
    let n = all.len();
    assert!(
        n > 12,
        "a 3-element unroll has more than 12 nodes, found {n}"
    );
    let unique: BTreeSet<u64> = all.iter().copied().collect();
    assert_eq!(unique.len(), n, "repeated ids: {all:?}");
}

fn costly() -> (CelEnvironment, CelProgram, CelActivation) {
    let env = env_with(CelLimits {
        max_cost: 1_000,
        ..CelLimits::default()
    });
    let roots: Vec<String> = (0..256).map(|i| format!("/r{i}")).collect();
    let p = json!({"fs": {"open": false, "root": "/ws", "deny_roots": roots}, "limit": 7});
    // Estimate 906: comprehension 1 + range 3 + init 1 + cond 3×100 + step 6×100 + result 1.
    let original = env
        .compile("policy.fs.deny_roots.exists(r, req.path == r)")
        .expect("the original is under the cost bound");
    let k = known(&env, &p);
    (env, original, k)
}

#[test]
fn residual_cost_is_bounded() {
    let (env, original, k) = costly();
    // The residual: 256 × 4 + 255 = 1 279.
    match env.specialize(&original, &k) {
        Err(CelError::Bounds { .. }) => {}
        other => panic!("expected CelError::Bounds, got {other:?}"),
    }
}

#[test]
fn the_residual_runs_on_the_vm() {
    let env = env();
    let (_, residual) = spec(&env, DENY, &policy(false));
    let bytecode = emit(&residual).expect("the residual emits");
    for path in ["/etc", "/etc/passwd", "/etcetera", "/proc/1/mem", "/home"] {
        let r = rest(&env, &req(path, 1.0, false));
        assert_eq!(
            outcome(Vm::new().eval(&bytecode, &r)),
            outcome(residual.evaluate(&r)),
            "req.path = {path}"
        );
    }
}

#[test]
fn a_specialize_error_carries_the_authored_source() {
    let (env, original, k) = costly();
    let err = env.specialize(&original, &k).expect_err("over the bound");
    assert_eq!(err.source(), Some(original.source()));
    assert_eq!(
        err.source(),
        Some("policy.fs.deny_roots.exists(r, req.path == r)")
    );
}

#[test]
fn a_specialize_refusal_renders_its_source_and_message() {
    let err = CelError::Specialize {
        source: Arc::from("z.exists(x, x > u.n)"),
        message: "known root `z` is not fully reducible".to_string(),
    };
    assert_eq!(err.source(), Some("z.exists(x, x > u.n)"));
    assert_eq!(
        err.to_string(),
        "z.exists(x, x > u.n)\n  known root `z` is not fully reducible"
    );
}

#[test]
fn the_residual_demand_is_exactly_what_the_residual_reads() {
    let env = env();
    // `req.flag` is read only under the branch the known `open` rules out.
    let (original, residual) = spec(
        &env,
        "policy.fs.open ? req.flag : req.size > 1.0",
        &policy(false),
    );
    assert_eq!(residual.source(), "req.size > 1.0");
    let key = |k: &str| {
        vec![
            Segment::Root("req".to_string()),
            Segment::Key(k.to_string()),
        ]
    };
    assert!(paths(&original).contains(&key("flag")));
    assert_eq!(paths(&residual), BTreeSet::from([key("size")]));
}

/// An EMPTY known list is spelled `[]` in the residual; the checker types it from its use, so
/// every shape over it re-checks, and the residual agrees with the original.
#[test]
fn an_empty_known_list_specializes() {
    let env = env();
    let empty = json!({"fs": {"open": false, "root": "/ws", "deny_roots": []}, "limit": 7});
    for src in [
        "req.path in policy.fs.deny_roots",
        "policy.fs.deny_roots.filter(r, req.path.startsWith(r)).size() > 0",
        "policy.fs.deny_roots.exists_one(r, req.path.startsWith(r))",
        r#"policy.fs.deny_roots.map(r, r + req.path).exists(x, x == "a")"#,
        r#"req.path in policy.fs.deny_roots.map(r, r + "/")"#,
        "policy.fs.deny_roots.all(r, req.path != r) && req.size in [policy.limit]",
        "size(policy.fs.deny_roots.filter(r, r == req.path)) == 0",
        "policy.fs.deny_roots.exists(r, req.path.startsWith(r))",
    ] {
        let original = compile(&env, src);
        let residual = env
            .specialize(&original, &known(&env, &empty))
            .unwrap_or_else(|e| panic!("`{src}` specializes: {e}"));
        for r in reqs() {
            assert_eq!(
                outcome(residual.evaluate(&rest(&env, &r))),
                outcome(original.evaluate(&full(&env, &empty, &r))),
                "`{src}` -> `{}` on {r}",
                residual.source()
            );
        }
    }
}

// ---- the typed constant pool ----

/// `policy = {fs: {default, writable_roots}}` and `req = {path}`, both declared as records.
fn pool_env() -> CelEnvironment {
    let mut e = CelEnvironment::new();
    e.declare(
        "policy",
        record(
            "policy",
            &[(
                "fs",
                record(
                    "policy.fs",
                    &[
                        ("default", CelTy::Str),
                        ("writable_roots", CelTy::list(CelTy::Str)),
                    ],
                ),
            )],
        ),
    );
    e.declare("req", record("req", &[("path", CelTy::Str)]));
    e
}

fn pool_policy() -> J {
    json!({"fs": {"default": "deny", "writable_roots": ["/ws"]}})
}

/// Does `e` hold a list or map LITERAL anywhere?
fn has_composite_literal(e: &IdedExpr) -> bool {
    match &e.expr {
        Expr::List(_) | Expr::Map(_) => true,
        Expr::Unspecified | Expr::Ident(_) | Expr::Literal(_) => false,
        Expr::Select(s) => has_composite_literal(&s.operand),
        Expr::Call(c) => {
            c.target.as_deref().is_some_and(has_composite_literal)
                || c.args.iter().any(has_composite_literal)
        }
        // A kept loop's plumbing carries the expander's own `[]` accumulator; only the author's
        // parts count.
        Expr::Comprehension(c) => has_composite_literal(&c.iter_range),
    }
}

#[test]
fn a_known_record_is_read_by_slot_not_reified() {
    let env = pool_env();
    let p = pool_policy();
    let req_path = BTreeSet::from([vec![
        Segment::Root("req".to_string()),
        Segment::Key("path".to_string()),
    ]]);

    // The plan's worked example: every composite it reads is indexed down to a scalar, so the
    // scalar inlines and no slot is needed. `false ||` drops out against a checked bool.
    let (_, residual) = spec(
        &env,
        r#"policy.fs.default == "allow" || req.path.startsWith(policy.fs.writable_roots[0])"#,
        &p,
    );
    assert_eq!(residual.source(), r#"req.path.startsWith("/ws")"#);
    assert_eq!(paths(&residual), req_path);

    // A composite the residual still READS is a slot, never a literal, and the source carries its
    // value in a legend.
    let (original, residual) = spec(
        &env,
        r#"policy.fs.default == "allow" || req.path in policy.fs.writable_roots"#,
        &p,
    );
    let tree = typed_cel::fork::expression_of(&residual);
    assert!(
        !has_composite_literal(tree),
        "the residual reifies a known composite: {}",
        residual.source()
    );
    assert_eq!(
        typed_cel::fork::unparse(tree).expect("renders"),
        // `false ||` drops out against a checked bool.
        "req.path in $k0"
    );
    assert_eq!(residual.source(), "req.path in $k0\n// $k0 = [\"/ws\"]");
    // The pool is not demand: nothing the host supplies stands behind a slot.
    assert_eq!(paths(&residual), req_path);
    assert_eq!(wide(&residual), BTreeSet::new());

    // It evaluates — on the evaluator and on the VM — without the known root bound.
    for path in ["/ws", "/home"] {
        let r = json!({ "path": path });
        let mut u = env.activation();
        u.bind("req", &r).expect("req binds");
        let mut ku = known(&env, &p);
        ku.bind("req", &r).expect("req binds");
        let want = outcome(original.evaluate(&ku));
        assert_eq!(outcome(residual.evaluate(&u)), want, "req.path = {path}");
        let code = emit(&residual).expect("the residual emits");
        assert_eq!(
            outcome(Vm::new().eval(&code, &u)),
            want,
            "VM, req.path = {path}"
        );
    }

    // A path read twice is ONE slot.
    let (_, twice) = spec(
        &env,
        r#"req.path in policy.fs.writable_roots || req.path + "/" in policy.fs.writable_roots"#,
        &p,
    );
    assert_eq!(
        twice.source(),
        "(req.path in $k0) || ((req.path + \"/\") in $k0)\n// $k0 = [\"/ws\"]"
    );
}

/// A record whose fields have DIFFERENT types — the shape that, written out as a map literal,
/// types as `map(string, dyn)`.
fn mixed_env() -> CelEnvironment {
    let mut e = CelEnvironment::new();
    e.declare(
        "r",
        support::record_opt(
            "r",
            &[
                ("n", CelTy::Num),
                ("s", CelTy::Str),
                ("l", CelTy::list(CelTy::Str)),
                ("o", CelTy::Str),
            ],
            &["o"],
        ),
    );
    e.declare("s", CelTy::Str);
    e
}

#[test]
fn a_constant_slot_is_typed_from_the_declaration() {
    let env = mixed_env();
    let mut k = env.activation();
    k.bind("r", &json!({"n": 7, "s": "a", "l": ["x"]}))
        .expect("r binds");
    for (src, slot_ty) in [
        // The whole record: its declared record type, not the map a literal of it would be.
        ("r.o == s", env.types().get("r").expect("declared").clone()),
        // A list field: `list(string)`, from the declaration.
        ("s in r.l", CelTy::list(CelTy::Str)),
    ] {
        let original = compile(&env, src);
        let (residual, slots) = typed_cel::fork::specialize_slots(&env, &original, &k)
            .unwrap_or_else(|e| panic!("`{src}` specializes: {e}"));
        assert_eq!(
            slots,
            vec![("$k0".to_string(), slot_ty.clone())],
            "`{src}` -> `{}`",
            residual.source()
        );
        assert!(
            !format!("{:?}", slots[0].1).contains("Dyn"),
            "`{src}`: a slot typed dyn: {:?}",
            slots[0].1
        );
    }
}

#[test]
fn the_absent_field_case_specializes_without_gradual_typing() {
    let env = mixed_env();
    let r = json!({"n": 7, "s": "a", "l": ["x", "y"]});
    let mut k = env.activation();
    k.bind("r", &r).expect("r binds");
    let original = compile(&env, "r.o == s");
    // `specialize` re-checks with the STRICT checker; a record written out as a literal would be
    // refused there.
    let residual = env
        .specialize(&original, &k)
        .unwrap_or_else(|e| panic!("specializes without gradual typing: {e}"));
    assert_eq!(
        residual.source(),
        "$k0.o == s\n// $k0 = {\"l\": [\"x\", \"y\"], \"n\": 7.0, \"s\": \"a\"}"
    );
    let mut u = env.activation();
    u.bind("s", &json!("a")).expect("s binds");
    let mut ku = env.activation();
    ku.bind("r", &r).expect("r binds");
    ku.bind("s", &json!("a")).expect("s binds");
    let native = original.evaluate(&ku).expect_err("`o` is absent");
    let spec_err = residual
        .evaluate(&u)
        .expect_err("`o` is absent in the residual too");
    let vm_err = Vm::new()
        .eval(&emit(&residual).expect("emits"), &u)
        .expect_err("and on the VM");
    let tail = |e: &CelError| e.to_string().lines().last().unwrap_or_default().to_string();
    assert_eq!(tail(&native), "  could not be evaluated: No such key: o");
    assert_eq!(tail(&spec_err), tail(&native));
    assert_eq!(tail(&vm_err), tail(&native));
}
