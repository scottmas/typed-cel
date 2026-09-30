//! A decision on the fast backend over a [`Facts`] implementation allocates nothing.
//!
//! The whole point of reading host data by field: a request is not packed into values, a string
//! field is a `&str` in a register, and a warmed [`FastScratch`] holds every register the run needs.
//! A counting allocator (this binary's only test, so nothing else allocates on its thread while it
//! counts) holds the claim at ZERO allocations per decision.

use typed_cel::CompileOpts;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering};

use typed_cel::{
    CelEnvironment, CelLimits, CelTy, Facts, FastProgram, FastScratch, FieldId, Record,
};

struct Counting;

static ALLOCS: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    static COUNTING: Cell<bool> = const { Cell::new(false) };
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if COUNTING.with(|c| c.get()) {
            ALLOCS.fetch_add(1, Ordering::SeqCst);
        }
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout)
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if COUNTING.with(|c| c.get()) {
            ALLOCS.fetch_add(1, Ordering::SeqCst);
        }
        System.realloc(ptr, layout, new_size)
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

fn rec(origin: &str, fields: &[(&str, CelTy)]) -> CelTy {
    Record::new(origin, fields.iter().map(|(n, t)| (*n, t.clone()))).into()
}

fn env() -> CelEnvironment {
    let mut e = CelEnvironment::with_limits(CelLimits::default());
    e.declare(
        "req",
        rec(
            "req",
            &[
                ("path_utf8", CelTy::Bool),
                ("path_text", CelTy::Str),
                ("access", CelTy::Str),
                ("target", CelTy::Str),
                ("subject", CelTy::Str),
            ],
        ),
    );
    e.declare(
        "policy",
        rec(
            "policy",
            &[(
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
            )],
        ),
    );
    e
}

/// The `fs.open` decision's shape: a ruling tag, compared with `"allow"`.
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

struct Req {
    utf8: bool,
    text: String,
    access: &'static str,
    target: &'static str,
    subject: &'static str,
}

#[derive(Clone, Copy)]
enum Field {
    Utf8,
    Text,
    Access,
    Target,
    Subject,
}

/// A request read by field: the `Facts` a chokepoint's `Req` would implement.
struct ReqFacts<'r> {
    req: &'r Req,
    map: &'r [Field],
}

impl Facts for ReqFacts<'_> {
    fn bool(&self, f: FieldId) -> Option<bool> {
        match self.map[f.index()] {
            Field::Utf8 => Some(self.req.utf8),
            _ => None,
        }
    }
    fn num(&self, _: FieldId) -> Option<f64> {
        None
    }
    fn str(&self, f: FieldId) -> Option<&str> {
        match self.map[f.index()] {
            Field::Text => Some(&self.req.text),
            Field::Access => Some(self.req.access),
            Field::Target => Some(self.req.target),
            Field::Subject => Some(self.req.subject),
            Field::Utf8 => None,
        }
    }
    fn has(&self, _: FieldId) -> bool {
        true
    }
}

fn reqs() -> Vec<Req> {
    let mut v = Vec::new();
    for p in ["/ws/a/b.txt", "/usr/lib/x.so", "/secret/k", "/etc/passwd"] {
        for access in ["read", "write"] {
            v.push(Req {
                utf8: true,
                text: p.to_string(),
                access,
                target: "file",
                subject: "own",
            });
        }
    }
    v
}

#[test]
fn a_facts_read_allocates_nothing() {
    let env = env();
    let program = env
        .compile(OPEN, &CompileOpts::default())
        .expect("compiles");
    let mut known = env.activation();
    known
        .bind(
            "policy",
            &serde_json::json!({"fs": {
                "default": "deny", "deny_other_process_proc": false,
                "writable_roots": ["/ws", "/tmp", "/home/u", "/var/tmp", "/run/user"],
                "readonly_roots": ["/usr", "/lib", "/etc", "/opt", "/bin"],
                "deny_roots": ["/secret", "/root", "/etc/shadow"]}}),
        )
        .expect("binds");
    let residual = env
        .compile(
            program.source(),
            &CompileOpts {
                known: Some(&known),
                ..Default::default()
            },
        )
        .expect("specializes");
    let code = FastProgram::new(&residual).expect("lowers");
    assert!(code.matcher_count() >= 3, "{}", residual.source());

    let map: Vec<Field> = code
        .fields()
        .iter()
        .map(|p| {
            let names: Vec<&str> = std::iter::once(p.root()).chain(p.segments()).collect();
            match names.as_slice() {
                ["req", "path_utf8"] => Field::Utf8,
                ["req", "path_text"] => Field::Text,
                ["req", "access"] => Field::Access,
                ["req", "target"] => Field::Target,
                ["req", "subject"] => Field::Subject,
                other => panic!("the residual reads {other:?}"),
            }
        })
        .collect();

    // The decisions are the evaluator's, and not all one way.
    let reqs = reqs();
    let mut verdicts = Vec::new();
    let mut scratch = FastScratch::default();
    for r in &reqs {
        let mut act = env.activation();
        act.bind(
            "req",
            &serde_json::json!({"path_utf8": r.utf8, "path_text": r.text, "access": r.access,
                                "target": r.target, "subject": r.subject}),
        )
        .expect("binds");
        let want = residual.evaluate(&act).expect("evaluates");
        let got = code
            .decide(&ReqFacts { req: r, map: &map }, &mut scratch)
            .expect("decides");
        assert_eq!(got, want, "{}", r.text);
        verdicts.push(got);
    }
    assert!(verdicts.contains(&true) && verdicts.contains(&false));

    // Warmed: the scratch already holds every register the program needs.
    const DECISIONS: usize = 10_000;
    ALLOCS.store(0, Ordering::SeqCst);
    COUNTING.with(|c| c.set(true));
    let mut allowed = 0usize;
    for i in 0..DECISIONS {
        let r = &reqs[i % reqs.len()];
        if code
            .decide(&ReqFacts { req: r, map: &map }, &mut scratch)
            .expect("decides")
        {
            allowed += 1;
        }
    }
    COUNTING.with(|c| c.set(false));
    let allocs = ALLOCS.load(Ordering::SeqCst);
    assert!(allowed > 0);
    assert_eq!(
        allocs, 0,
        "{allocs} allocations over {DECISIONS} decisions — a read or a register boxed a value"
    );
}
