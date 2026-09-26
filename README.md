# typed-cel

A statically typed dialect of [CEL](https://github.com/google/cel-spec) in Rust. It drops the parts
of CEL that force an interpreter to check types on every step: dynamic values, the int/uint/double
split, protobuf, timestamps and optionals. In return it gets two things:

1. **It's fast.** Every program is type-checked, then compiled to register bytecode over unboxed
   values. At run time there are no type checks, no boxing and no allocation.
2. **It gets faster still if you split static inputs from dynamic ones.** Bind the inputs that
   don't change per request (a policy, a config, an allowlist) at compile time. typed-cel folds
   them into the program, so what runs per request reads only the request. With a large enough
   static input, it beats the equivalent hand-written Rust.

Numbers below are ns per evaluation, with allocations per evaluation in brackets. They come from a
Hetzner cx33 (AMD EPYC-Rome, one pinned core). Method and every table:
[`docs/PERFORMANCE.md`](./typed-cel/docs/PERFORMANCE.md).

## 1. Typed and compiled: ~100× faster than cel-rust, zero allocations

```text
req.body.account.owner_id == req.user && req.body.account.tier == "gold"
```

| | ns / eval | allocations |
|---|---:|---:|
| cel-rust 0.14.2 | 8,293 | 193 |
| **typed-cel** | **87** | **0** |
| hand-written Rust | 8.7 | 0 |

A dynamically typed CEL builds a map of boxed values for every request, looks each field up by
name, and checks operand types on every operation. typed-cel resolves every field a program reads
to an index at compile time. Your own struct answers those indices, with no conversion to JSON or
to CEL values.

```rust
use typed_cel::{CelEnvironment, CelTy, Facts, FastProgram, FastScratch, FieldId, Record};

// Your own request type. typed-cel never copies it into CEL values.
struct Req {
    user: String,
    owner_id: String,
    tier: String,
}

// Answer each field the program reads, by index, straight from the struct.
struct ReqFacts<'a> {
    req: &'a Req,
    fields: &'a [fn(&Req) -> &str],
}

impl Facts for ReqFacts<'_> {
    fn str(&self, f: FieldId) -> Option<&str> {
        Some((self.fields[f.index()])(self.req))
    }
    fn bool(&self, _: FieldId) -> Option<bool> {
        None
    }
    fn num(&self, _: FieldId) -> Option<f64> {
        None
    }
    fn has(&self, _: FieldId) -> bool {
        true
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut env = CelEnvironment::new();
    let account = Record::new("account", [("owner_id", CelTy::Str), ("tier", CelTy::Str)]);
    let body = Record::new("body", [("account", account.into())]);
    env.declare("req", Record::new("req", [("user", CelTy::Str), ("body", body.into())]));

    // Mistakes are compile errors, not runtime surprises.
    assert!(env.compile("req.usr == 'a'").is_err()); // no such field
    assert!(env.compile("req.user == 1").is_err()); // string vs number

    let program = env.compile(
        r#"req.body.account.owner_id == req.user && req.body.account.tier == "gold""#,
    )?;
    let fast = FastProgram::new(&program)?;

    // Map each field the program reads to a getter, once.
    let fields: Vec<fn(&Req) -> &str> = fast
        .fields()
        .iter()
        .map(|f| -> fn(&Req) -> &str {
            match f.segments().collect::<Vec<_>>().as_slice() {
                ["user"] => |r| &r.user,
                ["body", "account", "owner_id"] => |r| &r.owner_id,
                ["body", "account", "tier"] => |r| &r.tier,
                other => panic!("unexpected field {other:?}"),
            }
        })
        .collect();

    // Per request: no allocation once `scratch` is warm.
    let mut scratch = FastScratch::default();
    let req = Req { user: "u1".into(), owner_id: "u1".into(), tier: "gold".into() };
    assert!(fast.decide(&ReqFacts { req: &req, fields: &fields }, &mut scratch)?);
    Ok(())
}
```

## 2. Split static from dynamic: faster than hand-written Rust

Most rules take two kinds of input: things fixed when you load them (the policy, the allowlist, the
tenant's config) and things that arrive with each request. Declare both, bind the static half once,
and `specialize`. typed-cel evaluates everything that depends only on the static half,
unrolls loops over static lists, and turns large lists of string prefixes into a sorted matcher.
What runs per request is a residual program that reads only the request.

Here is an open checked against 1,000 allowed directory roots:

```text
policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))
```

| | ns / eval | allocations |
|---|---:|---:|
| cel-rust 0.14.2 | 878,800 | 18,257 |
| typed-cel, no specialization | 301,000 | 822 |
| **typed-cel, specialized** | **205** | **0** |
| hand-written Rust (loop over the roots) | 2,226 | 0 |

That's **4,300× faster than cel-rust, and 11× faster than the Rust.** The Rust version was compiled
before anyone knew the roots, so it has to loop over them. The specialized program was compiled
after, with the roots as constants. (With 13 roots the Rust loop still wins, 35 ns against 75 ns.
The crossover comes where the static data gets big.)

```rust
use serde_json::json;
use typed_cel::{CelEnvironment, CelTy, Facts, FastProgram, FastScratch, FieldId, Record};

struct Path<'a>(&'a str);

impl Facts for Path<'_> {
    fn str(&self, _: FieldId) -> Option<&str> {
        Some(self.0) // the residual reads exactly one field: req.path
    }
    fn bool(&self, _: FieldId) -> Option<bool> {
        None
    }
    fn num(&self, _: FieldId) -> Option<f64> {
        None
    }
    fn has(&self, _: FieldId) -> bool {
        true
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut env = CelEnvironment::new();
    env.declare("policy", Record::new("policy", [("roots", CelTy::list(CelTy::Str))]));
    env.declare("req", Record::new("req", [("path", CelTy::Str)]));
    let program =
        env.compile(r#"policy.roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#)?;

    // Static: bind the policy once, when it loads.
    let mut known = env.activation();
    known.bind("policy", &json!({ "roots": ["/srv/app", "/var/cache/app", "/tmp"] }))?;
    let residual = env.specialize(&program, &known)?;

    // The residual no longer reads `policy` at all.
    assert_eq!(residual.demand().roots().into_iter().collect::<Vec<_>>(), ["req"]);
    let fast = FastProgram::new(&residual)?;

    // Dynamic: per request, only the path.
    let mut scratch = FastScratch::default();
    assert!(fast.decide(&Path("/srv/app/index.html"), &mut scratch)?);
    assert!(!fast.decide(&Path("/srv/application"), &mut scratch)?);
    assert!(!fast.decide(&Path("/etc/passwd"), &mut scratch)?);
    Ok(())
}
```

The same program works unspecialized, with both halves bound per request. Specialization is an
optimization you opt into, not a different language.

## What you give up

The dialect removes whatever would force a type check at run time:

- **One number type** (`f64`). No `int`/`uint`, no `%`.
- **No dynamic values.** Lists are homogeneous, both branches of a conditional have the same type,
  and `dyn()` is gone.
- **Homogeneous equality.** `1 == "1"` is a compile error, not `false`.
- **No protobuf, timestamps or optionals.** Durations stay (`30s`), with no wall clock.
- **Undeclared names are compile errors,** even behind a short circuit. `true || typo` doesn't
  compile.

Every removal has a reason and a rejection test; the full table is in
[`typed-cel/README.md`](./typed-cel/README.md#relationship-to-spec-cel). What remains still passes
the [cel-spec](https://github.com/google/cel-spec) conformance corpus: 443 + 26 cases pass, 0 fail,
and 1,875 cases that use the removed features are excluded, each with its reason.

## Status

Experimental. Not on crates.io, and the API moves. It's the expression language of the policy
engine in cynch, a syscall-brokering sandbox, and it's here to be read and argued with.

It's a fork of [cel-rust](https://github.com/cel-rust/cel-rust) 0.14.2 (MIT). The parser is
generated from Google's `CEL.g4` (Apache-2.0), and the conformance corpus comes from
google/cel-spec v0.25.1 (Apache-2.0). See [LICENSE](./LICENSE), [NOTICE](./NOTICE) and
[`ATTRIBUTION.md`](./typed-cel/ATTRIBUTION.md).

```bash
cargo test --workspace                                  # includes both examples above
cd typed-cel/ablation && cargo bench --bench ablation   # the benchmarks, against upstream cel-rust
```
