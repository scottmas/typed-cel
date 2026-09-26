# typed-cel

A small, **fully statically typed** dialect of [CEL](https://github.com/google/cel-spec) (Common
Expression Language), in Rust.

Every program must pass a type checker before it can run. There is one number type, no `dyn`
values, no protobuf, no optionals, no timestamps, and a name nobody declared is a compile error
rather than a runtime surprise. In exchange you get things a dynamically typed CEL cannot easily
give you: diagnostics that point at the mistake when the expression is written, a list of exactly
which paths a program reads, partial evaluation against values known at compile time, and a
register-machine backend over unboxed values.

It is a fork of [cel-rust](https://github.com/cel-rust/cel-rust) 0.14.2, absorbed rather than
depended on, and it was built as the expression language of the policy engine in cynch, a
syscall-brokering sandbox. The crate itself knows nothing about sandboxes or policies; a source
scan in its test suite keeps it that way.

**Status: experimental.** It is not published to crates.io, the API moves, and it has one user.
It is here to be read and argued with.

## Why a typed dialect

Policy expressions are written once and evaluated millions of times, often by someone other than
the author, and often in a place where "the expression errored" has to turn into a decision (deny,
revoke, hold). Standard CEL defers most mistakes to evaluation time: `body.no_such_field` is an
error only when a request arrives, and `true || x` with an unbound `x` answers `true`, so a typo
can hide behind a short circuit. For this
use, every construct that exists to *defeat* the checker is a liability, so the dialect removes
them instead of making them optional:

- **Every program is checked.** Undeclared variables, unknown fields, unknown functions and
  mismatched operand types are compile errors, and a program must produce exactly the declared
  result type (`bool` by default). A typo in a generated program can never be absorbed by a short
  circuit.
- **One numeric type (`f64`).** An integer literal widens; `7 / 2` is `3.5`; there is no `uint`, no
  `int()`, and no `%` (it has no meaning a policy wants over doubles). JSON numbers are doubles
  anyway, and an integer type would be unsound for a schema that admits `1e300`.
- **No `dyn` values.** A heterogeneous list, a conditional whose branches differ, or any use of an
  `unknown`-typed field other than `has()` is refused. `dyn()` itself is gone.
- **Homogeneous equality and ordering.** `(T, T) -> bool`: comparing a number with a string, or a
  duration with a bare number, is a type error rather than `false`.
- **Durations, no clock.** `30s` desugars to `duration('30s')` (the dialect's only syntactic
  addition); `timestamp` and every wall-clock read are removed.

The full list of removals, divergences and additions, each with its reason and the test that holds
it, is the dialect table in [`typed-cel/README.md`](./typed-cel/README.md#relationship-to-spec-cel).

## What else is in here

- **Type checker** (`src/check.rs`, `src/sigs.rs`): a typed fold over the AST with structural
  record types, lists, maps, durations and bytes. Types are declared directly (`CelTy`, `Record`)
  or can be produced from a JSON schema by a schema layer, which lives outside this repository.
  The signature table *is* the dialect: `signature_table()` renders it, and a test holds the
  README's copy of it to the code in both directions.
- **Demand extraction** (`src/demand.rs`): every literal path a program reads, as data, before it
  runs — `files["/a"].closed.elapsed` reports `files ▸ "/a" ▸ "closed" ▸ "elapsed"`. A host can
  populate only what the program reads, and an operator can answer "what does this watch?" from the
  compiled artifact. A computed key is a compile error rather than a silent "read everything".
- **Partial evaluation / specialization** (`src/specialize.rs`): bind the roots that are fixed at
  compile time (a policy document, say) and `specialize`; subtrees reading only them are folded by
  the one evaluator, comprehensions over a known list unroll, and non-scalar constants go into a
  typed constant pool. The residual is an ordinary program that reads only the per-request input,
  and it never silently reads a folded root.
- **A fast typed backend** (`src/fast/`): a checked program lowers to a register program over
  unboxed values, with names resolved to fields and functions to ops. It can pause on a read that
  has not arrived and resume later, and it reads host data by field (`Facts`) instead of packing it
  into values. It is differential-tested against the reference tree evaluator on generated typed
  programs, eager and lazy, and on the conformance corpus (`tests/vm_differential.rs`,
  `tests/fast_eval.rs`).
- **Streamed / governed values** (`src/governed.rs`): evaluate over a JSON body *as it streams in*.
  The program's demand is laid over the declared type as a small trie; the document is fed as
  `Event`s and never held, undemanded members are skipped, memory is bounded by the program's shape
  and a cap rather than by the document, and the paused program resumes only when a cell it reads
  settles. (Tokenizing bytes into `Event`s is the caller's job.)
- **Lazy values and host functions** (`src/lazy.rs`, `src/hostfn.rs`): values served on access
  instead of materialized, and typed, pure host functions the checker types and partial evaluation
  treats as opaque until their arguments are known.
- **Bounds** (`src/bounds.rs`): source length, nesting depth, estimated cost, list sizes and unroll
  limits, checked at compile and bind time. The fork arrived with none.

## Quickstart

```rust
use serde_json::json;
use typed_cel::{emit, CelEnvironment, CelTy, Record, Vm};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Declare the variables an expression may name, and their types.
    let mut env = CelEnvironment::new();
    env.declare(
        "req",
        Record::new("req", [("path", CelTy::Str), ("size", CelTy::Num)]),
    );
    env.declare(
        "policy",
        Record::new(
            "policy",
            [
                ("deny_roots", CelTy::list(CelTy::Str)),
                ("max_size", CelTy::Num),
            ],
        ),
    );

    // Mistakes are compile errors, not runtime surprises.
    let typo = env.compile("req.pth == '/etc'").unwrap_err();
    assert!(typo.to_string().contains("pth"));
    assert!(env.compile("req.size == '10'").is_err()); // number vs string
    assert!(env.compile("req.size + 1.0").is_err()); // not a bool
    assert!(env.compile("req.size % 2 == 0").is_err()); // no `%` in this dialect

    let program = env.compile(
        r#"req.size <= policy.max_size
           && !policy.deny_roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#,
    )?;

    // What the program reads, before it runs.
    assert_eq!(
        program.demand().roots().into_iter().collect::<Vec<_>>(),
        ["policy", "req"]
    );

    // Evaluate with everything bound.
    let policy = json!({"deny_roots": ["/etc", "/proc"], "max_size": 1024});
    let mut activation = env.activation();
    activation.bind("policy", &policy)?;
    activation.bind("req", &json!({"path": "/ws/a.txt", "size": 10}))?;
    assert!(program.evaluate(&activation)?);

    // Specialize against the policy once; the residual reads only `req`.
    let mut known = env.activation();
    known.bind("policy", &policy)?;
    let residual = env.specialize(&program, &known)?;
    println!("{}", residual.source());
    assert_eq!(
        residual.demand().roots().into_iter().collect::<Vec<_>>(),
        ["req"]
    );

    // Lower the residual to bytecode and run it on the fast backend.
    let bytecode = emit(&residual)?;
    let mut per_request = env.activation();
    per_request.bind("req", &json!({"path": "/etc/passwd", "size": 10}))?;
    assert!(!Vm::new().eval(&bytecode, &per_request)?);

    Ok(())
}
```

The residual it prints:

```text
(req.size <= 1024.0) && (!(((req.path == "/etc") || req.path.startsWith("/etc/")) || ((req.path == "/proc") || req.path.startsWith("/proc/"))))
```

The quickstart is compiled and run as a doctest, so `cargo test` keeps it honest.

## Layout

```text
typed-cel/                 the crate (package `typed-cel`, lib `typed_cel`)
  src/                     absorbed cel-rust source (module layout unchanged) + the dialect's files
    check.rs sigs.rs ty.rs   the type checker, signature table and type lattice
    specialize.rs            partial evaluation
    demand.rs                demand extraction
    fast/                    the typed register-machine backend
    governed.rs event.rs     streamed evaluation over JSON events
    parser/gen/              ANTLR-generated parser from Google's CEL.g4
  tests/                   integration tests, including the dialect's rejection tests
  conformance/             the cel-spec conformance lane (corpus, harness, exclusions, report)
  ATTRIBUTION.md           fork point, and every change made to the absorbed source
```

## Conformance

`typed-cel/conformance/` vendors the `simple` test corpus of google/cel-spec v0.25.1 and runs every
case through the same checker and evaluator a program goes through. The current result, from
[`conformance/report.md`](./typed-cel/conformance/report.md):

```text
443 pass   26 static (the checker refused, where the spec expects an evaluation error)
0 fail     1875 excluded
```

Every excluded case names the dialect row that excludes it in
[`EXCLUSIONS.toml`](./typed-cel/conformance/EXCLUSIONS.toml) (protobuf messages, `uint`, optionals,
timestamps, extension libraries, `dyn`, and so on), and tests hold that file, the README's dialect
table and a live run of the corpus to each other. The report and the generated per-case tests are
regenerated with:

```bash
cargo run -p typed-cel --features conformance --bin conformance-report -- --write
```

For comparison, [ATTRIBUTION.md](./typed-cel/ATTRIBUTION.md) records what came in with the fork,
measured with every exclusion switched off: 1037 pass / 1307 fail of 2344.

## Building and testing

```bash
cargo test --workspace
```

Rust 1.86 or newer. The workspace sets `opt-level = 1` for `typed-cel` and `antlr4rust` in the dev
profile: at `opt-level = 0` the ANTLR-generated parser's frames are large enough to overflow a 2 MiB
test-thread stack on deeply nested input before its own recursion bound fires. A project depending
on this crate needs the same override for debug builds.

There are no benchmarks in this repository, so it makes no performance claims.

## Licensing and attribution

- The code is MIT-licensed ([LICENSE](./LICENSE)). It is a fork of cel-rust, which is MIT-licensed,
  Copyright (c) 2022 Tom Forbes and Contributors; that notice is retained in
  [`typed-cel/LICENSE-MIT`](./typed-cel/LICENSE-MIT).
- `typed-cel/src/parser/gen/` contains Google's `CEL.g4` grammar and the parser ANTLR generated from
  it; the grammar is Copyright 2018 Google LLC, Apache-2.0.
- `typed-cel/conformance/corpus/` vendors test data from
  [google/cel-spec](https://github.com/google/cel-spec) v0.25.1, Apache-2.0.

The Apache-2.0 text is in [LICENSE-APACHE](./LICENSE-APACHE); [NOTICE](./NOTICE) lists the
third-party material. [`typed-cel/ATTRIBUTION.md`](./typed-cel/ATTRIBUTION.md) records the exact fork
point and every change made to the absorbed source.
