# typed-cel

A statically checked CEL dialect, built for the policy language of cynch (a syscall-brokering
sandbox). An expression is a boolean predicate over typed data whose variables are declared up
front, so a policy's mistakes are found at compile time rather than when a request arrives. A
compiled program also reports what it reads and what shape it has without being run. It is a fork
of cel-rust 0.14.2, absorbed rather than depended on ([ATTRIBUTION.md](./ATTRIBUTION.md)), because what the dialect wants most are
subtractions.

## Contents

- [Quickstart](#quickstart) · [Installation](#installation) · [Core Concepts](#core-concepts)
- [Why a typed dialect](#why-a-typed-dialect) — what the dialect gives up, and what it buys, measured
- [Usage](#usage) — declaring, compiling, evaluating, bytecode, specializing, demand, proving
  presence, shape queries, lazy values
- [API Reference](#api-reference) and [Signatures](#signatures) — every function the dialect has
- [Configuration](#configuration) — features and bounds
- [Relationship to spec CEL](#relationship-to-spec-cel) — **the divergences live here**
  - [Compatibility](#compatibility) · [Removed](#removed) · [Not implemented](#not-implemented) ·
    [Divergences](#divergences) · [Added](#added)
- [Testing](#testing)

## Quickstart

```rust
use typed_cel::{CelEnvironment, CelTy, CompileOpts, Record};
use serde_json::json;

let mut env = CelEnvironment::new();
env.declare("body", Record::new("body", [("user_id", CelTy::Str), ("amount", CelTy::Num)]));
env.declare("session", Record::new("session", [("user_id", CelTy::Str)]));

let program = env.compile("body.user_id == session.user_id && body.amount < 100", &CompileOpts::default())?;

let mut activation = env.activation();
activation.bind("body", &json!({"user_id": "u1", "amount": 42}))?;
activation.bind("session", &json!({"user_id": "u1"}))?;

assert_eq!(program.evaluate(&activation)?, true);
```

`env.compile("body.no_such_field == 1", &CompileOpts::default())` fails at build time with a caret under the field and the
list of fields that do exist.

## Installation

```toml
[dependencies]
typed-cel = { git = "https://github.com/scottmas/typed-cel" }   # default features: bytes
```

Depends on `antlr4rust` (the generated parser runtime). No native code, no platform restriction.
The workspace root `Cargo.toml` sets `[profile.dev.package.typed-cel] opt-level = 1` (and the same
for `antlr4rust`): at `opt-level = 0` the ANTLR parser's frames overflow a test thread's 2 MiB stack
before its own recursion bound fires. A consumer outside this workspace needs the same override for
debug builds.

## Core Concepts

An expression is standard CEL, narrowed. What a policy author can write:

```
body.user_id == session.user_id
body.documents.all(d, d.owner_id == session.user_id)
uptime > 40s && metrics.cpu.max["40s"] < 0.05
listeners.exists(p, listeners[p].listen.elapsed > 10s)
```

Five things about that are worth knowing before writing any of it:

- **The result must BE `bool`.** Not "be truthy", not "be compatible with". An expression that
  evaluates to a string is a compile error rather than a condition that is always true. A program
  with more than two outcomes is compiled with `CompileOpts::returning`, which requires the declared
  type EXACTLY in the same way — `dyn` never qualifies.
- **There is one numeric type.** The checker knows one number type, `double`; there is no `int`
  and no `uint` to reconcile. Its VALUES are held exactly: an integer (up to `u64::MAX`) is an
  integer, so `9007199254740993 != 9007199254740992`; anything else is an `f64`. Comparison is by
  exact value across the two, integer arithmetic is exact and errors on overflow, and division is
  real division — `7 / 2` is `3.5`, `1 / 0` is `+inf` — so no operator changes meaning with the
  operand's provenance. There is no `%`.
- **Durations are the only temporal type.** `30s` is an alias for `duration('30s')`, and it is the
  whole of this dialect's syntactic deviation from spec CEL. There is no `timestamp` and no clock
  read — a condition that fires because NTP stepped is not a policy.
- **There are no custom functions.** The [signature table](#signatures) is a closed enumeration, so
  `is_owner(body.user_id)` is an *unknown function* error rather than something a caller can enable.
  The DIALECT declares none; an embedding environment may register typed, PURE host functions
  (`register_host`) that belong to that environment alone — a numeric argument arrives as
  `CelValue::Int`, `UInt` or `Num`, read with `CelValue::num` — and a host function never shadows a
  dialect name — a built-in, a removal, a macro or an operator spelling is refused at registration.
- **There are no optional values, and absence is real.** An optional field, a key only an index
  signature allows, and any `map` key may be absent, and a read of one compiles only where it is
  PROVEN present — by `has`/`in`, by iterating the container, by a known value, or by an
  `unsafe_map` declaration. See [Proving presence](#proving-presence):

  ```text
  schema:   {"discount?": "number"}
  policy:   body.discount < 10                          -> compile error: `body.discount` may be absent
  fixed:    has(body.discount) && body.discount < 10    -> compiles  (absent: false)
  or:       !has(body.discount) || body.discount < 10   -> compiles  (absent: true)
  or:       body.?discount.orValue(0) < 10              -> compiles  (absent: reads 0)
  ```

Comparisons are homogeneous — `(T, T) -> bool` with `T` a real type variable — so
`body.amount == session.user_id` is a build error, and so is `elapsed > 300` where a duration was
meant. A dropped unit suffix must not compare against whatever unit the evaluator carries
internally.

The pieces, in the order a caller meets them:

| piece | role |
|---|---|
| `CelEnvironment` | the roster of variables and their types; compiles many expressions |
| `CelProgram` | one checked expression: evaluate it, ask what it reads, ask its shape |
| `CelActivation` | the values for one evaluation, bound against the environment's roster |
| `DemandSet` | the literal paths a program reads, as data |
| `LazyValue` | the one extension point: a value served on access instead of materialized |

The crate is environment-agnostic. It knows about types, not about what a `body`, a `listener` or
a `grant` is; each roster is just a declaration, made by the application that embeds it.

## Why a typed dialect

This dialect gives up most of spec CEL's dynamic surface — on purpose — in exchange for two things
spec CEL cannot have: every program is checked before it can run, and a checked program compiles to
register bytecode over unboxed values. The table measures each step of that trade, in ns per
decision (allocations per decision); the columns are defined in
[`docs/PERFORMANCE.md`](./docs/PERFORMANCE.md).

<!-- ablation:begin -->
| workload | Rust | (1) upstream | (2) typed tree † | (3a) bytecode, activation | (3b) bytecode, facts | (4) + partial evaluation |
|---|---:|---:|---:|---:|---:|---:|
| `fs_open_allow_all` | 8.1 ns (0) | 4810 ns (92) | 4612 ns (92) | 455 ns (0) | n/a (composite root: `policy.fs.readonly_roots`) | 32.4 ns (0) |
| `fs_open_13` | 33.2 ns (0) | 11.1 µs (248.8) | 11.0 µs (248.8) | 627 ns (0) | n/a (composite root: `policy.fs.readonly_roots`) | 73.4 ns (0) |
| `fs_open_1000` | 1386 ns (0) | 865.2 µs (17064.4) | 829.6 µs (17064.4) | 11.0 µs (0) | n/a (composite root: `policy.fs.readonly_roots`) | 161 ns (0) |
| `prefix_13` | 36.3 ns† (0) | 11.8 µs (247.8) | 11.7 µs (247.8) | 447 ns† (0) | n/a (composite root: `policy.roots`) | 48.0 ns† (0) |
| `nested_fields` | 8.7 ns (0) | 8878 ns (193) | 8460 ns (193) | 239 ns (0) | 35.9 ns (0) | — (reads no policy) |
| `all_items` | 18.0 ns (0) | 21.5 µs (455.4) | 20.7 µs (481.8) | 782 ns (0) | n/a (composite root: `req.body.items`) | — (reads no policy) |
| `policy_residual` | 25.1 ns (0) | 6357 ns (143.1) | 6223 ns (143.1) | 548 ns (0) | n/a (composite root: `policy.methods`) | 63.2 ns (0) |

† Column (2) is historical: measured on the typed dialect's first engine, since deleted (docs/PERFORMANCE.md, "Historical"). Every other column is this run.
<!-- ablation:end -->

**What you give up.** Each is a row in [Relationship to spec CEL](#relationship-to-spec-cel):

- integer and `uint` TYPES — one number type (integers inside it are still exact), so `7 / 2` is `3.5` and `1 / 0` is `+inf` (`removed: integer division`, `removed: uint`)
- `%` (`removed: modulo`)
- `dyn()` and every dyn value: heterogeneous lists and maps, branches of different types (`removed: dyn()`, `removed: dyn values`)
- heterogeneous equality (`diverges: equality is homogeneous`)
- ordering beyond numbers, strings and durations (`removed: ordering beyond numbers and strings`)
- timestamps and every clock read (`removed: timestamp`)
- protobuf messages and enums (`removed: protobuf`)
- optional values: `optional.*`, `.value()`, `[?x]`, `{?k: v}` (`removed: optional values`) —
  absence is proven with `has()`/`in`, and an optional READ with a default (`x.?f.orValue(d)`,
  `added: optional reads`) is spelled as spec CEL spells it
- type values and conversion functions: `type()`, `int()`, `string()`, … (`removed: type values`, `removed: type conversion functions`)
- `size()` on strings (`removed: size() on strings`)
- bytes concatenation (`removed: bytes concatenation`)
- the extension libraries (`removed: extension libraries`)
- two-variable comprehensions (`not implemented: two-variable comprehension macros`)
- container name resolution (`not implemented: container name resolution`)
- backtick field selection (`not implemented: backtick-quoted field selection`)
- custom functions, except typed host functions an embedder declares (`added: host functions`)

Against cel-spec v0.25.1 that is 1875 of 2344 cases excluded (the block in
[Compatibility](#compatibility)).

**What you get.**

- Mistakes at compile time, with a caret: `body.no_such_field`, `elapsed > 300`,
  `body.amount == session.user_id` and an unknown function are all build errors, never a runtime deny.
- One engine. Every program — evaluated, specialized, streamed, paused and resumed — runs on the same
  register backend. There is no second implementation to disagree with.
- Speed: `fs_open_1000` with its policy bound decides in 161 ns — 5373.9× faster than upstream
  cel-rust 0.14.2 (865.2 µs) and 8.6× faster than the hand-written Rust reference (1386 ns), which
  scans the 1000 roots linearly. `policy_residual` decides in 63.2 ns against upstream's 6357 ns, 100.6×.
- Zero allocations per decision on the facts path: every (3b) and (4) cell reads `(0)`, and
  `tests/fast_alloc.rs` holds it at exactly 0 over 10 000 decisions.
- Partial evaluation: bind the policy once, and the per-request program reads only the request (the
  [Specializing](#specializing) example; the `policy_residual` row).
- Predictable cost: depth, cost and input size are bounded at build time (`CelLimits`); a decision is
  a loop over a fixed op list with no allocation and no dynamic dispatch on values.

**What it costs.** A compile runs the checker and the lowering, so it is slower than upstream's
parse: `policy_residual` compiles and emits in 151.9 µs against upstream's 91.8 µs, and `fs_open_13`
in 630.5 µs against 551.0 µs. A policy compiles once per process.

<!-- historical:begin -->
Column (2) was measured once, on the typed tree evaluator this crate forked from cel-rust, before
that evaluator was deleted — on the last revision that still carried it (typed-cel `55d75a8`, whose
engine source is identical to the measured one up to formatting). It isolates what typing alone
bought (1.0× on every headline row). See [`docs/PERFORMANCE.md`](./docs/PERFORMANCE.md),
"Historical".
<!-- historical:end -->

## Usage

### Declaring an environment

An environment is the variables an expression may name and their field structure. One environment
serves many expressions — `compile` takes `&self` — because a policy compiles dozens of assertions
against one endpoint's schemas.

Declare each variable with its type:

```rust
let mut env = CelEnvironment::new();
env.declare("uptime", CelTy::Duration);                    // a scalar
env.declare("files", CelTy::map(CelTy::Str, CelTy::Num));  // a keyed root
env.declare(                                               // a record, without naming `Rc`
    "session",
    Record::new("session", [
        ("user_id", CelTy::Str),
        ("tenant_id", CelTy::Str),
    ]),
);
```

`Record::new` chains: `.with_optional(["a"])` marks the fields a schema declared with `?`, and
`.with_index(CelTy::Str, CelTy::Str)` carries an index signature so an undeclared key stays
nameable. Where a JSON schema already describes the data, generating these declarations from it
(in a schema layer outside this crate) is preferable to writing them twice — two type systems
describing one request body is two things to keep in step, and the one nobody edits is the one that
goes wrong.

### Compiling an expression

`compile` runs desugar → bounds → parse → check, and returns a `CelProgram` or the first thing that
went wrong. This is where a policy's mistakes are found:

```rust
let cond = CompileOpts::default();                                 // a condition: `bool`
let program = env.compile("body.user_id == session.user_id", &cond)?;   // ok

env.compile("body.no_such_field == session.user_id", &cond)      // error, at build:
//   body.no_such_field == session.user_id
//        ^^^^^^^^^^^^^
//   no field `no_such_field` on `body`; available: user_id, tenant_id, amount
```

The caret points at the column the **author** typed, not the desugared one — a diagnostic quoting
source the author did not write is a diagnostic about the wrong program. `CelProgram::source`
returns the authored form for the same reason.

A failed compile carries structured parts rather than one formatted string, so a caller that knows
the endpoint and the file position assembles the final rendering: `CelError::source`,
`CelError::span`, `CelError::available`. `Display` renders the first error only — a cascade is a
diagnostic nobody reads — while `CelError::all` returns every error the checker found, for a caller
listing a whole file's problems.

### Evaluating

Evaluation returns `Result<bool, _>`. `Ok(true)` / `Ok(false)` mean the expression evaluated to a
bool; everything else — an evaluation error, or a non-bool result — is `Err`:

```rust
let mut activation = env.activation();
activation.bind("body", &json)?;          // schema-directed: the TYPE leads, not the JSON's shape

program.evaluate(&activation)?;           // Result<bool, CelError>
```

**The library does not say what a failure should CAUSE.** That is the caller's, and it points a
different way at every site: an assertion that cannot be evaluated must *deny* the request, a
`revoke_after` that cannot be evaluated must *revoke* the grant, and a transition step that cannot
be evaluated must *hold* the permission it already has rather than advance. One enum here could not
have named the third, and a single "false on error" convention would make the first fail *open*.
The mapping lives with whoever chose it.

Binding is **schema-directed**: the declared type leads and the JSON is pulled to match, rather than
the JSON's shape choosing a type. A declared-optional field that is absent at runtime stays absent,
so `NoSuchKey` fires and the caller maps the `Err` to a deny — filling it with `null` would make
`body.a == body.b` true when *neither* exists. A CHECKED program cannot reach that path through an
optional field or a `map` key (it must prove presence first, [Proving presence](#proving-presence));
the binder keeps the behaviour as defence in depth, for a value that breaks its type's promise — a
lazy view missing a member, a host result missing a field, an `unsafe_map` runtime that did not
pre-create a key (`a_broken_promise_is_still_a_run_time_error`).

### Running bytecode

A compiled program can also be lowered for the fast backend — a register machine over unboxed
values, every name resolved to a field or a constant and every function to an op at lowering:

```rust
let program = env.compile("body.amount > 5", &CompileOpts::default())?;
let bytecode = typed_cel::emit(&program)?;       // Result<CelBytecode, CelError>
let vm = typed_cel::Vm::new();
vm.eval(&bytecode, &activation)?;                 // Result<bool, CelError> — same answers as program.evaluate
```

`Vm::eval` and `CelProgram::evaluate` are the same backend run over an activation, so they answer
identically, including the text of their errors. A failure means the same thing it means under
[Evaluating](#evaluating): the caller decides what it causes. There is one backend (`src/fast/`),
and every way of running a program — evaluated, emitted, specialized, streamed, paused and resumed —
runs on it. `FastProgram::decide` runs the same program over a caller's own
`Facts` — fields read by index, nothing packed into values — and a `VmRun` pauses and resumes it
for data still arriving.

### Specializing

A decision whose configuration is fixed for a process's life can be compiled against it once. Bind
the fixed roots and compile with them KNOWN (`CompileOpts::known`); the result is an ordinary
`CelProgram` over the remaining roots. Checking happens inside that same compile, with the known
values in view:

```rust
let source = r#"policy.fs.deny_roots.exists(r, req.path == r || req.path.startsWith(r + "/"))"#;
let mut known = env.activation();
known.bind("policy", &json!({"mode": "enforce", "fs": {"root": "/ws", "deny_roots": ["/etc", "/proc"]}, "limit": 7}))?;

let residual = env.compile(source, &CompileOpts { known: Some(&known), ..Default::default() })?;   // Result<CelProgram, CelError>
residual.source();   // ((req.path == "/etc") || req.path.startsWith("/etc/")) || ((req.path == "/proc") || req.path.startsWith("/proc/"))
residual.demand();   // [req ▸ path]
```

The residual evaluates, emits and runs on the backend like any compiled program, and agrees with the
original on every value of the roots it still reads. Three rules a caller relies on:

- **`bind` roots are folded.** Every subtree reading only them is computed by the backend and
  written back — a scalar as a literal, a list or map as a typed constant slot (`$k0`, spelled in a
  `// $k0 = …` line of `source()`); `exists`/`all`/`map` over a bound list unroll, up to
  `CelLimits::max_unroll` elements.
- **`bind_lazy` roots are not.** A view is never read at specialize time — rebinding a name lazily
  after `bind` makes it unknown again.
- **A residual never reads a folded root.** A value no literal can spell leaves a read behind, and
  that is `CelError::Specialize` rather than a half-folded program. The residual's cost is bounded
  again with the environment's limits (`CelError::Bounds`), because unrolling replaces the
  estimate's assumed iteration count with the real one.

`residual.demand()` is harvested by checking the residual against the same roster, so it is exactly
what the residual reads: a read under a branch the fold ruled out is gone. A residual that does not
check is refused as `CelError::Specialize`. An error the fold meets (`1 / 0`, a missing key) is
never baked in: the node stays and fails at run time, in place.

### Extracting demand

The crate's most unusual export, and the one with no analogue in any other CEL implementation. It
answers **"what does this expression read?"** as data, before anything runs:

```rust
let program = env.compile("files[\"/run/secrets/tls.key\"].closed.elapsed > 30s", &CompileOpts::default())?;
program.demand().paths();       // [ files ▸ "/run/secrets/tls.key" ▸ "closed" ▸ "elapsed" ]
program.demand().keyed_reads(); // [ ("files", "/run/secrets/tls.key", "closed", "elapsed") ]
```

Two consumers need it, for different reasons:

- **A host populates only these paths.** An expression evaluated for the life of a process (a
  sandbox monitor, say) has per-tick work proportional to the *policy* rather than to the state it
  ranges over. A policy naming one file leaves the state's file map at one entry no matter how many
  files are open.
- **An operator can answer "what does this policy watch?" from the artifact**, without running it:
  a policy whose watched surface cannot be enumerated cannot be reviewed.

Demand is also what makes the SYSTEM environment's keyed roots total. Every demanded path exists in
the activation from load, zero-valued, so `files["/a"].closed.elapsed` reads `0s` for a file that
was never touched — which is why those roots are declared `unsafe_map` (`added: unsafe_map`) and a
read of one needs no presence proof. Everything else proves presence
([Proving presence](#proving-presence)).

A computed key (`files[somevar]`) is a build error rather than a widening, because widening one
unreviewable expression silently turns the whole policy into "populate everything". The one
exception is a comprehension over the same map, where the iteration itself proves the range.

### Proving presence

A read is **possibly absent** exactly when its container is filled by someone other than the
program: a record field the schema declared optional (`?`), a key only a record's index signature
allows, and any `map` key. A required field needs nothing. A possibly-absent read compiles only
where one of four things proves it present, and nothing else does:

1. a guard — `has(p)` / `'k' in m` — in a position the rules below allow;
2. iteration over the same container (`m.all(k, m[k] > 0)`);
3. a KNOWN value supplied to `compile` (`CompileOpts::known`) that contains the path — a map
   literal is one too, so `{"a": 1}["a"]` compiles and `{"a": 1}["b"]` does not;
4. the container's declared type is `unsafe_map(K, V)`, whose declarer asserts every nameable key
   reads as a value (`added: unsafe_map`).

A **presence path** is a root (a declared variable, or a comprehension variable identified by its
SCOPE, never by its name) followed by literal keys. A field select and a literal-key index produce
the same segment, so `has(m.k)` proves `m["k"]`. `P(e)` is what `e` proves present when it is
`true`, `N(e)` when it is `false`:

| expression | `P` (when true) | `N` (when false) |
|---|---|---|
| `has(p)` (a `Select` with `test`) | `{p}` and every prefix of `p` | `{}` |
| `k in x`, `k` a string literal (`x` a map or a record — the one guard for a key no selector can spell, `'x-trace' in headers`) | `{x.k}` and every prefix | `{}` |
| `!e` | `N(e)` | `P(e)` |
| `a && b` | `P(a) ∪ P(b)` | `{}` |
| `a \|\| b` | `{}` | `N(a) ∪ N(b)` |
| anything else | `{}` | `{}` |

Proofs flow down, and ORDER-INSENSITIVELY: each side of `a && b` is checked with what the other
side proves when true, and each side of `a || b` with what the other proves when false — CEL's
`&&`/`||` absorb an error on either side, so `body.o > 1 && has(body.o)` is as safe as its mirror.
A guard never proves the reads inside itself: `has(a.b)` READS `a`, so `has(a) && has(a.b) &&
a.b.c > 1` is the chain. The one exception to the symmetry is `c ? t : f`: `t` is checked with
`P(c)`, `f` with `N(c)`, and `c` with nothing new, because a conditional does NOT absorb an error in
its condition. A read whose operand has no presence path (`(c ? x : y).f`, a host call's result) is
proven only by its operand's TYPE.

This is TypeScript's `noUncheckedIndexedAccess`, on by construction. The fix a refusal suggests is
one of two guards, depending on what the absent case should mean:

```text
has(body.discount) && body.discount < 10     // absent: false
!has(body.discount) || body.discount < 10    // absent: true
body.?discount.orValue(0) < 10               // absent: reads 0
```

#### Optional reads

Spec CEL's optional reads compile, with spec CEL's answers (`added: optional reads`), and there is
still no optional VALUE: `x.?f` and `m[?k]` are legal only as the operand of `.orValue(d)`,
`.hasValue()` or `has()`. The parser rewrites each into the guards that prove it, so the presence
rules above are the only rules. A chain is a root followed by segments, `k0` its first optional
segment; `P_i` is the root followed by segments `1 … i` written as PLAIN reads, and `test(i)` is
`has(P_{i-1}.f)` for a field segment and `k in P_{i-1}` for an index segment:

| authored | rewritten |
|---|---|
| `chain.orValue(d)` | `test(k0) && … && test(n) ? P_n : d` |
| `chain.hasValue()` | `test(k0) && … && test(n)` |
| `has(chain.f)` | `test(k0) && … && test(n) && has(P_n.f)` |

```cel
body.?shipping.?address.?zip.orValue('')
  -> has(body.shipping) && has(body.shipping.address) && has(body.shipping.address.zip)
       ? body.shipping.address.zip : ''
req.headers[?'x-tenant'].orValue('default')
  -> 'x-tenant' in req.headers ? req.headers['x-tenant'] : 'default'
body.items.all(i, i.?note.orValue('') != 'x')
  -> body.items.all(i, (has(i.note) ? i.note : '') != 'x')
```

Once a chain is optional, every later segment is: `{}.?null_key.invalid.hasValue()` is `false`
(the corpus case `map_undefined_entry_hasValue`), and `body.?s.z.orValue('')` guards `z` as well as
`s`. A plain read BEFORE the first `.?` is an ordinary read and must be proven like any other, so
with an optional `shipping`, `body.shipping.?zip` is refused and `body.?shipping.?zip` is the
spelling. The default is evaluated only when the value is absent (`diverges: orValue's default is
lazy`) — it is the `: d` arm of the rewrite. A refusal of an unproven read offers the optional read
as a third fix. An optional index on a LIST (`xs[?i]`) is refused: bounds are not presence, and
`size(xs) > i ? xs[i] : d` is the spelling (`not implemented: optional index on a list`).

### Querying an expression's shape

Demand answers "what does this read?". `conjuncts` answers "what shape is this?" — enough to write
a lint over an expression, without re-parsing the authored source in the caller:

```rust
let program = env.compile("uptime > 40s && metrics.cpu.max[\"40s\"] < 0.05", &CompileOpts::default())?;
program.conjuncts();
// [ Conjunct { path: uptime,                       operator: ">", literal: Duration("40s") },
//   Conjunct { path: metrics ▸ "cpu" ▸ "max" ▸ "40s", operator: "<", literal: Num(0.05) } ]
```

The path uses the same `Segment` vocabulary `DemandSet` does, so a caller matches against one thing
and not two. A duration is reported **as the author wrote it** — `40s`, not the `duration('40s')`
the alias expanded to — because a lint comparing window keys against guard thresholds compares
`40s` to `40s`.

`&&` is the only connective a guard can be proven through, so it is the only one flattened. A `||`,
a comprehension or a call is **one opaque conjunct**: reported, with no operator and no literal.
Flattening `_||_` as well would produce a list that reads like a conjunction and is not one, and a
lint built on it would approve exactly the expression it exists to reject. A conjunct whose right
side is not a constant is reported with `literal: None` rather than dropped, for the same reason —
a lint that silently skips what it cannot read is a lint that passes.

It is deliberately shallow: enough to lint a shape, not enough to reimplement the checker. A caller
that needs more wants a second narrow query, not the AST.

### Serving values on access

The library materializes an activation from JSON by default, and that is the right shape for a
request: the body is already a `serde_json::Value` and it is read once. It is the wrong shape for a
condition evaluated on every tick for the life of a sandbox — building a map of the whole state per
evaluation makes the cost of a policy proportional to the *state* rather than to the *policy*.

So there is exactly one extension point:

```rust
pub trait LazyValue: Send + Sync + Debug + 'static {
    fn member(&self, name: &str) -> Result<CelValue, CelError>;
    fn keys(&self) -> Option<Box<dyn Iterator<Item = &CelKey> + '_>> { None }
}

activation.bind_lazy("files", CelValue::Lazy(Arc::new(my_view)))?;
```

`member` serves `x.field` and `x["key"]` alike — CEL does not distinguish them. `keys` is what makes
a value iterable, so `m.exists(k, m[k].n > 0)` works; returning `None` means "not a container", and
a comprehension over it is an error rather than a silently empty one. Keys come out **by reference**
(`&CelKey`), because a signature handing back owned `String`s would allocate per key per tick and
undo the whole point.

Everything crossing the boundary is a `CelValue`, the crate's one value type — what a caller binds,
what a lazy value or a host function returns, and what a program's result is:

```rust
pub enum CelValue {
    Bool(bool), Num(f64), Int(i64), UInt(u64), Str(Arc<str>), Duration(CelDuration),
    Bytes(Arc<[u8]>), List(Arc<[CelValue]>), Map(CelMap), Null, Lazy(Arc<dyn LazyValue>),
}

CelValue::record([(CelKey::from("user_id"), CelValue::from("u1"))]);   // a record is a string-keyed map
CelDuration::from_millis(40_000);                                       // the unit is always explicit
```

A `CelMap` holds its entries sorted by `CelMapKey` (`Num < Bool < Str`), so lookup is a binary
search and a comprehension over a map is deterministic. A number key is integral: `1` and `1.0` name
one key, and `1.5` names none. Every variant is cheap to clone — composites and strings are shared.

**The fork is private.** `common`, `context`, `objects`, `functions` and `parser` are private
modules and no parser or evaluator type is re-exported, so the fork's internals stay ours to change
without breaking a caller. That claim is asserted by `tests/purity.rs::the_fork_is_not_public`,
because for as long as it stood unchecked it was false. The fork's `Program` — parse with no
checker, run with no roster — is crate-private too, so `CelEnvironment::compile` is the only way a
caller gets a program. One gap remains: the fork's `ExecutionError` is still declared `pub` directly
in `lib.rs`. Treat it as internal; it is not part of the contract.

The crate's own harnesses — the cel-spec corpus and `tests/dialect.rs` — need a program's value
of any type, not only a `bool`, because a corpus case's answer can be a list or a string. They run
the backend for it through `typed_cel::fork::fast_value`, after the checker admits the case
(`fork::compile_any`). `fork` is `#[doc(hidden)]` and gated on the `conformance` feature that
nothing but this crate's own test build enables. Nothing under `fork` is contract, and changing it
is not a breaking change.

## API Reference

`cargo doc -p typed-cel --open` for the full docs. The public contract:

| item | purpose |
|---|---|
| `CelEnvironment` | `new`, `with_limits`, `declare(name, ty)`, `parse`, `compile(source, &CompileOpts)`, `activation`, `limits`, `types` |
| `CelProgram` | `evaluate(&CelActivation) -> Result<bool, CelError>`, `source`, `demand`, `conjuncts` |
| `CelActivation` | `bind(name, &serde_json::Value)` (schema-directed), `bind_lazy(name, CelValue)`, `bind_fact(name, CelValue)` |
| `CelError` | `source`, `span`, `available`, `all`; `Display` renders the first error only |
| `CelTy`, `Record`, `Relax`, `Unusable` | the type lattice: `CelTy::list`, `CelTy::map`, `Record::new`/`with_optional`/`with_index`, `admits`/`admits_relaxed`; `Unusable` is the named reason a schema layer could not give a variable a type, refused only where an expression reads it |
| `DemandSet`, `Segment` | what a program reads: `paths`, `roots`, `wide_roots`, `keyed_reads`, `union`, `reverse_index` |
| `Conjunct`, `Literal` | the top-level `&&` shape of a program |
| `CelValue`, `CelMap`, `CelMapKey`, `CelDuration` | the one value type: `CelValue::record`, `CelValue::list`, `From<bool/f64/&str/String>`; `CelMap::new`/`get`/`iter` |
| `LazyValue`, `CelKey` | values served on access |
| `emit`, `CelBytecode`, `Vm` | a `CelProgram`'s bytecode, run explicitly; `Vm::new().eval(&bytecode, &activation)` is the backend `evaluate` runs |
| `CelLimits` | bounds (see [Configuration](#configuration)) |
| `desugar`, `SpanMap`, `DesugarError`, `Span` | the `30s` alias expansion and its authored-column map |
| `TypeEnv`, `CheckError`, `BindError` | the checker's roster and its individual errors |
| `signature_table()` | every function and overload, rendered as the table below |
| `StreamedProgram`, `StreamedRun`, `GovernedDoc`, `Event` | evaluate over a JSON document as it streams in, one `Event` at a time |

`typed_cel::fork` exists only under the `conformance` feature, is `#[doc(hidden)]`, and is not
contract.

## Signatures

Every function this dialect has, and nothing else. `tests/signatures.rs` compares this table
against `src/sigs.rs` **in both directions** — a hand-maintained doc beside a hand-maintained table
drifts within a month, so the test parses the rows rather than trusting them.

Making the table a CLOSED enumeration is what turns "outside the dialect" into a structural error
rather than a thing someone remembers. There is no fallback arm for an unrecognised name:
`is_owner(body.user_id)` is an **unknown function** error, not a type error and not a silent pass.

`T`, `K` and `V` are type VARIABLES, not wildcards — every `T` in one overload unifies to the same
type, which is what makes `(T, T) -> bool` reject `body.amount == session.user_id`.

| function | overloads | note |
|---|---|---|
| `_==_` | `(T, T) -> bool` | homogeneous. Comparing a string to a number is a policy bug even though the runtime would answer `false`: an expression that can never be true is a build error. `x == null` is legal on any type, including `dyn` |
| `_!=_` | `(T, T) -> bool` | as above |
| `_<_` | `(double, double) -> bool`, `(string, string) -> bool`, `(duration, duration) -> bool` | one numeric row, because `diverges: one numeric type` leaves no int/double/uint split to reconcile |
| `_<=_` | `(double, double) -> bool`, `(string, string) -> bool`, `(duration, duration) -> bool` | |
| `_>_` | `(double, double) -> bool`, `(string, string) -> bool`, `(duration, duration) -> bool` | `elapsed > 300` is a BUILD ERROR: a dropped unit suffix must not compare against whatever unit the evaluator carries internally |
| `_>=_` | `(double, double) -> bool`, `(string, string) -> bool`, `(duration, duration) -> bool` | |
| `_&&_` | `(bool, bool) -> bool` | |
| `_\|\|_` | `(bool, bool) -> bool` | |
| `!_` | `(bool) -> bool` | |
| `-_` | `(double) -> double` | |
| `_?_:_` | `(bool, T, T) -> T` | the branches must agree |
| `_+_` | `(double, double) -> double`, `(string, string) -> string`, `(list(T), list(T)) -> list(T)`, `(duration, duration) -> duration` | the widest operator in the dialect, and still four rows |
| `_-_` | `(double, double) -> double`, `(duration, duration) -> duration` | |
| `_*_` | `(double, double) -> double` | **no `duration * double`.** Every such addition widens a surface where the internal unit (nanoseconds, via `chrono::TimeDelta`) leaks into a policy's arithmetic. Durations are compared and added |
| `_/_` | `(double, double) -> double` | |
| `_[_]` | `(list(T), double) -> T`, `(map(K, V), K) -> V` | a string-literal index into a RECORD never reaches the table — see `diverges: literal-key record index`. `x[?k]` is an optional read (`added: optional reads`): only the operand of `.orValue`, `.hasValue` or `has` |
| `@in` | `(T, list(T)) -> bool`, `(K, map(K, V)) -> bool` | written `x in y`. The map row is the membership spelling the system environment needs (`"8080" in listeners`) |
| `duration` | `(string) -> duration` | the ONE temporal constructor. `timestamp` is absent, and its absence is structural |
| `getSeconds` | `duration.getSeconds() -> double` | |
| `getMilliseconds` | `duration.getMilliseconds() -> double` | |
| `size` | `(list(T)) -> double`, `(map(K, V)) -> double`, `list(T).size() -> double`, `map(K, V).size() -> double` | **no string arm** — that is `removed: size() on strings`; the evaluator has no string or bytes `size` either |
| `startsWith` | `string.startsWith(string) -> bool` | |
| `endsWith` | `string.endsWith(string) -> bool` | |
| `contains` | `string.contains(string) -> bool` | |
| `matches` | `string.matches(string) -> bool` | |

Absent by construction, and each absence is a row above or a row in [Removed](#removed): numeric
aggregates (`sum`, `min`, `max` — a `math` extension, and `extension libraries are gone`), the type
denotations, `bool()`, `int()`, `uint()`, `timestamp()`, `dyn()`, `%` (`removed: modulo`), and every
custom function. The
crate registers none, so `is_owner(...)` cannot be made to work by adding one here.

## Configuration

Features (`bytes` is on by default, so a plain `cargo test -p typed-cel` runs every absorbed unit
test). `regex` (`matches()`), `chrono` (`duration()`, `30s` literals) and `serde_json` (the
activation binds from `serde_json::Value`) are plain dependencies: the dialect uses all three
unconditionally.

| feature | enables |
|---|---|
| `bytes` | the bytes type |
| `conformance` | the cel-spec harness, `typed_cel::fork`, the `conformance-report` bin; turned on for this crate's own tests by a self dev-dependency |

No environment variables.

### Bounds

The fork arrived with none — nothing in the absorbed source bounds recursion, iteration or input
size — so an expression over attacker-controlled data is bounded here or not at all:

```rust
pub struct CelLimits {
    pub max_source_len: usize,      // default 8192 — checked on the DESUGARED form, before the parser
    pub max_depth: u32,             // default 32 — scanned from source: the parser is what recurses first
    pub max_cost: u64,              // default 1000000 — static estimate; comprehension bodies multiply
    pub max_list_len: usize,        // default 1000000 — elements in any one bound list. HTTP environment only
    pub max_total_elements: usize,  // default 1000000 — elements across the whole activation
    pub max_unroll: usize,          // default 256 — elements a specialization unrolls a known-range exists/all/map into
}
```

`tests/bounds.rs` reads those defaults back out of this block, so the numbers here are the numbers
the crate uses. `max_cost` admits two nested comprehensions over declared lists and refuses three —
the point at which the runtime becomes a product of more attacker-controlled lengths than a reviewer
can hold in their head.

Depth and cost are refused **at build time**, when a human is present to read the error. Input caps
are a precondition of constructing the activation, because `execute` cannot be interrupted once it
has started. `max_list_len` is a correctness knob as well as a cost one: a legitimately large
response that exceeds it is denied.

## Relationship to spec CEL

Everything below is this dialect measured against standard CEL: what it scores on the spec's own
corpus, what it removed, what it never implemented, where it deliberately disagrees, and what it
added.

There is no list of open bugs, because there are none: every one of cel-spec's 2344 cases resolves
to PASS or to EXCLUDED, and the block below reads `0 fail`. A case that starts failing is a red
test, not a row in a table — `tests/readme.rs::every_failing_section_is_a_known_bug` is what keeps
it that way.

Every row in these tables carries an **id**. That id is what a conformance exclusion cites, and the
citation is checked in both directions — a reason that names no row fails, and a row that excludes
nothing is a dead letter. This is where a new exclusion has to be argued for, which is what stops
EXCLUDED becoming a place to hide failures.

### Compatibility

Measured, not claimed. The block below is generated from a live run against google/cel-spec
v0.25.1 and committed; `the_conformance_summary_is_current` regenerates it and fails the build when
it drifts. Per-file counts, and every failing section by name, are in
[`conformance/report.md`](./conformance/report.md).

Every case is compiled through the checker a policy compiles through, with its bindings declared
at their values' types, and runs only if the checker admits it. Each case resolves to exactly one of
three outcomes:

| outcome | meaning |
|---|---|
| **PASS** | the checker admitted it, and it ran and matched the expected value — or it expects an evaluation error and the checker refused it first (*pass statically*, counted apart) |
| **EXCLUDED** | the dialect does not implement this construct — requires a row in [`conformance/EXCLUSIONS.toml`](./conformance/EXCLUSIONS.toml) whose reason is a dialect-row id below |
| **FAIL** | neither of the above — a checker refusal no exclusion names is a FAIL too. A red test. There is no fourth state and no `#[should_panic]`. |

<!-- @generated conformance summary -->

```text
  google/cel-spec v0.25.1 — 2344 cases, each checked, then evaluated

      526  pass
       29  pass statically (the case expects an error; the checker refused it first)
     1789  excluded by dialect
        0  fail

  Excluded by dialect:
        1  diverges: absence must be proven
        1  diverges: duration() takes a string
        1  diverges: equality is homogeneous
        5  diverges: exact integers span int64 and uint64
        2  diverges: nesting is bounded
       19  diverges: undeclared names are compile errors
        6  not implemented: backtick-quoted field selection
       13  not implemented: container name resolution
        1  not implemented: optional index on a list
       47  not implemented: the cel-spec checker
       46  not implemented: two-variable comprehension macros
        4  removed: bytes concatenation
       18  removed: dyn values
       92  removed: dyn()
      454  removed: extension libraries
       12  removed: integer division
        4  removed: logic on non-bools
       12  removed: modulo
       44  removed: optional values
       25  removed: ordering beyond numbers and strings
      659  removed: protobuf
        7  removed: size() on strings
       55  removed: timestamp
       54  removed: type conversion functions
       25  removed: type values
      182  removed: uint
```

<!-- @end conformance summary -->

### Removed

The construct does not exist. Naming it is an error.

Each row names the test in [`tests/dialect.rs`](./tests/dialect.rs) that asserts the rejection. A
removal with no test is a claim about the language rather than a property of it — the construct
keeps working, nobody notices, and a policy gets written against something this table says is gone.

| id | construct | rejection test | why |
|---|---|---|---|
| `removed: protobuf` | protobuf messages, `Expr::Struct`, enums, wrappers | `message_construction_is_gone` | nothing in either environment produces one |
| `removed: dyn()` | `dyn()` | `dyn_is_gone` | one numeric type and a real checker make it unnecessary; it exists to defeat type checking |
| `removed: optional values` | the `optional` type and every function over it (`optional.of`, `optional.none`, `optional.ofNonZeroValue`, `.value()`, `.or()`, `.optMap()`, `.optFlatMap()`, `==` on optionals), `[?x]` list elements, `{?k: v}` map entries, and an optional read anywhere but under `.orValue`/`.hasValue`/`has` | `optional_values_are_gone` | absence is proven at compile time (`added: proven presence`), and an optional READ with a default (`added: optional reads`) covers what authors reach for; a first-class optional value would be a second way to say both |
| `removed: timestamp` | `timestamp`, and every wall-clock reading | `timestamp_is_gone` | **a clock read in a sandbox decision is a bug.** `CLOCK_MONOTONIC` is a repo rule; a revocation that fires because NTP stepped is not a policy |
| `removed: uint` | the `u` literal suffix, `uint()` and the `uint` type | `uint_is_gone` | one numeric type: a large integer is written without a `u` and held exactly. The trap where a serde-converted positive integer arrives as a `u64` and picks a different arithmetic stays closed because arithmetic and comparison are defined across every representation of a number |
| `removed: size() on strings` | `size()` over a string | `size_on_a_string_is_gone` | it returns **bytes**, not code points: `size('πέντε')` is 10. A length predicate that means something different on non-ASCII input is worse than none |
| `removed: extension libraries` | `math`, `strings`, `encoders`, `bindings`, `block` | `extension_libraries_are_gone` | none shipped upstream; none added. 454 corpus cases, the largest single exclusion |
| `removed: type values` | `type()` and the type denotations (`int`, `string`, `list`, `map`, `bool`, `double`, `bytes`, `null_type`, `type`) | `type_values_are_gone` | the dialect has a STATIC checker, so a runtime type value has no job: every question `type(x) == type(y)` answers is either already decided at build time or a comparison the signature table refuses. 24 corpus cases exist for a feature no expression can reach |
| `removed: type conversion functions` | `bool()`, `int()`, `string()`, `double()`, `bytes()` | `type_conversion_functions_are_gone` | one numeric type leaves nothing for `int()` to convert to, `bool('true')` is string-typed truthiness that the checker exists to prevent, and `string()` on a bytes value is lossy in a way the caller would not notice (`conversions/string/bytes_invalid` turns invalid UTF-8 into U+FFFD). `double()` converts to the number every value already is, `bytes('…')` is the literal `b'…'`, and `uint()` rides `removed: uint` |
| `removed: integer division` | integer (truncating) division and division-by-zero errors | `integer_division_is_gone` | the dialect has one number type, so `/` cannot mean two things by the operands' spelling: it is real division, `7 / 2` is `3.5`, and a zero divisor answers IEEE's `+inf`/`NaN` as spec CEL's doubles do. Integers are otherwise exact — `+`, `-`, `*` and comparison never round |
| `removed: dyn values` | a value of no static type: a heterogeneous list or map literal, a conditional whose branches differ, and any use of a `dyn`-typed expression except `has()` (and `size()` of a list or map holding them) | `dyn_values_are_gone` | a typed backend holds every value unboxed at a known type, and a `dyn` is what would force it to keep a boxed escape hatch. No program cynch generates needs one. Refused by the CHECKER |
| `removed: ordering beyond numbers and strings` | `<`, `<=`, `>`, `>=` on anything but numbers, strings and durations — bools, bytes, lists, maps, `null` | `ordering_beyond_numbers_and_strings_is_gone` | no generated program orders a bool or a byte string, and each extra ordering is a comparison a typed backend carries for nobody. Refused by the checker, and the backend has no op for it |
| `removed: logic on non-bools` | the logical operators (and, or, `!`) with an operand that is not a `bool` — including spec CEL's `false && 32`, which short-circuits past the number | `logic_on_non_bools_is_gone` | a number where a truth value goes is a bug the checker exists to report, whether or not a short circuit would have hidden it. Refused by the CHECKER; at run time a non-bool operand is an error like any other |
| `removed: bytes concatenation` | `+` on two `bytes` | `bytes_concatenation_is_gone` | nothing a program reads is assembled from byte strings. Refused by the checker, and the backend has no op for it |
| `removed: modulo` | `%` | `modulo_is_on_doubles_or_gone` | no generated program uses it, and over one number kind it could only be a floating-point remainder nobody asked for. Refused by the checker, and the backend has no op for it |

Every program is checked before it runs, so the evaluator carries no arm for a construct the
checker refuses: `size()` on a string or a byte string, `string()`, `double()`, `bytes()`, ordering
on bools, bytes and `null`, and `+` on bytes are refused by the [signature table](#signatures) first
and have no overload left in the evaluator either. `removed: type values` is the one row that bites
at check alone — `type()` never had a runtime implementation in this crate. The two corpus rows where the
byte/codepoint difference of `size()` is observable are excluded like the rest.

Every other row's construct is gone from the implementation, not merely from the API: the
`the_corpus_rows_moved` test asserts that every cel-spec case NAMING a removed construct is
EXCLUDED rather than passing or failing.

### Not implemented

Standard CEL this dialect does not provide, and does not intend to.

| id | construct | why |
|---|---|---|
| `not implemented: two-variable comprehension macros` | `list.exists(i, v, …)` and friends | the one-variable forms cover both environments |
| `not implemented: container name resolution` | the `container` namespace qualified identifiers resolve against | both environments bind their roots by name into a flat activation, so there is no namespace to resolve against |
| `not implemented: the cel-spec checker` | cel-spec's `type_deduction` phase | typed-cel has a checker, but a different one — over structural declared types rather than proto descriptors — and it is tested directly |
| `not implemented: backtick-quoted field selection` | ``m.`content-type` `` | the index form `m['content-type']` works, is what the HTTP environment already uses, and is the form `diverges: literal-key record index` is written about. Two spellings for one access is a second thing to keep in step. Rejected by the CHECKER (`backtick_field_selection_is_gone`), because the parser leaves the backticks in the field name and the select would otherwise fail at evaluation as a missing key |
| `not implemented: optional index on a list` | `xs[?i]` | bounds are not presence, and the presence rules do not track a list's length; `size(xs) > i ? xs[i] : d` is the spelling. Pinned by `optional_reads_that_stay_refused` |

### Divergences

Spec CEL says one thing and this dialect does another, on purpose.

| id | divergence | note |
|---|---|---|
| `diverges: one numeric type` | one number TYPE, `double`, to the checker; at run time its values are held exactly — an `i64`, a `u64` above `i64::MAX`, or an `f64` (`CelNum`) — and compare by value across those | ergonomic: no `1` vs `1.0` type errors, no operator whose meaning depends on how an operand was spelled. The values are exact because a rounded one is a bypass: `9007199254740993` and `9007199254740992` are different account ids and one double |
| `diverges: exact integers span int64 and uint64` | an integer is exact across `[i64::MIN, u64::MAX]`: `9223372036854775807 + 1` is `9223372036854775808`, where spec CEL's `int` overflows. Past that range it is an error here too | the one number type has no `int64` to overflow; stopping at `i64::MAX` would refuse a `u64` id or `RLIM_INFINITY` a document legitimately carries. Pinned by `one_numeric_type_many_representations` |
| `diverges: absence must be proven` | a read that may be absent — an optional field, a key only an index signature allows, any `map` key — must be proven present at compile time; spec CEL evaluates it and errors at run time | a policy that silently denies every request missing an optional field is a bug found at authoring time; pinned by `unproven_map_reads_are_refused` |
| `diverges: orValue's default is lazy` | `x.?f.orValue(d)` evaluates `d` only when `x.f` is absent; spec CEL evaluates a function's argument eagerly, so a `d` that errors is an error there even when `x.f` is present | it reads as what an author means — "use `d` if there is nothing there" — and it is what the rewrite (`has(x.f) ? x.f : d`) is. Pinned by `lazy_default` |
| `diverges: literal-key record index` | a string-literal index into a record is checked field access | `headers['content-type']` must keep unknown-key detection |
| `diverges: dyn must be narrowed` | a `dyn` value must be narrowed before it is used; spec CEL checks one against everything | a schema's `unknown` is a statement about DATA; CEL's `dyn` is a statement about VERIFICATION. This dialect DELETED `dyn()` because it exists to defeat type checking, so a schema must not be able to manufacture what an author may not write |
| `diverges: undeclared names are compile errors` | an unbound variable or an unknown function is a CHECK error; spec CEL defers both to evaluation, where a short circuit can absorb the error (spec CEL answers `true` for an unbound `x` or-ed with `true`) | a typo in a generated program must never be silently absorbed by a short circuit. Every name a program may read is declared in its environment |
| `diverges: equality is homogeneous` | `==` and `!=` between two different types (`['one'] == [2, 3]`) are a check error, not `false` | the [signature table](#signatures) types equality `(T, T) -> bool`: an expression that can never be true is a bug |
| `diverges: duration() takes a string` | `duration()` accepts only a string; spec CEL's identity overload `duration(duration)` is absent | nothing needs to convert a duration to itself |
| `diverges: nesting is bounded` | an expression nests at most `CelLimits::max_depth` deep (32 by default); spec CEL's `!!!…!true` at 32 negations is refused | `added: evaluation bounds` — nothing bounds an expression over attacker-controlled data unless this crate does |
| `diverges: durations without timestamps` | the only temporal type is a span | a `Duration` has no clock attached, so computing one from two `Instant`s is exactly right. `Timestamp` is deleted for the opposite reason |

#### `dyn` must be narrowed

A `dyn` says "some JSON value". It does not say "stop checking". On a `dyn` value:

| legal | why |
|---|---|
| `has(x.k)` | existence is answerable without a type |
| `size(x)` of a list or map holding `dyn` members | a length asks nothing of the members |

| a build error | why |
|---|---|
| `x > 1`, `x + 1`, ordering and arithmetic | there is no type to pick an overload with. At runtime this is `No such overload`, and therefore a deny or a REVOKE |
| `x == null`, `x != null`, `k in x`, `x == y` | every one is a USE of the value (`removed: dyn values`); ask `has()` for presence |
| iterating it, putting it in a literal, returning it from a `map` step | the same: each makes a `dyn` value something else reads |
| `x.field` | field access on something not known to be an object. This barely arises: "it is an object" derives `map(string, dyn)`, not `dyn` |
| `x` as the whole expression's result | the result must be `bool`, and `dyn` is not `bool` |

The cost, stated so nobody rediscovers it in a bug report: a policy whose schema declares
`body: unknown` and wants `body.user_id` is a BUILD ERROR where it used to be a runtime deny. The
fix is for the author to declare the field in the schema, and that is the right pressure — a
policy's checkability comes from its schema.

Fail-open at build and fail-closed at runtime is not a security hole; every mistake lands as a
recoverable error. What it costs is WHEN you find out and WHAT it costs: in HTTP a typo becomes a
403 in production instead of a build error, and in the system environment a typo becomes a
revocation, for a reason nobody wrote down.

### Added

The reason this is a crate and not a vendored copy. Each row names the public items that carry it,
and `every_addition_row_has_public_api` checks they exist.

The table is each addition's contract, written once here rather than re-derived per change. A row is
not a status report — it either has its API or it is in the test's output.

| id | addition | public API | why |
|---|---|---|---|
| `added: type checker` | a static type checker over declared structural types | `CelEnvironment`, `CelTy` | a policy's mistakes are found when it is written, not when a request arrives. Upstream has no checker at all, so `body.no_such_field` is an evaluation-time error in production |
| `added: demand extraction` | every literal path an expression reads, as data | `CelProgram::demand`, `DemandSet` | the runtime populates only what a policy reads, and an operator can answer "what does this watch?" from the artifact. See [Extracting demand](#extracting-demand) |
| `added: evaluation bounds` | depth, cost and input caps | `CelLimits` | the fork arrived with **none** — nothing bounds an expression over attacker-controlled data unless this crate does |
| `added: duration literals` | `30s` desugars to `duration('30s')` | `desugar`, `SpanMap` | the whole of this dialect's syntactic deviation from spec CEL, and it expands to a standard call. The span map is what keeps a diagnostic pointing at the authored column |
| `added: source spans` | offsets survive a *successful* parse | `Span`, `CelError::span`, `SpanMap` | upstream keeps the map only for parse errors; our type errors come later and have nothing but expression ids, so a checker error could name the mistake but not point at it |
| `added: record builders` | a record without naming `Rc` or `BTreeSet` | `Record::new`, `Record::with_optional`, `Record::with_index` | the struct-literal form needs four fields at every roster site, and the same private `record()` helper had already been written twice — in the embedding application and in this crate's test support. Two copies is the signal |
| `added: all check errors` | every error the checker found, not just the first | `CelError::all`, `CheckError` | `Display` still renders only the first, because a cascade is a diagnostic nobody reads — but a policy compiler listing a file's problems wants every one, and dropping them at the boundary meant it could never have them |
| `added: structural query` | the top-level `&&` conjuncts of a compiled expression | `CelProgram::conjuncts`, `Conjunct`, `Literal` | a caller that lints an expression's SHAPE — "is there a guard conjunct for each window this reads?" — would otherwise re-parse the authored source, which is a second parser that disagrees with the first the day either changes. `&&` is the only connective a guard can be proven through, so a `||` is ONE opaque conjunct |
| `added: the lazy seam` | activations that are read, not materialized | `LazyValue`, `CelValue`, `CelKey`, `CelActivation::bind_lazy` | an expression may be evaluated on every tick for the life of a process. Building a map of the process's state per tick makes the cost of a policy proportional to that state rather than to the policy. The trait is the crate's ONLY extension point, and what crosses it is `CelValue`, the crate's one value type. See [Serving values on access](#serving-values-on-access) |
| `added: compile with known values` | one `compile(source, &CompileOpts)`: the required result type, and the roots whose values are known now. The check runs WITH the known values in view (a known value proves presence), then every read of a known root folds, leaving a residual over the rest | `CelEnvironment::compile`, `CompileOpts`, `Parsed`, `CelEnvironment::parse`, `CelError::Specialize` | a decision whose configuration is fixed for a process's life is compiled against it ONCE; the per-call program reads only the per-call input. The fold runs on the backend, so it adds no second semantics. See [Specializing](#specializing) |
| `added: proven presence` | a read that may be absent — an optional field, a key only an index signature allows, any `map` key — compiles only where something proves it present: a guard (`has`, `in`), iteration over the same container, a known value, or an `unsafe_map` declaration | `CelEnvironment::compile` | a policy that silently denies every request missing an optional field is found when it is written. Pinned by `unproven_record_reads_are_refused` and `a_compiled_program_never_raises_no_such_key`. See [Proving presence](#proving-presence) |
| `added: unsafe_map` | a map type whose DECLARER asserts every key a program can name reads as a value, so a read of one needs no proof; a schema never derives one | `CelTy::unsafe_map` | an embedder that fills a root from the program's own demand (pre-creating every key the program names) has a root that is total by construction — and saying so in the type keeps the same program text meaning the same thing against the same declared types everywhere |
| `added: optional reads` | `x.?f.orValue(d)`, `m[?k].orValue(d)`, `x.?f.hasValue()` and `has(x.?a.b)`, rewritten at parse time into the guards that prove them (`has(x.f) ? x.f : d`) — spec CEL's spelling and spec CEL's answers | `CelEnvironment::compile` | a read with a fallback is the commonest thing an author writes against an optional field; spelling it as CEL spells it, and proving it with the rules that already exist, costs nothing at run time. See [Proving presence](#proving-presence) |
| `added: host functions` | typed, pure functions an embedding environment declares | `CelEnvironment::register_host`, `HostCall` | an embedder's matching engines (route tables, schema checks) are exposed as calls the checker types and partial evaluation treats as opaque until every argument is known, instead of being re-implemented in CEL or left outside it. The backend dispatches them, and builds a matcher through one over a known list |
| `added: closed string sets` | an environment may declare that a string field holds one of a fixed list of values; nothing about its meaning changes | `CelEnvironment::declare_enum`, `TAG_OTHER`, `Facts` | a field like an access mode is compared with a handful of literals on every decision. The fast backend compares a listed literal as a TAG — the value's index — which a `Facts` provider may answer without producing a string at all; `f == "a" \|\| f == "b"` over listed values is one mask test. A literal outside the list is still an ordinary string comparison |
| `added: typed results` | programs that must produce a declared non-bool type, and the runtime to run them | `CelEnvironment::compile`, `CompileOpts`, `ResultKind`, `CelRuntime`, `CelActivation::bind_fact`, `Vm::eval_result`, `FastProgram::decide_tag` | a decision point with more than two outcomes (allow / read-only / a specific errno) needs a result the checker can still prove the type of, and a specialization of it keeps that type. The fast backend answers such a program with the index of a tag rather than a string value, so the answer allocates nothing |
| `added: bytecode` | a CHECKED expression lowered to a register program over unboxed values and run by one fast backend (`src/fast/`); an unchecked expression has no lowering | `emit`, `CelBytecode`, `Vm::eval`, `FastProgram`, `Facts` | one evaluation is a loop over explicit state rather than a recursive walk, which is what lets an evaluation stop and resume, and it reads host data by field rather than packing it into values. Held to its answers by the cel-spec corpus, a frozen golden of every generated program's answer, single-engine laws over generated programs (every host alike, eager and lazy) and pinned edges (`tests/generated_golden.rs`, `tests/metamorphic.rs`, `tests/backend_edges.rs`) |

## Testing

```bash
cargo test -p typed-cel                  # everything, including the absorbed unit tests and the cel-spec corpus
cargo run -p typed-cel --features conformance --bin conformance-report              # the table
cargo run -p typed-cel --features conformance --bin conformance-report -- --write   # regenerate
cargo run -p typed-cel --features conformance --bin conformance-report -- --failures [file]
```

`--write` regenerates `conformance/{gen/cases.rs, report.md, baseline.toml}` **and this README's
compatibility block**, all of which are committed and held to a live run by tests. Do not edit a
generated block by hand; regenerate it, and say in the commit message what moved.

This README is itself under test: `tests/signatures.rs` holds the Signatures table to `src/sigs.rs`
in both directions, `tests/readme.rs` holds the Removed and Added tables to `tests/dialect.rs` and to
`src/`, `tests/bounds.rs` reads the `CelLimits` defaults out of the block above, and
`tests/conformance.rs` requires every exclusion reason to be a dialect-row id here. Keep the
`## Signatures`, `### Removed` and `### Added` headings and the `| \`id\` |` row shape intact.
