# Attribution

`typed-cel` is a fork of **cel-rust**, taken at version 0.14.2 — upstream commit
`593c11634fa47b03102a1b9c3b58b2da1d16048a` (tag `v0.14.2`, tag object
`178afa95543fb6497c673db2c4370d3459ee3e40`), from the `cel/` subdirectory of the upstream
workspace.

Upstream: https://github.com/cel-rust/cel-rust — MIT, retained in [LICENSE-MIT](./LICENSE-MIT).

We do not track upstream. This is a deliberate fork: the dialect's changes are mostly
SUBTRACTIONS (see README.md), which upstream has no reason to accept, and the fork point is
recorded here so a reader can diff.

To reproduce the fork point:

```sh
curl -sL https://github.com/cel-rust/cel-rust/archive/refs/tags/v0.14.2.tar.gz | tar xz
diff -r cel-rust-0.14.2/cel/src typed-cel/src
```

`src/` was taken verbatim and is byte-identical to that tree apart from the changes listed below.
It is deliberately **not** run through `cargo fmt`: reformatting 17k absorbed lines would make the
fork point undiffable, which is the one thing this file promises a reader they can do. Only files
we author are formatted.

`conformance/corpus/` vendors **google/cel-spec v0.25.1** (commit
`7f3c4c513b42d471d0be9439bf5bde38f45f8404`) — Apache-2.0, retained in
[LICENSE-APACHE](./LICENSE-APACHE), with the modifications described in
`conformance/EXCLUSIONS.toml`.

## What we inherited, measured

Against google/cel-spec v0.25.1, with **every exclusion switched off** — so this is cel-rust
0.14.2's behaviour, not the dialect's:

```
1037 pass / 1307 fail / 2344 total     (44.2%)
```

This is the only chance to measure what came IN as opposed to what we built, and it is what makes
the dialect's deletions auditable: a deletion that does not move corpus rows from FAIL to EXCLUDED
has removed a construct from the API and not from the implementation.

`conformance/report.md` carries the current, dialect-aware number. It is generated and checked in;
`the_conformance_table_is_current` fails the build when it drifts.

For context on what the upstream number means: cel-rust's own harness (PR #291) reports
`2343 passed; 0 failed; 0 ignored` — while 1455 of those tests carry `#[should_panic]` and pass BY
failing. That harness's honest figure is 888/2343. Ours is a different harness with different
strictness, so the two are not directly comparable; what is comparable is that neither of ours can
be reported as green while failing.

## Changes from the fork point

Each entry is a change we made on the way in, or a deletion the dialect requires. Later changes
append to this list.

### Absorbing the fork

- **Package renamed** `cel` → `typed-cel`; the lib target `cel` → `typed_cel`. The internal
  module layout (`parser/`, `common/`, the evaluator) is unchanged, so the diff above stays
  readable. The 24 `cel::` paths inside doc comments were rewritten to `typed_cel::` — a single
  reproducible substitution (`perl -pi -e 's/\bcel::/typed_cel::/g'`), needed because the
  doctests reference the crate by name and would otherwise not compile.
- **Benches dropped.** `benches/runtime.rs` and its `criterion` / `dhat` dev-dependencies, and
  the `dhat-heap` feature, did not come across. They measured upstream's evaluator, not the
  dialect. The ablation in `ablation/` replaces them: a standalone workspace that measures this
  crate against upstream cel-rust 0.14.2 and hand-written Rust (`docs/PERFORMANCE.md`).
- **`serde`'s `derive` feature is now asked for directly**, as a dev-dependency. The absorbed
  `ser.rs` tests `#[derive(Serialize)]` their fixture structs and got the macro by accident,
  through feature unification with criterion's `serde`. Dropping the upstream benches made that accident
  visible as 15 compile errors in the test build.
- **Default features changed** from `["regex", "chrono"]` to
  `["regex", "chrono", "json", "bytes"]`. `json` and `bytes` are load-bearing here (the
  activation is JSON-shaped, and a schema can declare a bytes field), and a plain
  `cargo test -p typed-cel` must run every absorbed unit test — a feature-gated test that never
  runs is the same silent green this crate exists to avoid. `structs` stays off and is deleted
  outright when `Expr::Struct` goes.
- **`Parser::parse_with_source_info` added** (`src/parser/parser.rs`), returning
  `(IdedExpr, Arc<SourceInfo>)`. Upstream builds a complete source map and attaches it only to
  `ParseError`s, so a *successful* parse yields expression ids with no offsets and a later type
  error has nothing to point at. `parse()` is unchanged in behaviour and delegates.
  `tests/source_info.rs` pins the map's semantics, including the one that is easy to get wrong:
  the recorded range is INCLUSIVE, and it addresses the token that ANCHORS a node — the operator
  for a call, the `.` for a select — not the node's full extent. A diagnostic about
  `body.no_such_field` therefore carets the dot and must name the field in its message.
- **`[profile.dev.package]` overrides added to the workspace root** for `typed-cel` and
  `antlr4rust`, both at `opt-level = 1`. cel-rust's own workspace sets `[profile.dev]
  opt-level = 1`; this workspace does not, and at `opt-level = 0` the ANTLR visitor's frames are
  fat enough that `parser::tests::malformed_nested_expression_does_not_panic` overflows the
  2 MiB test-thread stack and aborts the whole binary. Reproduced on macOS and Linux. This is a
  build-profile dependency, not a fix — a parse-depth bound that is not a stack bound is a real
  fragility, and closing it belongs to the evaluation-bounds work.

### The conformance harness

- **`conformance/` added**, and with it an optional `conformance` feature. `toml` is an OPTIONAL
  normal dependency rather than a dev one, because `src/bin/conformance-report.rs` is a bin and a
  bin cannot see dev-dependencies; the feature keeps it out of what a consumer of the dialect
  links. The crate dev-depends on itself with the feature on, so `cargo test -p typed-cel` builds
  the harness without any consumer inheriting it.
- **`conformance/corpus/` vendors google/cel-spec v0.25.1's `tests/simple/testdata/`** verbatim,
  29 files and 2344 cases. `conformance/corpus/UPSTREAM-README.md` is that directory's own README,
  kept alongside it.
- **`run::run` catches panics** and reports them as conformance failures. The corpus contains
  inputs this evaluator panics on in a debug build — `-(-9223372036854775808)` reaches a bare
  negation in `src/common/types/int.rs` — and an escaping panic would abort the report and take
  the other 2343 cases with it. A panic is a genuine failure (CEL says return an error); catching
  it means the report and the generated tests share ONE definition of the outcome.
- **`README.md`'s compatibility block is generated too.** `--write` splices it between the file's
  `@generated conformance summary` markers, and `the_conformance_summary_is_current` re-derives it
  from a live run. The README is the document people actually read, so a hand-kept number there
  would go stale in exactly the way the committed report cannot.

### The dialect's deletions

Five constructs removed FROM THE ABSORBED SOURCE. Each is a rejection test in `tests/dialect.rs`, a
set of corpus rows moved from FAIL (or PASS) to EXCLUDED in `conformance/EXCLUSIONS.toml`, and a row
in `README.md`.

`README.md` carries more removal rows than there are bullets here, and the gap is the point: a
removal only appears in this section when it took code out of the fork. `removed: type values` is
refused by the CHECKER alone — `type()` was never in the absorbed evaluator.
`the_corpus_rows_moved` holds the three together: every corpus case that NAMES a removed construct
must be EXCLUDED, so a deletion cannot be half-done — the construct still working and the deletion
leaving its rows red are both failures of that test.

- **`Expr::Struct` and protobuf message construction deleted.** The AST variant, `StructExpr`,
  `StructFieldExpr` and the `EntryExpr::StructField` arm are gone, along with
  `common/types/struct.rs`, `Env::add_struct`/`StructDef`, `Kind::Struct` and the `structs`
  feature. `visit_CreateMessage` now reports a parse error naming the dialect. The grammar under
  `src/parser/gen/` still HAS the production — it is generated from Google's `CEL.g4` and is not
  ours to edit — so the refusal lives in the visitor, which keeps it a recoverable diagnostic with
  a source position rather than a panic. Map literals are a different production and still parse;
  the parser test table asserts the pair.
- **Optional syntax and `OptionalValue` deleted.** `Parser::enable_optional_syntax` is gone rather
  than defaulted off — an option is something a future caller can set. All four spellings (`[?k]`,
  `.?f`, `?k: v`, `?x`) report one message. `common/types/optional.rs`, `OPTIONAL_TYPE`,
  `objects::OptionalValue`, the `optional.*` constructors, `value`/`hasValue`/`or`/`orValue`, and
  the `operators::OPT_INDEX`/`OPT_SELECT` handling all went with it. The AST lost
  `MapEntryExpr.optional` and `ListExpr.optional_indices`, so an optional entry is not
  constructible at all. This deletes a feature that is measurably WRONG on maps upstream —
  `{'a':1}.?missing.orValue(0)` raises `NoSuchKey` instead of yielding the default — which is why
  fixing it was never the alternative.
- **`timestamp` deleted, `duration` kept.** `Value::Timestamp`, `ValueType::Timestamp`,
  `common/types/timestamp.rs`, `TIMESTAMP_TYPE`, `Kind::Timestamp`, `ser::Timestamp`, the
  `MAX_TIMESTAMP`/`MIN_TIMESTAMP` bounds and the `TsOp` checked arithmetic are gone. Every duration
  operation is untouched, because the entire system environment is span comparison. The two share
  chrono-backed conversion paths, so `timestamp_is_gone` asserts the PAIR in one test: deleting one
  by deleting the shared path would silently take the other.
- **`uint` deleted.** `Value::UInt`, `ValueType::UInt`, `objects::Key::Uint`/`KeyRef::Uint`,
  `common/types/uint.rs`, `UINT_TYPE`, `Kind::UInt`, `LiteralValue::UInt`, the `uint()` conversion
  and every cross-kind numeric arm in `eq`/`partial_cmp`/`add`/`sub`/`mul`/`div`/`rem`. `visit_Uint`
  reports a parse error rather than widening `1u` to an `Int`: a policy that spells `1u` was written
  against a language with two integer types, and reinterpreting it silently would make the removal
  invisible to whoever wrote it. Three consequences worth naming:
  - `Map::get` lost its cross-kind fallback. Upstream retried a lookup with the same integer spelled
    as the other key kind so that `{1: 'a'}[1u]` would hit; with one integer key kind there is
    nothing to reconcile.
  - `From<u64> for Value` and `From<u64> for objects::Key` are gone rather than lossy. A `u64`
    above `i64::MAX` has no representation in this dialect, so serde's `serialize_u64` returns an
    error instead of wrapping to a negative. Smaller unsigned Rust integers land on the one integer
    type, which is pinned in `ser.rs`'s `test_json_data_conversion`.
  - the conformance harness's `to_runtime` returns `None` for a uint binding or expectation rather
    than re-typing it as `Int`, so those cases fail loudly until excluded.
- **`dyn()` deleted.** `common/types/dyn.rs` and its stdlib registration. `Kind::Dyn` and
  `DYN_TYPE` stay: they are the type lattice's top, used by overload declarations, not the cast.
- **What the checker refuses, deleted from the evaluator too.** Every program is checked before it
  runs, so an evaluator arm only a refused program reaches is a second semantics nobody can
  observe. Gone: `Comparer` on `Bool` and `Bytes` and the `Bool`/`Null` arms of
  `Value::partial_cmp` (`removed: ordering beyond numbers and strings`); `Adder` on `Bytes`
  (`removed: bytes concatenation`); `Sizer` on `String` and `Bytes` and the four `size` overloads
  for them (`removed: size() on strings`); the `string()`, `double()` and `bytes()` overloads with
  `common/types/bytes.rs`'s whole stdlib (`removed: type conversion functions`); the
  `duration(duration)` identity overload (`diverges: duration() takes a string`); `getHours` and
  `getMinutes`, which the signature table never had; and the unregistered `functions::{string,
  bytes, double, max, min, time::get_hours, time::get_minutes}`, reachable only from their own
  tests. `duration::format_duration` went with `string(duration)`, its only caller. Each such
  construct is now `NoSuchOverload` or an undeclared reference at evaluation, which
  `tests/dialect.rs` asserts beside the checker's refusal. The logical operators keep their arms: a
  non-bool operand is already an error there (`no_bool_coercion`), which a deciding operand
  absorbs as it absorbs any other.

The deletions moved **279 corpus cases** into EXCLUDED, in two waves. The first wave is the obvious
one — cases that started failing. The second is not: **33 cases went from FAIL to PASS**, because
they expect an EVAL ERROR and kept producing one after the construct was removed, just a different
error. A deletion that turns a red into a green is the quietest way to lose coverage there is, and
those 33 were found only because `the_corpus_rows_moved` asks whether a case NAMES a removed
construct rather than whether it failed.

`conformance/report.md` carries the resulting numbers.

The absorbed unit tests went from **109 `#[test]`s to 86**, and `the_absorbed_tests_still_pass`'s
floor moved with them. The checker-refused deletions above took it from 88 to **81**:
`functions::tests::{test_max, test_min, test_string, test_bytes, test_double,
test_chrono_string}` and `duration::tests::test_format_durations` went with their functions, and
`functions::tests::{test_size, test_duration}` and `objects::tests::test_float_compare` lost only
their string/bytes-size, `getHours`/`getMinutes`/`duration(duration)` and `double('NaN')` rows. All 23 belong to deleted constructs: the tests inside
`common/types/{dyn,uint,optional,struct}.rs` went with those files, and
`objects::tests::{test_numeric_map_access, list_access_uint, invalid_uint_math, test_optional}`,
`functions::tests::{test_uint, test_timestamp}` and `ser::tests::test_u64_zero` went with theirs.
Where a test covered a removed construct AND a surviving one it was narrowed rather than deleted:
`ser::tests::{test_time_types, test_time_json}` keep every duration assertion and lose the
timestamp field, and `functions::tests::{test_int, no_bool_coercion, test_chrono_string}` and
`objects::tests::test_heterogeneous_compare` lost only their uint or timestamp rows. The parser's
own test table kept its message-construction, uint-literal and optional-syntax inputs and now
asserts the REFUSAL each one produces, which is strictly more coverage than deleting them.

Running every program on the one engine took the floor to **80**:
`activation::tests::activations_share_one_function_table` went with the evaluator's function table it
guarded — an activation no longer carries one.

The absorbed evaluator's unit tests then moved to `tests/runtime.rs` or were dropped with the
construct they tested, taking the floor to **44**. All 5 of `lib.rs`'s (`parse`, `from_str`,
`variables`, `references`, `test_execution_errors`), all 14 of `functions.rs`'s, and 17 of
`objects.rs`'s run on the backend there now — ported where the checker admits the program, asserted
as the checker's refusal where it does not (a heterogeneous comparison, a wrong-typed operand, an
undeclared name, a non-bool `||` operand). Dropped outright: `objects::tests::opaque::{test_opaque_fn,
opaque_eq}`, which run an opaque host value and a function registered on a `Context`, neither of
which a checked program can reach. `objects.rs` keeps `reference_to_value`, `test_value_holder_dbg`
and `test_json`, which convert values and run nothing. The `ser.rs` tests assert on `to_value`
directly instead of comparing through a program, and `Program`'s `TryFrom<&str>` is deleted.

Deleting the evaluator took the floor to **43**: `env::tests` went with `src/env.rs`.

Replacing the fork's value model took it to **29**: the 10 `ser::tests`, the 1 `json::tests` and the
3 left in `objects::tests` went with the bridges and the value they tested.

Replacing the fork's store took it to **15**: the tests inside `common/types/*`, `common/value.rs`
and `context.rs` went with the value trait, the types and the variable store they tested.

### One engine

- **The tree evaluator and its function-call machinery are deleted**: `src/functions.rs`,
  `src/magic.rs`, `src/resolvers.rs`, `src/macros.rs`, `src/env.rs`; from `src/objects.rs`,
  `Value::resolve_all`/`resolve`/`resolve_val` with `absorbs`, `bool`, `try_bool` and the
  `impl Add/Sub/Div/Mul for Value`; from `src/lib.rs`, `Program::execute` and `Program::compile`
  and the `fork::{Env, extractors, Program}` doors; the `stdlib(env)` registration function of
  each of `common/types/{duration,list,map,string}.rs` and `FunctionDecl::find_overload` in
  `common/decls.rs`, whose only caller was `Env`. The fast backend (`src/fast/`) is the only
  engine: `CelProgram::evaluate`, partial evaluation's fold and the conformance lane all run on it.
- **`Context` keeps variables only**: the `Env` and the function registry a root carried, and
  `env`/`get_function`/`add_function`/`resolve`/`resolve_all`/`with_env`, are gone;
  `Context::default()` is `Context::empty()`, a root with no variables.
- **`objects.rs` keeps the value types**, and gained the `From<f64/bool/i64/…> for Value`
  conversions `magic.rs` used to generate (`impl_conversions!`). `Map::contains_key`, dead with the
  evaluator, is deleted.
- **`ExecutionError` loses the variants nothing constructs**: `InvalidArgumentCount`,
  `NotSupportedAsMethod`, `MissingArgumentOrTarget`, `ValuesNotComparable`, and the deprecated
  `UnsupportedUnaryOperator`, `UnsupportedMapIndex`, `UnsupportedListIndex`, `UnsupportedIndex`,
  `UnsupportedFunctionCallIdentifierType`, `UnsupportedFieldsConstruction`, with their
  constructors.
- **The fork's `Value` model and its serde bridges are deleted**: `src/objects.rs` (`Value`, `Key`,
  `Map`, `Opaque`, `OpaqueVal`, `ValueType`, `TryIntoValue`, `ResolveResult`), `src/ser.rs`
  (serde → `Value`) and `src/json.rs` (`Value` → JSON), with `Context::add_variable` (serde) and the
  `base64` and `serde_bytes` dependencies only they used. The public `CelValue` (`src/value.rs`) is
  the one value: what a caller binds, what a program returns, what a constant slot holds and what
  every `ExecutionError` carries. Its `Debug` renders exactly as `Value`'s did (`Float(5.0)`,
  `String("x")`, `Map(Map { map: {…} })`), because error text embeds it; a map now iterates in key
  order (`Num < Bool < Str`, the fork's `Key` order) where the fork's `HashMap` did not, and a
  duration keeps nanoseconds where `CelValue::Duration` held milliseconds.
- **The fork's value trait, value types and variable store are deleted**: `src/context.rs`
  (`Context`, `VariableResolver`), `src/common/value.rs` (`Val`), `src/common/traits.rs`,
  `src/common/types/` (every fork value type), `src/common/decls.rs`, `src/common/functions.rs`, and
  the `LazyAdapter` bridge in `lazy.rs`. A run's roots live in a small `Bindings` (`src/bindings.rs`),
  a register borrows a `CelValue` (`Reg::Val`), and a lazy view is read through `LazyValue` directly.
  `src/common/` keeps only the AST; the four scalars a literal carries (`Bool`, `Bytes`, `Double`,
  `String`) move to `src/common/ast/literal.rs` as plain syntax, unchanged in name and shape so the
  parser and the checker read as before. A map is iterated in key order.
- **`DefaultMap::steal` is no longer called.** The backend tracked, per register, whether the
  evaluator would have held a value owned, only to call `steal` on an owned map — which answered a
  fractional number key `UnsupportedKeyType` where the same key into a borrowed map answered
  `NoSuchKey`. Indexing a map is now one rule: a number that names no key is `NoSuchKey`, wherever
  the map lives.

### The dialect's additions

The files authored for the dialect, alongside the absorbed source rather than woven into it. They are listed
here because they change the dependency graph, which a reader diffing against the fork point will
otherwise have to derive from the `Cargo.toml`.

- **`src/ty.rs` added.** `CelTy` is the dialect's type lattice: structural records, lists, maps,
  one number type, durations, and a `Dyn` that must be narrowed. Types are declared by the caller
  (`CelEnvironment::declare`, `Record::new`), or produced from a JSON schema by a schema layer that
  lives outside this repository. Upstream has no type system at all: an unknown field is an
  evaluation-time error.

### Fixes to the absorbed source

Bugs the fork arrived with. Each is a cel-spec conformance failure this crate FIXED rather than
excluded, so each moved corpus rows from FAIL to PASS and struck a row from `README.md`'s
`Known bugs` table. They are listed apart from the deletions because they are the opposite motion:
a deletion narrows the language, and these restore behaviour it always had.

- **The literal decoder rewritten** (`src/parser/parse.rs`), closing **71 corpus rows** across
  `parse/string_literals`, `parse/bytes_literals` and `basic/self_eval_nonzeroish`. Three defects,
  fixed together because each one hid the others:
  - The delimiter was assumed to be ONE character. `visit_Bytes` cut a hardcoded `[2..len-1]` and
    `parse_string` dispatched on the first character alone, so a triple-quoted bytes literal kept
    two of its own quotes in the value and a triple-quoted string containing a lone quote did not
    parse at all. `split_literal` is now the one place that knows a literal's shape — prefix flags
    in either order and either case, longest delimiter first — and both decoders take the whole
    token.
  - The bytes escape table was `\xHH` and three-digit octal, and rejected everything else outright.
    `simple_escape` is now shared by both decoders, and the hex arm takes either case, which was
    eight corpus rows on its own.
  - An escaped quote kept its backslash when the OTHER delimiter enclosed it, and a raw literal did
    the reverse — it DROPPED the backslash before a quote. Both are unconditional now: an escaped
    quote decodes to the bare quote, and a raw literal never reaches the escape table.

  `parse_quoted_string` and `parse_raw_string` are gone. The quote-tracking state machine they
  shared existed only to find a terminator `split_literal` has already found, and it is what made a
  lone quote inside a triple-quoted body look like the end of the literal.

  Three absorbed unit tests pinned the behaviour cel-spec disagrees with, and were RE-PINNED
  against the corpus rather than deleted: `double_quotes_interprets_escapes` (one row),
  `raw_string_does_not_interpret_escapes` (all four) and `parses_bytes` (which now passes a whole
  token). The invalid-escape error is deliberately kept — cel-spec has no case for one, so a
  decoder that passed unknown escapes through would score identically and lose the ability to
  report a typo. `tests/literals.rs` is what holds that line.

- **The duration range made CEL's rather than `chrono`'s** (`src/duration.rs`,
  `src/common/types/duration.rs`), closing the six `timestamps/duration_range` rows. Two bounds
  were being confused for one:

  | bound | value | who enforced it |
  |---|---|---|
  | `chrono::TimeDelta` as nanoseconds | ±9223372036s, ~292 years | `Duration::nanoseconds`, by saturating |
  | CEL | ±315576000000s, ~10000 years | nobody |

  CEL's range is 34x wider than what fits in i64 nanoseconds, so `to_duration`'s
  `Duration::nanoseconds((num * unit.nanos() as f64).trunc() as i64)` could not represent a legal
  duration at all — and a float-to-int cast SATURATES in Rust, so `duration('320000000000s')`
  returned a plausible-looking 292-year span instead of an error. It now builds from seconds plus a
  remainder, and `parse_duration` folds with `checked_add` instead of `+`.

  `Adder`/`Subtractor for Duration` already used `checked_add`, which is why the arithmetic looked
  covered: it was checking `TimeDelta`'s range, and two in-range operands sum well inside it. The
  language's bound is now `duration::in_cel_range`, consulted at both sites — and it compares
  sub-second remainder at the boundary, because `num_seconds` truncates toward zero and the bound
  plus one nanosecond otherwise reports as exactly the bound.

- **Unary `!` and `-` fixed** (`src/parser/parser.rs`, `src/common/types/int.rs`,
  `src/common/types/bool.rs`), closing `integer_math/int64_math` and `parse/repeat`. Three defects,
  one of which is a crate-invariant violation rather than only a conformance failure:
  - `Negator for Int` was `self.0.neg()`, which PANICS on `i64::MIN` in a debug build and wraps in
    release. The rule here is that a failure the caller could inspect must never become a fatal one,
    and this is an evaluator a host may call on every tick. It is `checked_neg` now.
  - `Bool` implemented `Negator`, so arithmetic negation dispatched to LOGICAL not and `-false`
    quietly answered `true` — an operator the language does not have, answering as if it did.
    `as_negator` returns `None`; `!` has its own `operators::LOGICAL_NOT` arm and never came
    through there.
  - `visit_LogicalNot` and `visit_Negate` emitted ONE call for a whole run of operators, so
    `!!true` was `false` and the corpus's 32 of them were `false` where the language says `true`.
    Both now emit one call per operator. The old code's `if ctx.ops.len() % 2 == 0 { visit(..) }`
    was an id-burning half-measure that changed no result.

- **Comprehension absorption** (`src/objects.rs`), closing `macros/all`. CEL's logical operators
  absorb rather than short-circuit left to right: a `false` operand makes `&&` false whatever the
  other operand did, INCLUDING erroring. The fork already had that for the plain binary form; what
  it lacked was the accumulator being able to hold an error. `Value::resolve_val(&loop_step, ..)?`
  ended the loop AT the failing element, so `[1, 2, 3].all(e, 6 / (2 - e) == 6)` never reached the
  `e == 3` element whose `false` settles it. There is no error VALUE to bind to `@result` here, so
  the error is carried beside the accumulator and cleared only by a DETERMINING value — `false` for
  `&&`, `true` for `||`, read off the step's operator. A later `true` does not clear it, which is
  the direction that matters: an `all()` nothing determined must stay an `Err`, because a caller
  maps that to a deny and `false` would make an unevaluatable assertion look like a cleanly failed
  one.
- **A negative hex literal parses** (`src/parser/parser.rs`), closing the last
  `basic/self_eval_nonzeroish` row. The sign is part of the TOKEN — the grammar is
  `Int : sign=MINUS? tok=NUM_INT` — so `"-0x55".strip_prefix("0x")` missed and the decimal fallback
  `"-0x55".parse::<i64>()` could not read a radix. `hex_digits` takes the sign off before the prefix
  test and puts it back on for `from_str_radix`, rather than parsing a magnitude and negating:
  `0x8000000000000000` is not representable as a positive `i64`, which is the same boundary
  `Negator for Int` guards from the other side. Lowercase `0x` only — Google's `CEL.g4` spells the
  token `NUM_INT : DIGIT+ | '0x' HEXDIGIT+`, so `0XFF` dies in the lexer and is pinned as refused.
