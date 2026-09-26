# Performance: what the typed dialect and the compile step each buy

`typed-cel` makes two bets over upstream cel-rust:

1. **A typed dialect.** Every program is checked before it runs; one number kind, no `dyn`, homogeneous
   equality, no type values.
2. **A compile step.** A checked program is lowered once to register bytecode and run by an
   interpreter over unboxed values that reads the caller's data by field.

The ablation in [`../ablation/`](../ablation/) isolates each bet on the same workloads, against
upstream cel-rust **0.14.2** from crates.io and against hand-written Rust.

| column | engine | what it isolates |
|---|---|---|
| **Rust** | a hand-written function over the same typed request struct | the floor |
| **(1) upstream** | cel-rust 0.14.2, untyped: `Program::compile` + `execute` over a `Context` bound once per request | the baseline: full CEL, dynamic values |
| **(2) typed tree** † | the typed tree evaluator this crate forked from cel-rust, on the typed dialect — **deleted**; historical numbers only (below) | what TYPING ALONE bought: still a recursive walk over boxed values |
| **(3a) bytecode, activation** | `Vm::eval(&bytecode, &activation)` over the same bound `CelActivation` — the backend `CelProgram::evaluate` runs | typing + the compile step, same input shape as (1) |
| **(3b) bytecode, facts** | `FastProgram::decide(&facts, &mut scratch)`, the request read by field | the same, with the host reading typed fields in place (how a host that already holds typed fields calls it) |
| **(4) + partial evaluation** | the policy bound at compile time (`specialize`), the residual on `decide` | the per-request residual: only `req.*` is read at run time |

## Machine

| | |
|---|---|
| host | Hetzner Cloud cx33 VM |
| CPU | AMD EPYC-Rome Processor, 4 cores (the bench pinned to core 1 with `taskset -c 1`) |
| kernel | 6.12.107+deb13-cloud-amd64 |
| rustc | rustc 1.98.1 (48a229cea 2026-09-01) |
| profile | `bench`: `opt-level = 3`, `codegen-units = 1`, `debug = false` |

```bash
cd typed-cel/ablation
cargo bench --bench ablation --no-run
# on the VM, three runs, then their median:
B=$(ls -t target/release/deps/ablation-* | grep -v "\.d$" | head -1)
for i in 1 2 3; do taskset -c 1 $B --bench > ablation.$i.txt; done
$B --combine ablation.1.txt ablation.2.txt ablation.3.txt \
  --historical hist.1.txt hist.2.txt hist.3.txt   # the raw runs that measured column (2)
```

## Methodology

- **Equal verdicts first.** Before timing anything, every available leg runs every request and must
  return `Ok(v)` with the same `v`, and each workload's request set (8 to 10 requests) must produce
  both verdicts. A leg that answered differently would be measuring a different program.
- **ns/eval**: 10 000 warm-up evaluations, then 15 rounds, each timing a batch sized to run at least
  20 ms (`Instant`, cycling through the request set, inputs and outputs through
  `std::hint::black_box`). A run reports the median round. The whole bench ran 3 times; each cell is
  the median of the three medians, and a `†` marks a cell whose three medians spread more than 10%.
- **allocs/eval** (in parentheses): a counting `GlobalAlloc` over 10 000 warmed evaluations, divided.
- **compile**: median of 50 compiles from source — upstream `Program::compile`; checked compile
  `env.compile`;
  (3) `env.compile` + `emit`; (4) reported split as compile / specialize (a fresh activation, bind the
  policy, `specialize`) / lower (`FastProgram::new` on the residual).
- **retained bytes**: bytes allocated and not freed by building and keeping the program — the upstream
  `Program`; the checked `CelProgram`; the `CelProgram` + `CelBytecode`; the residual + its `FastProgram`
  (the policy activation and the original program dropped). Each build runs once unmeasured first so
  a lazily built global is not charged to it.
- **Binding is outside the timed loop** for every non-streamed leg: upstream binds `policy` and `req`
  into one `Context` per request (`add_variable_from_value`, durations as `cel::Value::Duration`); the
  dialect binds the same data per request with `CelActivation::bind` from JSON; (3b) and (4) resolve
  each field the program reads to the request's value once per request.
- **`n/a (composite root)`** in (3b): `Facts` answers scalar fields only, and the program reads a list
  or record whole (`policy.roots`, `req.body.items`, …). Column (4) is where such a program is served
  by field: specialization folds the policy's lists into matchers and the residual reads only `req`
  scalars. **`—`** in (4): the workload reads no policy, so there is nothing to specialize.
- **The streamed rows are asymmetric, deliberately.** `streamed_body_early`/`_late` evaluate
  `body.account.tier == "gold" && body.amount < 100` over a ~4 KiB JSON document whose demanded fields
  sit at its start or its end. The buffered legs — (1), (3a) — are timed INCLUDING
  `serde_json::from_str` and the bind (a buffered evaluator must parse). The streamed leg, shown in
  the (3b) column, is a `StreamedProgram` run fed pre-tokenized `typed_cel::Event`s (64-byte
  fragments), so it EXCLUDES tokenization — the producer is not this crate's. There is no Rust or (4)
  column for them.

## Results

Each cell: median ns/eval (allocations/eval).

The headline puts the historical column (2) beside this run's columns. Every ratio below is read
within ONE run: (1)/(2) and (2)/(3a) from the historical run, everything else from this one.

<!-- ablation:begin -->
| workload | Rust | (1) upstream | (2) typed tree † | (3a) bytecode, activation | (3b) bytecode, facts | (4) + partial evaluation |
|---|---:|---:|---:|---:|---:|---:|
| `fs_open_allow_all` | 8.0 ns (0) | 4762 ns† (92) | 4612 ns (92) | 843 ns† (2) | n/a (composite root: `policy.fs.writable_roots`) | 57.9 ns (0) |
| `fs_open_13` | 32.6 ns (0) | 10.8 µs (248.8) | 11.0 µs (248.8) | 2877 ns (9) | n/a (composite root: `policy.fs.writable_roots`) | 140 ns (0) |
| `fs_open_1000` | 1367 ns (0) | 827.5 µs (17064.4) | 829.6 µs (17064.4) | 215.8 µs (578.8) | n/a (composite root: `policy.fs.writable_roots`) | 390 ns† (0) |
| `prefix_13` | 35.1 ns (0) | 11.6 µs (247.8) | 11.7 µs (247.8) | 4068 ns (15) | n/a (composite root: `policy.roots`) | 74.7 ns (0) |
| `nested_fields` | 8.7 ns (0) | 8293 ns† (193) | 8460 ns (193) | 338 ns† (1) | 86.6 ns (0) | — (reads no policy) |
| `all_items` | 17.9 ns (0) | 21.1 µs (455.4) | 20.7 µs (481.8) | 3227 ns (2) | n/a (composite root: `req.body.items`) | — (reads no policy) |
| `policy_residual` | 24.0 ns (0) | 6329 ns (143.1) | 6223 ns (143.1) | 2099 ns (9.4) | n/a (composite root: `policy.methods`) | 144 ns (0) |

† Column (2) is historical: measured on the typed dialect's first engine, since deleted (docs/PERFORMANCE.md, "Historical"). Every other column is this run.
<!-- ablation:end -->

### Time and allocations

| workload | Rust | (1) upstream | (3a) bytecode, activation | (3b) bytecode, facts | (4) + partial evaluation |
|---|---:|---:|---:|---:|---:|
| `prefix_1` | 10.7 ns (0) | 1411 ns (28.2) | 575 ns (3.5) | n/a (composite root: `policy.roots`) | 59.8 ns (0) |
| `prefix_13` | 35.1 ns (0) | 11.6 µs (247.8) | 4068 ns (15) | n/a (composite root: `policy.roots`) | 74.7 ns (0) |
| `prefix_1000` | 2226 ns (0) | 878.8 µs (18256.8) | 301.0 µs (822) | n/a (composite root: `policy.roots`) | 205 ns (0) |
| `fs_open_allow_all` | 8.0 ns (0) | 4762 ns† (92) | 843 ns† (2) | n/a (composite root: `policy.fs.writable_roots`) | 57.9 ns (0) |
| `fs_open_13` | 32.6 ns (0) | 10.8 µs (248.8) | 2877 ns (9) | n/a (composite root: `policy.fs.writable_roots`) | 140 ns (0) |
| `fs_open_1000` | 1367 ns (0) | 827.5 µs (17064.4) | 215.8 µs (578.8) | n/a (composite root: `policy.fs.writable_roots`) | 390 ns† (0) |
| `method_in_literal` | 7.0 ns (0) | 514 ns (13) | 161 ns (1) | 57.6 ns (0) | — (reads no policy) |
| `method_in_policy` | 9.3 ns (0) | 530 ns† (13) | 239 ns (1) | n/a (composite root: `policy.methods`) | 58.8 ns (0) |
| `user_eq` | 7.6 ns (0) | 334 ns (6.9) | 205 ns (1) | 65.0 ns (0) | 55.6 ns (0) |
| `nested_fields` | 8.7 ns (0) | 8293 ns† (193) | 338 ns† (1) | 86.6 ns (0) | — (reads no policy) |
| `short_circuit_first` | 7.2 ns (0) | 4651 ns (99.5) | 610 ns (1) | 160 ns (0) | — (reads no policy) |
| `short_circuit_last` | 7.3 ns (0) | 8262 ns (175) | 1034 ns (1) | 235 ns (0) | — (reads no policy) |
| `all_items` | 17.9 ns (0) | 21.1 µs (455.4) | 3227 ns (2) | n/a (composite root: `req.body.items`) | — (reads no policy) |
| `exists_items` | 15.7 ns (0) | 18.0 µs (416.2) | 2409 ns (2) | n/a (composite root: `req.body.items`) | — (reads no policy) |
| `durations` | 7.0 ns (0) | 696 ns (10) | 204 ns (1) | 87.4 ns (0) | — (reads no policy) |
| `streamed_body_early` | — (streamed row) | 47.0 µs (579.2) | 38.2 µs (539) | 3696 ns (26.8) | — (streamed row) |
| `streamed_body_late` | — (streamed row) | 47.9 µs (579.2) | 37.8 µs (539) | 17.0 µs† (67.8) | — (streamed row) |
| `policy_residual` | 24.0 ns (0) | 6329 ns (143.1) | 2099 ns (9.4) | n/a (composite root: `policy.methods`) | 144 ns (0) |

### Compile and memory

| workload | (1) compile | checked compile | (3) compile + emit | (4) compile / specialize / lower | (1) `Program` | `CelProgram` | (3) + `CelBytecode` | (4) residual + `FastProgram` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `prefix_1` | 45.3 µs | 49.4 µs | 70.4 µs | 49.4 µs / 14.9 µs / 0.9 µs | 1788 B | 2588 B | 5464 B | 1996 B |
| `prefix_13` | 61.3 µs | 72.1 µs | 70.0 µs | 72.1 µs / 111.8 µs / 4.0 µs | 1788 B | 2588 B | 5464 B | 15.7 KiB |
| `prefix_1000` | 44.5 µs | 50.8 µs | 57.4 µs | 50.8 µs / 526.8 µs / 313.4 µs | 1788 B | 2588 B | 5464 B | 126.4 KiB |
| `fs_open_allow_all` | 565.9 µs | 646.3 µs | 613.4 µs | 646.3 µs / 70.6 µs / 2.2 µs | 12.8 KiB | 19.1 KiB | 33.6 KiB | 4004 B |
| `fs_open_13` | 551.0 µs | 611.1 µs | 630.5 µs | 611.1 µs / 209.9 µs / 13.1 µs | 12.8 KiB | 19.1 KiB | 33.6 KiB | 26.1 KiB |
| `fs_open_1000` | 514.5 µs | 840.5 µs | 706.6 µs | 840.5 µs / 854.0 µs / 441.8 µs | 12.8 KiB | 19.1 KiB | 33.6 KiB | 183.8 KiB |
| `method_in_literal` | 30.5 µs | 32.4 µs | 34.1 µs | — | 482 B | 1037 B | 2335 B | — |
| `method_in_policy` | 13.9 µs | 15.6 µs | 17.3 µs | 15.6 µs / 11.2 µs / 1.3 µs | 284 B | 914 B | 2065 B | 2257 B |
| `user_eq` | 13.4 µs | 15.7 µs | 17.3 µs | 15.7 µs / 8.9 µs / 0.9 µs | 285 B | 903 B | 2050 B | 1391 B |
| `nested_fields` | 32.1 µs | 36.4 µs | 40.8 µs | — | 915 B | 1936 B | 4036 B | — |
| `short_circuit_first` | 64.7 µs | 101.1 µs | 111.1 µs | — | 2100 B | 4476 B | 9180 B | — |
| `short_circuit_last` | 65.0 µs | 102.1 µs | 111.7 µs | — | 2100 B | 4476 B | 9180 B | — |
| `all_items` | 39.4 µs | 44.6 µs | 60.9 µs | — | 1451 B | 2199 B | 5454 B | — |
| `exists_items` | 28.4 µs | 32.2 µs | 35.2 µs | — | 1181 B | 1913 B | 4040 B | — |
| `durations` | 34.1 µs | 39.0 µs | 42.1 µs | — | 1081 B | 1845 B | 3539 B | — |
| `streamed_body_early` | 25.7 µs | 30.2 µs | 33.1 µs | — | 625 B | 1440 B | 3221 B | — |
| `streamed_body_late` | 26.0 µs | 29.0 µs | 31.9 µs | — | 625 B | 1440 B | 3221 B | — |
| `policy_residual` | 91.8 µs | 137.3 µs | 151.9 µs | 137.3 µs / 78.7 µs / 5.6 µs | 3038 B | 5198 B | 9968 B | 11.6 KiB |

### Streamed body: document and run state

| workload | document | streamed run state (max over the set) |
|---|---:|---:|
| `streamed_body_early` | 4026 B | 383 B |
| `streamed_body_late` | 4026 B | 383 B |

† the runs' medians spread more than 10%: fs_open_allow_all / upstream: 11%; fs_open_allow_all / bytecode_act: 12%; fs_open_1000 / specialized: 11%; method_in_policy / upstream: 11%; nested_fields / upstream: 11%; nested_fields / bytecode_act: 12%; streamed_body_late / bytecode_facts: 43%

Measured on the engine source of this revision (the backend reads `CelValue` directly; the tree evaluator is gone).

One cell is more than 10% slower than the run in the historical section: (4) `fs_open_13`, 126 ns
then and 140 ns now (+11.1%). Every other (3a), (3b) and (4) cell is within 10% of it or faster.

## Reading the table

Each figure is a quotient of two cells of one run, to one decimal.

- **(1)/(2), what typing alone bought** (historical run): 1.0 on every headline row
  (`fs_open_allow_all` 4833/4612, `nested_fields` 8499/8460, `policy_residual` 6149/6223).
- **(2)/(3a), what the compile step and the register interpreter bought on top** (historical run):
  4.0 `fs_open_allow_all`, 3.1 `fs_open_13`, 3.1 `fs_open_1000`, 2.3 `prefix_13`, 17.6
  `nested_fields`, 4.4 `all_items`, 2.3 `policy_residual`.
- **(1)/(3a), over the same bound activation** (this run): 5.6 `fs_open_allow_all`, 3.8
  `fs_open_13`, 3.8 `fs_open_1000`, 2.9 `prefix_13`, 24.5 `nested_fields`, 6.5 `all_items`, 3.0
  `policy_residual`.
- **(1)/(3b), the typed bytecode backend reading the request by field** (this run): 95.8
  `nested_fields`, 5.1 `user_eq`; 193 and 6.9 allocations per decision against 0.
- **(3b)/(4), what binding the policy at compile time bought** (this run): 1.2 `user_eq`, the one
  workload with both cells. Where (3b) is `n/a`, (3a)/(4): 14.6 `fs_open_allow_all`, 20.6
  `fs_open_13`, 553.3 `fs_open_1000`, 54.5 `prefix_13`, 14.6 `policy_residual`.
- **(1)/(4)** (this run): 82.2 `fs_open_allow_all`, 77.1 `fs_open_13`, 2121.8 `fs_open_1000`, 155.3
  `prefix_13`, 44.0 `policy_residual`. **Rust/(4)**: 3.5 on `fs_open_1000` (1367 ns / 390 ns), where
  the hand-written Rust scans the 1000 roots linearly and (4) runs a matcher; 0.1 to 0.5 on the other
  headline rows.
- **Streamed**: buffered (1) over the streamed run, 12.7 with the demanded fields early (47.0 µs /
  3696 ns) and 2.8 with them late (47.9 µs / 17.0 µs); the streamed run holds 383 B of state for a
  4026 B document.
- **Compile**: (3) compile + emit over (1) compile, 1.1 on `fs_open_13` (630.5 µs / 551.0 µs) and 1.7
  on `policy_residual` (151.9 µs / 91.8 µs).

### Historical: the tree evaluator, column (2)

Measured on the last revision that still carried the tree evaluator (typed-cel `55d75a8`, whose engine
source is identical to the measured one up to formatting); these numbers cannot be re-run from this tree. The other columns are from that same run, so (2) is compared with them and
never with the tables above.

| workload | Rust | (1) upstream | (2) typed tree | (3a) bytecode, activation | (3b) bytecode, facts | (4) + partial evaluation |
|---|---:|---:|---:|---:|---:|---:|
| `prefix_1` | 10.8 ns (0) | 1401 ns (28.2) | 1479 ns† (28.2) | 690 ns (3.5) | n/a (composite root: `policy.roots`) | 60.2 ns (0) |
| `prefix_13` | 36.1 ns (0) | 11.3 µs (247.8) | 11.7 µs (247.8) | 5059 ns (15) | n/a (composite root: `policy.roots`) | 76.0 ns (0) |
| `prefix_1000` | 2318 ns (0) | 860.2 µs (18256.8) | 878.7 µs (18256.8) | 367.6 µs (822) | n/a (composite root: `policy.roots`) | 214 ns (0) |
| `fs_open_allow_all` | 8.0 ns (0) | 4833 ns (92) | 4612 ns (92) | 1163 ns (2) | n/a (composite root: `policy.fs.writable_roots`) | 56.4 ns (0) |
| `fs_open_13` | 29.6 ns (0) | 10.6 µs (248.8) | 11.0 µs (248.8) | 3563 ns† (9) | n/a (composite root: `policy.fs.writable_roots`) | 126 ns (0) |
| `fs_open_1000` | 1329 ns (0) | 804.4 µs (17064.4) | 829.6 µs (17064.4) | 265.5 µs (578.8) | n/a (composite root: `policy.fs.writable_roots`) | 384 ns (0) |
| `method_in_literal` | 6.9 ns (0) | 513 ns (13) | 459 ns (12) | 179 ns (1) | 58.9 ns (0) | — (reads no policy) |
| `method_in_policy` | 10.7 ns (0) | 553 ns† (13) | 540 ns (13) | 310 ns (1) | n/a (composite root: `policy.methods`) | 58.2 ns (0) |
| `user_eq` | 7.3 ns (0) | 322 ns (6.9) | 335 ns (6.9) | 284 ns (1) | 64.6 ns (0) | 54.5 ns (0) |
| `nested_fields` | 8.4 ns (0) | 8499 ns (193) | 8460 ns (193) | 482 ns (1) | 81.8 ns (0) | — (reads no policy) |
| `short_circuit_first` | 7.1 ns (0) | 4618 ns (99.5) | 4745 ns (99.5) | 791 ns (1) | 148 ns (0) | — (reads no policy) |
| `short_circuit_last` | 7.1 ns (0) | 7921 ns (175) | 8260 ns (175) | 1367 ns (1) | 227 ns (0) | — (reads no policy) |
| `all_items` | 17.6 ns (0) | 20.0 µs (455.4) | 20.7 µs (481.8) | 4679 ns (2) | n/a (composite root: `req.body.items`) | — (reads no policy) |
| `exists_items` | 15.6 ns (0) | 17.8 µs (416.2) | 18.3 µs (429.5) | 3197 ns (2) | n/a (composite root: `req.body.items`) | — (reads no policy) |
| `durations` | 6.9 ns (0) | 694 ns (10) | 656 ns (10) | 274 ns (1) | 83.1 ns (0) | — (reads no policy) |
| `streamed_body_early` | — (streamed row) | 47.0 µs (579.2) | 63.5 µs (846) | 66.0 µs (830) | 6123 ns (80.8) | — (streamed row) |
| `streamed_body_late` | — (streamed row) | 47.3 µs (579.2) | 63.3 µs (846) | 63.3 µs (830) | 18.7 µs (121.8) | — (streamed row) |
| `policy_residual` | 24.1 ns (0) | 6149 ns (143.1) | 6223 ns (143.1) | 2661 ns (9.4) | n/a (composite root: `policy.methods`) | 141 ns (0) |

† in this table: the runs' medians spread more than 10%: prefix_1 / typed_tree: 15%; fs_open_13 /
bytecode_act: 26%; method_in_policy / upstream: 12%.
