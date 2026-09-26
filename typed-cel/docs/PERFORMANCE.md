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

Measured after the fast-path work (inline hot ops, the stack register path, fused
read-compare-branch ops, the specializer's folds; see the fast-path ledger below).

The headline puts the historical column (2) beside this run's columns. Every ratio below is read
within ONE run: (1)/(2) and (2)/(3a) from the historical run, everything else from this one.

<!-- ablation:begin -->
| workload | Rust | (1) upstream | (2) typed tree † | (3a) bytecode, activation | (3b) bytecode, facts | (4) + partial evaluation |
|---|---:|---:|---:|---:|---:|---:|
| `fs_open_allow_all` | 8.1 ns (0) | 5121 ns (92) | 4612 ns (92) | 893 ns† (2) | n/a (composite root: `policy.fs.writable_roots`) | 31.3 ns (0) |
| `fs_open_13` | 32.7 ns (0) | 12.2 µs† (248.8) | 11.0 µs (248.8) | 2798 ns (9) | n/a (composite root: `policy.fs.writable_roots`) | 123 ns† (0) |
| `fs_open_1000` | 1490 ns (0) | 882.5 µs (17064.4) | 829.6 µs (17064.4) | 213.9 µs (578.8) | n/a (composite root: `policy.fs.writable_roots`) | 366 ns† (0) |
| `prefix_13` | 35.2 ns (0) | 12.3 µs (247.8) | 11.7 µs (247.8) | 4257 ns (15) | n/a (composite root: `policy.roots`) | 59.3 ns (0) |
| `nested_fields` | 9.0 ns (0) | 9742 ns (193) | 8460 ns (193) | 312 ns (0) | 42.5 ns (0) | — (reads no policy) |
| `all_items` | 19.0 ns (0) | 23.0 µs (455.4) | 20.7 µs (481.8) | 3298 ns (2) | n/a (composite root: `req.body.items`) | — (reads no policy) |
| `policy_residual` | 25.5 ns (0) | 6933 ns (143.1) | 6223 ns (143.1) | 2154 ns (9.4) | n/a (composite root: `policy.methods`) | 86.2 ns (0) |

† Column (2) is historical: measured on the typed dialect's first engine, since deleted (docs/PERFORMANCE.md, "Historical"). Every other column is this run.
<!-- ablation:end -->

### Time and allocations

| workload | Rust | (1) upstream | (3a) bytecode, activation | (3b) bytecode, facts | (4) + partial evaluation |
|---|---:|---:|---:|---:|---:|
| `prefix_1` | 10.8 ns (0) | 1460 ns (28.2) | 562 ns (3.5) | n/a (composite root: `policy.roots`) | 42.2 ns (0) |
| `prefix_13` | 35.2 ns (0) | 12.3 µs (247.8) | 4257 ns (15) | n/a (composite root: `policy.roots`) | 59.3 ns (0) |
| `prefix_1000` | 2331 ns (0) | 949.9 µs (18256.8) | 298.3 µs (822) | n/a (composite root: `policy.roots`) | 207 ns (0) |
| `fs_open_allow_all` | 8.1 ns (0) | 5121 ns (92) | 893 ns† (2) | n/a (composite root: `policy.fs.writable_roots`) | 31.3 ns (0) |
| `fs_open_13` | 32.7 ns (0) | 12.2 µs† (248.8) | 2798 ns (9) | n/a (composite root: `policy.fs.writable_roots`) | 123 ns† (0) |
| `fs_open_1000` | 1490 ns (0) | 882.5 µs (17064.4) | 213.9 µs (578.8) | n/a (composite root: `policy.fs.writable_roots`) | 366 ns† (0) |
| `method_in_literal` | 7.1 ns (0) | 555 ns (13) | 131 ns (0) | 44.5 ns (0) | — (reads no policy) |
| `method_in_policy` | 9.3 ns (0) | 568 ns (13) | 217 ns (0) | n/a (composite root: `policy.methods`) | 43.6 ns (0) |
| `user_eq` | 7.7 ns (0) | 373 ns (6.9) | 199 ns (0) | 49.9 ns (0) | 47.7 ns (0) |
| `nested_fields` | 9.0 ns (0) | 9742 ns (193) | 312 ns (0) | 42.5 ns (0) | — (reads no policy) |
| `short_circuit_first` | 7.3 ns (0) | 5123 ns (99.5) | 569 ns (0) | 79.1 ns (0) | — (reads no policy) |
| `short_circuit_last` | 7.2 ns (0) | 8953 ns (175) | 915 ns (0) | 93.1 ns (0) | — (reads no policy) |
| `all_items` | 19.0 ns (0) | 23.0 µs (455.4) | 3298 ns (2) | n/a (composite root: `req.body.items`) | — (reads no policy) |
| `exists_items` | 16.5 ns (0) | 20.2 µs (416.2) | 2508 ns (2) | n/a (composite root: `req.body.items`) | — (reads no policy) |
| `durations` | 7.1 ns (0) | 758 ns (10) | 189 ns (0) | 70.4 ns (0) | — (reads no policy) |
| `streamed_body_early` | — (streamed row) | 51.9 µs (579.2) | 40.4 µs (538) | 3278 ns (22.2) | — (streamed row) |
| `streamed_body_late` | — (streamed row) | 50.4 µs (579.2) | 41.0 µs (538) | 15.3 µs (63.2) | — (streamed row) |
| `policy_residual` | 25.5 ns (0) | 6933 ns (143.1) | 2154 ns (9.4) | n/a (composite root: `policy.methods`) | 86.2 ns (0) |

### Compile and memory

| workload | (1) compile | checked compile | (3) compile + emit | (4) compile / specialize / lower | (1) `Program` | `CelProgram` | (3) + `CelBytecode` | (4) residual + `FastProgram` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `prefix_1` | 44.3 µs | 51.8 µs | 74.5 µs | 51.8 µs / 15.1 µs / 1.3 µs | 1788 B | 2588 B | 5464 B | 2428 B |
| `prefix_13` | 54.6 µs | 57.6 µs | 76.9 µs | 57.6 µs / 108.9 µs / 4.7 µs | 1788 B | 2588 B | 5464 B | 16.1 KiB |
| `prefix_1000` | 52.7 µs | 59.4 µs | 66.5 µs | 59.4 µs / 598.9 µs / 349.1 µs | 1788 B | 2588 B | 5464 B | 126.4 KiB |
| `fs_open_allow_all` | 623.1 µs | 652.7 µs | 713.8 µs | 652.7 µs / 71.3 µs / 0.6 µs | 12.8 KiB | 19.1 KiB | 33.7 KiB | 887 B |
| `fs_open_13` | 711.2 µs | 716.3 µs | 747.0 µs | 716.3 µs / 212.7 µs / 14.9 µs | 12.8 KiB | 19.1 KiB | 33.7 KiB | 26.1 KiB |
| `fs_open_1000` | 573.2 µs | 642.7 µs | 670.2 µs | 642.7 µs / 859.3 µs / 454.0 µs | 12.8 KiB | 19.1 KiB | 33.7 KiB | 183.8 KiB |
| `method_in_literal` | 31.6 µs | 33.6 µs | 36.3 µs | — | 482 B | 1037 B | 2335 B | — |
| `method_in_policy` | 13.2 µs | 15.7 µs | 18.5 µs | 15.7 µs / 11.2 µs / 1.3 µs | 284 B | 914 B | 2065 B | 2257 B |
| `user_eq` | 13.4 µs | 18.6 µs | 19.5 µs | 18.6 µs / 9.2 µs / 1.1 µs | 285 B | 903 B | 2050 B | 1391 B |
| `nested_fields` | 31.8 µs | 36.8 µs | 42.9 µs | — | 915 B | 1936 B | 4084 B | — |
| `short_circuit_first` | 70.6 µs | 116.0 µs | 135.6 µs | — | 2100 B | 4476 B | 9804 B | — |
| `short_circuit_last` | 64.8 µs | 103.7 µs | 111.0 µs | — | 2100 B | 4476 B | 9804 B | — |
| `all_items` | 40.8 µs | 45.8 µs | 61.7 µs | — | 1451 B | 2199 B | 5454 B | — |
| `exists_items` | 30.3 µs | 43.3 µs | 36.6 µs | — | 1181 B | 1913 B | 4040 B | — |
| `durations` | 33.8 µs | 38.4 µs | 42.8 µs | — | 1081 B | 1845 B | 3563 B | — |
| `streamed_body_early` | 25.2 µs | 29.2 µs | 33.2 µs | — | 625 B | 1440 B | 3557 B | — |
| `streamed_body_late` | 30.6 µs | 29.7 µs | 35.8 µs | — | 625 B | 1440 B | 3557 B | — |
| `policy_residual` | 97.5 µs | 147.0 µs | 160.1 µs | 147.0 µs / 82.4 µs / 6.4 µs | 3038 B | 5198 B | 10016 B | 11.6 KiB |

### Streamed body: document and run state

| workload | document | streamed run state (max over the set) |
|---|---:|---:|
| `streamed_body_early` | 4026 B | 383 B |
| `streamed_body_late` | 4026 B | 383 B |

† the runs' medians spread more than 10%: fs_open_allow_all / bytecode_act: 16%; fs_open_13 / upstream: 12%; fs_open_13 / specialized: 16%; fs_open_1000 / specialized: 12%

### Fast-path ledger

`decide` cycles per decision (ns in parentheses), `--cycles`, pinned to core 1, per-cell median of
three runs (`ablation/cycles-baseline.txt` is the baseline column). One column per
fast-path step (S2 the common ops inline, S3 the stack register path, S4 verified unchecked
fetches, S5 fused read-compare-branch ops, S6 the specializer's folds); the floor rows are the spikes in `ablation/benches/floor.rs`, and
`constant_true` is the program `true`, which costs only the fixed per-call path.

| workload | column | baseline | S2 | S3 | S4 | S5 | S6 |
|---|---|---:|---:|---:|---:|---:|---:|
| `constant_true` | (3b) | 97 (30.4) | 109 (30.7) | 81 (25.8) | 80 (25.9) | 77 (24.1) | 73 (23.1) |
| `durations` | (3b) | 286 (90.5) | 272 (85.4) | 242 (71.8) | 216 (64.6) | 224 (70.8) | 224 (69.2) |
| `fs_open_1000` | (4) | 1267 (396.2) | 1338 (405.1) | 1244 (383.7) | 1235 (373.5) | 1202 (365.3) | 1227 (381.0) |
| `fs_open_13` | (4) | 463 (139.7) | 457 (135.7) | 425 (129.3) | 396 (116.2) | 374 (115.7) | 364 (116.6) |
| `fs_open_allow_all` | (4) | 186 (57.7) | 194 (57.8) | 163 (49.3) | 156 (47.3) | 134 (42.9) | 110 (34.0) |
| `method_in_literal` | (3b) | 188 (57.7) | 174 (55.1) | 145 (45.6) | 141 (45.3) | 140 (45.2) | 138 (42.6) |
| `method_in_policy` | (4) | 188 (58.3) | 169 (52.4) | 151 (44.8) | 148 (42.4) | 142 (44.0) | 144 (42.5) |
| `nested_fields` | (3b) | 276 (83.5) | 240 (75.3) | 209 (64.3) | 201 (61.6) | 142 (42.5) | 136 (44.0) |
| `policy_residual` | (4) | 485 (147.2) | 388 (117.9) | 347 (108.4) | 322 (97.7) | 273 (85.7) | 276 (83.4) |
| `prefix_1` | (4) | 211 (62.0) | 180 (55.5) | 153 (47.4) | 151 (47.5) | 144 (44.9) | 141 (43.6) |
| `prefix_1000` | (4) | 714 (214.7) | 705 (214.5) | 619 (196.8) | 636 (198.7) | 626 (192.6) | 653 (201.2) |
| `prefix_13` | (4) | 257 (78.8) | 234 (71.6) | 210 (65.7) | 209 (63.7) | 200 (58.9) | 197 (58.4) |
| `short_circuit_first` | (3b) | 517 (151.6) | 344 (102.1) | 319 (99.9) | 284 (83.9) | 248 (79.1) | 250 (76.5) |
| `short_circuit_last` | (3b) | 768 (234.2) | 441 (141.8) | 404 (122.3) | 353 (106.6) | 312 (96.7) | 320 (93.3) |
| `user_eq` | (3b) | 214 (65.8) | 206 (62.7) | 170 (54.1) | 165 (51.2) | 166 (52.0) | 162 (48.8) |
| `user_eq` | (4) | 186 (56.2) | 184 (57.8) | 154 (47.7) | 148 (47.6) | 154 (48.2) | 158 (46.5) |
| `nested_fields` | floor: lean / fused / closures | 100 / 56 / 78 | 105 / 57 / 82 | 101 / 53 / 81 | 102 / 55 / 83 | 106 / 54 / 76 | 104 / 53 / 75 |
| `nested_fields` | Rust | 26 (8.1) | 29 (8.3) | 26 (8.4) | 26 (8.1) | 26 (8.1) | 26 (8.0) |

Reproduce, on a Linux x86_64 host with the PMU exposed (the bench binary is `target/release/deps/ablation-*`):

```bash
cd typed-cel/ablation && cargo bench --bench ablation --no-run
for i in 1 2 3; do taskset -c 1 $B --cycles > cycles.$i.txt; done
$B --cycles-median cycles.1.txt cycles.2.txt cycles.3.txt          # the median rows
taskset -c 1 $B --cycles --against cycles-baseline.txt               # exit 1: cycles > +5% with more instructions
```

## Reading the table

Each figure is a quotient of two cells of one run, to one decimal.

- **(1)/(2), what typing alone bought** (historical run): 1.0 on every headline row
  (`fs_open_allow_all` 4833/4612, `nested_fields` 8499/8460, `policy_residual` 6149/6223).
- **(2)/(3a), what the compile step and the register interpreter bought on top** (historical run):
  4.0 `fs_open_allow_all`, 3.1 `fs_open_13`, 3.1 `fs_open_1000`, 2.3 `prefix_13`, 17.6
  `nested_fields`, 4.4 `all_items`, 2.3 `policy_residual`.
- **(1)/(3a), over the same bound activation** (this run): 5.7 `fs_open_allow_all`, 4.4
  `fs_open_13`, 4.1 `fs_open_1000`, 2.9 `prefix_13`, 31.2 `nested_fields`, 7.0 `all_items`, 3.2
  `policy_residual`.
- **(1)/(3b), the typed bytecode backend reading the request by field** (this run): 229.2
  `nested_fields`, 7.5 `user_eq`; 193 and 6.9 allocations per decision against 0.
- **(3b)/(4), what binding the policy at compile time bought** (this run): 1.0 `user_eq`, the one
  workload with both cells. Where (3b) is `n/a`, (3a)/(4): 28.5 `fs_open_allow_all`, 22.7
  `fs_open_13`, 584.4 `fs_open_1000`, 71.8 `prefix_13`, 25.0 `policy_residual`.
- **(1)/(4)** (this run): 163.6 `fs_open_allow_all`, 99.2 `fs_open_13`, 2411.2 `fs_open_1000`, 207.4
  `prefix_13`, 80.4 `policy_residual`, 4588.9 `prefix_1000`. **Rust/(4)**: 4.1 on `fs_open_1000`
  (1490 ns / 366 ns) and 11.3 on `prefix_1000` (2331 ns / 207 ns), where the hand-written Rust scans
  the 1000 roots linearly and (4) runs a matcher; 0.3 to 0.6 on the other headline rows.
- **Streamed**: buffered (1) over the streamed run, 15.8 with the demanded fields early (51.9 µs /
  3278 ns) and 3.3 with them late (50.4 µs / 15.3 µs); the streamed run holds 383 B of state for a
  4026 B document.
- **Compile**: (3) compile + emit over (1) compile, 1.1 on `fs_open_13` (747.0 µs / 711.2 µs) and 1.6
  on `policy_residual` (160.1 µs / 97.5 µs).

### Historical: the tree evaluator, column (2)

Measured at `65ff900b0` — the typed tree evaluator was deleted in `1af0c39ea`; these numbers cannot be
re-run from this tree. The other columns are from that same run, so (2) is compared with them and
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
