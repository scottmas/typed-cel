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
  (3) `env.compile` + `emit`; (4) reported split as parse / compile with known (a fresh activation, bind the
  policy, `compile` with it known; the text is parsed once, outside the timing) / lower
  (`FastProgram::new` on the residual).
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

Measured after the fast-path work, the cost-model cliff fixes, the loop floor, the precomputed-head
string-set matchers and numbers held exactly (see the fast-path ledger below).

The headline puts the historical column (2) beside this run's columns. Every ratio below is read
within ONE run: (1)/(2) and (2)/(3a) from the historical run, everything else from this one.

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

### Time and allocations

| workload | Rust | (1) upstream | (3a) bytecode, activation | (3b) bytecode, facts | (4) + partial evaluation |
|---|---:|---:|---:|---:|---:|
| `prefix_1` | 10.4 ns (0) | 1455 ns (28.2) | 243 ns (0) | n/a (composite root: `policy.roots`) | 39.6 ns (0) |
| `prefix_13` | 36.3 ns† (0) | 11.8 µs (247.8) | 447 ns† (0) | n/a (composite root: `policy.roots`) | 48.0 ns† (0) |
| `prefix_1000` | 2343 ns† (0) | 881.3 µs (18256.8) | 14.7 µs (0) | n/a (composite root: `policy.roots`) | 110 ns (0) |
| `fs_open_allow_all` | 8.1 ns (0) | 4810 ns (92) | 455 ns (0) | n/a (composite root: `policy.fs.readonly_roots`) | 32.4 ns (0) |
| `fs_open_13` | 33.2 ns (0) | 11.1 µs (248.8) | 627 ns (0) | n/a (composite root: `policy.fs.readonly_roots`) | 73.4 ns (0) |
| `fs_open_1000` | 1386 ns (0) | 865.2 µs (17064.4) | 11.0 µs (0) | n/a (composite root: `policy.fs.readonly_roots`) | 161 ns (0) |
| `method_in_literal` | 7.1 ns (0) | 546 ns (13) | 131 ns (0) | 38.7 ns (0) | — (reads no policy) |
| `method_in_policy` | 9.0 ns (0) | 540 ns (13) | 179 ns (0) | n/a (composite root: `policy.methods`) | 37.9 ns (0) |
| `user_eq` | 7.7 ns (0) | 322 ns (6.9) | 163 ns (0) | 39.8 ns (0) | 37.5 ns (0) |
| `nested_fields` | 8.7 ns (0) | 8878 ns (193) | 239 ns (0) | 35.9 ns (0) | — (reads no policy) |
| `short_circuit_first` | 7.2 ns (0) | 4718 ns (99.5) | 435 ns (0) | 32.5 ns (0) | — (reads no policy) |
| `short_circuit_last` | 7.2 ns (0) | 8200 ns (175) | 723 ns (0) | 40.4 ns (0) | — (reads no policy) |
| `all_items` | 18.0 ns (0) | 21.5 µs (455.4) | 782 ns (0) | n/a (composite root: `req.body.items`) | — (reads no policy) |
| `exists_items` | 15.6 ns (0) | 19.9 µs (416.2) | 538 ns (0) | n/a (composite root: `req.body.items`) | — (reads no policy) |
| `durations` | 7.1 ns (0) | 721 ns (10) | 149 ns (0) | 39.7 ns (0) | — (reads no policy) |
| `optional_sum` | 7.5 ns (0) | 2937 ns (58) | 454 ns (0) | 110 ns (0) | — (reads no policy) |
| `required_sum` | 7.2 ns (0) | 3118 ns (56) | 470 ns (0) | 132 ns (0) | — (reads no policy) |
| `streamed_body_early` | — (streamed row) | 50.1 µs (579.2) | 38.6 µs (538) | 3107 ns (22.2) | — (streamed row) |
| `streamed_body_late` | — (streamed row) | 48.4 µs (579.2) | 38.4 µs (538) | 15.7 µs (63.2) | — (streamed row) |
| `policy_residual` | 25.1 ns (0) | 6357 ns (143.1) | 548 ns (0) | n/a (composite root: `policy.methods`) | 63.2 ns (0) |

### Compile and memory

| workload | (1) compile | checked compile | (3) compile + emit | (4) parse / compile with known / lower | (1) `Program` | `CelProgram` | (3) + `CelBytecode` | (4) residual + `FastProgram` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `prefix_1` | 45.1 µs | 50.3 µs | 82.4 µs | 50.3 µs / 17.1 µs / 2.6 µs | 1788 B | 2588 B | 4857 B | 2444 B |
| `prefix_13` | 46.3 µs | 53.4 µs | 68.7 µs | 53.4 µs / 132.0 µs / 19.3 µs | 1788 B | 2588 B | 4857 B | 16.6 KiB |
| `prefix_1000` | 44.9 µs | 50.9 µs | 66.7 µs | 50.9 µs / 575.8 µs / 358.3 µs | 1788 B | 2588 B | 4857 B | 170.1 KiB |
| `fs_open_allow_all` | 609.9 µs | 634.8 µs | 700.9 µs | 634.8 µs / 73.5 µs / 0.9 µs | 12.8 KiB | 19.1 KiB | 28.5 KiB | 887 B |
| `fs_open_13` | 596.4 µs | 674.0 µs | 699.0 µs | 674.0 µs / 260.4 µs / 42.2 µs | 12.8 KiB | 19.1 KiB | 28.5 KiB | 27.3 KiB |
| `fs_open_1000` | 537.4 µs | 649.9 µs | 642.0 µs | 649.9 µs / 819.9 µs / 582.4 µs | 12.8 KiB | 19.1 KiB | 28.5 KiB | 235.3 KiB |
| `method_in_literal` | 29.6 µs | 32.9 µs | 35.6 µs | — | 482 B | 1037 B | 2503 B | — |
| `method_in_policy` | 13.6 µs | 15.8 µs | 18.5 µs | 15.8 µs / 11.6 µs / 1.8 µs | 284 B | 914 B | 2137 B | 2353 B |
| `user_eq` | 13.5 µs | 19.7 µs | 18.1 µs | 19.7 µs / 9.4 µs / 1.5 µs | 285 B | 903 B | 2122 B | 1391 B |
| `nested_fields` | 32.3 µs | 37.2 µs | 46.2 µs | — | 915 B | 1936 B | 4160 B | — |
| `short_circuit_first` | 69.7 µs | 106.9 µs | 132.5 µs | — | 2100 B | 4476 B | 8844 B | — |
| `short_circuit_last` | 66.3 µs | 106.3 µs | 120.9 µs | — | 2100 B | 4476 B | 8844 B | — |
| `all_items` | 47.4 µs | 49.1 µs | 54.1 µs | — | 1451 B | 2199 B | 4870 B | — |
| `exists_items` | 28.5 µs | 31.3 µs | 38.1 µs | — | 1181 B | 1913 B | 3816 B | — |
| `durations` | 40.2 µs | 45.9 µs | 48.8 µs | — | 1081 B | 1845 B | 3995 B | — |
| `optional_sum` | 151.9 µs | 123.4 µs | 188.2 µs | — | 2488 B | 4308 B | 7308 B | — |
| `required_sum` | 37.3 µs | 59.5 µs | 68.2 µs | — | 1112 B | 2388 B | 4620 B | — |
| `streamed_body_early` | 27.1 µs | 31.7 µs | 37.8 µs | — | 625 B | 1440 B | 3629 B | — |
| `streamed_body_late` | 26.6 µs | 31.4 µs | 36.5 µs | — | 625 B | 1440 B | 3629 B | — |
| `policy_residual` | 108.9 µs | 161.9 µs | 178.5 µs | 161.9 µs / 107.6 µs / 18.3 µs | 3038 B | 5198 B | 8700 B | 11.7 KiB |

### Streamed body: document and run state

| workload | document | streamed run state (max over the set) |
|---|---:|---:|
| `streamed_body_early` | 4026 B | 383 B |
| `streamed_body_late` | 4026 B | 383 B |

† the runs' medians spread more than 10%: prefix_13 / rust: 36%; prefix_13 / bytecode_act: 16%; prefix_13 / specialized: 10%; prefix_1000 / rust: 13%

### Fast-path ledger

`decide` cycles per decision (ns in parentheses), `--cycles`, pinned to core 1, per-cell median of
three runs (`ablation/cycles-baseline.txt` is the baseline column). One column per
fast-path step (S2 the common ops inline, S3 the stack register path, S4 verified unchecked
fetches, S5 fused read-compare-branch ops, S6 the specializer's folds), then `cliffs`: after the
cost-model cliff fixes (below), then `loops`: after the loop floor, then `sets`: string-set
matchers comparing precomputed heads instead of calling `memcmp`, then `exact`: numbers held
exactly (an `Int` arm first on every fast path, the cross-representation compare out of line —
the current `ablation/cycles-baseline.txt`); the floor rows are the spikes in
`ablation/benches/floor.rs`, and
`constant_true` is the program `true`, which costs only the fixed per-call path.

`exact` costs no row more than noise, with one measured exception: `durations` (3b) runs 352
instructions where `sets` ran 339. Every numeric compare now tests an `Int` arm before the
`Duration` one in `ordering`, and a two-compare program pays that test twice. The first cut cost
far more — the exact cross-representation compare inlined into `exec` spilled its op pointer to
the stack, +20% on `fs_open_13`, a program with no number in it — until that compare moved out of
line and took its operands by value (`mixed_order`, `src/fast/mod.rs`).

| workload | column | baseline | S2 | S3 | S4 | S5 | S6 | cliffs | loops | sets | exact |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `constant_true` | (3b) | 97 (30.4) | 109 (30.7) | 81 (25.8) | 80 (25.9) | 77 (24.1) | 73 (23.1) | 82 (23.5) | 75 (24.2) | 79 (24.8) | 76 (22.6) |
| `durations` | (3b) | 286 (90.5) | 272 (85.4) | 242 (71.8) | 216 (64.6) | 224 (70.8) | 224 (69.2) | 130 (39.8) | 122 (37.0) | 128 (39.6) | 128 (38.6) |
| `fs_open_1000` | (4) | 1267 (396.2) | 1338 (405.1) | 1244 (383.7) | 1235 (373.5) | 1202 (365.3) | 1227 (381.0) | 1205 (368.0) | 1182 (375.5) | 537 (168.4) | 530 (163.6) |
| `fs_open_13` | (4) | 463 (139.7) | 457 (135.7) | 425 (129.3) | 396 (116.2) | 374 (115.7) | 364 (116.6) | 392 (115.7) | 372 (116.3) | 242 (76.4) | 242 (73.2) |
| `fs_open_allow_all` | (4) | 186 (57.7) | 194 (57.8) | 163 (49.3) | 156 (47.3) | 134 (42.9) | 110 (34.0) | 109 (33.7) | 104 (33.0) | 109 (34.3) | 105 (33.8) |
| `method_in_literal` | (3b) | 188 (57.7) | 174 (55.1) | 145 (45.6) | 141 (45.3) | 140 (45.2) | 138 (42.6) | 138 (43.7) | 138 (41.4) | 128 (40.5) | 123 (39.0) |
| `method_in_policy` | (4) | 188 (58.3) | 169 (52.4) | 151 (44.8) | 148 (42.4) | 142 (44.0) | 144 (42.5) | 140 (42.5) | 134 (42.0) | 130 (41.8) | 129 (37.9) |
| `nested_fields` | (3b) | 276 (83.5) | 240 (75.3) | 209 (64.3) | 201 (61.6) | 142 (42.5) | 136 (44.0) | 125 (39.1) | 122 (36.6) | 124 (38.0) | 109 (34.7) |
| `policy_residual` | (4) | 485 (147.2) | 388 (117.9) | 347 (108.4) | 322 (97.7) | 273 (85.7) | 276 (83.4) | 238 (72.5) | 246 (77.5) | 199 (67.5) | 195 (59.6) |
| `prefix_1` | (4) | 211 (62.0) | 180 (55.5) | 153 (47.4) | 151 (47.5) | 144 (44.9) | 141 (43.6) | 142 (43.6) | 137 (44.6) | 129 (39.9) | 123 (38.2) |
| `prefix_1000` | (4) | 714 (214.7) | 705 (214.5) | 619 (196.8) | 636 (198.7) | 626 (192.6) | 653 (201.2) | 648 (202.5) | 680 (209.9) | 358 (113.0) | 354 (111.9) |
| `prefix_13` | (4) | 257 (78.8) | 234 (71.6) | 210 (65.7) | 209 (63.7) | 200 (58.9) | 197 (58.4) | 204 (60.0) | 210 (63.8) | 178 (51.6) | 155 (47.6) |
| `short_circuit_first` | (3b) | 517 (151.6) | 344 (102.1) | 319 (99.9) | 284 (83.9) | 248 (79.1) | 250 (76.5) | 149 (47.2) | 110 (33.0) | 107 (33.3) | 112 (32.3) |
| `short_circuit_last` | (3b) | 768 (234.2) | 441 (141.8) | 404 (122.3) | 353 (106.6) | 312 (96.7) | 320 (93.3) | 188 (59.4) | 133 (41.0) | 135 (42.8) | 129 (39.5) |
| `user_eq` | (3b) | 214 (65.8) | 206 (62.7) | 170 (54.1) | 165 (51.2) | 166 (52.0) | 162 (48.8) | 161 (50.6) | 132 (42.0) | 136 (41.9) | 133 (40.0) |
| `user_eq` | (4) | 186 (56.2) | 184 (57.8) | 154 (47.7) | 148 (47.6) | 154 (48.2) | 158 (46.5) | 155 (46.8) | 131 (39.9) | 126 (40.3) | 128 (39.0) |
| `nested_fields` | floor: lean / fused / closures | 100 / 56 / 78 | 105 / 57 / 82 | 101 / 53 / 81 | 102 / 55 / 83 | 106 / 54 / 76 | 104 / 53 / 75 | 103 / 56 / 84 | 101 / 53 / 86 | 105 / 55 / 83 | 100 / 54 / 83 |
| `nested_fields` | Rust | 26 (8.1) | 29 (8.3) | 26 (8.4) | 26 (8.1) | 26 (8.1) | 26 (8.0) | 27 (8.2) | 29 (8.4) | 26 (9.0) | 25 (8.0) |

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
- **(1)/(3a), over the same bound activation** (this run): 10.6 `fs_open_allow_all`, 17.7 `fs_open_13`, 78.7 `fs_open_1000`, 26.4 `prefix_13`, 37.1 `nested_fields`, 27.5 `all_items`, 11.6 `policy_residual`.
- **(1)/(3b), the typed bytecode backend reading the request by field** (this run): 247.3
  `nested_fields`, 8.1 `user_eq`; 193 and 6.9 allocations per decision against 0.
- **(3b)/(4), what binding the policy at compile time bought** (this run): 1.1 `user_eq`, the one
  workload with both cells. Where (3b) is `n/a`, (3a)/(4): 14.0 `fs_open_allow_all`, 8.5 `fs_open_13`, 68.3 `fs_open_1000`, 9.3 `prefix_13`, 8.7 `policy_residual`.
- **(1)/(4)** (this run): 148.5 `fs_open_allow_all`, 151.2 `fs_open_13`, 5373.9 `fs_open_1000`, 245.8 `prefix_13`, 100.6 `policy_residual`, 8011.8 `prefix_1000`. **Rust/(4)**: 8.6 on `fs_open_1000`
  (1386 ns / 161 ns) and 21.3 on `prefix_1000` (2343 ns / 110 ns), where the hand-written Rust scans
  the 1000 roots linearly and (4) runs a matcher; 0.2 to 0.8 on the other headline rows.
- **Streamed**: buffered (1) over the streamed run, 16.1 with the demanded fields early (50.1 µs /
  3107 ns) and 3.1 with them late (48.4 µs / 15.7 µs); the streamed run holds 383 B of state for a
  4026 B document.
- **Compile**: (3) compile + emit over (1) compile, 1.2 on `fs_open_13` (699.0 µs / 596.4 µs) and 1.6
  on `policy_residual` (178.5 µs / 108.9 µs).

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

## Known cliffs

A sweep of program families (every comprehension macro, `in`, `size`, string ops over long strings,
nested loops, `&&`/`||` chains and nested conditionals up to the depth limit, durations, literal
lists and maps, `has()`, deep paths, streamed runs), each at N ∈ {1, 10, 100, 1000} and on four legs
(`Vm::eval` over an activation, `decide` over `Facts`, specialized with the collection known, and
specialized with it unknown), plus the generated typed corpus and the conformance lane. Every cliff
below was flagged by COST MODEL (deterministic counts of what a decision does), then timed, and is
pinned in [`../tests/perf_cliffs.rs`](../tests/perf_cliffs.rs) by a test whose budget is what a good
lowering needs — each red until its fix landed, green now.

**The counters.** `typed_cel::profile` (the `profile` cargo feature, `#[doc(hidden)]`, on only for
the crate's own test build through the self dev-dependency) counts ops dispatched (per op name),
entries into the out-of-line `slow` path, host field reads (per `FieldId`), values moved into a run's
store, entries into `exec`, and — under the test binary's `profile::CountingAlloc` global allocator —
allocations and bytes. `profile::measure(|| …)` returns a `RunProfile`. Every hook is `#[cfg]`'d out at
its call site without the feature: measured with `--cycles` against a pristine build of the same tree
(three runs, median), every gated cell's instruction count was identical (±1) and the gate passed.

**The harvester.** Not a gate: `#[ignore]`d, run explicitly.

```bash
cargo test -p typed-cel --test perf_harvest -- --ignored --nocapture --test-threads=1 --exact harvest
cargo test -p typed-cel --test perf_harvest -- --ignored --nocapture harvest_corpora
cargo test -p typed-cel --test perf_harvest -- --ignored --nocapture harvest_streamed
# the ns column: no `profile` feature, pinned to one core, on a Hetzner cx33
cd typed-cel/ablation && cargo bench --bench cliffs --no-run
taskset -c 1 $(ls -t target/release/deps/cliffs-* | grep -v '\.d$' | head -1)
# per element of an unspecialized loop, beside Rust; `--check` is the per-op instruction gate
cargo bench --bench loops --no-run
taskset -c 1 $(ls -t target/release/deps/loops-* | grep -v '\.d$' | head -1) --check
# where the instructions go: `LOOPS_PROFILE=<family>` spins one row for `perf record`
```

`harvest` prints one row per (family, leg, N) and flags `OPS/ELEM` (> 8 ops per element),
`SLOW/ELEM`, `INVARIANT-READ`, `SUPERLINEAR` (ops, allocations, store pushes or bytes growing faster
than N), `ALLOC` (a program that builds nothing its answer needs allocates), `FOLDABLE` (a residual
still computes over literals) and `COMPILE` (specialize's work or the residual superlinear in its
input). Every program's listing lands in `target/tmp/perf_harvest_listings.txt`.

The first sweep's thirteen cliffs are closed: every pin in the table below is green. What each was, and what it costs now — ns per decision
from `ablation/benches/cliffs.rs` (AMD EPYC-Rome, `taskset -c 1`, no `profile` feature):

| # | pin (`tests/perf_cliffs.rs`) | shape | before → after | fixed by |
|---|---|---|---|---|
| 1 | `predicate_loop_ops_per_element_is_bounded` | `names.exists(x, x == req.name)` over an activation, n=1000 | 158 µs → 31 µs | a predicate loop: the predicate a branch inside `IterNext … Jump` (`try_predicate_loop`) |
| 2 | `common_ops_stay_in_the_dispatch_loop` | a five-test scalar decision | 134 ns → 80 ns | `Not`, `Cmp`, `StrOp`, `Has`, loop ops inline in `exec` |
| 3 | `loop_invariant_field_is_read_once` | `m.all(k, policy.m[k] > req.n)`, n=1000 | 392 µs → 210 µs | `ReadCached`: a field read once per decision, on first use |
| 4 | `a_field_is_read_once_per_decision` | a 16-term `req.n < k` chain | 686 ns → 173 ns | the same, with `CondCmpFK` (row 9) |
| 5 | `startswith_of_concatenation_allocates_nothing` | `req.path.startsWith(req.name + "/")`; its loop over 1000 roots | 107 ns → 55 ns; 251 µs → 53 µs | `StrOp2`: the concatenation tested piecewise, never built |
| 6 | `map_and_filter_build_in_linear_space` | `size(nums.map(x, x * 2.0))`, n=1000 | 5.8 ms → 39 µs | `ListNew` / `Append` / `ListFreeze`: one list grown in place |
| 7 | `vm_eval_allocates_nothing_the_program_does_not_build` | `names.exists` at n=1 through `Vm::eval` | 386 ns → 211 ns | a scratch per thread |
| 8 | `a_literal_collection_of_fields_is_not_built_to_be_searched` | `req.name in [req.path, req.other]`; `{"a": req.n, "b": 2.0}["a"] > 0.0` | 114 ns → 66 ns; 188 ns → 43 ns | an `==` chain; an unrolled predicate; the indexed entry |
| 9 | `comparison_chain_ops_per_term_is_bounded` | `nums.all(x, x > req.n)` specialized at 256 | 10.8 µs → 1.9 µs | `logic_chain` (one pending register a chain) and `CondCmpFK` |
| 10 | `known_membership_is_a_lookup_at_every_size` | `m.exists(k, k == req.name)` specialized at 1000 | 89 µs → 153 ns | a known map's keys in the string matcher; `NumSet` for numbers |
| 11 | `loop_invariant_inner_comprehension_runs_once` | `names.exists(x, x == req.name \|\| nums.exists(y, y < 0.0))`, n=100 | 1.17 ms → 8.8 µs | an invariant comprehension computed once (`BrSet`) |
| 12 | `a_literal_only_subtree_is_folded_before_it_runs` | `req.n < 60.0 * 60.0 * 24.0` | 87 ns → 43 ns | a call over constants folded at lowering (`fold_call`) |
| 13 | `a_discarded_loop_error_allocates_nothing` | `items.exists(i, i.tags[5] == req.name \|\| i.qty > 999.0)` specialized at n=1000 | 1999 allocations → 0 | one in-flight error box, reused; a raised pending error moved, not copied |

Row 13's time did not move with its allocations (270 µs → 254 µs): each element still raises and
catches an index error through `slow`. Row 20 below pins it.

**Measured, not fixed: an integer against a fractional bound.** Numbers are held exactly, so the
rig's `nums` (`1.0`, `2.0`, …) bind as integers while `req.n` is `0.5`: every element of
`policy.nums.all(x, x > req.n)` compares an `Int` with a `Float`. That compare is exact — through
`f64` when the integer is within 2^53, which every `f64`-representable integer is, and through
`i128` otherwise (`cmp_i64_f64`, `src/num.rs`) — and it costs instructions the old all-double
compare did not. `loops --check`, instructions per element before → after numbers were exact:
`list/num/all` 26 → 35 (over its budget of 27 now), `record/all` 108 → 122, `build/filter-size`
175 → 193, `record/absorbed-error` 651 → 670, `build/map-size` 131 → 143. The first cut, which
compared every mixed pair through the general exact path, cost `list/num/all` 126.

### Fixed: the unspecialized loop floor

A second sweep measured what one more element costs a loop over a BOUND collection (`Vm::eval` over
an activation — the leg a policy runs on before, or without, specialization): a flat 20-171 ns per
element against 0.4-16 ns for the same loop in Rust. Two causes multiplied: too many ops per element
(a field test was three ops; `Select`, map iteration, `Arith`, `Matches` left the dispatch loop for
`slow`), and too many instructions per op (~88: `pc` in a stack slot, the 24-byte `Op` copied before
its tag was read, every register bounds-checked and copied to the stack).

The loop-floor work fixed both. The per-op half: fused ops and inline arms (a field test is one
op, `CondFR`; records, maps, arithmetic and regexes stay in the loop); `exec` fetches through a
pointer and matches the op in place; registers are read unchecked, on the strength of
`Code::verify`, and by reference; a small `CelMap` is scanned, not binary-searched. The per-element
half: a predicate loop (`exists`, `all`, `exists_one`) fetches with `IterScan`, which first passes
over every element its body would pass over — the body's leading tests (its REGION: field and
constant tests, `&&`/`||` chains, concatenation tests, regexes, known sets, record members, the map
value at the key) evaluated natively, the common one-test and record shapes as dedicated loops
(`src/fast/scan.rs`) — and hands every other element to the unchanged ops. It reads no host, raises
nothing and writes no register, so every pause, error and deciding element happens where it did.
`map`/`filter` do not scan: every kept element would pay a failed test first (measured +48% on a
filter that keeps all).

Measured by [`../ablation/benches/loops.rs`](../ablation/benches/loops.rs) on a Hetzner cx33 (AMD
EPYC-Rome, `taskset -c 1`): the per-element slope between n=10 and n=1000, ns / instructions; the
before column is `909d2d814`, the last commit before the per-op work. `--check` holds each family
to Rust's instructions + 20 per step a good lowering runs per element (a scanned element: one per
test and per member read).

| family (act leg) | before | after | Rust | budget | over? |
|---|---:|---:|---:|---:|---|
| `names.exists(x, x == req.name)` | 19.9 / 176 | **1.1 / 15** | 0.4 / 5 | 25 | |
| `roots.exists(r, req.path.startsWith(r))` | 26.5 / 198 | **5.7 / 47** | 4.3 / 32 | 52 | |
| `nums.all(x, x > req.n)` | 20.1 / 180 | **2.3 / 26** | 0.6 / 7 | 27 | |
| `names.exists_one(x, x == req.name)` | 20.3 / 176 | **1.1 / 15** | 0.6 / 7 | 27 | |
| `m.exists(k, k == req.name)` | 19.8 / 173 | **1.2 / 15** | 0.4 / 5 | 25 | |
| `m.all(k, policy.m[k] > req.n)` | 27.5 / 253 | **11.5 / 128** | 31.4 / 286 (HashMap) | 326 | |
| `names.exists(x, x.contains(req.name))` | 30.9 / 281 ¹ | **10.8 / 137** | 29.4 / 268 | 288 | |
| `long.exists(x, x.contains(req.name))` (200 B) | 14.1 / 215 ¹ | 15.2 / 157 | 13.3 / 205 | 225 | |
| `req.name in policy.names` | 0.8 / 8 | 0.8 / 8 | 0.5 / 5 | 25 | |
| `roots.exists(r, req.path == r \|\| req.path.startsWith(r + "/"))` | 36.0 / 311 | 20.4 / 188 | 5.1 / 36 | 76 | over |
| `names.exists(x, x.matches("^zz$"))` | 21.8 / 189 | 6.4 / 66 | 2.8 / 27 | 47 | over |
| `items.exists(i, i.id == req.name && i.qty > req.n)` | 69.0 / 455 | 7.9 / 97 | 0.6 / 5 | 45 | over |
| `items.all(i, i.qty > req.n)` | 67.8 / 459 | 9.1 / 108 | 0.6 / 8 | 48 | over |
| `items.exists(i, i.tags.exists(t, t == req.name))` (per item) | 171.1 / 1095 | 72.3 / 497 | 15.7 / 109 | 249 | over |
| `items.all(i, i.tags[5] == req.name \|\| i.qty > 0.0)` | 164.3 / 1102 | 89.4 / 653 | 0.9 / 8 | 168 | over, not scanned |
| `size(nums.map(x, x * 2.0))` | 29.9 / 218 | 15.6 / 130 | ~0 (elided) | 80 | over, not scanned |
| `size(nums.filter(x, x > req.n))` | 35.5 / 295 | 19.5 / 174 | 1.5 / 17 | 97 | over, not scanned |

¹ measured when the family was added (Story 6), before the prebuilt substring searcher.

The counts behind it are pinned in [`../tests/perf_cliffs.rs`](../tests/perf_cliffs.rs):
`a_skipped_element_dispatches_no_op` (no op, no `slow` entry, and ≥ 0.95 elements scanned per
element, for 16 loops) and `a_scanned_loop_reads_what_its_unfused_twin_reads`; the answers, against
the unscanned lowering (`with_unfused_loops`), in [`../tests/comprehensions.rs`](../tests/comprehensions.rs)
`a_scanned_loop_answers_as_its_unfused_twin`.

**Open — the families still over budget, and why** (`loops.rs --check` exits 1 on these eight):

- **Records** (`items.exists`/`all`: 97 / 108 against 45 / 48). A member lookup chases two pointers —
  the record's entries and the key's bytes, each its own allocation — ~35 instructions and two
  likely cache misses per member, where Rust reads a struct field. The next lever is binding a
  record of a declared type as a fixed layout (members by position), not a map.
- **Regex** (66 against 47). Rust's own loop inlines `Regex::search_half`, whose length check
  rejects `^zz$` against an 8-byte name without searching; called from the scan it stays out of
  line (~50 instructions a call).
- **A two-leaf chain with a concatenation** (188 against 76), and the **nested loop's outer
  level** (497 against 249): the generic region walker costs ~90 instructions a step; the outer
  loop's body (a `Select`, an inner `IterInit`/`IterScan`) is not a region, so it dispatches 4 ops
  per item at full cost.
- **Not scanned by design**: an element that errors (`items.all(i, i.tags[5] …)` — the error path is
  the body's), and `map` / a `filter` that keeps its elements (every element runs `Append`). A native
  build loop — a scan that also appends — is the next plan for these.

**SIMD, evaluated.** A bound list is 24-byte `CelValue`s, strings behind a pointer: comparing many
elements at once needs a gather (numbers) or has nothing to vectorize (strings: a length check
rejects most, and `bcmp` is SIMD already), and the scalar scan meets the numeric budgets. The one
place a vector searcher paid is a substring test against a loop-invariant needle:
`memchr::memmem::Finder` (a dependency already in the lock through `regex`), built once per scan —
8-byte names 30.9 → 10.8 ns, where `str::contains` builds its searcher per call. On x86_64 a
200-byte haystack was already SIMD in `str::contains` (flat); aarch64, which has no such path in
std, is expected to gain there too — unmeasured.

A regression the cycles gate caught on the way: a known collection (a residual's `$kN` slot) in a
CONDITION lowered as a predicate loop over the constant instead of `try_match_exists`' matcher —
`fs_open_1000` 1205 → 32742 cycles. `a_known_string_list_is_one_matcher_at_every_size` now holds the
branch shape too, and fails on any element scanned.

**What is already fine** — each held by a GREEN GUARD in the same file:

- a known list of strings under `==`/`startsWith` is one matcher at every size (242 ns at n=1000 vs
  351 µs on the activation leg) — `a_known_string_list_is_one_matcher_at_every_size`;
- string predicates over a 64 KiB string are the same ops and allocate nothing —
  `long_string_predicates_are_constant_ops_and_allocate_nothing`;
- a path five members deep is one read, read or tested for presence — `a_deep_path_is_one_read`;
- a streamed run costs the same ops, reads and allocations at 64 B and 64 KiB of padding before the
  demanded fields — `a_streamed_run_costs_the_same_at_every_document_size`;
- `specialize` leaves no literal-only call in a residual, and its own allocations and the residual's
  node count grow linearly while it unrolls (≈35 allocations and 5 nodes per element) —
  `the_specializer_leaves_no_literal_only_call`;
- `in` and `size` over a bound collection, durations, `has()` and the typed/conformance corpora showed
  no outlier beyond the shapes above (the corpora's worst ops-per-node programs are all nested
  comprehensions, cliff 1; their allocations are errors caught in loop bodies, cliff 13).

`in` over a known number list is a `NumSet` lookup, not a scan, and past `max_unroll` a known
collection falls from the unrolled chain to a predicate loop of a few ops an element.
