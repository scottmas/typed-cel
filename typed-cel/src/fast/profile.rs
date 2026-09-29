//! Deterministic run counters: what a run DID, counted, never timed.
//!
//! Compiled only under the `profile` feature, which the crate's own test build turns on (the self
//! dev-dependency in `Cargo.toml`) and nothing a consumer links does. With the feature off every
//! hook below is `#[cfg]`'d away at its call site, so the production dispatch loop is the same code
//! it was before this module existed.
//!
//! A measurement is [`measure`]: reset this thread's counters, run the closure, read them back.
//! Counters are per THREAD and none of them allocates, so a measurement never perturbs what it
//! measures — the allocation count in particular counts only the closure's own allocations.
//!
//! Allocations are counted by [`CountingAlloc`], which a test binary installs as its
//! `#[global_allocator]`; without it [`RunProfile::allocs`] stays 0 and
//! [`alloc_counting_installed`] says so.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;

/// The distinct op names one thread can count; far above the op set's size.
const NAMES: usize = 64;
/// Fields counted by index; a read of a later field lands in `reads_past`.
const FIELDS: usize = 256;

struct Counters {
    ops: [(&'static str, u64); NAMES],
    slow: [(&'static str, u64); NAMES],
    reads: [u64; FIELDS],
    reads_past: u64,
    store: u64,
    execs: u64,
    scanned: u64,
}

impl Counters {
    const ZERO: Counters = Counters {
        ops: [("", 0); NAMES],
        slow: [("", 0); NAMES],
        reads: [0; FIELDS],
        reads_past: 0,
        store: 0,
        execs: 0,
        scanned: 0,
    };
}

thread_local! {
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
    static COUNTERS: RefCell<Counters> = const { RefCell::new(Counters::ZERO) };
    static ALLOCS: Cell<u64> = const { Cell::new(0) };
    static ALLOC_BYTES: Cell<u64> = const { Cell::new(0) };
}

#[inline(always)]
fn active() -> bool {
    ACTIVE.with(Cell::get)
}

fn bump(table: &mut [(&'static str, u64); NAMES], name: &'static str) {
    for slot in table.iter_mut() {
        if slot.1 == 0 && slot.0.is_empty() {
            *slot = (name, 1);
            return;
        }
        if std::ptr::eq(slot.0, name) || slot.0 == name {
            slot.1 += 1;
            return;
        }
    }
}

/// One op dispatched by `exec`.
#[inline(always)]
pub(crate) fn op(name: &'static str) {
    if active() {
        COUNTERS.with(|c| bump(&mut c.borrow_mut().ops, name));
    }
}

/// One op that went out of line, to `slow`.
#[inline(always)]
pub(crate) fn slow(name: &'static str) {
    if active() {
        COUNTERS.with(|c| bump(&mut c.borrow_mut().slow, name));
    }
}

/// One host read of field `f` — its value, its tag or its presence.
#[inline(always)]
pub(crate) fn read(f: u32) {
    if active() {
        COUNTERS.with(|c| {
            let mut c = c.borrow_mut();
            match c.reads.get_mut(f as usize) {
                Some(n) => *n += 1,
                None => c.reads_past += 1,
            }
        });
    }
}

/// One value moved into a run's store (a string, list or map the run built, or an owned value).
#[inline(always)]
pub(crate) fn store() {
    if active() {
        COUNTERS.with(|c| c.borrow_mut().store += 1);
    }
}

/// `n` loop elements an `IterNext` scanned past: passed over without dispatching the body's ops.
#[inline(always)]
pub(crate) fn scanned(n: usize) {
    if active() {
        COUNTERS.with(|c| c.borrow_mut().scanned += n as u64);
    }
}

/// One entry into `exec` — a run, a resumed run, or a fold the partial evaluator ran.
#[inline(always)]
pub(crate) fn exec() {
    if active() {
        COUNTERS.with(|c| c.borrow_mut().execs += 1);
    }
}

/// What one measured closure did.
#[derive(Clone, Debug, Default)]
pub struct RunProfile {
    /// Ops dispatched, in total.
    pub ops: u64,
    /// Ops dispatched, per op name.
    pub by_op: BTreeMap<&'static str, u64>,
    /// Ops that went out of line, to `slow`.
    pub slow: u64,
    /// ... per op name.
    pub slow_by_op: BTreeMap<&'static str, u64>,
    /// Host field reads (value, tag or presence), in total.
    pub reads: u64,
    /// Host field reads per field index ([`FieldId`](super::FieldId)); trailing zeros trimmed.
    pub reads_by_field: Vec<u64>,
    /// Values a run moved into its store: every string, list or map it BUILT.
    pub store: u64,
    /// Entries into the interpreter loop.
    pub execs: u64,
    /// Loop elements an `IterNext` scanned past, dispatching none of the body's ops.
    pub scanned: u64,
    /// Allocations the closure made (0 unless [`CountingAlloc`] is the global allocator).
    pub allocs: u64,
    /// Bytes those allocations asked for.
    pub alloc_bytes: u64,
}

impl RunProfile {
    /// How many times op `name` was dispatched.
    pub fn op(&self, name: &str) -> u64 {
        self.by_op.get(name).copied().unwrap_or(0)
    }

    /// How many times op `name` went to `slow`.
    pub fn slow_of(&self, name: &str) -> u64 {
        self.slow_by_op.get(name).copied().unwrap_or(0)
    }

    /// How many times `program` read the field spelled `names` (`["req", "path"]`) — 0 when the
    /// program reads no such field. Meaningful for a measurement that ran `program` alone.
    pub fn reads_of(&self, program: &super::FastProgram, names: &[&str]) -> u64 {
        program
            .field(names)
            .and_then(|f| self.reads_by_field.get(f.index()).copied())
            .unwrap_or(0)
    }

    /// Every count, one line, for a failure message or a report row.
    pub fn summary(&self) -> String {
        let ops: Vec<String> = self.by_op.iter().map(|(k, v)| format!("{k}={v}")).collect();
        let slow: Vec<String> = self
            .slow_by_op
            .iter()
            .map(|(k, v)| format!("{k}={v}"))
            .collect();
        format!(
            "ops={} [{}] slow={} [{}] reads={} {:?} store={} execs={} scanned={} allocs={} ({} B)",
            self.ops,
            ops.join(" "),
            self.slow,
            slow.join(" "),
            self.reads,
            self.reads_by_field,
            self.store,
            self.execs,
            self.scanned,
            self.allocs,
            self.alloc_bytes
        )
    }
}

/// Run `f` with this thread's counters on, and hand back what it did. Not re-entrant.
pub fn measure<T>(f: impl FnOnce() -> T) -> (T, RunProfile) {
    assert!(!active(), "profile::measure is not re-entrant");
    COUNTERS.with(|c| *c.borrow_mut() = Counters::ZERO);
    ALLOCS.with(|a| a.set(0));
    ALLOC_BYTES.with(|a| a.set(0));
    ACTIVE.with(|a| a.set(true));
    let out = f();
    ACTIVE.with(|a| a.set(false));
    let allocs = ALLOCS.with(Cell::get);
    let alloc_bytes = ALLOC_BYTES.with(Cell::get);
    let p = COUNTERS.with(|c| {
        let c = c.borrow();
        let table = |t: &[(&'static str, u64); NAMES]| -> BTreeMap<&'static str, u64> {
            t.iter()
                .filter(|(n, v)| !n.is_empty() && *v > 0)
                .copied()
                .collect()
        };
        let by_op = table(&c.ops);
        let slow_by_op = table(&c.slow);
        let mut reads_by_field = c.reads.to_vec();
        while reads_by_field.last() == Some(&0) {
            reads_by_field.pop();
        }
        RunProfile {
            ops: by_op.values().sum(),
            slow: slow_by_op.values().sum(),
            by_op,
            slow_by_op,
            reads: c.reads.iter().sum::<u64>() + c.reads_past,
            reads_by_field,
            store: c.store,
            execs: c.execs,
            scanned: c.scanned,
            allocs,
            alloc_bytes,
        }
    });
    (out, p)
}

/// Is [`CountingAlloc`] this binary's global allocator? Probed by allocating while counting.
pub fn alloc_counting_installed() -> bool {
    let (_, p) = measure(|| std::hint::black_box(Box::new(0u64)));
    p.allocs > 0
}

/// A global allocator that counts, per thread, the allocations made inside [`measure`]. Install
/// it in a test binary: `#[global_allocator] static A: CountingAlloc = CountingAlloc;`.
pub struct CountingAlloc;

impl CountingAlloc {
    #[inline(always)]
    fn count(size: usize) {
        // `try_with`: an allocation during thread teardown finds the slots gone and is not counted.
        if ACTIVE.try_with(Cell::get).unwrap_or(false) {
            let _ = ALLOCS.try_with(|a| a.set(a.get() + 1));
            let _ = ALLOC_BYTES.try_with(|a| a.set(a.get() + size as u64));
        }
    }
}

// SAFETY: every method defers to `System`; counting touches only const-initialized thread-locals,
// which never allocate.
unsafe impl GlobalAlloc for CountingAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        Self::count(layout.size());
        System.alloc(layout)
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        Self::count(layout.size());
        System.alloc_zeroed(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout)
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        Self::count(new_size);
        System.realloc(ptr, layout, new_size)
    }
}
