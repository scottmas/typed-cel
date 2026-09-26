//! A counting global allocator: `tests/fast_alloc.rs`'s, extended with the bytes still LIVE.
//!
//! Both counters are gated on thread-local switches, so the timed loops pay one thread-local read
//! per allocation and nothing else. The bench is single-threaded.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::atomic::{AtomicIsize, AtomicUsize, Ordering};

pub struct Counting;

/// Allocations (and reallocations) made while [`count`] was on.
pub static ALLOCS: AtomicUsize = AtomicUsize::new(0);
/// Bytes allocated minus bytes freed while [`track`] was on.
pub static LIVE: AtomicIsize = AtomicIsize::new(0);

thread_local! {
    static COUNTING: Cell<bool> = const { Cell::new(false) };
    static TRACKING: Cell<bool> = const { Cell::new(false) };
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if COUNTING.with(|c| c.get()) {
            ALLOCS.fetch_add(1, Ordering::Relaxed);
        }
        if TRACKING.with(|c| c.get()) {
            LIVE.fetch_add(layout.size() as isize, Ordering::Relaxed);
        }
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if TRACKING.with(|c| c.get()) {
            LIVE.fetch_sub(layout.size() as isize, Ordering::Relaxed);
        }
        System.dealloc(ptr, layout)
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if COUNTING.with(|c| c.get()) {
            ALLOCS.fetch_add(1, Ordering::Relaxed);
        }
        if TRACKING.with(|c| c.get()) {
            LIVE.fetch_add(
                new_size as isize - layout.size() as isize,
                Ordering::Relaxed,
            );
        }
        System.realloc(ptr, layout, new_size)
    }
}

/// Allocations per call of `f`, over `n` calls.
pub fn allocs_per<F: FnMut(usize)>(n: usize, mut f: F) -> f64 {
    ALLOCS.store(0, Ordering::SeqCst);
    COUNTING.with(|c| c.set(true));
    for i in 0..n {
        f(i);
    }
    COUNTING.with(|c| c.set(false));
    ALLOCS.load(Ordering::SeqCst) as f64 / n as f64
}

/// The bytes `build` leaves live: everything it allocated and did not free, including what the
/// value it returns holds. The value is dropped after the measurement.
pub fn retained<T, F: FnOnce() -> T>(build: F) -> isize {
    LIVE.store(0, Ordering::SeqCst);
    TRACKING.with(|c| c.set(true));
    let kept = build();
    let live = LIVE.load(Ordering::SeqCst);
    TRACKING.with(|c| c.set(false));
    drop(kept);
    live
}
