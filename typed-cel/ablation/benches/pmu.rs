//! Hardware counters for the timed loop, through `perf_event_open(2)` — a cloud VM may expose the
//! PMU but carry no `perf` binary. User-space counts only (`exclude_kernel | exclude_hv`).

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
mod imp {
    use std::arch::asm;

    unsafe fn syscall5(nr: usize, a: usize, b: usize, c: usize, d: usize, e: usize) -> isize {
        let ret: isize;
        asm!("syscall", inlateout("rax") nr as isize => ret, in("rdi") a, in("rsi") b,
             in("rdx") c, in("r10") d, in("r8") e, lateout("rcx") _, lateout("r11") _,
             options(nostack));
        ret
    }
    const SYS_READ: usize = 0;
    const SYS_PERF_EVENT_OPEN: usize = 298;
    /// PERF_TYPE_HARDWARE configs: cycles, instructions, branch instructions, branch misses.
    const CONFIGS: [u64; 4] = [0, 1, 4, 5];

    pub struct Ctr {
        fds: [isize; 4],
    }

    impl Ctr {
        pub fn new() -> Option<Ctr> {
            let mut fds = [-1isize; 4];
            for (i, config) in CONFIGS.into_iter().enumerate() {
                // struct perf_event_attr, PERF_ATTR_SIZE_VER8 = 136 bytes, zeroed:
                //   u32 type @0 (0 = HARDWARE), u32 size @4, u64 config @8, flags bitfield @40.
                let mut attr = [0u64; 17];
                attr[0] = 136u64 << 32;
                attr[1] = config;
                attr[5] = (1 << 5) | (1 << 6); // exclude_kernel | exclude_hv; enabled from open
                                               // pid 0 (this thread), cpu -1 (any), group_fd -1, flags 0
                let fd = unsafe {
                    syscall5(
                        SYS_PERF_EVENT_OPEN,
                        attr.as_ptr() as usize,
                        0,
                        usize::MAX,
                        usize::MAX,
                        0,
                    )
                };
                if fd < 0 {
                    return None;
                }
                fds[i] = fd;
            }
            Some(Ctr { fds })
        }

        pub fn read(&self) -> [u64; 4] {
            let mut out = [0u64; 4];
            for (i, fd) in self.fds.iter().enumerate() {
                unsafe {
                    syscall5(
                        SYS_READ,
                        *fd as usize,
                        &mut out[i] as *mut u64 as usize,
                        8,
                        0,
                        0,
                    )
                };
            }
            out
        }
    }
}

#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
mod imp {
    pub struct Ctr;
    impl Ctr {
        pub fn new() -> Option<Ctr> {
            None
        }
        pub fn read(&self) -> [u64; 4] {
            [0; 4]
        }
    }
}

pub use imp::Ctr;

/// Per-call (cycles, instructions, branches, branch misses) over `iters` calls of `f`.
pub fn per_call<F: FnMut(usize) -> bool>(c: &Ctr, n: usize, iters: usize, f: &mut F) -> [f64; 4] {
    let a = c.read();
    for i in 0..iters {
        std::hint::black_box(f(std::hint::black_box(i % n)));
    }
    let b = c.read();
    let mut o = [0f64; 4];
    for k in 0..4 {
        o[k] = (b[k] - a[k]) as f64 / iters as f64;
    }
    o
}
