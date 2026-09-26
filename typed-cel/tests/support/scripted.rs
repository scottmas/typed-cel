//! A lazy value whose members the test sets while an evaluation is suspended.
//!
//! Shared by `tests/lazy_poll.rs` and the later steppable-VM and streamed-run test files; included
//! with `#[path]` from each.

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::sync::Mutex;

use typed_cel::{Access, CelError, CelValue, DemandHandle, LazyValue, Presence};

/// A lazy whose members are set by the test while an evaluation is suspended. Every read is
/// counted per member, so a test can prove a member was never touched.
#[derive(Debug, Default)]
pub struct Scripted {
    state: Mutex<BTreeMap<String, Slot>>,
    reads: Mutex<BTreeMap<String, usize>>,
}

#[derive(Clone, Debug)]
pub enum Slot {
    Ready(CelValue),
    Pending(u32),
    Missing,
    Fails(String),
}

impl Scripted {
    pub fn set(&self, name: &str, slot: Slot) {
        self.state.lock().unwrap().insert(name.into(), slot);
    }

    pub fn reads(&self, name: &str) -> usize {
        *self.reads.lock().unwrap().get(name).unwrap_or(&0)
    }
}

impl LazyValue for Scripted {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        // The evaluator must never reach this: it reads through the polls. The distinct text lets a
        // test see it if it does.
        match self.poll_member(name)? {
            Access::Ready(v) => Ok(v),
            Access::Pending(_) => Err(CelError::Bind {
                message: "scripted: pending".into(),
            }),
        }
    }

    fn poll_member(&self, name: &str) -> Result<Access, CelError> {
        *self.reads.lock().unwrap().entry(name.into()).or_default() += 1;
        let slot = self
            .state
            .lock()
            .unwrap()
            .get(name)
            .cloned()
            .unwrap_or(Slot::Missing);
        match slot {
            Slot::Ready(v) => Ok(Access::Ready(v)),
            Slot::Pending(id) => Ok(Access::Pending(DemandHandle::new(id))),
            Slot::Missing => Err(CelError::NoSuchMember { key: name.into() }),
            Slot::Fails(m) => Err(CelError::Bind { message: m }),
        }
    }

    fn poll_has(&self, name: &str) -> Result<Presence, CelError> {
        match self.poll_member(name) {
            Ok(Access::Ready(_)) => Ok(Presence::Known(true)),
            Ok(Access::Pending(h)) => Ok(Presence::Pending(h)),
            Err(CelError::NoSuchMember { .. }) => Ok(Presence::Known(false)),
            Err(e) => Err(e),
        }
    }
}
