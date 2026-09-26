//! Lazy facts that do bounded synchronous work when READ.
//!
//! A program that can suspend reads a value that is still arriving through a [`LazyValue`] that
//! may answer "not yet". The other members such a program reads are facts computed on demand —
//! a lookup, a liveness probe — that answer at once. For those, short-circuiting IS the ordering
//! rule, and it holds only if a fact:
//!
//! 1. runs only when the program reads it,
//! 2. runs at most once per value, however many times it is read — a failure is remembered like
//!    a success, so one run never sees two answers for the same fact,
//! 3. never reports `Pending`.
//!
//! [`SyncFacts`] guarantees all three, so no caller hand-writes a `LazyValue` for such a fact.
//! Presence (`has(f.x)`, `"x" in f`) is answered from the declared names and never runs a fact.

use std::sync::OnceLock;

use crate::lazy::{CelKey, CelValue, LazyValue, Presence};
use crate::CelError;

/// One fact: bounded synchronous work, run at most once. The error is the fact's own message.
///
/// `'static` because a [`LazyValue`] is, and because a run that suspends outlives the call that
/// built it and may move between threads: a fact OWNS what it captures (a `&'static` handle to a
/// process-wide service, owned copies of the scalars it needs), never a borrow.
pub type FactFn = Box<dyn Fn() -> Result<CelValue, String> + Send + Sync>;

/// A record of facts that are computed when READ.
///
/// Members run in the order the program reads them, at most once per value, and never report
/// `Pending`. Build one per run: memoization is per value.
pub struct SyncFacts {
    names: Vec<CelKey>,
    facts: Vec<(FactFn, OnceLock<Result<CelValue, String>>)>,
}

impl SyncFacts {
    pub fn new() -> SyncFacts {
        SyncFacts {
            names: Vec::new(),
            facts: Vec::new(),
        }
    }

    /// Declare `name`. A second declaration of the same name replaces the first.
    pub fn with(mut self, name: &str, fact: FactFn) -> SyncFacts {
        let slot = (fact, OnceLock::new());
        match self.names.iter().position(|k| k.as_str() == name) {
            Some(ix) => self.facts[ix] = slot,
            None => {
                self.names.push(CelKey::new(name));
                self.facts.push(slot);
            }
        }
        self
    }
}

impl Default for SyncFacts {
    fn default() -> SyncFacts {
        SyncFacts::new()
    }
}

impl std::fmt::Debug for SyncFacts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SyncFacts")
            .field("names", &self.names)
            .finish_non_exhaustive()
    }
}

impl LazyValue for SyncFacts {
    fn member(&self, name: &str) -> Result<CelValue, CelError> {
        let ix = self
            .names
            .iter()
            .position(|k| k.as_str() == name)
            .ok_or_else(|| CelError::NoSuchMember {
                key: name.to_string(),
            })?;
        let (fact, once) = &self.facts[ix];
        match once.get_or_init(fact) {
            Ok(v) => Ok(v.clone()),
            // `CelError` is not `Clone`; a fresh one per read, from the memoized text.
            Err(m) => Err(CelError::Bind {
                message: format!("`{name}` could not be read: {m}"),
            }),
        }
    }

    // `poll_member`: the trait default, which is never `Pending`.

    /// Presence is known from the declaration. The default would derive it from `member`, which
    /// would spend the fact's work to answer an existence question.
    fn poll_has(&self, name: &str) -> Result<Presence, CelError> {
        Ok(Presence::Known(
            self.names.iter().any(|k| k.as_str() == name),
        ))
    }

    fn keys(&self) -> Option<Box<dyn Iterator<Item = &CelKey> + '_>> {
        Some(Box::new(self.names.iter()))
    }
}
