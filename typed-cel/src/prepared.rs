//! The run-time half of an environment: what a compiled program needs to evaluate, and nothing
//! it needed to compile.
//!
//! A [`CelEnvironment`](crate::CelEnvironment) holds a roster of `CelTy`s, which hold `Rc`s, so it
//! is neither `Send` nor `Sync` and cannot sit in anything shared across threads. A [`CelRuntime`]
//! holds only the limits, so a per-evaluation activation costs a handful of empty maps.

use crate::bounds::CelLimits;
use crate::CelActivation;

/// What a compiled program needs at run time: the limits.
///
/// Built once per compiled program with [`CelEnvironment::runtime`](crate::CelEnvironment::runtime);
/// holds nothing borrowed from, or cloned out of, the environment's roster, so it outlives it.
#[derive(Clone)]
pub struct CelRuntime {
    limits: CelLimits,
}

impl std::fmt::Debug for CelRuntime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CelRuntime")
            .field("limits", &self.limits)
            .finish_non_exhaustive()
    }
}

impl CelRuntime {
    pub(crate) fn new(limits: CelLimits) -> CelRuntime {
        CelRuntime { limits }
    }

    /// A fresh activation for ONE evaluation, with no roster: bind with
    /// [`CelActivation::bind_fact`]. No roster clone.
    pub fn activation(&self) -> CelActivation {
        CelActivation::prepared(self.limits)
    }
}
