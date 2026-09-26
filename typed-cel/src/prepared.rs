//! The run-time half of an environment: what a compiled program needs to evaluate, and nothing
//! it needed to compile.
//!
//! A [`CelEnvironment`](crate::CelEnvironment) holds a roster of `CelTy`s, which hold `Rc`s, so it
//! is neither `Send` nor `Sync` and cannot sit in anything shared across threads. A [`CelRuntime`]
//! holds only the function table and the limits. Every activation it makes shares ONE function
//! table, so a per-evaluation activation costs a handful of empty maps, not a stdlib.

use std::sync::Arc;

use crate::bounds::CelLimits;
use crate::CelActivation;

/// What a compiled program needs at run time: the function table and the limits.
///
/// Built once per compiled program with [`CelEnvironment::runtime`](crate::CelEnvironment::runtime);
/// holds nothing borrowed from, or cloned out of, the environment's roster, so it outlives it.
#[derive(Clone)]
pub struct CelRuntime {
    functions: Arc<crate::env::Env>,
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
    pub(crate) fn new(functions: Arc<crate::env::Env>, limits: CelLimits) -> CelRuntime {
        CelRuntime { functions, limits }
    }

    /// A fresh activation for ONE evaluation, with no roster: bind with
    /// [`CelActivation::bind_fact`]. No roster clone and no function-table rebuild.
    pub fn activation(&self) -> CelActivation {
        CelActivation::prepared(self.functions.clone(), self.limits)
    }
}
