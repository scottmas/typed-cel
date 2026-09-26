//! `emit`: a compiled program, lowered for the one backend that runs it (`fast/`).
//!
//! A [`CelBytecode`] is the lowered program with the authored source and demand set it came from.
//! [`Vm::eval`](crate::Vm::eval), [`Vm::eval_result`](crate::Vm::eval_result) and a
//! [`VmRun`](crate::VmRun) all execute it on the fast backend; there is no other.

use std::sync::Arc;

use crate::demand::DemandSet;
use crate::FastProgram;

/// One expression, lowered. Cheap to clone (the program is shared), `Send + Sync`.
#[derive(Clone, Debug)]
pub struct CelBytecode {
    pub(crate) fast: Arc<FastProgram>,
    demand: DemandSet,
    source: Arc<str>,
}

impl CelBytecode {
    /// The AUTHORED source this was emitted from.
    pub fn source(&self) -> &str {
        &self.source
    }

    /// The lowered program, to decide over a caller's own data ([`FastProgram::decide`],
    /// [`FastProgram::decide_tag`]).
    pub fn program(&self) -> &FastProgram {
        &self.fast
    }

    /// What the expression reads — the checker's demand set, carried unchanged.
    pub fn demand(&self) -> &DemandSet {
        &self.demand
    }
}

/// Lower a compiled program. The bytecode carries the program's authored source and demand set.
///
/// Every program [`CelEnvironment::compile`](crate::CelEnvironment::compile) or
/// [`specialize`](crate::CelEnvironment::specialize) produced lowers; a refusal
/// ([`CelError::Emit`](crate::CelError::Emit)) is a defect of the backend, never a fallback.
pub fn emit(p: &crate::CelProgram) -> Result<CelBytecode, crate::CelError> {
    Ok(CelBytecode {
        fast: Arc::clone(p.lowered()?),
        demand: p.demand().clone(),
        source: p.source_arc(),
    })
}
