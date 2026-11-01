//! Deterministic kernels (Fritz 2020, Def. 10.1).

use crate::error::Result;
use crate::kernel::Kernel;
use crate::markov::{Compose, Tensor};
use crate::prob::Prob;

/// Whether `f ≫ copy(cod)` equals `copy(dom) ≫ (f ⊗ f)` under
/// `Kernel::approx_eq`, or the `Error::TooLarge` of building either side.
/// Returns `true` with no kernel built when the domain is empty.
pub fn is_deterministic<P: Prob>(f: &Kernel<P>) -> Result<bool> {
    if f.domain().card() == 0 {
        return Ok(true);
    }
    let lhs = f.compose(&Kernel::copy(f.codomain())?)?;
    let rhs = Kernel::copy(f.domain())?.compose(&f.tensor(f)?)?;
    Ok(lhs.approx_eq(&rhs))
}
