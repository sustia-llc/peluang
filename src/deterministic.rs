//! Deterministic kernels (Fritz 2020, Def. 10.1) and almost surely
//! deterministic kernels (Fritz 2020, Def. 13.11).

use crate::almost_sure::as_equal;
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

/// For `p : A → X` and `f : X → Y`, whether `f ≫ copy(Y)` and
/// `copy(X) ≫ (f ⊗ f)` are `p`-almost surely equal under
/// `almost_sure::as_equal` (Fritz 2020, Def. 13.11). Returns
/// `Error::NotComposable` when the codomain of `p` differs from the domain of
/// `f`, with no kernel built, then `true` with no kernel built when the domain
/// of `f` is empty, then the `Error::TooLarge` of building either side.
/// `f ⊗ f` has `X.card()² · Y.card()²` weights, and it is built whether or not
/// `p` reaches each input. An input counts as reached when its weight under
/// `p` is `!= P::zero()`, and entries are compared under `Prob::approx_eq`: in
/// the `f64` lane an input with a positive weight below `F64_TOLERANCE` is
/// reached, and underflow in a composite `p` can turn a positive weight into
/// zero, so a reached input can count as unreached.
pub fn is_as_deterministic<P: Prob>(p: &Kernel<P>, f: &Kernel<P>) -> Result<bool> {
    p.composable(f)?;
    if f.domain().card() == 0 {
        return Ok(true);
    }
    let lhs = f.compose(&Kernel::copy(f.codomain())?)?;
    let rhs = Kernel::copy(f.domain())?.compose(&f.tensor(f)?)?;
    as_equal(p, &lhs, &rhs)
}
