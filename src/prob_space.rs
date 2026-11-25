//! Morphisms of states and their couplings (Fritz 2020, Def. 13.8,
//! Prop. 13.9 (b), equation (13.2)).

use crate::error::{Error, Result};
use crate::finset::FinObj;
use crate::kernel::Kernel;
use crate::markov::Compose;
use crate::prob::Prob;

/// For `psi : A → X`, `f : X → Y` and `phi : A → Y`, whether `psi ≫ f` equals
/// `phi` under `Kernel::approx_eq`; with `A` equal to `FinObj::unit()`, whether
/// `f` is a morphism of states `(X, psi) → (Y, phi)` (Fritz 2020, Def. 13.8).
/// Returns `Error::NotComposable` when the codomain of `psi` differs from the
/// domain of `f`, then `Error::NotParallel` when the domain of `phi` differs
/// from the domain of `psi` or the codomain of `phi` differs from the codomain
/// of `f`, both with no kernel built, then `Error::TooLarge` when a product
/// overflows `usize` or reserving a `Vec` capacity fails.
pub fn is_state_preserving<P: Prob>(
    psi: &Kernel<P>,
    f: &Kernel<P>,
    phi: &Kernel<P>,
) -> Result<bool> {
    psi.composable(f)?;
    if psi.domain() != phi.domain() || f.codomain() != phi.codomain() {
        return Err(Error::NotParallel {
            fst: Box::new((psi.domain().clone(), f.codomain().clone())),
            snd: Box::new((phi.domain().clone(), phi.codomain().clone())),
        });
    }
    Ok(psi.compose(f)?.approx_eq(phi))
}

/// For a state `psi : FinObj::unit() → X` and `f : X → Y`, the kernel
/// `psi ≫ copy(X) ≫ whisker_left(X, f)` of type `FinObj::unit() → X ⊗ Y`, with
/// weight `psi(x) · f(y|x)` at output `(x, y)` (Fritz 2020, Prop. 13.9 (b);
/// equation (13.2), left side). Returns `Error::NotAState` when the domain of
/// `psi` is not `FinObj::unit()`, then `Error::NotComposable` when the codomain
/// of `psi` differs from the domain of `f`, both with no kernel built, then
/// `Error::TooLarge` when a product overflows `usize` or reserving a `Vec`
/// capacity fails.
pub fn coupling<P: Prob>(psi: &Kernel<P>, f: &Kernel<P>) -> Result<Kernel<P>> {
    if *psi.domain() != FinObj::unit() {
        return Err(Error::NotAState {
            domain: psi.domain().clone(),
        });
    }
    psi.composable(f)?;
    let x = f.domain();
    psi.compose(&Kernel::copy(x)?)?
        .compose(&Kernel::whisker_left(x, f)?)
}
