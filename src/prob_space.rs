//! Morphisms of states and their couplings (Fritz 2020, Def. 13.8,
//! Prop. 13.9 (b), equation (13.2)).

use crate::error::{Error, Result};
use crate::finset::{FinObj, reserve};
use crate::kernel::Kernel;
use crate::markov::Compose;
use crate::prob::Prob;

/// For a state `psi : FinObj::unit() → X`, `f : X → Y` and `phi`, whether
/// `psi ≫ f` equals `phi` under `Kernel::approx_eq`: whether `f` is a morphism
/// of states `(X, psi) → (Y, phi)` (Fritz 2020, Def. 13.8). Returns
/// `Error::NotAState` when the domain of `psi` is not `FinObj::unit()`, then
/// `Error::NotComposable` when the codomain of `psi` differs from the domain
/// of `f`, then `Error::NotParallel` when the domain of `phi` differs from the
/// domain of `psi` or the codomain of `phi` differs from the codomain of `f`,
/// all three with no kernel built, then `Error::TooLarge` when a product
/// overflows `usize` or reserving a `Vec` capacity fails. The
/// `Error::NotParallel` holds in `fst` the domain of `psi` and the codomain of
/// `f`, the type of `psi ≫ f`, and in `snd` the domain and the codomain of
/// `phi`.
pub fn is_state_preserving<P: Prob>(
    psi: &Kernel<P>,
    f: &Kernel<P>,
    phi: &Kernel<P>,
) -> Result<bool> {
    if *psi.domain() != FinObj::unit() {
        return Err(Error::NotAState {
            domain: psi.domain().clone(),
        });
    }
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
/// `FinObj::unit() → X ⊗ Y` with the weight `psi(x) · f(y|x)`, one
/// `Prob::mul`, at output `(x, y)`, `X` major (Fritz 2020, Prop. 13.9 (b);
/// equation (13.2), left side). The result is built without the column tests
/// of `Kernel::new`. Returns `Error::NotAState` when the domain of `psi` is
/// not `FinObj::unit()`, then `Error::NotComposable` when the codomain of
/// `psi` differs from the domain of `f`, both with no kernel built, then
/// `Error::TooLarge` when a product overflows `usize` or reserving a `Vec`
/// capacity fails; no other allocation reports an error.
pub fn coupling<P: Prob>(psi: &Kernel<P>, f: &Kernel<P>) -> Result<Kernel<P>> {
    if *psi.domain() != FinObj::unit() {
        return Err(Error::NotAState {
            domain: psi.domain().clone(),
        });
    }
    psi.composable(f)?;
    let (x, y) = (f.domain(), f.codomain());
    let cod = x.tensor(y)?;
    let mut data = reserve(1, cod.card())?;
    for i in 0..x.card() {
        for j in 0..y.card() {
            data.push(psi.weight(0, i).mul(f.weight(i, j)));
        }
    }
    Ok(Kernel::from_parts(FinObj::unit(), cod, data))
}
