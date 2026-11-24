//! The composites of causality (Fritz 2020, Def. 11.31), positivity (Fritz
//! 2020, Def. 11.22) and relative positivity (Fritz 2020, Def. 13.16) on
//! kernels.

use crate::almost_sure::as_equal;
use crate::error::Result;
use crate::kernel::Kernel;
use crate::markov::{Compose, Tensor};
use crate::prob::Prob;

/// For `g : W → X` and `h : X → Y`, the kernel `g ≫ copy(X) ≫ (h ⊗ id_X)` of
/// type `W → Y ⊗ X`, with weight `g(x|w) · h(y|x)` of output `(y, x)` on input
/// `w`. Returns `Error::NotComposable` when the codomain of `g` differs from
/// the domain of `h`, with no kernel built, then the `Error::TooLarge` of
/// building the composite.
pub fn copy_then<P: Prob>(g: &Kernel<P>, h: &Kernel<P>) -> Result<Kernel<P>> {
    g.composable(h)?;
    let x = g.codomain();
    g.compose(&Kernel::copy(x)?)?
        .compose(&Kernel::whisker_right(h, x)?)
}

/// For `f : X → Y` and `g : Y → Z`, the kernels `f ≫ copy(Y) ≫ (g ⊗ id_Y)`
/// and `copy(X) ≫ ((f ≫ g) ⊗ f)` of type `X → Z ⊗ Y`, under the errors of
/// `copy_then(f, g)`, then the `Error::TooLarge` of building the second
/// kernel.
fn sides<P: Prob>(f: &Kernel<P>, g: &Kernel<P>) -> Result<(Kernel<P>, Kernel<P>)> {
    let lhs = copy_then(f, g)?;
    let rhs = Kernel::copy(f.domain())?.compose(&f.compose(g)?.tensor(f)?)?;
    Ok((lhs, rhs))
}

/// For `f : X → Y` and `g : Y → Z`, whether `f ≫ copy(Y) ≫ (g ⊗ id_Y)` equals
/// `copy(X) ≫ ((f ≫ g) ⊗ f)` under `Kernel::approx_eq`. Returns
/// `Error::NotComposable` when the codomain of `f` differs from the domain of
/// `g`, with no kernel built, then `true` with no kernel built when the domain
/// of `f` is empty, then the `Error::TooLarge` of building either side.
pub fn copy_comp_natural<P: Prob>(f: &Kernel<P>, g: &Kernel<P>) -> Result<bool> {
    f.composable(g)?;
    if f.domain().card() == 0 {
        return Ok(true);
    }
    let (lhs, rhs) = sides(f, g)?;
    Ok(lhs.approx_eq(&rhs))
}

/// For `p : A → X`, `f : X → Y` and `g : Y → Z`, whether
/// `f ≫ copy(Y) ≫ (g ⊗ id_Y)` and `copy(X) ≫ ((f ≫ g) ⊗ f)` are `p`-almost
/// surely equal under `almost_sure::as_equal`. Returns `Error::NotComposable`
/// when the codomain of `p` differs from the domain of `f`, then when the
/// codomain of `f` differs from the domain of `g`, each with no kernel built,
/// then `true` with no kernel built when the domain of `f` is empty, then the
/// `Error::TooLarge` of building either side. Both sides are built whether or
/// not `p` reaches each input.
pub fn copy_comp_natural_as<P: Prob>(p: &Kernel<P>, f: &Kernel<P>, g: &Kernel<P>) -> Result<bool> {
    p.composable(f)?;
    f.composable(g)?;
    if f.domain().card() == 0 {
        return Ok(true);
    }
    let (lhs, rhs) = sides(f, g)?;
    as_equal(p, &lhs, &rhs)
}
