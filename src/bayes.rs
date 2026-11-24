//! Bayesian inverses of finite kernels (Fritz 2020, Remark 13.10,
//! equation (13.2); Cho–Jacobs, arXiv:1709.00322, equation (5), Example 3.8).

use crate::conditional::conditional;
use crate::error::{Error, Result};
use crate::finset::FinObj;
use crate::kernel::Kernel;
use crate::markov::Compose;
use crate::prob::Prob;

/// For a state `p : FinObj::unit() → X` and `f : X → Y`, the kernel `Y → X`
/// that `conditional::conditional` returns on the joint
/// `p ≫ copy(X) ≫ whisker_right(f, X) : FinObj::unit() → Y ⊗ X` with the
/// factors `(Y, X)`: the column at `y` has weight `p(x) · f(y|x) / s` at output
/// `x`, where `s = Σ_x' p(x') · f(y|x')`, and the uniform weight
/// `1 / X.card()` at every output when `s == P::zero()` (Cho–Jacobs,
/// Example 3.8). Returns `Error::NotAState` when the domain of `p` is not
/// `FinObj::unit()`, then `Error::NotComposable` when the codomain of `p`
/// differs from the domain of `f`, both with no kernel built, then
/// `Error::TooLarge` when a product overflows `usize` or reserving a `Vec`
/// capacity fails, and `Error::NoUniformWeight` when a column has
/// `s == P::zero()` and `Prob::div_checked` returns `None` on `P::one()` over
/// `P::one()` added `X.card()` times. In the `f64` lane, underflow can turn a
/// positive weight into zero, so a column with mass can count as zero-mass.
pub fn bayesian_inverse<P: Prob>(p: &Kernel<P>, f: &Kernel<P>) -> Result<Kernel<P>> {
    if *p.domain() != FinObj::unit() {
        return Err(Error::NotAState {
            domain: p.domain().clone(),
        });
    }
    p.composable(f)?;
    let (x, y) = (f.domain(), f.codomain());
    let joint = p
        .compose(&Kernel::copy(x)?)?
        .compose(&Kernel::whisker_right(f, x)?)?;
    conditional(&joint, y, x)
}

/// For `p : A → X`, `f : X → Y` and `g : Y → X`, whether
/// `p ≫ copy(X) ≫ whisker_left(X, f)` equals
/// `(p ≫ f) ≫ copy(Y) ≫ whisker_right(g, Y)` under `Kernel::approx_eq`
/// (Fritz 2020, equation (13.2)). Returns `Error::NotComposable` when the
/// codomain of `p` differs from the domain of `f`, then when the codomain of
/// `f` differs from the domain of `g`, then when the codomain of `g` differs
/// from the domain of `f`, each with no kernel built, then `Error::TooLarge`
/// when a product overflows `usize` or reserving a `Vec` capacity fails.
/// `almost_sure::as_equal` tests support with `!= P::zero()`, so in the `f64`
/// lane two kernels `g` can both pass here and fail `as_equal` with respect to
/// `p ≫ f`.
pub fn is_bayesian_inverse<P: Prob>(p: &Kernel<P>, f: &Kernel<P>, g: &Kernel<P>) -> Result<bool> {
    p.composable(f)?;
    f.composable(g)?;
    g.composable(f)?;
    let (x, y) = (f.domain(), f.codomain());
    let lhs = p
        .compose(&Kernel::copy(x)?)?
        .compose(&Kernel::whisker_left(x, f)?)?;
    let rhs = p
        .compose(f)?
        .compose(&Kernel::copy(y)?)?
        .compose(&Kernel::whisker_right(g, y)?)?;
    Ok(lhs.approx_eq(&rhs))
}
