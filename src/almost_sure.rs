//! Almost-sure equality of kernels with respect to a kernel into their domain
//! (Fritz 2020, Def. 13.1, Example 13.2).

use crate::error::{Error, Result};
use crate::kernel::Kernel;
use crate::markov::Compose;
use crate::prob::Prob;

/// Whether `f` and `g` are `p`-almost surely equal: for every input `x` of `f`
/// with `p(x|a) != P::zero()` at some input `a` of `p`, each entry of the
/// column of `f` at `x` agrees with that of `g` under `Prob::approx_eq`.
/// Returns `Error::NotComposable` when the codomain of `p` differs from the
/// domain of `f`, then `Error::NotParallel` when `f` and `g` differ in domain
/// or codomain.
pub fn as_equal<P: Prob>(p: &Kernel<P>, f: &Kernel<P>, g: &Kernel<P>) -> Result<bool> {
    p.composable(f)?;
    if f.domain() != g.domain() || f.codomain() != g.codomain() {
        return Err(Error::NotParallel {
            fst: Box::new((f.domain().clone(), f.codomain().clone())),
            snd: Box::new((g.domain().clone(), g.codomain().clone())),
        });
    }
    let zero = P::zero();
    let (inputs, outputs) = (p.domain().card(), f.codomain().card());
    for x in 0..f.domain().card() {
        let supported = (0..inputs).any(|a| *p.weight(a, x) != zero);
        if supported && !(0..outputs).all(|y| f.weight(x, y).approx_eq(g.weight(x, y))) {
            return Ok(false);
        }
    }
    Ok(true)
}
