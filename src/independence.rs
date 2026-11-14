//! Independence of the two outputs of a kernel into a tensor product
//! (Fritz 2020, Def. 12.12, in the form of Lemma 12.11 (a)), and the composite
//! of Def. 12.16 that displays conditional independence.

use crate::error::Result;
use crate::finset::FinObj;
use crate::kernel::Kernel;
use crate::markov::{Compose, Tensor};
use crate::prob::Prob;

/// Whether `f : A → x ⊗ y` equals `copy(A)` followed by the tensor of the
/// first and second marginals of `f`, for every kernel `f` and every pair of
/// objects `x`, `y`: whether `f((i, j) | a)` agrees with
/// `fst(i | a) · snd(j | a)` under `Prob::approx_eq` at every input `a` and
/// every output `(i, j)`, where `fst` and `snd` are `Kernel::marginal_fst` and
/// `Kernel::marginal_snd` of `f`. Returns `Error::NotATensor` unless the
/// factors of the codomain of `f` are those of `x` followed by those of `y`,
/// or `Error::TooLarge` when building either marginal overflows `usize` or
/// fails to reserve a `Vec` capacity; no other allocation reports an error.
pub fn is_independent<P: Prob>(f: &Kernel<P>, x: &FinObj, y: &FinObj) -> Result<bool> {
    let fst = f.marginal_fst(x, y)?;
    let snd = f.marginal_snd(x, y)?;
    let (nx, ny) = (x.card(), y.card());
    for a in 0..f.domain().card() {
        for i in 0..nx {
            for j in 0..ny {
                let product = fst.weight(a, i).mul(snd.weight(a, j));
                if !f.weight(a, i * ny + j).approx_eq(&product) {
                    return Ok(false);
                }
            }
        }
    }
    Ok(true)
}

/// The composite of Fritz 2020, Def. 12.16, `Δ[A] ≫ (A ◁ Δ[A]) ≫
/// (A ◁ (g ▷ A)) ≫ (A ◁ ((Δ[W] ≫ (W ◁ Δ[W])) ▷ A)) ≫ (A ◁ α[W, W ⊗ W, A]) ≫
/// (A ◁ W ◁ α[W, W, A]) ≫ α⁻¹[A, W, W ⊗ (W ⊗ A)] ≫ (h ⊗ (W ◁ k))`, a kernel
/// from `A` to the codomain of `h`, then `W`, then the codomain of `k`, for
/// every `g : A → W` and every pair of kernels `h`, `k`;
/// `Kernel::associator` stands for both `α` and `α⁻¹`. Returns
/// `Error::NotComposable` unless the factors of the domain of `h`, then of
/// `W`, then of the domain of `k` are those of `A ⊗ W ⊗ W ⊗ W ⊗ A`, or
/// `Error::TooLarge` when a product overflows `usize` or reserving a `Vec`
/// capacity fails; no other allocation reports an error.
pub fn cond_indep_form<P: Prob>(g: &Kernel<P>, h: &Kernel<P>, k: &Kernel<P>) -> Result<Kernel<P>> {
    let (a, w) = (g.domain(), g.codomain());
    let ww = w.tensor(w)?;
    let wa = w.tensor(a)?;
    let w_copy3 = Kernel::copy(w)?.compose(&Kernel::whisker_left(w, &Kernel::copy(w)?)?)?;
    Kernel::copy(a)?
        .compose(&Kernel::whisker_left(a, &Kernel::copy(a)?)?)?
        .compose(&Kernel::whisker_left(a, &Kernel::whisker_right(g, a)?)?)?
        .compose(&Kernel::whisker_left(
            a,
            &Kernel::whisker_right(&w_copy3, a)?,
        )?)?
        .compose(&Kernel::whisker_left(a, &Kernel::associator(w, &ww, a)?)?)?
        .compose(&Kernel::whisker_left(
            a,
            &Kernel::whisker_left(w, &Kernel::associator(w, w, a)?)?,
        )?)?
        .compose(&Kernel::associator(a, w, &w.tensor(&wa)?)?)?
        .compose(&h.tensor(&Kernel::whisker_left(w, k)?)?)
}
