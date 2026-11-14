//! Independence of the two outputs of a kernel into a tensor product
//! (Fritz 2020, Def. 12.12, in the form of Lemma 12.11 (a)), and the composite
//! of Def. 12.16 that displays conditional independence.

use crate::error::{Error, Result};
use crate::finset::{FinObj, reserve};
use crate::kernel::Kernel;
use crate::markov::Compose;
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
/// (A ◁ W ◁ α[W, W, A]) ≫ α⁻¹[A, W, W ⊗ (W ⊗ A)] ≫ (h ⊗ (W ◁ k))`, for every
/// `g : A → W`, `h : A ⊗ W → X` and `k : W ⊗ A → Y`: the kernel from `A` to
/// `X ⊗ (W ⊗ Y)` whose weight of output `(x, w, y)` on input `a` is
/// `g(w | a) · h(x | (a, w)) · k(y | (w, a))`, multiplied in that order, with
/// the first factor major in every input and output. Returns
/// `Error::NotComposable` with codomain `A ⊗ W` and domain the domain of `h`
/// unless the factors of the domain of `h` are those of `A` followed by those
/// of `W`, then `Error::NotComposable` with codomain `W ⊗ A` and domain the
/// domain of `k` unless the factors of the domain of `k` are those of `W`
/// followed by those of `A`, or `Error::TooLarge` when a product overflows
/// `usize` or reserving a `Vec` capacity fails; no other allocation reports an
/// error.
pub fn cond_indep_form<P: Prob>(g: &Kernel<P>, h: &Kernel<P>, k: &Kernel<P>) -> Result<Kernel<P>> {
    let (a, w) = (g.domain(), g.codomain());
    let aw = a.tensor(w)?;
    if *h.domain() != aw {
        return Err(Error::NotComposable {
            codomain: aw,
            domain: h.domain().clone(),
        });
    }
    let wa = w.tensor(a)?;
    if *k.domain() != wa {
        return Err(Error::NotComposable {
            codomain: wa,
            domain: k.domain().clone(),
        });
    }
    let (x, y) = (h.codomain(), k.codomain());
    let cod = x.tensor(&w.tensor(y)?)?;
    let (na, nw, nx, ny) = (a.card(), w.card(), x.card(), y.card());
    let mut data = reserve(na, cod.card())?;
    for ia in 0..na {
        for ix in 0..nx {
            for iw in 0..nw {
                let gh = g.weight(ia, iw).mul(h.weight(ia * nw + iw, ix));
                for iy in 0..ny {
                    data.push(gh.mul(k.weight(iw * na + ia, iy)));
                }
            }
        }
    }
    Ok(Kernel::from_parts(a.clone(), cod, data))
}
