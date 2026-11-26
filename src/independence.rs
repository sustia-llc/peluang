//! Independence of the two outputs of a kernel into a tensor product
//! (Fritz 2020, Def. 12.12, in the form of Lemma 12.11 (a)), the composite
//! of Def. 12.16 that displays conditional independence, and the conditional
//! independence of three lists of factors of a state as an equation between
//! products of marginals.

use crate::error::{Error, Result};
use crate::finset::{FinObj, reserve};
use crate::kernel::Kernel;
use crate::markov::{Compose, factor_list, factor_offsets};
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

/// Whether the factors `xs` and the factors `ys` of the state `psi` are
/// conditionally independent given the factors `ws`, for every kernel `psi`
/// with domain `FinObj::unit()` and every three lists of indices into the
/// factors of its codomain: with `p` the `Kernel::marginal` of `psi` on the
/// indices of the three lists, and `p(w)`, `p(x, w)`, `p(w, y)` the
/// `Kernel::marginal` of `p` on the factors of `ws`, of `xs` and `ws`, and of
/// `ws` and `ys`, whether `p(x, w, y) · p(w)` agrees with
/// `p(x, w) · p(w, y)` under `Prob::approx_eq` at every element `x` of the
/// factors `xs`, `w` of the factors `ws` and `y` of the factors `ys`. A factor
/// in no list is summed out, and the function divides no weight. Returns
/// `Error::NotAState` unless the domain of `psi` is `FinObj::unit()`, then
/// `Error::NotAFactorList` with the codomain of `psi` and the first of `xs`,
/// `ws`, `ys` that is not strictly increasing or holds an index that is not
/// below the number of factors of that codomain, then `Error::NotAFactorList`
/// with that codomain and the second list of the first of the pairs
/// `(xs, ws)`, `(xs, ys)`, `(ws, ys)` that share an index, or
/// `Error::TooLarge` when a product of cardinalities of factors of that
/// codomain overflows `usize` or reserving a `Vec` capacity fails; no other
/// allocation reports an error. `prob::sum` states the effect of a parallel
/// run on `f64` weights.
pub fn is_cond_independent_state<P: Prob>(
    psi: &Kernel<P>,
    xs: &[usize],
    ws: &[usize],
    ys: &[usize],
) -> Result<bool> {
    if *psi.domain() != FinObj::unit() {
        return Err(Error::NotAState {
            domain: psi.domain().clone(),
        });
    }
    let cod = psi.codomain();
    for list in [xs, ws, ys] {
        factor_list(cod, list)?;
    }
    for (fst, snd) in [(xs, ws), (xs, ys), (ws, ys)] {
        if fst.iter().any(|index| snd.binary_search(index).is_ok()) {
            return Err(Error::NotAFactorList {
                codomain: cod.clone(),
                list: snd.to_vec(),
            });
        }
    }
    let union = merged(&[xs, ws, ys])?;
    let xw = merged(&[xs, ws])?;
    let wy = merged(&[ws, ys])?;
    let p = psi.marginal(&union)?;
    let p_w = p.marginal(&positions(ws, &union)?)?;
    let p_xw = p.marginal(&positions(&xw, &union)?)?;
    let p_wy = p.marginal(&positions(&wy, &union)?)?;
    let (x_in_p, w_in_p, y_in_p) = (
        offsets(cod, xs, &union)?,
        offsets(cod, ws, &union)?,
        offsets(cod, ys, &union)?,
    );
    let (x_in_xw, w_in_xw) = (offsets(cod, xs, &xw)?, offsets(cod, ws, &xw)?);
    let (w_in_wy, y_in_wy) = (offsets(cod, ws, &wy)?, offsets(cod, ys, &wy)?);
    for (ix, x) in x_in_p.iter().enumerate() {
        for (iw, w) in w_in_p.iter().enumerate() {
            let xw_weight = p_xw.weight(0, x_in_xw[ix] + w_in_xw[iw]);
            let w_weight = p_w.weight(0, iw);
            for (iy, y) in y_in_p.iter().enumerate() {
                let lhs = p.weight(0, x + w + y).mul(w_weight);
                let rhs = xw_weight.mul(p_wy.weight(0, w_in_wy[iw] + y_in_wy[iy]));
                if !lhs.approx_eq(&rhs) {
                    return Ok(false);
                }
            }
        }
    }
    Ok(true)
}

/// The indices of `lists` in increasing order, for strictly increasing lists
/// with no shared index, or `Error::TooLarge` when reserving a `Vec` capacity
/// fails.
fn merged(lists: &[&[usize]]) -> Result<Vec<usize>> {
    let mut out = reserve(lists.iter().map(|list| list.len()).sum(), 1)?;
    for list in lists {
        out.extend_from_slice(list);
    }
    out.sort_unstable();
    Ok(out)
}

/// The position in `of` of each index of `sub`, for strictly increasing lists
/// with every index of `sub` in `of`, or `Error::TooLarge` when reserving a
/// `Vec` capacity fails.
fn positions(sub: &[usize], of: &[usize]) -> Result<Vec<usize>> {
    let mut out = reserve(sub.len(), 1)?;
    out.extend(sub.iter().map(|index| {
        of.binary_search(index)
            .expect("invariant: every index of sub is in of")
    }));
    Ok(out)
}

/// `markov::factor_offsets` of the factors `sub` inside the object of the
/// factors `of` of `cod`, for strictly increasing lists of indices into
/// `cod.factors()` with every index of `sub` in `of`, under the errors of
/// `markov::factor_offsets`.
fn offsets(cod: &FinObj, sub: &[usize], of: &[usize]) -> Result<Vec<usize>> {
    let mut cards = reserve(of.len(), 1)?;
    cards.extend(of.iter().map(|&index| cod.factors()[index].card()));
    factor_offsets(&cards, &positions(sub, of)?)
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
