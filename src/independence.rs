//! Independence of the two outputs of a kernel into a tensor product
//! (Fritz 2020, Def. 12.12, in the form of Lemma 12.11 (a)).

use crate::error::Result;
use crate::finset::FinObj;
use crate::kernel::Kernel;
use crate::markov::{Compose, Tensor};
use crate::prob::Prob;

/// Whether `f : A → x ⊗ y` equals `copy(A)` followed by the tensor of the
/// first and second marginals of `f`, compared with `Kernel::approx_eq`, for
/// every kernel `f` and every pair of objects `x`, `y`. Returns
/// `Error::NotATensor` unless the factors of the codomain of `f` are those of
/// `x` followed by those of `y`, or `Error::TooLarge` when a product overflows
/// `usize` or reserving a `Vec` capacity fails while building either marginal
/// or the composite; no other allocation reports an error.
pub fn is_independent<P: Prob>(f: &Kernel<P>, x: &FinObj, y: &FinObj) -> Result<bool> {
    let fst = f.marginal_fst(x, y)?;
    let snd = f.marginal_snd(x, y)?;
    let rhs = Kernel::copy(f.domain())?.compose(&fst.tensor(&snd)?)?;
    Ok(f.approx_eq(&rhs))
}
