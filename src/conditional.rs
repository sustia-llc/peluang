//! Conditionals of finite kernels into a tensor product (Fritz 2020, Def. 11.5,
//! Example 11.6).

use crate::error::Result;
use crate::finset::{FinObj, reserve};
use crate::kernel::Kernel;
use crate::markov::Compose;
use crate::prob::{Prob, sum};

/// The conditional of `f : A → x ⊗ y` on `x`: the kernel `x ⊗ A → y`, inputs
/// ordered `x ⊗ A` with input `(i, a)` at index `i * A.card() + a`, whose
/// column at `(i, a)` has weight `f((i, y) | a) / s` at output `y`, where
/// `s = Σ_y' f((i, y') | a)` through `prob::sum`, and the uniform weight
/// `1 / y.card()` at every output when `s == P::zero()`. Returns
/// `Error::NotATensor` unless the codomain of `f` equals `x ⊗ y`,
/// `Error::TooLarge` when a product overflows `usize` or reserving a `Vec`
/// capacity fails, and otherwise the errors of `Kernel::new`, which builds the
/// result. `prob::sum` states the effect of a parallel run on `f64` weights.
pub fn conditional<P: Prob>(f: &Kernel<P>, x: &FinObj, y: &FinObj) -> Result<Kernel<P>> {
    f.split(x, y)?;
    let dom = x.tensor(f.domain())?;
    let (inputs, nx, ny) = (f.domain().card(), x.card(), y.card());
    let mut data = reserve(dom.card(), ny)?;
    let mut uniform: Option<P> = None;
    for i in 0..nx {
        for a in 0..inputs {
            let column = f.column(a).expect("invariant: a < dom.card() has a column");
            let terms = &column[i * ny..(i + 1) * ny];
            let mass = sum(terms);
            if mass == P::zero() {
                let weight = match &uniform {
                    Some(weight) => weight.clone(),
                    None => {
                        let mut ones = reserve(ny, 1)?;
                        ones.resize(ny, P::one());
                        let weight = P::one().div_checked(&sum(&ones)).expect(
                            "invariant: a column of f sums to one over x ⊗ y, so y is nonempty",
                        );
                        uniform = Some(weight.clone());
                        weight
                    }
                };
                data.extend(std::iter::repeat_n(weight, ny));
            } else {
                for term in terms {
                    data.push(
                        term.div_checked(&mass)
                            .expect("invariant: the divisor differs from P::zero()"),
                    );
                }
            }
        }
    }
    Kernel::new(dom, y.clone(), data)
}
