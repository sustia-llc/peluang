//! Conditionals of finite kernels into a tensor product (Fritz 2020, Def. 11.5,
//! Example 11.6).

use crate::error::{Error, Result};
use crate::finset::{FinObj, reserve};
use crate::kernel::Kernel;
use crate::markov::Compose;
use crate::prob::{Prob, sum};

/// The conditional of `f : A → x ⊗ y` on `x`: the kernel `x ⊗ A → y`, inputs
/// ordered `x ⊗ A` with input `(i, a)` at index `i * A.card() + a`, whose
/// column at `(i, a)` has weight `f((i, y) | a) / s` at output `y`, where
/// `s = Σ_y' f((i, y') | a)` through `prob::sum`, and the uniform weight
/// `1 / y.card()` at every output when `s == P::zero()`. The result is built
/// without the column tests of `Kernel::new`, so it is not tested for
/// normalization. Returns
/// `Error::NotATensor` unless the codomain of `f` equals `x ⊗ y`,
/// `Error::TooLarge` when a product overflows `usize` or reserving a `Vec`
/// capacity fails, and `Error::NoUniformWeight` when a column has
/// `s == P::zero()` and `Prob::div_checked` returns `None` on `P::one()` over
/// `P::one()` added `y.card()` times. `prob::sum` states the effect of a
/// parallel run on `f64` weights. In the `f64` lane, underflow can turn a
/// positive weight into zero, so a column with mass can count as zero-mass.
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
                let weight = uniform_weight(&mut uniform, ny)?;
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
    Ok(Kernel::from_parts(dom, y.clone(), data))
}

/// The conditional of `f : A → x ⊗ y` on `y`: the kernel `y ⊗ A → x`, inputs
/// ordered `y ⊗ A` with input `(j, a)` at index `j * A.card() + a`, whose
/// column at `(j, a)` has weight `f((i, j) | a) / s` at output `i`, where
/// `s = Σ_i' f((i', j) | a)` through `prob::sum`, and the uniform weight
/// `1 / x.card()` at every output when `s == P::zero()`. The result is built
/// without the column tests of `Kernel::new`, so it is not tested for
/// normalization. Returns `Error::NotATensor`
/// unless the codomain of `f` equals `x ⊗ y`, `Error::TooLarge` when reserving
/// a `Vec` capacity fails, and `Error::NoUniformWeight` when a column has
/// `s == P::zero()` and `Prob::div_checked` returns `None` on `P::one()` over
/// `P::one()` added `x.card()` times. `prob::sum` states the effect of a
/// parallel run on `f64` weights.
pub fn conditional_snd<P: Prob>(f: &Kernel<P>, x: &FinObj, y: &FinObj) -> Result<Kernel<P>> {
    f.split(x, y)?;
    let dom = y.tensor(f.domain())?;
    let (inputs, nx, ny) = (f.domain().card(), x.card(), y.card());
    let mut data = reserve(dom.card(), nx)?;
    let mut uniform: Option<P> = None;
    for j in 0..ny {
        for a in 0..inputs {
            let column = f.column(a).expect("invariant: a < dom.card() has a column");
            let start = data.len();
            data.extend((0..nx).map(|i| column[i * ny + j].clone()));
            let mass = sum(&data[start..]);
            if mass == P::zero() {
                let weight = uniform_weight(&mut uniform, nx)?;
                data[start..].fill(weight);
            } else {
                for term in &mut data[start..] {
                    *term = term
                        .div_checked(&mass)
                        .expect("invariant: the divisor differs from P::zero()");
                }
            }
        }
    }
    Ok(Kernel::from_parts(dom, x.clone(), data))
}

/// `P::one()` over `P::one()` added `card` times: the value in `cache` when it
/// holds one, else computed and stored there. Returns
/// `Error::NoUniformWeight` when `Prob::div_checked` returns `None` on that
/// quotient.
fn uniform_weight<P: Prob>(cache: &mut Option<P>, card: usize) -> Result<P> {
    if let Some(weight) = cache {
        return Ok(weight.clone());
    }
    let total = (0..card).fold(P::zero(), |acc, _| acc.add(&P::one()));
    let weight = P::one()
        .div_checked(&total)
        .ok_or(Error::NoUniformWeight { card })?;
    *cache = Some(weight.clone());
    Ok(weight)
}
