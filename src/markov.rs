//! Markov-category structure on `Kernel`: composition, the tensor product, the
//! structure maps of a strict symmetric monoidal category with copy and
//! discard, and marginals.

use crate::error::{Error, Result};
use crate::finset::{Factor, FinObj, product, reserve};
use crate::kernel::Kernel;
use crate::prob::{Prob, sum};

/// Morphisms with a domain and a codomain, composed in diagrammatic order.
pub trait Compose: Sized {
    /// The type of the domain and codomain.
    type Object: Eq;

    /// The domain.
    fn domain(&self) -> &Self::Object;

    /// The codomain.
    fn codomain(&self) -> &Self::Object;

    /// `self` followed by `other`; an error when `composable` fails.
    fn compose(&self, other: &Self) -> Result<Self>;

    /// `Ok` exactly when the codomain of `self` equals the domain of `other`.
    fn composable(&self, other: &Self) -> Result<()>;
}

/// Morphisms with a tensor product.
pub trait Tensor: Sized {
    /// The morphism from the tensor of the domains to the tensor of the
    /// codomains, `self` on the first factors and `other` on the second.
    fn tensor(&self, other: &Self) -> Result<Self>;
}

impl<P: Prob> Compose for Kernel<P> {
    type Object = FinObj;

    fn domain(&self) -> &FinObj {
        self.dom()
    }

    fn codomain(&self) -> &FinObj {
        self.cod()
    }

    /// The kernel with weight `Σ_y self(y|x) · other(z|y)` of output `z` on
    /// input `x`, each sum through `prob::sum`, or `Error::NotComposable` when
    /// the codomain of `self` differs from the domain of `other`, or
    /// `Error::TooLarge` when a product overflows `usize` or reserving a `Vec`
    /// capacity fails; no other allocation reports an error. `prob::sum` states
    /// the effect of a parallel run on `f64` weights.
    fn compose(&self, other: &Self) -> Result<Self> {
        self.composable(other)?;
        let (inputs, middle, outputs) = (self.dom().card(), self.cod().card(), other.cod().card());
        let mut data = reserve(inputs, outputs)?;
        let mut terms = terms_buffer(inputs, middle)?;
        for x in 0..inputs {
            for z in 0..outputs {
                terms.clear();
                terms.extend((0..middle).map(|y| self.weight(x, y).mul(other.weight(y, z))));
                data.push(sum(&terms));
            }
        }
        Ok(Self::from_parts(
            self.dom().clone(),
            other.cod().clone(),
            data,
        ))
    }

    fn composable(&self, other: &Self) -> Result<()> {
        if self.cod() == other.dom() {
            Ok(())
        } else {
            Err(Error::NotComposable {
                codomain: self.cod().clone(),
                domain: other.dom().clone(),
            })
        }
    }
}

impl<P: Prob> Tensor for Kernel<P> {
    /// The kernel with weight `self(y|x) · other(y'|x')` of output `(y, y')` on
    /// input `(x, x')`, the first factor major in input and output, or
    /// `Error::TooLarge` when a product overflows `usize` or reserving a `Vec`
    /// capacity fails; no other allocation reports an error.
    fn tensor(&self, other: &Self) -> Result<Self> {
        let dom = self.dom().tensor(other.dom())?;
        let cod = self.cod().tensor(other.cod())?;
        let mut data = reserve(dom.card(), cod.card())?;
        for x in 0..self.dom().card() {
            for x2 in 0..other.dom().card() {
                for y in 0..self.cod().card() {
                    for y2 in 0..other.cod().card() {
                        data.push(self.weight(x, y).mul(other.weight(x2, y2)));
                    }
                }
            }
        }
        Ok(Self::from_parts(dom, cod, data))
    }
}

impl<P: Prob> Kernel<P> {
    /// The identity on `x`, or `Error::TooLarge` when a product overflows
    /// `usize` or reserving a `Vec` capacity fails; no other allocation reports
    /// an error.
    pub fn identity(x: &FinObj) -> Result<Self> {
        Self::from_fn(x.clone(), x.clone(), |i| i)
    }

    /// The kernel `x → x ⊗ x` sending `i` to `(i, i)`, or `Error::TooLarge`
    /// when a product overflows `usize` or reserving a `Vec` capacity fails; no
    /// other allocation reports an error.
    pub fn copy(x: &FinObj) -> Result<Self> {
        let n = x.card();
        Self::from_fn(x.clone(), x.tensor(x)?, |i| i * n + i)
    }

    /// The kernel `x → FinObj::unit()`, or `Error::TooLarge` when reserving a
    /// `Vec` capacity fails; no other allocation reports an error.
    pub fn del(x: &FinObj) -> Result<Self> {
        Self::from_fn(x.clone(), FinObj::unit(), |_| 0)
    }

    /// The kernel `x ⊗ y → y ⊗ x` sending `(a, b)` to `(b, a)`, or
    /// `Error::TooLarge` when a product overflows `usize` or reserving a `Vec`
    /// capacity fails; no other allocation reports an error.
    pub fn swap(x: &FinObj, y: &FinObj) -> Result<Self> {
        let (nx, ny) = (x.card(), y.card());
        Self::from_fn(x.tensor(y)?, y.tensor(x)?, |i| (i % ny) * nx + i / ny)
    }

    /// The associator of `x`, `y`, `z`: the identity on `x ⊗ y ⊗ z`, or
    /// `Error::TooLarge` when a product overflows `usize` or reserving a `Vec`
    /// capacity fails; no other allocation reports an error. The error depends
    /// on nesting when an intermediate product overflows: it returns
    /// `Error::TooLarge` when `x.card() * y.card()` overflows, also when
    /// `z.card() == 0`.
    pub fn associator(x: &FinObj, y: &FinObj, z: &FinObj) -> Result<Self> {
        Self::identity(&x.tensor(y)?.tensor(z)?)
    }

    /// The left unitor of `x`: the identity on `FinObj::unit() ⊗ x`, or
    /// `Error::TooLarge` when a product overflows `usize` or reserving a `Vec`
    /// capacity fails; no other allocation reports an error.
    pub fn left_unitor(x: &FinObj) -> Result<Self> {
        Self::identity(&FinObj::unit().tensor(x)?)
    }

    /// The right unitor of `x`: the identity on `x ⊗ FinObj::unit()`, or
    /// `Error::TooLarge` when a product overflows `usize` or reserving a `Vec`
    /// capacity fails; no other allocation reports an error.
    pub fn right_unitor(x: &FinObj) -> Result<Self> {
        Self::identity(&x.tensor(&FinObj::unit())?)
    }

    /// The identity on `z` tensored with `f`, under the errors of `identity`
    /// and `Tensor::tensor`.
    pub fn whisker_left(z: &FinObj, f: &Self) -> Result<Self> {
        Self::identity(z)?.tensor(f)
    }

    /// `f` tensored with the identity on `z`, under the errors of `identity`
    /// and `Tensor::tensor`.
    pub fn whisker_right(f: &Self, z: &FinObj) -> Result<Self> {
        f.tensor(&Self::identity(z)?)
    }

    /// The first marginal of `self : dom → x ⊗ y`: each weight of `x` is the
    /// sum over `y`, through `prob::sum`. Returns `Error::NotATensor` unless
    /// the codomain equals `x ⊗ y`, or `Error::TooLarge` when reserving a `Vec`
    /// capacity fails; no other allocation reports an error. `prob::sum` states
    /// the effect of a parallel run on `f64` weights.
    pub fn marginal_fst(&self, x: &FinObj, y: &FinObj) -> Result<Self> {
        self.split(x, y)?;
        let (inputs, ny) = (self.dom().card(), y.card());
        let mut data = reserve(inputs, x.card())?;
        for a in 0..inputs {
            let column = self
                .column(a)
                .expect("invariant: a < dom.card() has a column");
            for i in 0..x.card() {
                data.push(sum(&column[i * ny..(i + 1) * ny]));
            }
        }
        Ok(Self::from_parts(self.dom().clone(), x.clone(), data))
    }

    /// The second marginal of `self : dom → x ⊗ y`: each weight of `y` is the
    /// sum over `x`, through `prob::sum`. Returns `Error::NotATensor` unless
    /// the codomain equals `x ⊗ y`, or `Error::TooLarge` when reserving a `Vec`
    /// capacity fails; no other allocation reports an error. `prob::sum` states
    /// the effect of a parallel run on `f64` weights.
    pub fn marginal_snd(&self, x: &FinObj, y: &FinObj) -> Result<Self> {
        self.split(x, y)?;
        let (inputs, nx, ny) = (self.dom().card(), x.card(), y.card());
        let mut data = reserve(inputs, ny)?;
        let mut terms = terms_buffer(inputs, nx)?;
        for a in 0..inputs {
            for j in 0..ny {
                terms.clear();
                terms.extend((0..nx).map(|i| self.weight(a, i * ny + j).clone()));
                data.push(sum(&terms));
            }
        }
        Ok(Self::from_parts(self.dom().clone(), y.clone(), data))
    }

    /// The marginal of `self : dom → cod` on the factors of `cod` at the
    /// indices `keep`, a strictly increasing list of indices into
    /// `cod.factors()`: the kernel from `dom` to the object of those factors,
    /// in that order with their labels, whose weight at each output is the sum
    /// of the weights of `self` over the elements of the other factors, in
    /// increasing order of the index in `cod`, through `prob::sum`. The empty
    /// list gives a kernel into `FinObj::unit()`, and the list of every index
    /// gives a kernel equal to `self`. Returns `Error::NotAFactorList` with
    /// `cod` and `keep` when `keep` is not strictly increasing or holds an
    /// index that is not below `cod.factors().len()`, or `Error::TooLarge`
    /// when a product of cardinalities of factors of `cod` overflows `usize`
    /// or reserving a `Vec` capacity fails; no other allocation reports an
    /// error. `prob::sum` states the effect of a parallel run on `f64`
    /// weights.
    pub fn marginal(&self, keep: &[usize]) -> Result<Self> {
        factor_list(self.cod(), keep)?;
        let factors = self.cod().factors();
        let mut cod = FinObj::unit();
        let mut cards = reserve(factors.len(), 1)?;
        let mut dropped = reserve(factors.len(), 1)?;
        for (index, factor) in factors.iter().enumerate() {
            cards.push(factor.card());
            if keep.binary_search(&index).is_ok() {
                cod = cod.tensor(&single(factor))?;
            } else {
                dropped.push(index);
            }
        }
        let kept_offsets = factor_offsets(&cards, keep)?;
        let dropped_offsets = factor_offsets(&cards, &dropped)?;
        let inputs = self.dom().card();
        let mut data = reserve(inputs, kept_offsets.len())?;
        let mut terms = terms_buffer(inputs, dropped_offsets.len())?;
        for a in 0..inputs {
            let column = self
                .column(a)
                .expect("invariant: a < dom.card() has a column");
            for &kept in &kept_offsets {
                terms.clear();
                terms.extend(
                    dropped_offsets
                        .iter()
                        .map(|&other| column[kept + other].clone()),
                );
                data.push(sum(&terms));
            }
        }
        Ok(Self::from_parts(self.dom().clone(), cod, data))
    }

    /// `Ok` exactly when the factors of the codomain are those of `x` followed
    /// by those of `y`.
    pub(crate) fn split(&self, x: &FinObj, y: &FinObj) -> Result<()> {
        let matches = self
            .cod()
            .factors()
            .split_at_checked(x.factors().len())
            .is_some_and(|(fst, snd)| fst == x.factors() && snd == y.factors());
        if matches {
            Ok(())
        } else {
            Err(Error::NotATensor {
                codomain: self.cod().clone(),
                fst: x.clone(),
                snd: y.clone(),
            })
        }
    }
}

/// `Ok` exactly when `list` is strictly increasing and each of its indices is
/// below `cod.factors().len()`; otherwise `Error::NotAFactorList` with `cod`
/// and `list`.
pub(crate) fn factor_list(cod: &FinObj, list: &[usize]) -> Result<()> {
    let increasing = list.windows(2).all(|pair| pair[0] < pair[1]);
    let in_range = list.iter().all(|&index| index < cod.factors().len());
    if increasing && in_range {
        Ok(())
    } else {
        Err(Error::NotAFactorList {
            codomain: cod.clone(),
            list: list.to_vec(),
        })
    }
}

/// For `cards` the factor cardinalities of an object and `keep` a strictly
/// increasing list of indices into `cards`: the vector with one entry for each
/// element of the object of the kept factors, in index order with the first
/// factor major, holding the index in the whole object of the element with the
/// same digits at the kept factors and digit 0 at every other factor. Returns
/// `Error::TooLarge` when a product of entries of `cards` overflows `usize` or
/// reserving a `Vec` capacity fails.
pub(crate) fn factor_offsets(cards: &[usize], keep: &[usize]) -> Result<Vec<usize>> {
    let mut strides = reserve(cards.len(), 1)?;
    let mut stride = 1_usize;
    for &card in cards.iter().rev() {
        strides.push(stride);
        stride = product(card, stride)?;
    }
    strides.reverse();
    let mut offsets = reserve(1, 1)?;
    offsets.push(0_usize);
    for &index in keep {
        let (card, stride) = (cards[index], strides[index]);
        let mut next = reserve(offsets.len(), card)?;
        for &base in &offsets {
            next.extend((0..card).map(|digit| base + digit * stride));
        }
        offsets = next;
    }
    Ok(offsets)
}

/// The object with the one factor `factor`.
fn single(factor: &Factor) -> FinObj {
    match factor.labels() {
        Some(labels) => FinObj::labeled(labels.to_vec())
            .expect("invariant: the labels of a factor of a FinObj are distinct"),
        None => FinObj::new(factor.card()),
    }
}

/// An empty vector with capacity for `terms` elements, unreserved when
/// `inputs == 0`, or `Error::TooLarge` when reserving that capacity fails.
fn terms_buffer<T>(inputs: usize, terms: usize) -> Result<Vec<T>> {
    if inputs == 0 {
        Ok(Vec::new())
    } else {
        reserve(terms, 1)
    }
}
