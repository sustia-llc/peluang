//! Markov-category structure on `Kernel`: composition, the tensor product, the
//! structure maps of a strict symmetric monoidal category with copy and
//! discard, and marginals.

use crate::error::{Error, Result};
use crate::finset::{FinObj, reserve};
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
    /// `Error::TooLarge` when the result cannot be allocated.
    fn compose(&self, other: &Self) -> Result<Self> {
        self.composable(other)?;
        let (inputs, middle, outputs) = (self.dom().card(), self.cod().card(), other.cod().card());
        let mut data = reserve(inputs, outputs)?;
        let mut terms = reserve(middle, 1)?;
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
    /// `Error::TooLarge` when a product overflows `usize` or the result cannot
    /// be allocated.
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
    /// The identity on `x`, or `Error::TooLarge` when it cannot be allocated.
    pub fn identity(x: &FinObj) -> Result<Self> {
        Self::from_fn(x.clone(), x.clone(), |i| i)
    }

    /// The kernel `x → x ⊗ x` sending `i` to `(i, i)`, or `Error::TooLarge`
    /// when a product overflows `usize` or it cannot be allocated.
    pub fn copy(x: &FinObj) -> Result<Self> {
        let n = x.card();
        Self::from_fn(x.clone(), x.tensor(x)?, |i| i * n + i)
    }

    /// The kernel `x → FinObj::unit()`, or `Error::TooLarge` when it cannot be
    /// allocated.
    pub fn del(x: &FinObj) -> Result<Self> {
        Self::from_fn(x.clone(), FinObj::unit(), |_| 0)
    }

    /// The kernel `x ⊗ y → y ⊗ x` sending `(a, b)` to `(b, a)`, or
    /// `Error::TooLarge` when a product overflows `usize` or it cannot be
    /// allocated.
    pub fn swap(x: &FinObj, y: &FinObj) -> Result<Self> {
        let (nx, ny) = (x.card(), y.card());
        Self::from_fn(x.tensor(y)?, y.tensor(x)?, |i| (i % ny) * nx + i / ny)
    }

    /// The associator of `x`, `y`, `z`: the identity on `x ⊗ y ⊗ z`, or
    /// `Error::TooLarge` when a product overflows `usize` or it cannot be
    /// allocated.
    pub fn associator(x: &FinObj, y: &FinObj, z: &FinObj) -> Result<Self> {
        Self::identity(&x.tensor(y)?.tensor(z)?)
    }

    /// The left unitor of `x`: the identity on `FinObj::unit() ⊗ x`, or
    /// `Error::TooLarge` when it cannot be allocated.
    pub fn left_unitor(x: &FinObj) -> Result<Self> {
        Self::identity(&FinObj::unit().tensor(x)?)
    }

    /// The right unitor of `x`: the identity on `x ⊗ FinObj::unit()`, or
    /// `Error::TooLarge` when it cannot be allocated.
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
    /// the codomain equals `x ⊗ y`, or `Error::TooLarge` when the result cannot
    /// be allocated.
    pub fn marginal_fst(&self, x: &FinObj, y: &FinObj) -> Result<Self> {
        self.split(x, y)?;
        let ny = y.card();
        self.marginal(x, ny, |i, j| i * ny + j)
    }

    /// The second marginal of `self : dom → x ⊗ y`: each weight of `y` is the
    /// sum over `x`, through `prob::sum`. Returns `Error::NotATensor` unless
    /// the codomain equals `x ⊗ y`, or `Error::TooLarge` when the result cannot
    /// be allocated.
    pub fn marginal_snd(&self, x: &FinObj, y: &FinObj) -> Result<Self> {
        self.split(x, y)?;
        let ny = y.card();
        self.marginal(y, x.card(), |j, i| i * ny + j)
    }

    /// `Ok` exactly when the factors of the codomain are those of `x` followed
    /// by those of `y`.
    fn split(&self, x: &FinObj, y: &FinObj) -> Result<()> {
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

    /// The kernel `dom → kept` whose weight of `k` on input `a` is the sum, over
    /// `s < summed`, of the weight of output `index(k, s)` on `a`.
    fn marginal(
        &self,
        kept: &FinObj,
        summed: usize,
        index: impl Fn(usize, usize) -> usize,
    ) -> Result<Self> {
        let inputs = self.dom().card();
        let mut data = reserve(inputs, kept.card())?;
        let mut terms = reserve(summed, 1)?;
        for a in 0..inputs {
            for k in 0..kept.card() {
                terms.clear();
                terms.extend((0..summed).map(|s| self.weight(a, index(k, s)).clone()));
                data.push(sum(&terms));
            }
        }
        Ok(Self::from_parts(self.dom().clone(), kept.clone(), data))
    }
}
