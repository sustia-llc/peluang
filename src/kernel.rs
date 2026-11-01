//! Finite stochastic kernels: dense column-stochastic matrices of `Prob`
//! weights between `FinObj`s.

use crate::error::{Error, Result};
use crate::finset::{FinObj, product, reserve};
use crate::prob::Prob;

/// A stochastic kernel `dom → cod`. Entry `x * cod.card() + y` of the data is
/// the weight of output `y` on input `x`, so each input's distribution is one
/// contiguous column.
#[derive(Clone, Debug, PartialEq)]
pub struct Kernel<P> {
    dom: FinObj,
    cod: FinObj,
    data: Vec<P>,
}

impl<P: Prob> Kernel<P> {
    /// The kernel `dom → cod` with columns taken from `data`, or the first
    /// failure of these tests in this order: `Error::TooLarge` when
    /// `dom.card() * cod.card()` overflows `usize`, `Error::DataLength` when
    /// `data` does not have that length, `Error::NegativeWeight` at the first
    /// entry failing `Prob::is_nonneg`, `Error::NotNormalized` at the first
    /// column failing `Prob::is_normalized`. `Kernel::state` runs these tests
    /// through this function. No other constructor runs them, and in the `f64`
    /// lane a composite can drift past `F64_TOLERANCE`.
    pub fn new(dom: FinObj, cod: FinObj, data: Vec<P>) -> Result<Self> {
        let width = cod.card();
        let expected = product(dom.card(), width)?;
        if data.len() != expected {
            return Err(Error::DataLength {
                expected,
                found: data.len(),
            });
        }
        if let Some(index) = data.iter().position(|weight| !weight.is_nonneg()) {
            return Err(Error::NegativeWeight {
                input: index / width,
                output: index % width,
            });
        }
        for input in 0..dom.card() {
            let start = input * width;
            let column = &data[start..start + width];
            if !P::is_normalized(column.iter().cloned()) {
                return Err(Error::NotNormalized { input });
            }
        }
        Ok(Self { dom, cod, data })
    }

    /// The kernel `FinObj::unit() → cod` with the single column `weights`,
    /// under the tests and errors of `Kernel::new`.
    pub fn state(cod: FinObj, weights: Vec<P>) -> Result<Self> {
        Self::new(FinObj::unit(), cod, weights)
    }

    /// The deterministic kernel sending each input `x` of `dom` to output
    /// `f(x)`, or `Error::NotAFunction` at the first input with
    /// `f(x) >= cod.card()`, or `Error::TooLarge` when `dom.card() * cod.card()`
    /// overflows `usize` or reserving a `Vec` capacity fails; no other
    /// allocation reports an error.
    pub fn from_fn(dom: FinObj, cod: FinObj, f: impl Fn(usize) -> usize) -> Result<Self> {
        let width = cod.card();
        let len = product(dom.card(), width)?;
        let mut data = reserve(dom.card(), width)?;
        data.resize(len, P::zero());
        for input in 0..dom.card() {
            let output = f(input);
            if output >= width {
                return Err(Error::NotAFunction { input, output });
            }
            data[input * width + output] = P::one();
        }
        Ok(Self { dom, cod, data })
    }

    /// The distribution of input `x`, `None` when `x >= dom.card()`.
    pub fn column(&self, x: usize) -> Option<&[P]> {
        if x >= self.dom.card() {
            return None;
        }
        let width = self.cod.card();
        let start = x * width;
        self.data.get(start..start + width)
    }

    /// Whether `other` has the same domain and codomain and each entry agrees
    /// under `Prob::approx_eq`.
    pub fn approx_eq(&self, other: &Self) -> bool {
        self.dom == other.dom
            && self.cod == other.cod
            && self
                .data
                .iter()
                .zip(&other.data)
                .all(|(a, b)| a.approx_eq(b))
    }

    /// The kernel with exactly these fields, under no test.
    pub(crate) fn from_parts(dom: FinObj, cod: FinObj, data: Vec<P>) -> Self {
        Self { dom, cod, data }
    }

    /// The domain.
    pub(crate) fn dom(&self) -> &FinObj {
        &self.dom
    }

    /// The codomain.
    pub(crate) fn cod(&self) -> &FinObj {
        &self.cod
    }

    /// The weight of output `y` on input `x`, for `x < dom.card()` and
    /// `y < cod.card()`.
    pub(crate) fn weight(&self, x: usize, y: usize) -> &P {
        &self.data[x * self.cod.card() + y]
    }
}
