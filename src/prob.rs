//! Probability-weight types: the `Prob` trait, its exact rational
//! implementation, the optional `f64` implementation, and a runtime law
//! verifier.

use crate::error::{Error, Result};

/// Absolute tolerance used by `Prob::approx_eq` on `f64` weights.
#[cfg(feature = "f64-prob")]
pub const F64_TOLERANCE: f64 = 1e-12;

/// A commutative semiring of probability weights with checked division and
/// an equality relation used by every law check and normalization test.
pub trait Prob: Clone + PartialEq + core::fmt::Debug + Send + Sync {
    /// Additive identity.
    fn zero() -> Self;

    /// Multiplicative identity.
    fn one() -> Self;

    /// Sum of two weights.
    fn add(&self, other: &Self) -> Self;

    /// Product of two weights.
    fn mul(&self, other: &Self) -> Self;

    /// Quotient `self / other`, `None` exactly when `other == Self::zero()`.
    fn div_checked(&self, other: &Self) -> Option<Self>;

    /// Whether the weight is at least `Self::zero()`.
    fn is_nonneg(&self) -> bool;

    /// Equality up to the type's declared tolerance: exact for rationals,
    /// within `F64_TOLERANCE` for `f64`.
    fn approx_eq(&self, other: &Self) -> bool;

    /// Whether the weights in `terms` sum to `Self::one()` under `approx_eq`;
    /// an empty iterator sums to `Self::zero()`.
    fn is_normalized<I: IntoIterator<Item = Self>>(terms: I) -> bool {
        let total = terms
            .into_iter()
            .fold(Self::zero(), |acc, term| acc.add(&term));
        total.approx_eq(&Self::one())
    }
}

/// Exact rational weights with arbitrary-precision numerator and denominator.
pub type Exact = num_rational::Ratio<num_bigint::BigInt>;

impl Prob for Exact {
    fn zero() -> Self {
        <Self as num_traits::Zero>::zero()
    }

    fn one() -> Self {
        <Self as num_traits::One>::one()
    }

    fn add(&self, other: &Self) -> Self {
        self + other
    }

    fn mul(&self, other: &Self) -> Self {
        self * other
    }

    fn div_checked(&self, other: &Self) -> Option<Self> {
        if num_traits::Zero::is_zero(other) {
            None
        } else {
            Some(self / other)
        }
    }

    fn is_nonneg(&self) -> bool {
        !num_traits::Signed::is_negative(self)
    }

    fn approx_eq(&self, other: &Self) -> bool {
        self == other
    }
}

#[cfg(feature = "f64-prob")]
impl Prob for f64 {
    fn zero() -> Self {
        0.0
    }

    fn one() -> Self {
        1.0
    }

    fn add(&self, other: &Self) -> Self {
        self + other
    }

    fn mul(&self, other: &Self) -> Self {
        self * other
    }

    fn div_checked(&self, other: &Self) -> Option<Self> {
        if *other == 0.0 {
            None
        } else {
            Some(self / other)
        }
    }

    fn is_nonneg(&self) -> bool {
        *self >= 0.0
    }

    fn approx_eq(&self, other: &Self) -> bool {
        (self - other).abs() <= F64_TOLERANCE
    }
}

/// Tuning constant: the slice length at or above which `sum` runs in
/// parallel under the `parallel` feature.
pub const PAR_THRESHOLD: usize = 1024;

/// Sum of `terms` under `Prob::add`, `Self::zero()` on an empty slice; under
/// the `parallel` feature, parallel exactly when `terms.len()` is at least
/// `PAR_THRESHOLD`. A parallel run uses the rayon pool of the calling thread:
/// the `exec::Executor` pool inside `Executor::run`, the global pool on a
/// thread outside any rayon pool. On that thread, the last combining `add`
/// runs on the calling thread.
pub fn sum<P: Prob>(terms: &[P]) -> P {
    #[cfg(feature = "parallel")]
    {
        sum_with(terms, terms.len() >= PAR_THRESHOLD)
    }
    #[cfg(not(feature = "parallel"))]
    {
        terms.iter().fold(P::zero(), |acc, term| acc.add(term))
    }
}

/// Sum of `terms` under `Prob::add`, `Self::zero()` on an empty slice,
/// computed by a rayon reduction when `parallel` is true and by a sequential
/// fold otherwise. The rayon reduction uses the rayon pool of the calling
/// thread: the `exec::Executor` pool inside `Executor::run`, the global pool
/// on a thread outside any rayon pool. On that thread, the last combining
/// `add` runs on the calling thread.
#[cfg(feature = "parallel")]
pub fn sum_with<P: Prob>(terms: &[P], parallel: bool) -> P {
    rayon_cond::CondIterator::new(terms, parallel)
        .fold(P::zero, |acc, term| acc.add(term))
        .reduce(P::zero, |a, b| a.add(&b))
}

/// Checks the commutative-semiring laws and checked division on the sample
/// triple `(a, b, c)`, every comparison under `approx_eq`, returning the first
/// violated law as `Error::AxiomViolation` with `law` one of `add_assoc`,
/// `add_comm`, `add_zero`, `mul_assoc`, `mul_one`, `one_mul`, `left_distrib`,
/// `right_distrib`, `zero_absorbs`, `div_mul`, in that order.
pub fn verify_prob_axioms<P: Prob>(a: &P, b: &P, c: &P) -> Result<()> {
    let zero = P::zero();
    let one = P::one();

    let check = |holds: bool, law: &'static str| -> Result<()> {
        if holds {
            Ok(())
        } else {
            Err(Error::AxiomViolation { law })
        }
    };

    check(a.add(b).add(c).approx_eq(&a.add(&b.add(c))), "add_assoc")?;
    check(a.add(b).approx_eq(&b.add(a)), "add_comm")?;
    check(a.add(&zero).approx_eq(a), "add_zero")?;
    check(a.mul(b).mul(c).approx_eq(&a.mul(&b.mul(c))), "mul_assoc")?;
    check(a.mul(&one).approx_eq(a), "mul_one")?;
    check(one.mul(a).approx_eq(a), "one_mul")?;
    check(
        a.mul(&b.add(c)).approx_eq(&a.mul(b).add(&a.mul(c))),
        "left_distrib",
    )?;
    check(
        a.add(b).mul(c).approx_eq(&a.mul(c).add(&b.mul(c))),
        "right_distrib",
    )?;
    check(
        a.mul(&zero).approx_eq(&zero) && zero.mul(a).approx_eq(&zero),
        "zero_absorbs",
    )?;

    for x in [a, b, c] {
        if x.approx_eq(&zero) {
            continue;
        }
        let divides = match a.div_checked(x) {
            Some(q) => q.mul(x).approx_eq(a),
            None => false,
        };
        check(divides, "div_mul")?;
    }
    check(a.div_checked(&zero).is_none(), "div_mul")?;

    Ok(())
}
