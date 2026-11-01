//! Generated tests of the Markov-category laws on `Kernel`, on objects of
//! cardinality 1 to 4 and kernels whose columns are positive integers from 1 to
//! 9 over their sum: on `Exact` weights under `==` in every feature lane, on
//! `f64` weights under `Kernel::approx_eq` under `f64-prob`.

use std::ops::RangeInclusive;

use peluang::error::Result;
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::{Compose, Tensor};
use peluang::prob::{Exact, Prob};
use proptest::collection::vec;
use proptest::prelude::*;

/// What a law body needs from a weight type: the weight `n / d` and the
/// equality of kernels of the lane.
struct Lane<P> {
    weight: fn(u32, u32) -> P,
    same: fn(&Kernel<P>, &Kernel<P>) -> bool,
}

const EXACT: Lane<Exact> = Lane {
    weight: |n, d| Exact::new(n.into(), d.into()),
    same: |a, b| a == b,
};

#[cfg(feature = "f64-prob")]
const FLOAT: Lane<f64> = Lane {
    weight: |n, d| f64::from(n) / f64::from(d),
    same: Kernel::approx_eq,
};

/// A kernel `FinObj::new(dom) → FinObj::new(cod)` as integers, one vector per
/// input.
#[derive(Clone, Debug)]
struct Draw {
    dom: usize,
    cod: usize,
    columns: Vec<Vec<u32>>,
}

impl Draw {
    /// The kernel with each column divided by its sum.
    fn kernel<P: Prob>(&self, lane: &Lane<P>) -> Result<Kernel<P>> {
        let data = self
            .columns
            .iter()
            .flat_map(|column| {
                let total: u32 = column.iter().sum();
                column.iter().map(move |&n| (lane.weight)(n, total))
            })
            .collect();
        Kernel::new(FinObj::new(self.dom), FinObj::new(self.cod), data)
    }
}

fn card() -> RangeInclusive<usize> {
    1..=4
}

fn draw(dom: usize, cod: usize) -> impl Strategy<Value = Draw> {
    vec(vec(1_u32..=9, cod), dom).prop_map(move |columns| Draw { dom, cod, columns })
}

fn morphism() -> impl Strategy<Value = Draw> {
    (card(), card()).prop_flat_map(|(dom, cod)| draw(dom, cod))
}

fn composable_pair() -> impl Strategy<Value = (Draw, Draw)> {
    (card(), card(), card()).prop_flat_map(|(a, b, c)| (draw(a, b), draw(b, c)))
}

fn composable_triple() -> impl Strategy<Value = (Draw, Draw, Draw)> {
    (card(), card(), card(), card())
        .prop_flat_map(|(a, b, c, d)| (draw(a, b), draw(b, c), draw(c, d)))
}

/// Fails the case unless `observed` equals `expected` in the lane.
fn check<P: Prob>(
    lane: &Lane<P>,
    law: &str,
    observed: &Kernel<P>,
    expected: &Kernel<P>,
) -> std::result::Result<(), TestCaseError> {
    prop_assert!(
        (lane.same)(observed, expected),
        "{law}: expected {expected:?}, observed {observed:?}"
    );
    Ok(())
}

type Outcome = std::result::Result<(), TestCaseError>;

fn identity_law<P: Prob>(lane: &Lane<P>, f: &Draw) -> Outcome {
    let f = f.kernel(lane)?;
    let left = Kernel::identity(f.domain())?.compose(&f)?;
    let right = f.compose(&Kernel::identity(f.codomain())?)?;
    check(lane, "𝟙 X ≫ f = f", &left, &f)?;
    check(lane, "f ≫ 𝟙 Y = f", &right, &f)
}

fn associativity_law<P: Prob>(lane: &Lane<P>, (f, g, h): &(Draw, Draw, Draw)) -> Outcome {
    let (f, g, h) = (f.kernel(lane)?, g.kernel(lane)?, h.kernel(lane)?);
    let left = f.compose(&g)?.compose(&h)?;
    let right = f.compose(&g.compose(&h)?)?;
    check(lane, "(f ≫ g) ≫ h = f ≫ (g ≫ h)", &left, &right)
}

fn interchange_law<P: Prob>(
    lane: &Lane<P>,
    (f, h): &(Draw, Draw),
    (g, k): &(Draw, Draw),
) -> Outcome {
    let (f, g) = (f.kernel(lane)?, g.kernel(lane)?);
    let (h, k) = (h.kernel(lane)?, k.kernel(lane)?);
    let left = f.tensor(&g)?.compose(&h.tensor(&k)?)?;
    let right = f.compose(&h)?.tensor(&g.compose(&k)?)?;
    check(
        lane,
        "(f ⊗ₘ g) ≫ (h ⊗ₘ k) = (f ≫ h) ⊗ₘ (g ≫ k)",
        &left,
        &right,
    )
}

fn swap_natural_law<P: Prob>(lane: &Lane<P>, f: &Draw, g: &Draw) -> Outcome {
    let (f, g) = (f.kernel(lane)?, g.kernel(lane)?);
    let left = f
        .tensor(&g)?
        .compose(&Kernel::swap(f.codomain(), g.codomain())?)?;
    let right = Kernel::swap(f.domain(), g.domain())?.compose(&g.tensor(&f)?)?;
    check(lane, "(f ⊗ₘ g) ≫ β_ = β_ ≫ (g ⊗ₘ f)", &left, &right)
}

fn copy_coassociative_law<P: Prob>(lane: &Lane<P>, x: usize) -> Outcome {
    let x = FinObj::new(x);
    let copy = Kernel::<P>::copy(&x)?;
    let id = Kernel::identity(&x)?;
    let left = copy
        .compose(&copy.tensor(&id)?)?
        .compose(&Kernel::associator(&x, &x, &x)?)?;
    let right = copy.compose(&id.tensor(&copy)?)?;
    check(lane, "Δ ≫ (Δ ▷ X) ≫ α_ = Δ ≫ (X ◁ Δ)", &left, &right)
}

fn copy_cocommutative_law<P: Prob>(lane: &Lane<P>, x: usize) -> Outcome {
    let x = FinObj::new(x);
    let copy = Kernel::<P>::copy(&x)?;
    let swapped = copy.compose(&Kernel::swap(&x, &x)?)?;
    check(lane, "Δ ≫ β_ = Δ", &swapped, &copy)
}

fn counit_law<P: Prob>(lane: &Lane<P>, x: usize) -> Outcome {
    let x = FinObj::new(x);
    let (copy, del) = (Kernel::<P>::copy(&x)?, Kernel::<P>::del(&x)?);
    let id = Kernel::identity(&x)?;
    let left = copy
        .compose(&del.tensor(&id)?)?
        .compose(&Kernel::left_unitor(&x)?)?;
    let right = copy
        .compose(&id.tensor(&del)?)?
        .compose(&Kernel::right_unitor(&x)?)?;
    check(lane, "Δ ≫ (ε ▷ X) ≫ λ_ = 𝟙 X", &left, &id)?;
    check(lane, "Δ ≫ (X ◁ ε) ≫ ρ_ = 𝟙 X", &right, &id)
}

fn copy_tensor_law<P: Prob>(lane: &Lane<P>, x: usize, y: usize) -> Outcome {
    let (x, y) = (FinObj::new(x), FinObj::new(y));
    let tensor_mu = Kernel::identity(&x)?
        .tensor(&Kernel::swap(&x, &y)?)?
        .tensor(&Kernel::identity(&y)?)?;
    let right = Kernel::<P>::copy(&x)?
        .tensor(&Kernel::copy(&y)?)?
        .compose(&tensor_mu)?;
    let left = Kernel::copy(&x.tensor(&y)?)?;
    check(lane, "Δ[X ⊗ Y] = (Δ[X] ⊗ₘ Δ[Y]) ≫ tensorμ", &left, &right)
}

fn discard_tensor_law<P: Prob>(lane: &Lane<P>, x: usize, y: usize) -> Outcome {
    let (x, y) = (FinObj::new(x), FinObj::new(y));
    let right = Kernel::<P>::del(&x)?
        .tensor(&Kernel::del(&y)?)?
        .compose(&Kernel::left_unitor(&FinObj::unit())?)?;
    let left = Kernel::del(&x.tensor(&y)?)?;
    check(lane, "ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ λ_ I", &left, &right)
}

fn discard_natural_law<P: Prob>(lane: &Lane<P>, f: &Draw) -> Outcome {
    let f = f.kernel(lane)?;
    let left = f.compose(&Kernel::del(f.codomain())?)?;
    let right = Kernel::del(f.domain())?;
    check(lane, "f ≫ ε[Y] = ε[X]", &left, &right)
}

/// The module `$module` with one generated test per law, in lane `$lane`.
macro_rules! law_tests {
    ($module:ident, $lane:expr) => {
        mod $module {
            use super::*;

            proptest! {
                #[test]
                fn identity(f in morphism()) {
                    identity_law(&$lane, &f)?;
                }

                #[test]
                fn associativity(triple in composable_triple()) {
                    associativity_law(&$lane, &triple)?;
                }

                #[test]
                fn interchange(first in composable_pair(), second in composable_pair()) {
                    interchange_law(&$lane, &first, &second)?;
                }

                #[test]
                fn swap_natural(f in morphism(), g in morphism()) {
                    swap_natural_law(&$lane, &f, &g)?;
                }

                #[test]
                fn copy_coassociative(x in card()) {
                    copy_coassociative_law(&$lane, x)?;
                }

                #[test]
                fn copy_cocommutative(x in card()) {
                    copy_cocommutative_law(&$lane, x)?;
                }

                #[test]
                fn counit(x in card()) {
                    counit_law(&$lane, x)?;
                }

                #[test]
                fn copy_tensor(x in card(), y in card()) {
                    copy_tensor_law(&$lane, x, y)?;
                }

                #[test]
                fn discard_tensor(x in card(), y in card()) {
                    discard_tensor_law(&$lane, x, y)?;
                }

                #[test]
                fn discard_natural(f in morphism()) {
                    discard_natural_law(&$lane, &f)?;
                }
            }
        }
    };
}

law_tests!(exact, EXACT);

#[cfg(feature = "f64-prob")]
law_tests!(float, FLOAT);
