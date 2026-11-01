//! Tests on `Kernel` of identity, associativity, interchange, naturality of
//! `swap`, `associator`, `left_unitor`, `right_unitor` and `del`,
//! coassociativity and cocommutativity of `copy`, the counit laws, `copy_tensor`
//! and `discard_tensor`, on objects of cardinality 0 to `CARD_MAX`. The laws on
//! kernels are generated: each column is integers from 0 to 9, not all zero,
//! over their sum, a cardinality is 0 at weight 1 in 10, and a codomain has
//! cardinality 0 only over a domain of cardinality 0. The five laws with no
//! kernel loop over each cardinality and each pair. Laws run on `Exact` weights
//! under `==` in every feature lane, on `f64` weights under `Kernel::approx_eq`
//! under `f64-prob`. The `parallel` and `async` lanes run the sequential branch
//! of `prob::sum`: the largest middle of a composite in this file is
//! `CARD_MAX.pow(4)`, in `copy_tensor`, and a const assertion holds it below
//! `PAR_THRESHOLD`.

use peluang::error::Result;
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::{Compose, Tensor};
use peluang::prob::{Exact, Prob};
use proptest::collection::vec;
use proptest::prelude::*;
use proptest::test_runner::TestCaseResult;

/// The largest cardinality of an object.
const CARD_MAX: usize = 4;

const _: () = assert!(CARD_MAX.pow(4) < peluang::prob::PAR_THRESHOLD);

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

/// A cardinality from 0 to `CARD_MAX`, 0 at weight 1 in 10.
fn card() -> impl Strategy<Value = usize> {
    prop_oneof![1 => Just(0), 9 => 1..=CARD_MAX]
}

/// The cardinalities of a codomain over a domain of cardinality `dom`: a
/// kernel from a nonempty domain to an empty codomain does not exist.
fn card_after(dom: usize) -> BoxedStrategy<usize> {
    if dom == 0 {
        card().boxed()
    } else {
        (1..=CARD_MAX).boxed()
    }
}

/// A column of `cod > 0` integers from 0 to 9, with one entry at least 1.
fn column(cod: usize) -> impl Strategy<Value = Vec<u32>> {
    (vec(0_u32..=9, cod), 0..cod, 1_u32..=9).prop_map(|(mut column, index, entry)| {
        column[index] = entry;
        column
    })
}

/// `dom` columns of `column(cod)`; the empty draw when `dom == 0`.
fn draw(dom: usize, cod: usize) -> BoxedStrategy<Draw> {
    if dom == 0 {
        Just(Draw {
            dom,
            cod,
            columns: Vec::new(),
        })
        .boxed()
    } else {
        vec(column(cod), dom)
            .prop_map(move |columns| Draw { dom, cod, columns })
            .boxed()
    }
}

fn morphism() -> impl Strategy<Value = Draw> {
    card().prop_flat_map(|dom| card_after(dom).prop_flat_map(move |cod| draw(dom, cod)))
}

/// Each object is drawn from `card_after` of the one before it, so each draw
/// has codomain 0 only over domain 0 and shares its middle object.
fn composable_pair() -> impl Strategy<Value = (Draw, Draw)> {
    card().prop_flat_map(|a| {
        card_after(a)
            .prop_flat_map(move |b| card_after(b).prop_flat_map(move |c| (draw(a, b), draw(b, c))))
    })
}

/// Each object is drawn from `card_after` of the one before it, as in
/// `composable_pair`.
fn composable_triple() -> impl Strategy<Value = (Draw, Draw, Draw)> {
    card().prop_flat_map(|a| {
        card_after(a).prop_flat_map(move |b| {
            card_after(b).prop_flat_map(move |c| {
                card_after(c).prop_flat_map(move |d| (draw(a, b), draw(b, c), draw(c, d)))
            })
        })
    })
}

/// Panics naming the cardinality at the first `x` up to `CARD_MAX` where `law`
/// fails.
fn at_each_card(law: impl Fn(usize) -> TestCaseResult) {
    for x in 0..=CARD_MAX {
        if let Err(failure) = law(x) {
            panic!("cardinality {x}: {failure}");
        }
    }
}

/// Panics naming the cardinalities at the first pair up to `CARD_MAX` where
/// `law` fails.
fn at_each_card_pair(law: impl Fn(usize, usize) -> TestCaseResult) {
    for x in 0..=CARD_MAX {
        for y in 0..=CARD_MAX {
            if let Err(failure) = law(x, y) {
                panic!("cardinalities {x}, {y}: {failure}");
            }
        }
    }
}

/// Fails the case unless `observed` equals `expected` in the lane.
fn check<P: Prob>(
    lane: &Lane<P>,
    law: &str,
    observed: &Kernel<P>,
    expected: &Kernel<P>,
) -> TestCaseResult {
    prop_assert!(
        (lane.same)(observed, expected),
        "{law}: expected {expected:?}, observed {observed:?}"
    );
    Ok(())
}

fn identity_law<P: Prob>(lane: &Lane<P>, f: &Draw) -> TestCaseResult {
    let f = f.kernel(lane)?;
    let left = Kernel::identity(f.domain())?.compose(&f)?;
    let right = f.compose(&Kernel::identity(f.codomain())?)?;
    check(lane, "𝟙 X ≫ f = f", &left, &f)?;
    check(lane, "f ≫ 𝟙 Y = f", &right, &f)
}

fn associativity_law<P: Prob>(lane: &Lane<P>, (f, g, h): &(Draw, Draw, Draw)) -> TestCaseResult {
    let (f, g, h) = (f.kernel(lane)?, g.kernel(lane)?, h.kernel(lane)?);
    let left = f.compose(&g)?.compose(&h)?;
    let right = f.compose(&g.compose(&h)?)?;
    check(lane, "(f ≫ g) ≫ h = f ≫ (g ≫ h)", &left, &right)
}

fn interchange_law<P: Prob>(
    lane: &Lane<P>,
    (f, h): &(Draw, Draw),
    (g, k): &(Draw, Draw),
) -> TestCaseResult {
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

fn swap_natural_law<P: Prob>(lane: &Lane<P>, f: &Draw, g: &Draw) -> TestCaseResult {
    let (f, g) = (f.kernel(lane)?, g.kernel(lane)?);
    let left = f
        .tensor(&g)?
        .compose(&Kernel::swap(f.codomain(), g.codomain())?)?;
    let right = Kernel::swap(f.domain(), g.domain())?.compose(&g.tensor(&f)?)?;
    check(lane, "(f ⊗ₘ g) ≫ β_ = β_ ≫ (g ⊗ₘ f)", &left, &right)
}

/// Both sides are `X ⊗ Y ⊗ Z → X' ⊗ Y' ⊗ Z'`, with each object of at most
/// 4 * 4 * 4 elements.
fn associator_natural_law<P: Prob>(lane: &Lane<P>, f: &Draw, g: &Draw, h: &Draw) -> TestCaseResult {
    let (f, g, h) = (f.kernel(lane)?, g.kernel(lane)?, h.kernel(lane)?);
    let left = f.tensor(&g)?.tensor(&h)?.compose(&Kernel::associator(
        f.codomain(),
        g.codomain(),
        h.codomain(),
    )?)?;
    let right = Kernel::associator(f.domain(), g.domain(), h.domain())?
        .compose(&f.tensor(&g.tensor(&h)?)?)?;
    check(
        lane,
        "((f ⊗ₘ g) ⊗ₘ h) ≫ α_ = α_ ≫ (f ⊗ₘ (g ⊗ₘ h))",
        &left,
        &right,
    )
}

/// `I ⊗ X` has the factors of `X`, so `𝟙 I ⊗ₘ f : I ⊗ X → I ⊗ Y`,
/// `λ_ X : I ⊗ X → X` and `λ_ Y : I ⊗ Y → Y` make both sides `I ⊗ X → Y`.
fn left_unitor_natural_law<P: Prob>(lane: &Lane<P>, f: &Draw) -> TestCaseResult {
    let f = f.kernel(lane)?;
    let left = Kernel::identity(&FinObj::unit())?
        .tensor(&f)?
        .compose(&Kernel::left_unitor(f.codomain())?)?;
    let right = Kernel::left_unitor(f.domain())?.compose(&f)?;
    check(lane, "(𝟙 I ⊗ₘ f) ≫ λ_ Y = λ_ X ≫ f", &left, &right)
}

/// `X ⊗ I` has the factors of `X`, so `f ⊗ₘ 𝟙 I : X ⊗ I → Y ⊗ I`,
/// `ρ_ X : X ⊗ I → X` and `ρ_ Y : Y ⊗ I → Y` make both sides `X ⊗ I → Y`.
fn right_unitor_natural_law<P: Prob>(lane: &Lane<P>, f: &Draw) -> TestCaseResult {
    let f = f.kernel(lane)?;
    let left = f
        .tensor(&Kernel::identity(&FinObj::unit())?)?
        .compose(&Kernel::right_unitor(f.codomain())?)?;
    let right = Kernel::right_unitor(f.domain())?.compose(&f)?;
    check(lane, "(f ⊗ₘ 𝟙 I) ≫ ρ_ Y = ρ_ X ≫ f", &left, &right)
}

fn copy_coassociative_law<P: Prob>(lane: &Lane<P>, x: usize) -> TestCaseResult {
    let x = FinObj::new(x);
    let copy = Kernel::<P>::copy(&x)?;
    let id = Kernel::identity(&x)?;
    let left = copy
        .compose(&copy.tensor(&id)?)?
        .compose(&Kernel::associator(&x, &x, &x)?)?;
    let right = copy.compose(&id.tensor(&copy)?)?;
    check(lane, "Δ ≫ (Δ ▷ X) ≫ α_ = Δ ≫ (X ◁ Δ)", &left, &right)
}

fn copy_cocommutative_law<P: Prob>(lane: &Lane<P>, x: usize) -> TestCaseResult {
    let x = FinObj::new(x);
    let copy = Kernel::<P>::copy(&x)?;
    let swapped = copy.compose(&Kernel::swap(&x, &x)?)?;
    check(lane, "Δ ≫ β_ = Δ", &swapped, &copy)
}

fn counit_law<P: Prob>(lane: &Lane<P>, x: usize) -> TestCaseResult {
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

fn copy_tensor_law<P: Prob>(lane: &Lane<P>, x: usize, y: usize) -> TestCaseResult {
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

fn discard_tensor_law<P: Prob>(lane: &Lane<P>, x: usize, y: usize) -> TestCaseResult {
    let (x, y) = (FinObj::new(x), FinObj::new(y));
    let right = Kernel::<P>::del(&x)?
        .tensor(&Kernel::del(&y)?)?
        .compose(&Kernel::left_unitor(&FinObj::unit())?)?;
    let left = Kernel::del(&x.tensor(&y)?)?;
    check(lane, "ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ λ_ I", &left, &right)
}

fn discard_natural_law<P: Prob>(lane: &Lane<P>, f: &Draw) -> TestCaseResult {
    let f = f.kernel(lane)?;
    let left = f.compose(&Kernel::del(f.codomain())?)?;
    let right = Kernel::del(f.domain())?;
    check(lane, "f ≫ ε[Y] = ε[X]", &left, &right)
}

/// The module `$module` with one test per law, in lane `$lane`.
macro_rules! law_tests {
    ($module:ident, $lane:expr) => {
        mod $module {
            use super::*;

            #[test]
            fn copy_coassociative() {
                at_each_card(|x| copy_coassociative_law(&$lane, x));
            }

            #[test]
            fn copy_cocommutative() {
                at_each_card(|x| copy_cocommutative_law(&$lane, x));
            }

            #[test]
            fn counit() {
                at_each_card(|x| counit_law(&$lane, x));
            }

            #[test]
            fn copy_tensor() {
                at_each_card_pair(|x, y| copy_tensor_law(&$lane, x, y));
            }

            #[test]
            fn discard_tensor() {
                at_each_card_pair(|x, y| discard_tensor_law(&$lane, x, y));
            }

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
                fn left_unitor_natural(f in morphism()) {
                    left_unitor_natural_law(&$lane, &f)?;
                }

                #[test]
                fn right_unitor_natural(f in morphism()) {
                    right_unitor_natural_law(&$lane, &f)?;
                }

                #[test]
                fn discard_natural(f in morphism()) {
                    discard_natural_law(&$lane, &f)?;
                }
            }

            proptest! {
                #![proptest_config(ProptestConfig::with_cases(32))]

                #[test]
                fn associator_natural(f in morphism(), g in morphism(), h in morphism()) {
                    associator_natural_law(&$lane, &f, &g, &h)?;
                }
            }
        }
    };
}

law_tests!(exact, EXACT);

#[cfg(feature = "f64-prob")]
law_tests!(float, FLOAT);
