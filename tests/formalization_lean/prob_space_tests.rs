//! Witnesses of the theorems of `Peluang.ProbStoch.Basic`,
//! `Peluang.ProbStoch.Dagger`, `Peluang.ProbStoch.Coupling` and
//! `Peluang.Instances.FinStoch.ProbStoch` at the running example:
//! `is_state_preserving` and `coupling` beside `as_equal`, `bayesian_inverse`
//! and `is_bayesian_inverse`. Also, untagged: the `Error::NotAState` and
//! `Error::NotComposable` of `coupling`, the `Error::NotComposable` and
//! `Error::NotParallel` of `is_state_preserving`, and `is_state_preserving` on
//! a `psi` whose domain is not the unit.

use peluang::bayes::bayesian_inverse;
use peluang::error::{Error, Result};
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::{Compose, Tensor};
use peluang::prob::Exact;
use peluang::prob_space::{coupling, is_state_preserving};

use crate::fixtures::{
    assert_as_equal, assert_bayesian_inverse, assert_differs, assert_kernel,
    assert_state_preserving, c, c3, coin, const_b, copy_whisker, dd, e, h, hot, k, lit, not_b,
    obj_b, obj_s, obj_t, obj_w, on_b, points, psi_t, r, s, s2, show,
};

/// `q : I → W`, `(1/10, 3/10, 3/5)`: the literal of `psi_t ≫ c`.
fn q() -> Result<Kernel<Exact>> {
    Kernel::state(obj_w()?, vec![r(1, 10), r(3, 10), r(3, 5)])
}

/// `hot ≫ c : I → W`, `(1/2, 1/2, 0)`, as a literal.
fn hot_c() -> Result<Kernel<Exact>> {
    Kernel::state(obj_w()?, vec![r(1, 2), r(1, 2), r(0, 1)])
}

/// The kernel `W → T` with the columns `sunny`, `cloudy`, `rainy`.
fn w_to_t(sunny: [Exact; 2], cloudy: [Exact; 2], rainy: [Exact; 2]) -> Result<Kernel<Exact>> {
    lit(obj_w()?, obj_t()?, &[&sunny, &cloudy, &rainy])
}

/// The kernel `W → T` with sunny `(1, 0)`, cloudy `(1, 0)` and the column
/// `rainy`.
fn g_rainy(rainy: [Exact; 2]) -> Result<Kernel<Exact>> {
    w_to_t([r(1, 1), r(0, 1)], [r(1, 1), r(0, 1)], rainy)
}

/// `c† : W → T`, sunny `(1, 0)`, cloudy `(1/3, 2/3)`, rainy `(0, 1)`: the
/// literal of `bayesian_inverse(psi_t, c)`.
fn c_dagger() -> Result<Kernel<Exact>> {
    w_to_t([r(1, 1), r(0, 1)], [r(1, 3), r(2, 3)], [r(0, 1), r(1, 1)])
}

/// The literal of `coupling(hot, c) : I → T ⊗ W`, `(1/2, 1/2, 0, 0, 0, 0)`.
fn coupling_hot_c() -> Result<Kernel<Exact>> {
    Kernel::state(
        obj_t()?.tensor(&obj_w()?)?,
        vec![r(1, 2), r(1, 2), r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
    )
}

/// The literal of `coupling(psi_t, c) : I → T ⊗ W`,
/// `(1/10, 1/10, 0, 0, 1/5, 3/5)`.
fn coupling_psi_t_c() -> Result<Kernel<Exact>> {
    Kernel::state(
        obj_t()?.tensor(&obj_w()?)?,
        vec![r(1, 10), r(1, 10), r(0, 1), r(0, 1), r(1, 5), r(3, 5)],
    )
}

/// `bayesian_inverse(p, f)` after asserting that it equals `expected`; panics
/// with `name` and the error when the engine returns an error.
#[track_caller]
fn inverse(
    name: &str,
    p: &Kernel<Exact>,
    f: &Kernel<Exact>,
    expected: &Kernel<Exact>,
) -> Kernel<Exact> {
    let observed = match bayesian_inverse(p, f) {
        Ok(observed) => observed,
        Err(e) => panic!(
            "{name} with p = {}, f = {}: expected Ok({}), observed Err({e:?})",
            show(p),
            show(f),
            show(expected)
        ),
    };
    assert_kernel(name, &observed, expected);
    observed
}

/// `coupling(psi, f)` after asserting that it equals `expected`; panics with
/// `name` and the error when the engine returns an error.
#[track_caller]
fn coupled(
    name: &str,
    psi: &Kernel<Exact>,
    f: &Kernel<Exact>,
    expected: &Kernel<Exact>,
) -> Kernel<Exact> {
    let observed = match coupling(psi, f) {
        Ok(observed) => observed,
        Err(e) => panic!(
            "{name} with psi = {}, f = {}: expected Ok({}), observed Err({e:?})",
            show(psi),
            show(f),
            show(expected)
        ),
    };
    assert_kernel(name, &observed, expected);
    observed
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.AlmostSurelyEq.tensorHom
#[test]
fn witness_almost_surely_eq_tensor_hom() -> Result<()> {
    let (hot, c, c3, s, s2) = (hot()?, c()?, c3()?, s()?, s2()?);
    assert_differs("c against c3", &c, &c3);
    assert_differs("s against s2", &s, &s2);
    assert_as_equal("hf: as_equal(hot, c, c3)", &hot, &c, &c3, true);
    let reached = hot_c()?;
    assert_kernel("hot ≫ c", &hot.compose(&c)?, &reached);
    assert_as_equal("hg: as_equal(hot ≫ c, s, s2)", &reached, &s, &s2, true);

    let tw = obj_t()?.tensor(&obj_w()?)?;
    let state = Kernel::state(
        tw.clone(),
        vec![r(1, 2), r(1, 2), r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
    )?;
    assert_kernel("hot ⊗ₘ (hot ≫ c)", &hot.tensor(&reached)?, &state);
    let (lhs, rhs) = (c.tensor(&s)?, c3.tensor(&s2)?);
    assert_as_equal(
        "as_equal(hot ⊗ₘ (hot ≫ c), c ⊗ₘ s, c3 ⊗ₘ s2)",
        &state,
        &lhs,
        &rhs,
        true,
    );

    let control = Kernel::state(
        tw,
        vec![r(1, 10), r(1, 10), r(0, 1), r(2, 5), r(2, 5), r(0, 1)],
    )?;
    assert_kernel("psi_t ⊗ₘ (hot ≫ c)", &psi_t()?.tensor(&reached)?, &control);
    assert_as_equal(
        "control: as_equal(psi_t ⊗ₘ (hot ≫ c), c ⊗ₘ s, c3 ⊗ₘ s2), (cold, sunny) reached",
        &control,
        &lhs,
        &rhs,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.ProbStoch.functor_map_eq_iff
#[test]
fn witness_prob_stoch_functor_map_eq_iff() -> Result<()> {
    let (hot, psi_t, c, c3, s, s2) = (hot()?, psi_t()?, c()?, c3()?, s()?, s2()?);
    assert_as_equal("as_equal(hot, c, c3)", &hot, &c, &c3, true);
    let reached = hot_c()?;
    assert_kernel("hot ≫ c", &hot.compose(&c)?, &reached);
    assert_as_equal("as_equal(hot ≫ c, s, s2)", &reached, &s, &s2, true);

    let (cs, c3s2) = (c.compose(&s)?, c3.compose(&s2)?);
    assert_kernel("c ≫ s", &cs, &h()?);
    assert_kernel(
        "c3 ≫ s2",
        &c3s2,
        &lit(
            obj_t()?,
            obj_s()?,
            &[&[r(2, 3), r(1, 3)], &[r(11, 18), r(7, 18)]],
        )?,
    );
    assert_differs("c ≫ s against c3 ≫ s2", &cs, &c3s2);
    assert_as_equal("as_equal(hot, c ≫ s, c3 ≫ s2)", &hot, &cs, &c3s2, true);
    assert_as_equal(
        "control: as_equal(psi_t, c ≫ s, c3 ≫ s2), cold reached",
        &psi_t,
        &cs,
        &c3s2,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: FinStoch.exists_ne_probStoch_map_eq
#[test]
fn witness_exists_ne_prob_stoch_map_eq() -> Result<()> {
    let (b, on_b, const_b) = (obj_b()?, on_b()?, const_b()?);
    let id = points(b.clone(), b.clone(), &[0, 1])?;
    assert_kernel("𝟙 B", &Kernel::identity(&b)?, &id);
    assert_state_preserving(
        "is_state_preserving(on_b, 𝟙 B, on_b)",
        &on_b,
        &id,
        &on_b,
        true,
    );
    assert_state_preserving(
        "is_state_preserving(on_b, const_b, on_b)",
        &on_b,
        &const_b,
        &on_b,
        true,
    );
    assert_differs("𝟙 B against const_b", &id, &const_b);
    assert_as_equal("as_equal(on_b, 𝟙 B, const_b)", &on_b, &id, &const_b, true);
    assert_state_preserving(
        "control: is_state_preserving(on_b, not_b, on_b)",
        &on_b,
        &not_b()?,
        &on_b,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: FinStoch.exists_probStoch_map_ne
#[test]
fn witness_exists_prob_stoch_map_ne() -> Result<()> {
    let (b, coin, not_b) = (obj_b()?, coin()?, not_b()?);
    let id = points(b.clone(), b.clone(), &[0, 1])?;
    assert_kernel("𝟙 B", &Kernel::identity(&b)?, &id);
    assert_state_preserving(
        "is_state_preserving(coin, 𝟙 B, coin)",
        &coin,
        &id,
        &coin,
        true,
    );
    assert_state_preserving(
        "is_state_preserving(coin, not_b, coin)",
        &coin,
        &not_b,
        &coin,
        true,
    );
    assert_as_equal("as_equal(coin, 𝟙 B, not_b)", &coin, &id, &not_b, false);
    assert_state_preserving(
        "control: is_state_preserving(coin, const_b, coin)",
        &coin,
        &const_b()?,
        &coin,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.ProbStoch.functor_map_tensorHom
#[test]
fn witness_prob_stoch_functor_map_tensor_hom() -> Result<()> {
    let (psi_t, c, coin, not_b, q) = (psi_t()?, c()?, coin()?, not_b()?, q()?);
    assert_state_preserving("is_state_preserving(psi_t, c, q)", &psi_t, &c, &q, true);
    assert_state_preserving(
        "is_state_preserving(coin, not_b, coin)",
        &coin,
        &not_b,
        &coin,
        true,
    );

    let state = Kernel::state(
        obj_t()?.tensor(&obj_b()?)?,
        vec![r(1, 10), r(1, 10), r(2, 5), r(2, 5)],
    )?;
    assert_kernel("psi_t ⊗ₘ coin", &psi_t.tensor(&coin)?, &state);
    let wb = obj_w()?.tensor(&obj_b()?)?;
    let image = Kernel::state(
        wb.clone(),
        vec![r(1, 20), r(1, 20), r(3, 20), r(3, 20), r(3, 10), r(3, 10)],
    )?;
    assert_kernel("(psi_t ≫ c) ⊗ₘ coin", &q.tensor(&coin)?, &image);
    let f = c.tensor(&not_b)?;
    assert_state_preserving(
        "is_state_preserving(psi_t ⊗ₘ coin, c ⊗ₘ not_b, (psi_t ≫ c) ⊗ₘ coin)",
        &state,
        &f,
        &image,
        true,
    );

    let other = Kernel::state(
        wb,
        vec![r(1, 4), r(1, 4), r(1, 4), r(1, 4), r(0, 1), r(0, 1)],
    )?;
    assert_kernel("(hot ≫ c) ⊗ₘ coin", &hot_c()?.tensor(&coin)?, &other);
    assert_state_preserving(
        "control: is_state_preserving(psi_t ⊗ₘ coin, c ⊗ₘ not_b, (hot ≫ c) ⊗ₘ coin)",
        &state,
        &f,
        &other,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsBayesianInverse.almostSurelyEq_of_almostSurelyEq
#[test]
fn witness_is_bayesian_inverse_almost_surely_eq_of_almost_surely_eq() -> Result<()> {
    let (hot, psi_t, c, c3) = (hot()?, psi_t()?, c()?, c3()?);
    assert_as_equal("hf: as_equal(hot, c, c3)", &hot, &c, &c3, true);
    let filled = g_rainy([r(1, 2), r(1, 2)])?;
    let g1 = inverse("g₁ = bayesian_inverse(hot, c)", &hot, &c, &filled);
    let g2 = inverse("g₂ = bayesian_inverse(hot, c3)", &hot, &c3, &filled);
    assert_bayesian_inverse("h₁: is_bayesian_inverse(hot, c, g₁)", &hot, &c, &g1, true);
    assert_bayesian_inverse("h₂: is_bayesian_inverse(hot, c3, g₂)", &hot, &c3, &g2, true);
    let reached = hot_c()?;
    assert_kernel("hot ≫ c", &hot.compose(&c)?, &reached);
    assert_as_equal("as_equal(hot ≫ c, g₁, g₂)", &reached, &g1, &g2, true);

    let g3 = g_rainy([r(1, 1), r(0, 1)])?;
    assert_differs("g₁ against g₃, rainy (1, 0)", &g1, &g3);
    assert_bayesian_inverse("h₂: is_bayesian_inverse(hot, c3, g₃)", &hot, &c3, &g3, true);
    assert_as_equal("as_equal(hot ≫ c, g₁, g₃)", &reached, &g1, &g3, true);

    assert_as_equal(
        "control hf: as_equal(psi_t, c, c3), cold reached",
        &psi_t,
        &c,
        &c3,
        false,
    );
    let d1 = inverse("bayesian_inverse(psi_t, c)", &psi_t, &c, &c_dagger()?);
    let d2 = inverse(
        "bayesian_inverse(psi_t, c3)",
        &psi_t,
        &c3,
        &w_to_t(
            [r(3, 11), r(8, 11)],
            [r(3, 11), r(8, 11)],
            [r(0, 1), r(1, 1)],
        )?,
    );
    let reached = q()?;
    assert_kernel("psi_t ≫ c", &psi_t.compose(&c)?, &reached);
    assert_as_equal(
        "control: as_equal(psi_t ≫ c, bayesian_inverse(psi_t, c), bayesian_inverse(psi_t, c3))",
        &reached,
        &d1,
        &d2,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.ProbStoch.dagger_map
#[test]
fn witness_prob_stoch_dagger_map() -> Result<()> {
    let (hot, c) = (hot()?, c()?);
    let (g1, g2) = (g_rainy([r(1, 1), r(0, 1)])?, g_rainy([r(0, 1), r(1, 1)])?);
    assert_differs("g₁ against g₂", &g1, &g2);
    assert_bayesian_inverse("is_bayesian_inverse(hot, c, g₁)", &hot, &c, &g1, true);
    assert_bayesian_inverse("is_bayesian_inverse(hot, c, g₂)", &hot, &c, &g2, true);
    let reached = hot_c()?;
    assert_kernel("hot ≫ c", &hot.compose(&c)?, &reached);
    assert_as_equal("as_equal(hot ≫ c, g₁, g₂)", &reached, &g1, &g2, true);

    let dagger = inverse(
        "bayesian_inverse(hot, c)",
        &hot,
        &c,
        &g_rainy([r(1, 2), r(1, 2)])?,
    );
    assert_differs("bayesian_inverse(hot, c) against g₁", &dagger, &g1);
    assert_differs("bayesian_inverse(hot, c) against g₂", &dagger, &g2);
    assert_as_equal(
        "as_equal(hot ≫ c, bayesian_inverse(hot, c), g₁)",
        &reached,
        &dagger,
        &g1,
        true,
    );
    assert_as_equal(
        "as_equal(hot ≫ c, bayesian_inverse(hot, c), g₂)",
        &reached,
        &dagger,
        &g2,
        true,
    );

    let changed = w_to_t([r(1, 1), r(0, 1)], [r(1, 2), r(1, 2)], [r(1, 1), r(0, 1)])?;
    assert_bayesian_inverse(
        "control: is_bayesian_inverse(hot, c, g₁ with cloudy (1/2, 1/2))",
        &hot,
        &c,
        &changed,
        false,
    );
    assert_as_equal(
        "control: as_equal(hot ≫ c, bayesian_inverse(hot, c), g₁ with cloudy (1/2, 1/2))",
        &reached,
        &dagger,
        &changed,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.ProbStoch.dagger_id
#[test]
fn witness_prob_stoch_dagger_id() -> Result<()> {
    let (t, hot, psi_t) = (obj_t()?, hot()?, psi_t()?);
    let id = points(t.clone(), t.clone(), &[0, 1])?;
    assert_kernel("𝟙 T", &Kernel::identity(&t)?, &id);

    assert_kernel("hot ≫ 𝟙 T", &hot.compose(&id)?, &hot);
    let filled = inverse(
        "bayesian_inverse(hot, 𝟙 T)",
        &hot,
        &id,
        &lit(t.clone(), t, &[&[r(1, 1), r(0, 1)], &[r(1, 2), r(1, 2)]])?,
    );
    assert_differs("bayesian_inverse(hot, 𝟙 T) against 𝟙 T", &filled, &id);
    assert_as_equal(
        "as_equal(hot, bayesian_inverse(hot, 𝟙 T), 𝟙 T)",
        &hot,
        &filled,
        &id,
        true,
    );

    assert_kernel("psi_t ≫ 𝟙 T", &psi_t.compose(&id)?, &psi_t);
    let exact = inverse("bayesian_inverse(psi_t, 𝟙 T)", &psi_t, &id, &id);
    assert_as_equal(
        "as_equal(psi_t, bayesian_inverse(psi_t, 𝟙 T), 𝟙 T)",
        &psi_t,
        &exact,
        &id,
        true,
    );
    assert_as_equal(
        "control: as_equal(psi_t, bayesian_inverse(hot, 𝟙 T), 𝟙 T), cold reached",
        &psi_t,
        &filled,
        &id,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.ProbStoch.dagger_comp
#[test]
fn witness_prob_stoch_dagger_comp() -> Result<()> {
    let (hot, psi_t, c, s, dd) = (hot()?, psi_t()?, c()?, s()?, dd()?);

    let cd = c.compose(&dd)?;
    assert_kernel("c ≫ dd", &cd, &k()?);
    let whole = inverse(
        "bayesian_inverse(hot, c ≫ dd)",
        &hot,
        &cd,
        &lit(
            obj_s()?,
            obj_t()?,
            &[&[r(1, 1), r(0, 1)], &[r(1, 2), r(1, 2)]],
        )?,
    );
    let reached = hot_c()?;
    assert_kernel("hot ≫ c", &hot.compose(&c)?, &reached);
    let second = inverse(
        "bayesian_inverse(hot ≫ c, dd)",
        &reached,
        &dd,
        &lit(
            obj_s()?,
            obj_w()?,
            &[&[r(1, 2), r(1, 2), r(0, 1)], &[r(1, 3), r(1, 3), r(1, 3)]],
        )?,
    );
    let first = inverse(
        "bayesian_inverse(hot, c)",
        &hot,
        &c,
        &g_rainy([r(1, 2), r(1, 2)])?,
    );
    let composite = second.compose(&first)?;
    assert_kernel(
        "bayesian_inverse(hot ≫ c, dd) ≫ bayesian_inverse(hot, c)",
        &composite,
        &lit(
            obj_s()?,
            obj_t()?,
            &[&[r(1, 1), r(0, 1)], &[r(5, 6), r(1, 6)]],
        )?,
    );
    assert_differs(
        "bayesian_inverse(hot, c ≫ dd) against the composite",
        &whole,
        &composite,
    );
    let at = Kernel::state(obj_s()?, vec![r(1, 1), r(0, 1)])?;
    assert_kernel("hot ≫ c ≫ dd", &hot.compose(&cd)?, &at);
    assert_as_equal(
        "as_equal(hot ≫ c ≫ dd, bayesian_inverse(hot, c ≫ dd), bayesian_inverse(hot ≫ c, dd) ≫ \
         bayesian_inverse(hot, c))",
        &at,
        &whole,
        &composite,
        true,
    );
    let at = Kernel::state(obj_s()?, vec![r(2, 5), r(3, 5)])?;
    assert_kernel("psi_t ≫ c ≫ dd", &psi_t.compose(&cd)?, &at);
    assert_as_equal(
        "control: as_equal(psi_t ≫ c ≫ dd, bayesian_inverse(hot, c ≫ dd), bayesian_inverse(hot ≫ \
         c, dd) ≫ bayesian_inverse(hot, c)), off reached",
        &at,
        &whole,
        &composite,
        false,
    );

    let cs = c.compose(&s)?;
    assert_kernel("c ≫ s", &cs, &h()?);
    let literal = lit(
        obj_s()?,
        obj_t()?,
        &[&[r(2, 5), r(3, 5)], &[r(1, 10), r(9, 10)]],
    )?;
    let whole = inverse("bayesian_inverse(psi_t, c ≫ s)", &psi_t, &cs, &literal);
    let reached = q()?;
    assert_kernel("psi_t ≫ c", &psi_t.compose(&c)?, &reached);
    let second = inverse(
        "bayesian_inverse(psi_t ≫ c, s)",
        &reached,
        &s,
        &lit(
            obj_s()?,
            obj_w()?,
            &[
                &[r(1, 10), r(9, 10), r(0, 1)],
                &[r(1, 10), r(0, 1), r(9, 10)],
            ],
        )?,
    );
    let first = inverse("bayesian_inverse(psi_t, c)", &psi_t, &c, &c_dagger()?);
    let composite = second.compose(&first)?;
    assert_kernel(
        "bayesian_inverse(psi_t ≫ c, s) ≫ bayesian_inverse(psi_t, c)",
        &composite,
        &literal,
    );
    let at = Kernel::state(obj_s()?, vec![r(1, 3), r(2, 3)])?;
    assert_kernel("psi_t ≫ c ≫ s", &psi_t.compose(&cs)?, &at);
    assert_as_equal(
        "as_equal(psi_t ≫ c ≫ s, bayesian_inverse(psi_t, c ≫ s), bayesian_inverse(psi_t ≫ c, s) ≫ \
         bayesian_inverse(psi_t, c))",
        &at,
        &whole,
        &composite,
        true,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.ProbStoch.dagger_dagger
#[test]
fn witness_prob_stoch_dagger_dagger() -> Result<()> {
    let (hot, psi_t, c) = (hot()?, psi_t()?, c()?);

    let dagger = inverse(
        "bayesian_inverse(hot, c)",
        &hot,
        &c,
        &g_rainy([r(1, 2), r(1, 2)])?,
    );
    let reached = hot_c()?;
    assert_kernel("hot ≫ c", &hot.compose(&c)?, &reached);
    let back = inverse(
        "bayesian_inverse(hot ≫ c, bayesian_inverse(hot, c))",
        &reached,
        &dagger,
        &c3()?,
    );
    assert_differs(
        "bayesian_inverse(hot ≫ c, bayesian_inverse(hot, c)) against c",
        &back,
        &c,
    );
    assert_as_equal(
        "as_equal(hot, bayesian_inverse(hot ≫ c, bayesian_inverse(hot, c)), c)",
        &hot,
        &back,
        &c,
        true,
    );
    assert_as_equal(
        "control: as_equal(psi_t, bayesian_inverse(hot ≫ c, bayesian_inverse(hot, c)), c), cold \
         reached",
        &psi_t,
        &back,
        &c,
        false,
    );

    let dagger = inverse("bayesian_inverse(psi_t, c)", &psi_t, &c, &c_dagger()?);
    let reached = q()?;
    assert_kernel("psi_t ≫ c", &psi_t.compose(&c)?, &reached);
    let literal = lit(
        obj_t()?,
        obj_w()?,
        &[&[r(1, 2), r(1, 2), r(0, 1)], &[r(0, 1), r(1, 4), r(3, 4)]],
    )?;
    let back = inverse(
        "bayesian_inverse(psi_t ≫ c, bayesian_inverse(psi_t, c))",
        &reached,
        &dagger,
        &literal,
    );
    assert_as_equal(
        "as_equal(psi_t, bayesian_inverse(psi_t ≫ c, bayesian_inverse(psi_t, c)), c)",
        &psi_t,
        &back,
        &c,
        true,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.ProbStoch.homEquivCoupling_map
#[test]
fn witness_prob_stoch_hom_equiv_coupling_map() -> Result<()> {
    let (t, w) = (obj_t()?, obj_w()?);
    let (hot, psi_t, c, c3) = (hot()?, psi_t()?, c()?, c3()?);
    assert_differs("c against c3", &c, &c3);

    let literal = coupling_hot_c()?;
    let fst = coupled("coupling(hot, c)", &hot, &c, &literal);
    let snd = coupled("coupling(hot, c3)", &hot, &c3, &literal);
    assert_kernel("coupling(hot, c) against coupling(hot, c3)", &fst, &snd);

    let joint = coupled("coupling(psi_t, c)", &psi_t, &c, &coupling_psi_t_c()?);
    let other = coupled(
        "coupling(psi_t, c3)",
        &psi_t,
        &c3,
        &Kernel::state(
            t.tensor(&w)?,
            vec![r(1, 10), r(1, 10), r(0, 1), r(4, 15), r(4, 15), r(4, 15)],
        )?,
    );
    assert_differs(
        "coupling(psi_t, c) against coupling(psi_t, c3)",
        &joint,
        &other,
    );
    assert_kernel(
        "marginal_fst of coupling(psi_t, c)",
        &joint.marginal_fst(&t, &w)?,
        &Kernel::state(t.clone(), vec![r(1, 5), r(4, 5)])?,
    );
    assert_kernel(
        "marginal_snd of coupling(psi_t, c)",
        &joint.marginal_snd(&t, &w)?,
        &q()?,
    );

    let (observed, expected) = (joint.codomain(), t.tensor(&w)?);
    assert!(
        *observed == expected,
        "the codomain of coupling(psi_t, c): expected {expected:?}, observed {observed:?}"
    );
    let left_wire = Kernel::state(
        w.tensor(&t)?,
        vec![r(1, 10), r(0, 1), r(1, 10), r(1, 5), r(0, 1), r(3, 5)],
    )?;
    assert_kernel(
        "psi_t ≫ Δ[T] ≫ (c ▷ T)",
        &copy_whisker(&psi_t, &c)?,
        &left_wire,
    );
    assert_differs(
        "coupling(psi_t, c) against psi_t ≫ Δ[T] ≫ (c ▷ T)",
        &joint,
        &left_wire,
    );
    assert_kernel(
        "coupling(psi_t, c) ≫ σ[T, W]",
        &joint.compose(&Kernel::swap(&t, &w)?)?,
        &left_wire,
    );

    for (name, p, expected) in [("hot", &hot, true), ("psi_t", &psi_t, false)] {
        assert_as_equal(&format!("as_equal({name}, c, c3)"), p, &c, &c3, expected);
        let (fst, snd) = (coupling(p, &c)?, coupling(p, &c3)?);
        let observed = fst == snd;
        assert_eq!(
            observed,
            expected,
            "coupling({name}, c) == coupling({name}, c3): expected {expected}, observed \
             {observed}: {} vs {}",
            show(&fst),
            show(&snd)
        );
    }
    Ok(())
}

#[test]
fn coupling_rejects_a_non_state_then_a_non_composable_pair() -> Result<()> {
    let (t, w, c) = (obj_t()?, obj_w()?, c()?);
    for (name, f) in [("composable s", s()?), ("non-composable e", e()?)] {
        let got = coupling(&c, &f);
        assert!(
            matches!(&got, Err(Error::NotAState { domain }) if *domain == t),
            "coupling(c, {name}): expected NotAState {{ domain: {t:?} }}, observed {got:?}"
        );
    }
    let got = coupling(&hot()?, &s()?);
    assert!(
        matches!(&got, Err(Error::NotComposable { codomain, domain })
            if *codomain == t && *domain == w),
        "coupling(hot, s): expected NotComposable {{ codomain: {t:?}, domain: {w:?} }}, observed \
         {got:?}"
    );
    Ok(())
}

#[test]
fn is_state_preserving_rejects_a_non_composable_pair_then_a_non_parallel_state() -> Result<()> {
    let (unit, t, w, sp) = (FinObj::unit(), obj_t()?, obj_w()?, obj_s()?);
    let (hot, psi_t, c, s) = (hot()?, psi_t()?, c()?, s()?);
    for (name, phi) in [("parallel coin", coin()?), ("non-parallel c", c.clone())] {
        let got = is_state_preserving(&hot, &s, &phi);
        assert!(
            matches!(&got, Err(Error::NotComposable { codomain, domain })
                if *codomain == t && *domain == w),
            "is_state_preserving(hot, s, {name}): expected NotComposable {{ codomain: {t:?}, \
             domain: {w:?} }}, observed {got:?}"
        );
    }
    for (name, psi, phi, fst, snd) in [
        (
            "(psi_t, c, psi_t), the codomain of phi differs",
            &psi_t,
            &psi_t,
            (&unit, &w),
            (&unit, &t),
        ),
        (
            "(psi_t, c, s), the domain of phi differs",
            &psi_t,
            &s,
            (&unit, &w),
            (&w, &sp),
        ),
        (
            "(𝟙 T, c, q), the domain of psi is not the unit",
            &Kernel::identity(&t)?,
            &q()?,
            (&t, &w),
            (&unit, &w),
        ),
    ] {
        let got = is_state_preserving(psi, &c, phi);
        assert!(
            matches!(&got, Err(Error::NotParallel { fst: a, snd: b })
                if (&a.0, &a.1) == fst && (&b.0, &b.1) == snd),
            "is_state_preserving{name}: expected NotParallel {{ fst: {fst:?}, snd: {snd:?} }}, \
             observed {got:?}"
        );
    }
    Ok(())
}

#[test]
fn is_state_preserving_compares_the_composite_on_a_domain_that_is_not_the_unit() -> Result<()> {
    let (c, s) = (c()?, s()?);
    assert_state_preserving("is_state_preserving(c, s, h)", &c, &s, &h()?, true);
    assert_state_preserving(
        "control: is_state_preserving(c, s, k)",
        &c,
        &s,
        &k()?,
        false,
    );
    Ok(())
}
