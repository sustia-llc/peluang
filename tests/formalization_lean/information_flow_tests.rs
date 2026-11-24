//! Witnesses of `Peluang.Causal`, `Peluang.Positive` and
//! `Peluang.Instances.FinStoch.InformationFlow` at the running example:
//! `copy_then`, `copy_comp_natural` and `copy_comp_natural_as` beside
//! `as_equal`, `is_deterministic` and `is_as_deterministic`. Also, untagged:
//! `copy_comp_natural` and `copy_comp_natural_as` on `(c, g0)` and on
//! `(c, dd)`; the `Error::NotComposable` of the three functions on the
//! running example, on `[2^19]` and on an empty domain; their
//! `Error::TooLarge` on `[2^19]`; and `Ok(true)` of the two boolean functions
//! on `0 → [2^19]`.

use std::fmt::Debug;

use peluang::error::{Error, Result};
use peluang::finset::FinObj;
use peluang::information_flow::{copy_comp_natural, copy_comp_natural_as, copy_then};
use peluang::kernel::Kernel;
use peluang::markov::Compose;
use peluang::prob::Exact;

use crate::fixtures::{
    assert_as_deterministic, assert_as_equal, assert_copy_comp_natural,
    assert_copy_comp_natural_as, assert_deterministic, assert_differs, assert_kernel, c, c2, coin,
    copy_whisker, dd, e, e_inv, g0, g2, hot, k, lit, m, obj_b, obj_s, obj_t, obj_w, psi_t, r, s,
    s2,
};

/// The literal of `copy_then(c, s) : T → S ⊗ W`.
fn copy_then_c_s() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_s()?.tensor(&obj_w()?)?,
        &[
            &[r(1, 6), r(1, 2), r(0, 1), r(1, 3), r(0, 1), r(0, 1)],
            &[r(0, 1), r(1, 4), r(0, 1), r(0, 1), r(0, 1), r(3, 4)],
        ],
    )
}

/// The literal of `copy_then(c, s2) : T → S ⊗ W`.
fn copy_then_c_s2() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_s()?.tensor(&obj_w()?)?,
        &[
            &[r(1, 6), r(1, 2), r(0, 1), r(1, 3), r(0, 1), r(0, 1)],
            &[r(0, 1), r(1, 4), r(3, 8), r(0, 1), r(0, 1), r(3, 8)],
        ],
    )
}

/// Asserts that `got` is `Err(Error::NotComposable { codomain, domain })`,
/// naming the call `name`.
#[track_caller]
fn assert_not_composable<T: Debug>(
    name: &str,
    got: &Result<T>,
    codomain: &FinObj,
    domain: &FinObj,
) {
    assert!(
        matches!(
            got,
            Err(Error::NotComposable { codomain: cod, domain: dom })
                if cod == codomain && dom == domain
        ),
        "{name}: expected Err(NotComposable {{ codomain: {codomain:?}, domain: {domain:?} }}), \
         observed {got:?}"
    );
}

/// `copy_then` and `copy_comp_natural` on `(s, c)` return the
/// `Error::NotComposable` of `S` and `T`. `copy_comp_natural_as` returns that
/// of `T` and `W` on `(hot, s, c)` and that of `W` and `T` on `(hot, c, c)`.
#[test]
fn information_flow_functions_return_not_composable_on_a_domain_mismatch() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (hot, c, s) = (hot()?, c()?, s()?);
    assert_not_composable("copy_then(s, c)", &copy_then(&s, &c), &sp, &t);
    assert_not_composable(
        "copy_comp_natural(s, c)",
        &copy_comp_natural(&s, &c),
        &sp,
        &t,
    );
    assert_not_composable(
        "copy_comp_natural_as(hot, s, c)",
        &copy_comp_natural_as(&hot, &s, &c),
        &t,
        &w,
    );
    assert_not_composable(
        "copy_comp_natural_as(hot, c, c)",
        &copy_comp_natural_as(&hot, &c, &c),
        &w,
        &t,
    );
    Ok(())
}

/// `[2^19]`, where `Kernel::copy` returns `Error::TooLarge` for `2^19 * 2^38`
/// weights.
fn wide() -> FinObj {
    FinObj::new(1 << 19)
}

/// Asserts that `got` is `Err(Error::TooLarge { fst: 2^19, snd: 2^38, source:
/// Some(_) })`, naming the call `name`.
#[track_caller]
fn assert_too_large<T: Debug>(name: &str, got: &Result<T>) {
    assert!(
        matches!(
            got,
            Err(Error::TooLarge { fst, snd, source: Some(_) })
                if u64::try_from(*fst).ok() == Some(1 << 19)
                    && u64::try_from(*snd).ok() == Some(1 << 38)
        ),
        "{name}: expected Err(TooLarge {{ fst: 2^19, snd: 2^38, source: Some(_) }}), observed \
         {got:?}"
    );
}

/// With `into_wide : I → [2^19]` and `ε[2^19] : [2^19] → I`: `copy_then` and
/// `copy_comp_natural` on `(into_wide, c)` return the `Error::NotComposable`
/// of `[2^19]` and `T`. `copy_comp_natural_as` returns that of `T` and `I` on
/// `(hot, into_wide, ε[2^19])` and that of `[2^19]` and `T` on
/// `(𝟙 I, into_wide, c)`.
#[test]
fn information_flow_functions_reject_before_they_build_a_kernel() -> Result<()> {
    let (t, wide, unit) = (obj_t()?, wide(), FinObj::unit());
    let (hot, c) = (hot()?, c()?);
    let into_wide = Kernel::<Exact>::from_fn(unit.clone(), wide.clone(), |_| 0)?;
    let del = Kernel::<Exact>::del(&wide)?;
    let id = Kernel::<Exact>::identity(&unit)?;
    assert_not_composable(
        "copy_then(I → [2^19], c)",
        &copy_then(&into_wide, &c),
        &wide,
        &t,
    );
    assert_not_composable(
        "copy_comp_natural(I → [2^19], c)",
        &copy_comp_natural(&into_wide, &c),
        &wide,
        &t,
    );
    assert_not_composable(
        "copy_comp_natural_as(hot, I → [2^19], ε[2^19])",
        &copy_comp_natural_as(&hot, &into_wide, &del),
        &t,
        &unit,
    );
    assert_not_composable(
        "copy_comp_natural_as(𝟙 I, I → [2^19], c)",
        &copy_comp_natural_as(&id, &into_wide, &c),
        &wide,
        &t,
    );
    Ok(())
}

/// With `into_wide : I → [2^19]` and `ε[2^19] : [2^19] → I`: `copy_then` and
/// `copy_comp_natural` on `(into_wide, ε[2^19])` and `copy_comp_natural_as` on
/// `(𝟙 I, into_wide, ε[2^19])` return `Error::TooLarge` with `fst` `2^19`,
/// `snd` `2^38` and a source.
#[test]
fn information_flow_functions_return_too_large_on_a_composable_pair_through_2_pow_19() -> Result<()>
{
    let (wide, unit) = (wide(), FinObj::unit());
    let into_wide = Kernel::<Exact>::from_fn(unit.clone(), wide.clone(), |_| 0)?;
    let del = Kernel::<Exact>::del(&wide)?;
    let id = Kernel::<Exact>::identity(&unit)?;
    assert_too_large(
        "copy_then(I → [2^19], ε[2^19])",
        &copy_then(&into_wide, &del),
    );
    assert_too_large(
        "copy_comp_natural(I → [2^19], ε[2^19])",
        &copy_comp_natural(&into_wide, &del),
    );
    assert_too_large(
        "copy_comp_natural_as(𝟙 I, I → [2^19], ε[2^19])",
        &copy_comp_natural_as(&id, &into_wide, &del),
    );
    Ok(())
}

/// `copy_comp_natural` on `(0 → [2^19], ε[2^19])` and `copy_comp_natural_as`
/// on `(0 → 0, 0 → [2^19], ε[2^19])` return `Ok(true)`.
#[test]
fn copy_comp_natural_and_its_as_form_on_an_empty_domain_build_no_kernel() -> Result<()> {
    let (empty, wide) = (FinObj::new(0), wide());
    let p = Kernel::<Exact>::new(empty.clone(), empty.clone(), Vec::new())?;
    let f = Kernel::<Exact>::new(empty, wide.clone(), Vec::new())?;
    let del = Kernel::<Exact>::del(&wide)?;
    let got = copy_comp_natural(&f, &del);
    assert!(
        matches!(got, Ok(true)),
        "copy_comp_natural(0 → [2^19], ε[2^19]): expected Ok(true), observed {got:?}"
    );
    let got = copy_comp_natural_as(&p, &f, &del);
    assert!(
        matches!(got, Ok(true)),
        "copy_comp_natural_as(0 → 0, 0 → [2^19], ε[2^19]): expected Ok(true), observed {got:?}"
    );
    Ok(())
}

/// `copy_comp_natural` on `(0 → S, c)` returns the `Error::NotComposable` of
/// `S` and `T`. `copy_comp_natural_as` returns that of `T` and `0` on
/// `(0 → T, 0 → S, e)` and that of `S` and `T` on `(0 → 0, 0 → S, c)`.
#[test]
fn copy_comp_natural_and_its_as_form_reject_a_non_composable_pair_on_an_empty_domain() -> Result<()>
{
    let (empty, t, sp) = (FinObj::new(0), obj_t()?, obj_s()?);
    let (c, e) = (c()?, e()?);
    let p = Kernel::<Exact>::new(empty.clone(), empty.clone(), Vec::new())?;
    let p_t = Kernel::<Exact>::new(empty.clone(), t.clone(), Vec::new())?;
    let f = Kernel::<Exact>::new(empty.clone(), sp.clone(), Vec::new())?;
    assert_not_composable(
        "copy_comp_natural(0 → S, c)",
        &copy_comp_natural(&f, &c),
        &sp,
        &t,
    );
    assert_not_composable(
        "copy_comp_natural_as(0 → T, 0 → S, e)",
        &copy_comp_natural_as(&p_t, &f, &e),
        &t,
        &empty,
    );
    assert_not_composable(
        "copy_comp_natural_as(0 → 0, 0 → S, c)",
        &copy_comp_natural_as(&p, &f, &c),
        &sp,
        &t,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CausalCategory.causal_eq
#[test]
fn witness_causal_eq() -> Result<()> {
    let (hot, psi_t) = (hot()?, psi_t()?);
    let lhs = copy_then(&c()?, &s()?)?;
    let rhs = copy_then(&c()?, &s2()?)?;
    assert_kernel("copy_then(c, s)", &lhs, &copy_then_c_s()?);
    assert_kernel("copy_then(c, s2)", &rhs, &copy_then_c_s2()?);

    assert_kernel(
        "hot ≫ copy_then(c, s) against hot ≫ copy_then(c, s2)",
        &hot.compose(&lhs)?,
        &hot.compose(&rhs)?,
    );
    assert_kernel(
        "hot ≫ Δ[T] ≫ (copy_then(c, s) ▷ T) against the same with s2",
        &copy_whisker(&hot, &lhs)?,
        &copy_whisker(&hot, &rhs)?,
    );
    assert_kernel(
        "hot ≫ Δ[T] ≫ (copy_then(c, s) ▷ T)",
        &copy_whisker(&hot, &lhs)?,
        &lit(
            FinObj::unit(),
            obj_s()?.tensor(&obj_w()?)?.tensor(&obj_t()?)?,
            &[&[
                r(1, 6),
                r(0, 1),
                r(1, 2),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(1, 3),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(0, 1),
            ]],
        )?,
    );

    assert_differs(
        "psi_t ≫ copy_then(c, s) against psi_t ≫ copy_then(c, s2)",
        &psi_t.compose(&lhs)?,
        &psi_t.compose(&rhs)?,
    );
    assert_differs(
        "psi_t ≫ Δ[T] ≫ (copy_then(c, s) ▷ T) against the same with s2",
        &copy_whisker(&psi_t, &lhs)?,
        &copy_whisker(&psi_t, &rhs)?,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.almostSurelyEq_copy_whiskerRight_of_hasConditionals
#[test]
fn witness_almost_surely_eq_copy_whisker_right_of_has_conditionals() -> Result<()> {
    let (hot, psi_t, c, s, s2) = (hot()?, psi_t()?, c()?, s()?, s2()?);
    let lhs = copy_then(&c, &s)?;
    let rhs = copy_then(&c, &s2)?;
    assert_kernel("copy_then(c, s)", &lhs, &copy_then_c_s()?);
    assert_kernel("copy_then(c, s2)", &rhs, &copy_then_c_s2()?);

    let hot_c = hot.compose(&c)?;
    let psi_c = psi_t.compose(&c)?;
    assert_kernel(
        "hot ≫ c",
        &hot_c,
        &Kernel::state(obj_w()?, vec![r(1, 2), r(1, 2), r(0, 1)])?,
    );
    assert_kernel(
        "psi_t ≫ c",
        &psi_c,
        &Kernel::state(obj_w()?, vec![r(1, 10), r(3, 10), r(3, 5)])?,
    );

    assert_as_equal("as_equal(hot ≫ c, s, s2)", &hot_c, &s, &s2, true);
    assert_as_equal(
        "as_equal(hot, copy_then(c, s), copy_then(c, s2))",
        &hot,
        &lhs,
        &rhs,
        true,
    );

    assert_as_equal("as_equal(psi_t ≫ c, s, s2)", &psi_c, &s, &s2, false);
    assert_as_equal(
        "as_equal(psi_t, copy_then(c, s), copy_then(c, s2))",
        &psi_t,
        &lhs,
        &rhs,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.AlmostSurelyEq.of_comp
#[test]
fn witness_almost_surely_eq_of_comp() -> Result<()> {
    let (t, sp) = (obj_t()?, obj_s()?);
    let (hot, psi_t, c, s, s2) = (hot()?, psi_t()?, c()?, s()?, s2()?);
    assert_as_equal("as_equal(hot ≫ c, s, s2)", &hot.compose(&c)?, &s, &s2, true);
    assert_as_equal(
        "as_equal(psi_t ≫ c, s, s2)",
        &psi_t.compose(&c)?,
        &s,
        &s2,
        false,
    );
    let c_s = c.compose(&s)?;
    let c_s2 = c.compose(&s2)?;
    assert_kernel(
        "c ≫ s",
        &c_s,
        &lit(
            t.clone(),
            sp.clone(),
            &[&[r(2, 3), r(1, 3)], &[r(1, 4), r(3, 4)]],
        )?,
    );
    assert_kernel(
        "c ≫ s2",
        &c_s2,
        &lit(t, sp, &[&[r(2, 3), r(1, 3)], &[r(5, 8), r(3, 8)]])?,
    );
    assert_as_equal("as_equal(hot, c ≫ s, c ≫ s2)", &hot, &c_s, &c_s2, true);
    assert_as_equal("as_equal(psi_t, c ≫ s, c ≫ s2)", &psi_t, &c_s, &c_s2, false);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsAlmostSurelyDeterministic.comp
#[test]
fn witness_is_almost_surely_deterministic_comp() -> Result<()> {
    let (hot, k, m) = (hot()?, k()?, m()?);
    let k_m = k.compose(&m)?;
    assert_kernel(
        "k ≫ m",
        &k_m,
        &lit(
            obj_t()?,
            obj_t()?,
            &[&[r(1, 1), r(0, 1)], &[r(5, 8), r(3, 8)]],
        )?,
    );
    assert_as_deterministic("is_as_deterministic(hot, k)", &hot, &k, true);
    assert_as_deterministic(
        "is_as_deterministic(hot ≫ k, m)",
        &hot.compose(&k)?,
        &m,
        true,
    );
    assert_as_deterministic("is_as_deterministic(hot, k ≫ m)", &hot, &k_m, true);
    assert_as_deterministic("is_as_deterministic(psi_t, k ≫ m)", &psi_t()?, &k_m, false);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.copy_comp_natural_of_relativelyPositive
#[test]
fn witness_copy_comp_natural_of_relatively_positive() -> Result<()> {
    let (c, c2, dd) = (c()?, c2()?, dd()?);
    assert_deterministic("c2 ≫ dd", &c2.compose(&dd)?, true);
    assert_deterministic("c2", &c2, false);
    assert_copy_comp_natural("copy_comp_natural(c2, dd)", &c2, &dd, true);

    let c_dd = c.compose(&dd)?;
    assert_kernel(
        "c ≫ dd",
        &c_dd,
        &lit(
            obj_t()?,
            obj_s()?,
            &[&[r(1, 1), r(0, 1)], &[r(1, 4), r(3, 4)]],
        )?,
    );
    assert_deterministic("c ≫ dd", &c_dd, false);
    assert_copy_comp_natural("copy_comp_natural(c, dd)", &c, &dd, false);
    Ok(())
}

/// THEOREM_MAP: FinStoch.exists_deterministic_comp_not_deterministic
#[test]
fn witness_exists_deterministic_comp_not_deterministic() -> Result<()> {
    let coin = coin()?;
    let del = Kernel::del(&obj_b()?)?;
    assert_deterministic("coin ≫ ε[B]", &coin.compose(&del)?, true);
    assert_deterministic("coin", &coin, false);
    assert_copy_comp_natural("copy_comp_natural(coin, ε[B])", &coin, &del, true);
    Ok(())
}

/// `is_deterministic` returns `false` on `c ≫ g0` and `copy_comp_natural`
/// returns `true` on `(c, g0)`. `is_as_deterministic` returns `false` on
/// `c ≫ g0` with respect to `psi_t` and `copy_comp_natural_as` returns `true`
/// on `(psi_t, c, g0)`.
#[test]
fn copy_comp_natural_and_its_as_form_hold_on_c_g0_where_the_composite_is_not_deterministic()
-> Result<()> {
    let (psi_t, c, g0) = (psi_t()?, c()?, g0()?);
    let c_g0 = c.compose(&g0)?;
    assert_deterministic("c ≫ g0", &c_g0, false);
    assert_copy_comp_natural("copy_comp_natural(c, g0)", &c, &g0, true);
    assert_as_deterministic("is_as_deterministic(psi_t, c ≫ g0)", &psi_t, &c_g0, false);
    assert_copy_comp_natural_as("copy_comp_natural_as(psi_t, c, g0)", &psi_t, &c, &g0, true);
    Ok(())
}

/// `is_as_deterministic` on `c ≫ dd` and `copy_comp_natural_as` on `(c, dd)`
/// return `true` with respect to `hot` and `false` with respect to `psi_t`
/// (Fritz 2020, Def. 13.16).
#[test]
fn copy_comp_natural_as_on_c_dd_at_hot_and_psi_t() -> Result<()> {
    let (hot, psi_t, c, dd) = (hot()?, psi_t()?, c()?, dd()?);
    let c_dd = c.compose(&dd)?;
    assert_as_deterministic("is_as_deterministic(hot, c ≫ dd)", &hot, &c_dd, true);
    assert_copy_comp_natural_as("copy_comp_natural_as(hot, c, dd)", &hot, &c, &dd, true);
    assert_as_deterministic("is_as_deterministic(psi_t, c ≫ dd)", &psi_t, &c_dd, false);
    assert_copy_comp_natural_as("copy_comp_natural_as(psi_t, c, dd)", &psi_t, &c, &dd, false);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsAlmostSurelyDeterministic.of_comp
#[test]
fn witness_is_almost_surely_deterministic_of_comp() -> Result<()> {
    let (hot, c, g2) = (hot()?, c()?, g2()?);
    let c_g2 = c.compose(&g2)?;
    assert_kernel(
        "c ≫ g2",
        &c_g2,
        &lit(
            obj_t()?,
            obj_s()?,
            &[&[r(1, 1), r(0, 1)], &[r(5, 8), r(3, 8)]],
        )?,
    );
    assert_as_deterministic("is_as_deterministic(hot, c)", &hot, &c, false);
    assert_as_deterministic("is_as_deterministic(hot, c ≫ g2)", &hot, &c_g2, true);
    assert_as_deterministic(
        "is_as_deterministic(hot ≫ c, g2)",
        &hot.compose(&c)?,
        &g2,
        true,
    );
    assert_deterministic("g2", &g2, false);
    Ok(())
}

/// `e ≫ e_inv` is the identity on `S`, `e_inv ≫ e` is the identity on `T`,
/// and `is_deterministic` returns `true` on `e` and on `e_inv` (Fritz 2020,
/// Remark 11.28).
/// THEOREM_MAP: mathlib:CategoryTheory.PositiveCategory.instDeterministicOfIsIso
#[test]
fn mutually_inverse_kernels_are_deterministic() -> Result<()> {
    let (e, e_inv) = (e()?, e_inv()?);
    assert_kernel(
        "e ≫ e_inv",
        &e.compose(&e_inv)?,
        &Kernel::identity(&obj_s()?)?,
    );
    assert_kernel(
        "e_inv ≫ e",
        &e_inv.compose(&e)?,
        &Kernel::identity(&obj_t()?)?,
    );
    assert_deterministic("e", &e, true);
    assert_deterministic("e_inv", &e_inv, true);
    Ok(())
}

/// THEOREM_MAP: FinStoch.exists_almostSurelyEq_comp_ne
#[test]
fn witness_exists_almost_surely_eq_comp_ne() -> Result<()> {
    let (s, s2) = (s()?, s2()?);
    assert_as_equal(
        "as_equal(hot ≫ c, s, s2)",
        &hot()?.compose(&c()?)?,
        &s,
        &s2,
        true,
    );
    assert_differs("s against s2", &s, &s2);
    Ok(())
}
