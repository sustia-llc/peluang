//! Witnesses of `Peluang.Causal`, `Peluang.Positive` and
//! `Peluang.Instances.FinStoch.InformationFlow` at the running example:
//! `copy_then`, `copy_comp_natural` and `copy_comp_natural_as` beside
//! `as_equal`, `is_deterministic` and `is_as_deterministic`. Also the
//! `Error::NotComposable` of the three functions.

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
    copy_whisker, dd, e, e_inv, g2, hot, k, lit, m, obj_b, obj_s, obj_t, obj_w, psi_t, r, s, s2,
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
    let c_s = c()?.compose(&s()?)?;
    let c_s2 = c()?.compose(&s2()?)?;
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
    assert_as_equal("as_equal(hot, c ≫ s, c ≫ s2)", &hot()?, &c_s, &c_s2, true);
    assert_as_equal(
        "as_equal(psi_t, c ≫ s, c ≫ s2)",
        &psi_t()?,
        &c_s,
        &c_s2,
        false,
    );
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

/// `is_as_deterministic` on `c ≫ dd` and `copy_comp_natural_as` on `(c, dd)`
/// return `true` with respect to `hot` and `false` with respect to `psi_t`
/// (Fritz 2020, Def. 13.16).
#[test]
fn copy_comp_natural_as_holds_exactly_where_the_composite_is_as_deterministic() -> Result<()> {
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
    assert_as_deterministic(
        "is_as_deterministic(hot, c ≫ g2)",
        &hot,
        &c.compose(&g2)?,
        true,
    );
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
