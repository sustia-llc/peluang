//! Witnesses of the marginal theorems of `Peluang.Markov.Derived` at the
//! running example: each side of a theorem equals a literal.

use peluang::error::Result;
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::{Compose, Tensor};
use peluang::prob::Exact;

use crate::fixtures::{
    assert_kernel, c, f, h, j, lit, obj_s, obj_t, obj_w, points, psi_t, r, s, show,
};

/// `(1/2, 1/2, 0)`, the column of `c` at hot.
fn c_hot() -> [Exact; 3] {
    [r(1, 2), r(1, 2), r(0, 1)]
}

/// `(0, 1/4, 3/4)`, the column of `c` at cold.
fn c_cold() -> [Exact; 3] {
    [r(0, 1), r(1, 4), r(3, 4)]
}

/// `A ◁ ε[B] ≫ (ρ_ A).hom ≫ g`.
fn discard_snd_then(a: &FinObj, b: &FinObj, g: &Kernel<Exact>) -> Result<Kernel<Exact>> {
    Kernel::whisker_left(a, &Kernel::del(b)?)?
        .compose(&Kernel::right_unitor(a)?)?
        .compose(g)
}

/// `ε[A] ▷ B ≫ (λ_ B).hom ≫ g`.
fn discard_fst_then(a: &FinObj, b: &FinObj, g: &Kernel<Exact>) -> Result<Kernel<Exact>> {
    Kernel::whisker_right(&Kernel::del(a)?, b)?
        .compose(&Kernel::left_unitor(b)?)?
        .compose(g)
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.marginalFst_comp
#[test]
fn witness_marginal_fst_comp() -> Result<()> {
    let (w, sp) = (obj_w()?, obj_s()?);
    let expected = Kernel::state(obj_w()?, vec![r(1, 10), r(3, 10), r(3, 5)])?;
    let lhs = psi_t()?.compose(&f()?)?.marginal_fst(&w, &sp)?;
    let rhs = psi_t()?.compose(&f()?.marginal_fst(&w, &sp)?)?;
    assert_kernel("marginalFst (k ≫ f)", &lhs, &expected);
    assert_kernel("k ≫ marginalFst f", &rhs, &expected);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.marginalSnd_comp
#[test]
fn witness_marginal_snd_comp() -> Result<()> {
    let (w, sp) = (obj_w()?, obj_s()?);
    let expected = Kernel::state(obj_s()?, vec![r(1, 3), r(2, 3)])?;
    let lhs = psi_t()?.compose(&f()?)?.marginal_snd(&w, &sp)?;
    let rhs = psi_t()?.compose(&f()?.marginal_snd(&w, &sp)?)?;
    assert_kernel("marginalSnd (k ≫ f)", &lhs, &expected);
    assert_kernel("k ≫ marginalSnd f", &rhs, &expected);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.marginalFst_copy
#[test]
fn witness_marginal_fst_copy() -> Result<()> {
    let w = obj_w()?;
    let expected = points(obj_w()?, obj_w()?, &[0, 1, 2])?;
    let lhs = Kernel::<Exact>::copy(&w)?.marginal_fst(&w, &w)?;
    let rhs = Kernel::identity(&w)?;
    assert_kernel("marginalFst Δ[W]", &lhs, &expected);
    assert_kernel("𝟙 W", &rhs, &expected);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.marginalSnd_copy
#[test]
fn witness_marginal_snd_copy() -> Result<()> {
    let w = obj_w()?;
    let expected = points(obj_w()?, obj_w()?, &[0, 1, 2])?;
    let lhs = Kernel::<Exact>::copy(&w)?.marginal_snd(&w, &w)?;
    let rhs = Kernel::identity(&w)?;
    assert_kernel("marginalSnd Δ[W]", &lhs, &expected);
    assert_kernel("𝟙 W", &rhs, &expected);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.MarkovCategory.marginalFst_copy_comp_tensorHom
#[test]
fn witness_marginal_fst_copy_comp_tensor_hom() -> Result<()> {
    let (w, sp) = (obj_w()?, obj_s()?);
    let joint = Kernel::copy(&obj_t()?)?.compose(&c()?.tensor(&h()?)?)?;
    let expected = lit(obj_t()?, obj_w()?, &[&c_hot(), &c_cold()])?;
    assert_kernel("Δ[T] ≫ (c ⊗ₘ h)", &joint, &j()?);
    assert_kernel(
        "marginalFst (Δ[T] ≫ (c ⊗ₘ h))",
        &joint.marginal_fst(&w, &sp)?,
        &expected,
    );
    assert_kernel("g", &c()?, &expected);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.MarkovCategory.marginalSnd_copy_comp_tensorHom
#[test]
fn witness_marginal_snd_copy_comp_tensor_hom() -> Result<()> {
    let (w, sp) = (obj_w()?, obj_s()?);
    let joint = Kernel::copy(&obj_t()?)?.compose(&c()?.tensor(&h()?)?)?;
    let expected = lit(
        obj_t()?,
        obj_s()?,
        &[&[r(2, 3), r(1, 3)], &[r(1, 4), r(3, 4)]],
    )?;
    assert_kernel("Δ[T] ≫ (c ⊗ₘ h)", &joint, &j()?);
    assert_kernel(
        "marginalSnd (Δ[T] ≫ (c ⊗ₘ h))",
        &joint.marginal_snd(&w, &sp)?,
        &expected,
    );
    assert_kernel("h", &h()?, &expected);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.MarkovCategory.marginalFst_tensorHom
#[test]
fn witness_marginal_fst_tensor_hom() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (hot, cold) = (c_hot(), c_cold());
    let expected = lit(
        t.tensor(&w)?,
        obj_w()?,
        &[&hot, &hot, &hot, &cold, &cold, &cold],
    )?;
    let lhs = c()?.tensor(&s()?)?.marginal_fst(&w, &sp)?;
    let rhs = discard_snd_then(&t, &w, &c()?)?;
    assert_kernel("marginalFst (c ⊗ₘ s)", &lhs, &expected);
    assert_kernel("T ◁ ε[W] ≫ ρ ≫ c", &rhs, &expected);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.MarkovCategory.marginalSnd_tensorHom
#[test]
fn witness_marginal_snd_tensor_hom() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (sunny, cloudy, rainy) = ([r(1, 3), r(2, 3)], [r(1, 1), r(0, 1)], [r(0, 1), r(1, 1)]);
    let expected = lit(
        t.tensor(&w)?,
        obj_s()?,
        &[&sunny, &cloudy, &rainy, &sunny, &cloudy, &rainy],
    )?;
    let lhs = c()?.tensor(&s()?)?.marginal_snd(&w, &sp)?;
    let rhs = discard_fst_then(&t, &w, &s()?)?;
    assert_kernel("marginalSnd (c ⊗ₘ s)", &lhs, &expected);
    assert_kernel("ε[T] ▷ W ≫ λ ≫ s", &rhs, &expected);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.marginalFst_whiskerRight
#[test]
fn witness_marginal_fst_whisker_right() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (hot, cold) = (c_hot(), c_cold());
    let expected = lit(t.tensor(&sp)?, obj_w()?, &[&hot, &hot, &cold, &cold])?;
    let lhs = Kernel::whisker_right(&c()?, &sp)?.marginal_fst(&w, &sp)?;
    let rhs = discard_snd_then(&t, &sp, &c()?)?;
    assert_kernel("marginalFst (c ▷ S)", &lhs, &expected);
    assert_kernel("T ◁ ε[S] ≫ ρ ≫ c", &rhs, &expected);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.marginalSnd_whiskerLeft
#[test]
fn witness_marginal_snd_whisker_left() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (hot, cold) = (c_hot(), c_cold());
    let expected = lit(sp.tensor(&t)?, obj_w()?, &[&hot, &cold, &hot, &cold])?;
    let lhs = Kernel::whisker_left(&sp, &c()?)?.marginal_snd(&sp, &w)?;
    let rhs = discard_fst_then(&sp, &t, &c()?)?;
    assert_kernel("marginalSnd (S ◁ c)", &lhs, &expected);
    assert_kernel("ε[S] ▷ T ≫ λ ≫ c", &rhs, &expected);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.MarkovCategory.marginalSnd_whiskerRight
#[test]
fn witness_marginal_snd_whisker_right() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let expected = points(t.tensor(&sp)?, obj_s()?, &[0, 1, 0, 1])?;
    let lhs = Kernel::whisker_right(&c()?, &sp)?.marginal_snd(&w, &sp)?;
    let rhs = Kernel::whisker_right(&Kernel::del(&t)?, &sp)?.compose(&Kernel::left_unitor(&sp)?)?;
    assert_kernel("marginalSnd (c ▷ S)", &lhs, &expected);
    assert_kernel("ε[T] ▷ S ≫ λ", &rhs, &expected);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.MarkovCategory.marginalFst_whiskerLeft
#[test]
fn witness_marginal_fst_whisker_left() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let expected = points(sp.tensor(&t)?, obj_s()?, &[0, 0, 1, 1])?;
    let lhs = Kernel::whisker_left(&sp, &c()?)?.marginal_fst(&sp, &w)?;
    let rhs = Kernel::whisker_left(&sp, &Kernel::del(&t)?)?.compose(&Kernel::right_unitor(&sp)?)?;
    assert_kernel("marginalFst (S ◁ c)", &lhs, &expected);
    assert_kernel("S ◁ ε[T] ≫ ρ", &rhs, &expected);
    Ok(())
}

#[test]
fn marginal_fst_equals_lean_composite() -> Result<()> {
    let (w, sp) = (obj_w()?, obj_s()?);
    let composite = f()?
        .compose(&Kernel::whisker_left(&w, &Kernel::del(&sp)?)?)?
        .compose(&Kernel::right_unitor(&w)?)?;
    let expected = lit(obj_t()?, obj_w()?, &[&c_hot(), &c_cold()])?;
    assert_kernel("f ≫ W ◁ ε[S] ≫ ρ", &composite, &expected);
    assert_kernel("marginal_fst f", &f()?.marginal_fst(&w, &sp)?, &expected);
    Ok(())
}

#[test]
fn marginal_snd_equals_lean_composite() -> Result<()> {
    let (w, sp) = (obj_w()?, obj_s()?);
    let composite = f()?
        .compose(&Kernel::whisker_right(&Kernel::del(&w)?, &sp)?)?
        .compose(&Kernel::left_unitor(&sp)?)?;
    let expected = lit(
        obj_t()?,
        obj_s()?,
        &[&[r(2, 3), r(1, 3)], &[r(1, 4), r(3, 4)]],
    )?;
    assert_kernel("f ≫ ε[W] ▷ S ≫ λ", &composite, &expected);
    assert_kernel("marginal_snd f", &f()?.marginal_snd(&w, &sp)?, &expected);
    Ok(())
}

#[test]
fn f_and_j_differ_with_equal_marginals() -> Result<()> {
    let (w, sp) = (obj_w()?, obj_s()?);
    let (f, j) = (f()?, j()?);
    assert!(
        f != j,
        "expected f != j, observed f = {}, j = {}",
        show(&f),
        show(&j)
    );
    assert_kernel(
        "marginal_fst j",
        &j.marginal_fst(&w, &sp)?,
        &f.marginal_fst(&w, &sp)?,
    );
    assert_kernel(
        "marginal_snd j",
        &j.marginal_snd(&w, &sp)?,
        &f.marginal_snd(&w, &sp)?,
    );
    Ok(())
}
