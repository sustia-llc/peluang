//! Witnesses of the `Deterministic` instances of
//! `Peluang.Deterministic.Lemmas` at the running example: `is_deterministic` and
//! the literal of each morphism.

use peluang::error::Result;
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::Tensor;

use crate::fixtures::{
    assert_deterministic, assert_kernel, d, e, lit, obj_s, obj_t, obj_w, points, r, s,
};

/// THEOREM_MAP: CategoryTheory.Deterministic.instCopy
#[test]
fn witness_inst_copy() -> Result<()> {
    let t = obj_t()?;
    let copy = Kernel::copy(&t)?;
    let expected = lit(
        obj_t()?,
        t.tensor(&t)?,
        &[
            &[r(1, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(1, 1)],
        ],
    )?;
    assert_kernel("Δ[T]", &copy, &expected);
    assert_deterministic("Δ[T]", &copy, true)
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instDiscard
#[test]
fn witness_inst_discard() -> Result<()> {
    let w = obj_w()?;
    let del = Kernel::del(&w)?;
    let expected = lit(
        obj_w()?,
        FinObj::unit(),
        &[&[r(1, 1)], &[r(1, 1)], &[r(1, 1)]],
    )?;
    assert_kernel("ε[W]", &del, &expected);
    assert_deterministic("ε[W]", &del, true)
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instTensorHom
#[test]
fn witness_inst_tensor_hom() -> Result<()> {
    let (w, t, sp) = (obj_w()?, obj_t()?, obj_s()?);
    let tensor = d()?.tensor(&e()?)?;
    let expected = points(w.tensor(&sp)?, sp.tensor(&t)?, &[0, 1, 2, 3, 2, 3])?;
    assert_kernel("d ⊗ₘ e", &tensor, &expected);
    assert_deterministic("d ⊗ₘ e", &tensor, true)?;
    assert_deterministic("d ⊗ₘ s", &d()?.tensor(&s()?)?, false)
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instWhiskerRight
#[test]
fn witness_inst_whisker_right() -> Result<()> {
    let (w, t, sp) = (obj_w()?, obj_t()?, obj_s()?);
    let whiskered = Kernel::whisker_right(&d()?, &t)?;
    let expected = points(w.tensor(&t)?, sp.tensor(&t)?, &[0, 1, 2, 3, 2, 3])?;
    assert_kernel("d ▷ T", &whiskered, &expected);
    assert_deterministic("d ▷ T", &whiskered, true)?;
    assert_deterministic("s ▷ T", &Kernel::whisker_right(&s()?, &t)?, false)
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instWhiskerLeft
#[test]
fn witness_inst_whisker_left() -> Result<()> {
    let (w, t, sp) = (obj_w()?, obj_t()?, obj_s()?);
    let whiskered = Kernel::whisker_left(&t, &d()?)?;
    let expected = points(t.tensor(&w)?, t.tensor(&sp)?, &[0, 1, 1, 2, 3, 3])?;
    assert_kernel("T ◁ d", &whiskered, &expected);
    assert_deterministic("T ◁ d", &whiskered, true)?;
    assert_deterministic("T ◁ s", &Kernel::whisker_left(&t, &s()?)?, false)
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instAssociator
#[test]
fn witness_inst_associator() -> Result<()> {
    let (t, sp, w) = (obj_t()?, obj_s()?, obj_w()?);
    let flat = t.tensor(&sp)?.tensor(&w)?;
    let outputs: Vec<usize> = (0..12).collect();
    let expected = points(flat.clone(), flat.clone(), &outputs)?;
    let associator = Kernel::associator(&t, &sp, &w)?;
    assert_kernel("α_ T S W", &associator, &expected);
    assert_kernel("𝟙 (T ⊗ S ⊗ W)", &Kernel::identity(&flat)?, &expected);
    assert_deterministic("α_ T S W", &associator, true)
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instLeftUnitor
#[test]
fn witness_inst_left_unitor() -> Result<()> {
    let w = obj_w()?;
    let expected = points(obj_w()?, obj_w()?, &[0, 1, 2])?;
    let unitor = Kernel::left_unitor(&w)?;
    assert_kernel("λ_ W", &unitor, &expected);
    assert_kernel("𝟙 W", &Kernel::identity(&w)?, &expected);
    assert_deterministic("λ_ W", &unitor, true)
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instRightUnitor
#[test]
fn witness_inst_right_unitor() -> Result<()> {
    let w = obj_w()?;
    let expected = points(obj_w()?, obj_w()?, &[0, 1, 2])?;
    let unitor = Kernel::right_unitor(&w)?;
    assert_kernel("ρ_ W", &unitor, &expected);
    assert_kernel("𝟙 W", &Kernel::identity(&w)?, &expected);
    assert_deterministic("ρ_ W", &unitor, true)
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instBraiding
#[test]
fn witness_inst_braiding() -> Result<()> {
    let (t, sp) = (obj_t()?, obj_s()?);
    let swap = Kernel::swap(&t, &sp)?;
    let expected = points(t.tensor(&sp)?, sp.tensor(&t)?, &[0, 2, 1, 3])?;
    assert_kernel("β_ T S", &swap, &expected);
    assert_deterministic("β_ T S", &swap, true)?;

    let w = obj_w()?;
    let swap = Kernel::swap(&w, &sp)?;
    let expected = points(w.tensor(&sp)?, sp.tensor(&w)?, &[0, 3, 1, 4, 2, 5])?;
    assert_kernel("β_ W S", &swap, &expected);
    assert_deterministic("β_ W S", &swap, true)
}
