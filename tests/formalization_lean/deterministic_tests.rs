//! Witnesses of the `Deterministic` instances of
//! `Peluang.Deterministic.Lemmas` at the running example: `is_deterministic` and
//! the literal of each morphism. Also the panic message of
//! `assert_deterministic` when `is_deterministic` returns an error.

use std::panic::{AssertUnwindSafe, catch_unwind};

use peluang::deterministic::is_deterministic;
use peluang::error::{Error, Result};
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::Tensor;
use peluang::prob::Exact;

use crate::fixtures::{
    assert_deterministic, assert_kernel, d, e, lit, obj_s, obj_t, obj_w, points, r, s,
};

/// `assert_deterministic` on the point mass `I → [2^19]`, where building
/// `Δ[2^19]` returns `Error::TooLarge` for `2^19 * 2^38` weights, panics
/// with `is_deterministic(<name>) on ` first and
/// `: expected Ok(<expected>), observed Err(<the error>)` last, for both
/// expected values.
#[test]
fn assert_deterministic_names_the_call_and_expected_value_on_an_error() -> Result<()> {
    let wide = Kernel::<Exact>::from_fn(FinObj::unit(), FinObj::new(1 << 19), |_| 0)?;
    let got = is_deterministic(&wide);
    assert!(
        matches!(
            got,
            Err(Error::TooLarge {
                fst: 524_288,
                snd: 274_877_906_944,
                source: Some(_)
            })
        ),
        "is_deterministic(I → [2^19]): expected Err(TooLarge {{ fst: 524288, snd: 274877906944, \
         source: Some(_) }}), observed {got:?}"
    );
    let err = got.err().map(|e| format!("{e:?}")).unwrap_or_default();
    for expected in [true, false] {
        let message = match catch_unwind(AssertUnwindSafe(|| {
            assert_deterministic("wide", &wide, expected);
        })) {
            Ok(()) => String::from("(no panic)"),
            Err(payload) => payload
                .downcast::<String>()
                .map_or_else(|_| String::from("(non-String payload)"), |m| *m),
        };
        let (head, tail) = (
            "is_deterministic(wide) on ",
            format!(": expected Ok({expected}), observed Err({err})"),
        );
        let shown = |m: &str| {
            let cut = m.char_indices().rev().nth(199).map_or(0, |(i, _)| i);
            format!(
                "{:?} … {:?}",
                m.chars().take(40).collect::<String>(),
                &m[cut..]
            )
        };
        assert!(
            message.starts_with(head) && message.ends_with(&tail),
            "assert_deterministic(wide, {expected}): expected a panic message starting {head:?} and \
             ending {tail:?}, observed {}",
            shown(&message)
        );
    }
    Ok(())
}

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
    assert_deterministic("Δ[T]", &copy, true);
    Ok(())
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
    assert_deterministic("ε[W]", &del, true);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instTensorHom
#[test]
fn witness_inst_tensor_hom() -> Result<()> {
    let (w, t, sp) = (obj_w()?, obj_t()?, obj_s()?);
    let tensor = d()?.tensor(&e()?)?;
    let expected = points(w.tensor(&sp)?, sp.tensor(&t)?, &[0, 1, 2, 3, 2, 3])?;
    assert_kernel("d ⊗ₘ e", &tensor, &expected);
    assert_deterministic("d ⊗ₘ e", &tensor, true);
    assert_deterministic("d ⊗ₘ s", &d()?.tensor(&s()?)?, false);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instWhiskerRight
#[test]
fn witness_inst_whisker_right() -> Result<()> {
    let (w, t, sp) = (obj_w()?, obj_t()?, obj_s()?);
    let whiskered = Kernel::whisker_right(&d()?, &t)?;
    let expected = points(w.tensor(&t)?, sp.tensor(&t)?, &[0, 1, 2, 3, 2, 3])?;
    assert_kernel("d ▷ T", &whiskered, &expected);
    assert_deterministic("d ▷ T", &whiskered, true);
    assert_deterministic("s ▷ T", &Kernel::whisker_right(&s()?, &t)?, false);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instWhiskerLeft
#[test]
fn witness_inst_whisker_left() -> Result<()> {
    let (w, t, sp) = (obj_w()?, obj_t()?, obj_s()?);
    let whiskered = Kernel::whisker_left(&t, &d()?)?;
    let expected = points(t.tensor(&w)?, t.tensor(&sp)?, &[0, 1, 1, 2, 3, 3])?;
    assert_kernel("T ◁ d", &whiskered, &expected);
    assert_deterministic("T ◁ d", &whiskered, true);
    assert_deterministic("T ◁ s", &Kernel::whisker_left(&t, &s()?)?, false);
    Ok(())
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
    assert_deterministic("α_ T S W", &associator, true);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instLeftUnitor
#[test]
fn witness_inst_left_unitor() -> Result<()> {
    let w = obj_w()?;
    let expected = points(obj_w()?, obj_w()?, &[0, 1, 2])?;
    let unitor = Kernel::left_unitor(&w)?;
    assert_kernel("λ_ W", &unitor, &expected);
    assert_kernel("𝟙 W", &Kernel::identity(&w)?, &expected);
    assert_deterministic("λ_ W", &unitor, true);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instRightUnitor
#[test]
fn witness_inst_right_unitor() -> Result<()> {
    let w = obj_w()?;
    let expected = points(obj_w()?, obj_w()?, &[0, 1, 2])?;
    let unitor = Kernel::right_unitor(&w)?;
    assert_kernel("ρ_ W", &unitor, &expected);
    assert_kernel("𝟙 W", &Kernel::identity(&w)?, &expected);
    assert_deterministic("ρ_ W", &unitor, true);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.Deterministic.instBraiding
#[test]
fn witness_inst_braiding() -> Result<()> {
    let (t, sp) = (obj_t()?, obj_s()?);
    let swap = Kernel::swap(&t, &sp)?;
    let expected = points(t.tensor(&sp)?, sp.tensor(&t)?, &[0, 2, 1, 3])?;
    assert_kernel("β_ T S", &swap, &expected);
    assert_deterministic("β_ T S", &swap, true);

    let w = obj_w()?;
    let swap = Kernel::swap(&w, &sp)?;
    let expected = points(w.tensor(&sp)?, sp.tensor(&w)?, &[0, 3, 1, 4, 2, 5])?;
    assert_kernel("β_ W S", &swap, &expected);
    assert_deterministic("β_ W S", &swap, true);
    Ok(())
}
