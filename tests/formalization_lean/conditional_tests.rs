//! Witnesses of the theorems of `Peluang.AlmostSure`,
//! `Peluang.Instances.FinStoch.AlmostSure` and
//! `Peluang.Instances.FinStoch.Conditional` at the running example, and the
//! rejections of `as_equal` and `conditional`.

use peluang::almost_sure::as_equal;
use peluang::conditional::conditional;
use peluang::error::{Error, Result};
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::{Compose, Tensor};
use peluang::prob::Exact;

use crate::fixtures::{assert_kernel, c, e, f, lit, obj_s, obj_t, obj_w, psi_t, r, s, show};

/// `q : I → W`, `(1/2, 1/2, 0)`: the column of `c` at hot.
fn q() -> Result<Kernel<Exact>> {
    Kernel::state(obj_w()?, vec![r(1, 2), r(1, 2), r(0, 1)])
}

/// `s` with the column at rainy replaced by `rainy`.
fn s_with_rainy(rainy: [Exact; 2]) -> Result<Kernel<Exact>> {
    lit(
        obj_w()?,
        obj_s()?,
        &[&[r(1, 3), r(2, 3)], &[r(1, 1), r(0, 1)], &rainy],
    )
}

/// `s'`: `s` with the column at rainy `(1, 0)`.
fn s_prime() -> Result<Kernel<Exact>> {
    s_with_rainy([r(1, 1), r(0, 1)])
}

/// `s''`: `s` with the column at sunny `(1, 0)`.
fn s_double_prime() -> Result<Kernel<Exact>> {
    lit(
        obj_w()?,
        obj_s()?,
        &[
            &[r(1, 1), r(0, 1)],
            &[r(1, 1), r(0, 1)],
            &[r(0, 1), r(1, 1)],
        ],
    )
}

/// `psi_t ≫ Δ[T] ≫ (T ◁ c) : I → T ⊗ W`.
fn joint() -> Result<Kernel<Exact>> {
    let t = obj_t()?;
    psi_t()?
        .compose(&Kernel::copy(&t)?)?
        .compose(&Kernel::whisker_left(&t, &c()?)?)
}

/// `p ≫ Δ[X] ≫ (Δ[X] ▷ X) ≫ ((f ▷ X) ⊗ₘ g)` with `X` the domain of `f`.
fn copy_tensor(p: &Kernel<Exact>, f: &Kernel<Exact>, g: &Kernel<Exact>) -> Result<Kernel<Exact>> {
    let x = f.domain();
    p.compose(&Kernel::copy(x)?)?
        .compose(&Kernel::whisker_right(&Kernel::copy(x)?, x)?)?
        .compose(&Kernel::whisker_right(f, x)?.tensor(g)?)
}

/// Asserts `as_equal(p, f, g) == expected`, naming the call `name`.
#[track_caller]
fn assert_as_equal(
    name: &str,
    p: &Kernel<Exact>,
    f: &Kernel<Exact>,
    g: &Kernel<Exact>,
    expected: bool,
) -> Result<()> {
    let observed = as_equal(p, f, g)?;
    assert_eq!(
        observed,
        expected,
        "{name} with f = {}, g = {}: expected {expected}, observed {observed}",
        show(f),
        show(g)
    );
    Ok(())
}

/// Asserts the column of `k` at input `x` equals `expected`, naming `side`.
#[track_caller]
fn assert_column(side: &str, k: &Kernel<Exact>, x: usize, expected: &[Exact]) {
    let fmt = |column: &[Exact]| {
        let weights: Vec<String> = column.iter().map(ToString::to_string).collect();
        format!("({})", weights.join(", "))
    };
    let observed = k.column(x);
    assert!(
        observed == Some(expected),
        "{side}: expected column {x} = {}, observed {} in {}",
        fmt(expected),
        observed.map_or_else(|| "none".to_owned(), fmt),
        show(k)
    );
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.almostSurelyEq_equivalence
#[test]
fn witness_almost_surely_eq_equivalence() -> Result<()> {
    let (q, s, s1) = (q()?, s()?, s_prime()?);
    let s2 = s_with_rainy([r(1, 2), r(1, 2)])?;
    assert_as_equal("refl: as_equal(q, s, s)", &q, &s, &s, true)?;
    let forward = as_equal(&q, &s1, &s)?;
    let backward = as_equal(&q, &s, &s1)?;
    assert!(
        forward && backward,
        "symm: expected as_equal(q, s', s) = as_equal(q, s, s') = true, observed {forward} and {backward}"
    );
    assert_as_equal("trans: as_equal(q, s, s')", &q, &s, &s1, true)?;
    assert_as_equal("trans: as_equal(q, s', s2)", &q, &s1, &s2, true)?;
    assert_as_equal("trans: as_equal(q, s, s2)", &q, &s, &s2, true)?;
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.AlmostSurelyEq.comp
#[test]
fn witness_almost_surely_eq_comp() -> Result<()> {
    let (q, s, s1, e) = (q()?, s()?, s_prime()?, e()?);
    assert_as_equal("as_equal(q, s', s)", &q, &s1, &s, true)?;
    assert_as_equal(
        "as_equal(q, s' ≫ e, s ≫ e)",
        &q,
        &s1.compose(&e)?,
        &s.compose(&e)?,
        true,
    )?;
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.AlmostSurelyEq.copy_tensorHom
#[test]
fn witness_almost_surely_eq_copy_tensor_hom() -> Result<()> {
    let (q, s, s1, s2) = (q()?, s()?, s_prime()?, s_double_prime()?);
    let (w, sp) = (obj_w()?, obj_s()?);
    let (on, off, zero) = ([r(1, 18), r(1, 9)], [r(1, 9), r(2, 9)], r(0, 1));
    let expected = Kernel::state(
        sp.tensor(&w)?.tensor(&sp)?,
        [
            &on[..],
            &[r(1, 2), zero.clone()],
            &[zero.clone(), zero.clone()],
            &off[..],
            &[zero.clone(), zero.clone()],
            &[zero.clone(), zero],
        ]
        .concat(),
    )?;
    let with_s = copy_tensor(&q, &s, &s)?;
    assert_kernel("q ≫ Δ ≫ (Δ ▷ W) ≫ ((s ▷ W) ⊗ₘ s)", &with_s, &expected);
    assert_kernel(
        "q ≫ Δ ≫ (Δ ▷ W) ≫ ((s' ▷ W) ⊗ₘ s')",
        &copy_tensor(&q, &s1, &s1)?,
        &with_s,
    );
    let control = copy_tensor(&q, &s2, &s2)?;
    assert!(
        control != with_s,
        "control: expected q ≫ Δ ≫ (Δ ▷ W) ≫ ((s'' ▷ W) ⊗ₘ s'') != {}, observed equal",
        show(&with_s)
    );
    Ok(())
}

/// THEOREM_MAP: FinStoch.almostSurelyEq_iff
#[test]
fn witness_almost_surely_eq_iff() -> Result<()> {
    let (q, s) = (q()?, s()?);
    assert_as_equal("as_equal(q, s', s)", &q, &s_prime()?, &s, true)?;
    assert_as_equal("as_equal(q, s'', s)", &q, &s_double_prime()?, &s, false)?;
    Ok(())
}

/// THEOREM_MAP: FinStoch.copy_comp_whiskerRight_mass
#[test]
fn witness_copy_comp_whisker_right_mass() -> Result<()> {
    let w = obj_w()?;
    let expected = Kernel::state(
        obj_s()?.tensor(&w)?,
        vec![r(1, 6), r(1, 2), r(0, 1), r(1, 3), r(0, 1), r(0, 1)],
    )?;
    let observed = q()?
        .compose(&Kernel::copy(&w)?)?
        .compose(&Kernel::whisker_right(&s()?, &w)?)?;
    assert_kernel("q ≫ Δ[W] ≫ (s ▷ W)", &observed, &expected);
    Ok(())
}

/// THEOREM_MAP: FinStoch.marginalFst_mass
#[test]
fn witness_marginal_fst_mass() -> Result<()> {
    let observed = f()?.marginal_fst(&obj_w()?, &obj_s()?)?;
    assert_kernel("marginalFst f", &observed, &c()?);
    Ok(())
}

/// THEOREM_MAP: FinStoch.isConditional_cond
#[test]
fn witness_is_conditional_cond() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);

    let joint = joint()?;
    let joint_literal = Kernel::state(
        t.tensor(&w)?,
        vec![r(1, 10), r(1, 10), r(0, 1), r(0, 1), r(1, 5), r(3, 5)],
    )?;
    assert_kernel("psi_t ≫ Δ[T] ≫ (T ◁ c)", &joint, &joint_literal);
    assert_column(
        "(a) cond(joint) at (cold, unit)",
        &conditional(&joint, &t, &w)?,
        1,
        &[r(0, 1), r(1, 4), r(3, 4)],
    );

    let f = f()?;
    let cond = conditional(&f, &w, &sp)?;
    let composite = Kernel::copy(&t)?
        .compose(&Kernel::whisker_right(&f.marginal_fst(&w, &sp)?, &t)?)?
        .compose(&Kernel::whisker_right(&Kernel::copy(&w)?, &t)?)?
        .compose(&Kernel::associator(&w, &w, &t)?)?
        .compose(&Kernel::whisker_left(&w, &cond)?)?;
    assert_kernel(
        "(b) Δ[T] ≫ (marginalFst f ▷ T) ≫ (Δ[W] ▷ T) ≫ α ≫ (W ◁ cond f)",
        &composite,
        &f,
    );

    let uniform = [r(1, 2), r(1, 2)];
    assert_column("(c) cond(f) at (sunny, cold)", &cond, 1, &uniform);
    assert_column("(c) cond(f) at (rainy, hot)", &cond, 4, &uniform);
    Ok(())
}

/// THEOREM_MAP: FinStoch.instHasConditionals
#[test]
fn witness_has_conditionals() -> Result<()> {
    let (t, w, sp, empty) = (obj_t()?, obj_w()?, obj_s()?, FinObj::new(0));
    let empty_s = Kernel::<Exact>::new(empty.clone(), w.tensor(&sp)?, Vec::new())?;
    let empty_empty = Kernel::<Exact>::new(empty.clone(), w.tensor(&empty)?, Vec::new())?;
    for (name, k, x, y, a) in [
        ("f", f()?, &w, &sp, &t),
        ("joint", joint()?, &t, &w, &FinObj::unit()),
        ("0 → W ⊗ S", empty_s, &w, &sp, &empty),
        ("0 → W ⊗ 0", empty_empty, &w, &empty, &empty),
    ] {
        let got = conditional(&k, x, y);
        let dom = x.tensor(a)?;
        assert!(
            matches!(&got, Ok(g) if g.domain() == &dom && g.codomain() == y),
            "conditional({name}): expected Ok of a kernel {dom:?} → {y:?}, observed {got:?}"
        );
    }
    Ok(())
}

#[test]
fn as_equal_rejects_mismatched_shapes() -> Result<()> {
    let (q, s, e) = (q()?, s()?, e()?);
    let got = as_equal(&q, &e, &e);
    assert!(
        matches!(&got, Err(Error::NotComposable { codomain, domain })
            if *codomain == obj_w()? && *domain == obj_s()?),
        "p into S-domain f: expected NotComposable {{ codomain: W, domain: S }}, observed {got:?}"
    );
    let got = as_equal(&q, &e, &s);
    assert!(
        matches!(&got, Err(Error::NotComposable { codomain, domain })
            if *codomain == obj_w()? && *domain == obj_s()?),
        "composability checked before the f/g shape: expected NotComposable, observed {got:?}"
    );
    let se = s.compose(&e)?;
    let s_shape = (obj_w()?, obj_s()?);
    for (name, g, g_shape) in [
        ("codomain differs", &se, (obj_w()?, obj_t()?)),
        ("domain differs", &e, (obj_s()?, obj_t()?)),
    ] {
        let got = as_equal(&q, &s, g);
        assert!(
            matches!(&got, Err(Error::NotParallel { fst, snd })
                if **fst == s_shape && **snd == g_shape),
            "{name}: expected NotParallel {{ fst: {s_shape:?}, snd: {g_shape:?} }}, observed {got:?}"
        );
    }
    Ok(())
}

#[test]
fn conditional_rejects_a_wrong_split() -> Result<()> {
    let (w, sp) = (obj_w()?, obj_s()?);
    let f = f()?;
    let cod = w.tensor(&sp)?;
    for (name, x, y) in [
        ("factors swapped", &sp, &w),
        ("mismatch only on y", &w, &w),
        ("x is the whole codomain", &cod, &FinObj::new(1)),
    ] {
        let got = conditional(&f, x, y);
        assert!(
            matches!(&got, Err(Error::NotATensor { codomain, fst, snd })
                if *codomain == cod && fst == x && snd == y),
            "{name}: expected NotATensor {{ codomain: {cod:?}, fst: {x:?}, snd: {y:?} }}, observed {got:?}"
        );
    }
    Ok(())
}
