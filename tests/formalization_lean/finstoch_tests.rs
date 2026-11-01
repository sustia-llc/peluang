//! Witnesses of `Peluang.Instances.FinStoch`: kernels compared with a literal
//! built through `Kernel::new`, and `is_deterministic` at a fixed expected value.

use peluang::deterministic::is_deterministic;
use peluang::error::Result;
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::{Compose, Tensor};
use peluang::prob::{Exact, Prob};

use crate::fixtures::{assert_kernel, c, d, h, lit, obj_s, obj_t, obj_w, points, r, s, show};

/// Whether each entry of `k` is `0` or `1`.
fn entries_are_zero_or_one(k: &Kernel<Exact>) -> bool {
    (0..k.domain().card())
        .flat_map(|x| k.column(x).expect("invariant: x < dom.card() has a column"))
        .all(|weight| *weight == Exact::zero() || *weight == Exact::one())
}

/// THEOREM_MAP: FinStoch.comp_mass
#[test]
fn witness_comp_mass() -> Result<()> {
    assert_kernel("c ≫ s", &c()?.compose(&s()?)?, &h()?);
    Ok(())
}

/// THEOREM_MAP: FinStoch.tensorHom_mass
#[test]
fn witness_tensor_hom_mass() -> Result<()> {
    let expected = lit(
        obj_t()?.tensor(&obj_w()?)?,
        obj_w()?.tensor(&obj_s()?)?,
        &[
            &[r(1, 6), r(1, 3), r(1, 6), r(1, 3), r(0, 1), r(0, 1)],
            &[r(1, 2), r(0, 1), r(1, 2), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(1, 2), r(0, 1), r(1, 2), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(1, 12), r(1, 6), r(1, 4), r(1, 2)],
            &[r(0, 1), r(0, 1), r(1, 4), r(0, 1), r(3, 4), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(1, 4), r(0, 1), r(3, 4)],
        ],
    )?;
    assert_kernel("c ⊗ₘ s", &c()?.tensor(&s()?)?, &expected);
    Ok(())
}

/// THEOREM_MAP: FinStoch.ofFun_id
#[test]
fn witness_of_fun_id() -> Result<()> {
    let w = obj_w()?;
    let expected = points(w.clone(), w.clone(), &[0, 1, 2])?;
    assert_kernel(
        "from_fn on W of the identity",
        &Kernel::from_fn(w.clone(), w.clone(), |x| x)?,
        &expected,
    );
    assert_kernel("𝟙 W", &Kernel::identity(&w)?, &expected);
    Ok(())
}

/// THEOREM_MAP: FinStoch.ofFun_comp
#[test]
fn witness_of_fun_comp() -> Result<()> {
    let (w, sp, t) = (obj_w()?, obj_s()?, obj_t()?);
    let to_s = |x: usize| usize::from(x > 0);
    let to_t = |y: usize| 1 - y;
    let expected = points(w.clone(), t.clone(), &[1, 0, 0])?;
    let composite = Kernel::<Exact>::from_fn(w.clone(), sp.clone(), to_s)?
        .compose(&Kernel::from_fn(sp.clone(), t.clone(), to_t)?)?;
    assert_kernel("from_fn d ≫ from_fn (1 - y)", &composite, &expected);
    assert_kernel(
        "from_fn of the composite",
        &Kernel::from_fn(w, t.clone(), |x| to_t(to_s(x)))?,
        &expected,
    );
    assert_kernel(
        "d ≫ the literal of 1 - y",
        &d()?.compose(&points(sp, t, &[1, 0])?)?,
        &expected,
    );
    Ok(())
}

/// THEOREM_MAP: FinStoch.copy_eq_ofFun
#[test]
fn witness_copy_eq_of_fun() -> Result<()> {
    let t = obj_t()?;
    let tt = t.tensor(&t)?;
    let expected = points(t.clone(), tt.clone(), &[0, 3])?;
    assert_kernel("Δ[T]", &Kernel::copy(&t)?, &expected);
    assert_kernel(
        "from_fn of the diagonal",
        &Kernel::from_fn(t, tt, |x| x * 2 + x)?,
        &expected,
    );
    Ok(())
}

/// THEOREM_MAP: FinStoch.discard_eq_ofFun
#[test]
fn witness_discard_eq_of_fun() -> Result<()> {
    let w = obj_w()?;
    let expected = points(w.clone(), FinObj::unit(), &[0, 0, 0])?;
    assert_kernel("ε[W]", &Kernel::del(&w)?, &expected);
    assert_kernel(
        "from_fn to the unit",
        &Kernel::from_fn(w, FinObj::unit(), |_| 0)?,
        &expected,
    );
    Ok(())
}

/// THEOREM_MAP: FinStoch.braiding_eq_ofFun
#[test]
fn witness_braiding_eq_of_fun() -> Result<()> {
    let (w, sp) = (obj_w()?, obj_s()?);
    let (ws, sw) = (w.tensor(&sp)?, sp.tensor(&w)?);
    let expected = points(ws.clone(), sw.clone(), &[0, 3, 1, 4, 2, 5])?;
    assert_kernel("β_ W S", &Kernel::swap(&w, &sp)?, &expected);
    assert_kernel(
        "from_fn of the swap",
        &Kernel::from_fn(ws, sw, |i| (i % 2) * 3 + i / 2)?,
        &expected,
    );
    Ok(())
}

/// THEOREM_MAP: FinStoch.deterministic_iff_mass
#[test]
fn witness_deterministic_iff_mass() -> Result<()> {
    for (name, kernel, expected) in [("d", d()?, true), ("s", s()?, false)] {
        let observed = is_deterministic(&kernel)?;
        let zero_one = entries_are_zero_or_one(&kernel);
        assert_eq!(
            observed,
            expected,
            "is_deterministic({name}) on {}: expected {expected}, observed {observed}",
            show(&kernel)
        );
        assert_eq!(
            zero_one,
            observed,
            "the 0/1 test on {name} ({}): expected {observed}, observed {zero_one}",
            show(&kernel)
        );
    }
    Ok(())
}

/// THEOREM_MAP: FinStoch.deterministic_iff_exists_ofFun
#[test]
fn witness_deterministic_iff_exists_of_fun() -> Result<()> {
    let function = Kernel::from_fn(obj_w()?, obj_s()?, |x| usize::from(x > 0))?;
    assert_kernel("from_fn of d", &function, &d()?);
    for (name, kernel, expected) in [("from_fn of d", function, true), ("s", s()?, false)] {
        let observed = is_deterministic(&kernel)?;
        assert_eq!(
            observed,
            expected,
            "is_deterministic({name}) on {}: expected {expected}, observed {observed}",
            show(&kernel)
        );
    }
    Ok(())
}

/// THEOREM_MAP: FinStoch.not_deterministic_bernoulli
#[test]
fn witness_not_deterministic_bernoulli() -> Result<()> {
    let bernoulli = Kernel::state(FinObj::new(2), vec![r(1, 2), r(1, 2)])?;
    let observed = is_deterministic(&bernoulli)?;
    assert!(
        !observed,
        "is_deterministic(bernoulli) on {}: expected false, observed {observed}",
        show(&bernoulli)
    );
    Ok(())
}

/// THEOREM_MAP: FinStoch.instMarkovCategory
#[test]
fn witness_markov_category() -> Result<()> {
    let (w, t, sp) = (obj_w()?, obj_t()?, obj_s()?);
    let unit = FinObj::unit();
    let ws = w.tensor(&sp)?;

    assert_kernel(
        "c ≫ ε[W]",
        &c()?.compose(&Kernel::del(&w)?)?,
        &points(t.clone(), unit.clone(), &[0, 0])?,
    );

    assert_kernel(
        "Δ[I]",
        &Kernel::copy(&unit)?,
        &lit(unit.clone(), unit.tensor(&unit)?, &[&[r(1, 1)]])?,
    );
    assert_kernel(
        "ε[I]",
        &Kernel::del(&unit)?,
        &lit(unit.clone(), unit.clone(), &[&[r(1, 1)]])?,
    );

    let tensor_mu = Kernel::identity(&w)?
        .tensor(&Kernel::swap(&w, &sp)?)?
        .tensor(&Kernel::identity(&sp)?)?;
    let copies = Kernel::<Exact>::copy(&w)?.tensor(&Kernel::copy(&sp)?)?;
    let diagonal = points(ws.clone(), ws.tensor(&ws)?, &[0, 7, 14, 21, 28, 35])?;
    assert_kernel("Δ[W ⊗ S]", &Kernel::copy(&ws)?, &diagonal);
    assert_kernel(
        "(Δ[W] ⊗ₘ Δ[S]) ≫ tensorμ",
        &copies.compose(&tensor_mu)?,
        &diagonal,
    );

    let to_unit = points(ws.clone(), unit.clone(), &[0, 0, 0, 0, 0, 0])?;
    let discards = Kernel::<Exact>::del(&w)?.tensor(&Kernel::del(&sp)?)?;
    assert_kernel("ε[W ⊗ S]", &Kernel::del(&ws)?, &to_unit);
    assert_kernel(
        "(ε[W] ⊗ₘ ε[S]) ≫ λ_ I",
        &discards.compose(&Kernel::left_unitor(&unit)?)?,
        &to_unit,
    );
    Ok(())
}
