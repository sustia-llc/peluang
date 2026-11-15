//! Witnesses of the almost-sure uniqueness of conditionals and of the three
//! rewrite rules of `Peluang.Conditional`, and of the countermodel of
//! `Peluang.Instances.FinStoch.Conditional`, at the running example and at
//! the two-element object `B`. The engine is strict: `Kernel::associator`
//! stands for both `α` and `α⁻¹`. Because the engine's associator is the
//! identity on the flattened object, these witnesses do not tell `α` from
//! `α⁻¹`.

use peluang::conditional::conditional;
use peluang::error::Result;
use peluang::kernel::Kernel;
use peluang::markov::Compose;
use peluang::prob::{Exact, Prob};

use crate::fixtures::{
    assert_as_equal, assert_deterministic, assert_differs, assert_kernel, coin,
    conditional_composite, d, e, f, h, lit, obj_b, obj_s, obj_t, obj_w, points, r, show,
};

/// `snd : B ⊗ B → B`, the second projection.
fn snd() -> Result<Kernel<Exact>> {
    let b = obj_b()?;
    points(b.tensor(&b)?, b, &[0, 1, 0, 1])
}

/// The state on `B ⊗ B` with weight `1/4` at every output.
fn quarters() -> Result<Kernel<Exact>> {
    let b = obj_b()?;
    Kernel::state(b.tensor(&b)?, vec![r(1, 4), r(1, 4), r(1, 4), r(1, 4)])
}

/// `k₁ = conditional(f, W, S) : W ⊗ T → S`.
fn k1() -> Result<Kernel<Exact>> {
    conditional(&f()?, &obj_w()?, &obj_s()?)
}

/// `k` with the column at input `x` replaced by `column`.
fn with_column(k: &Kernel<Exact>, x: usize, column: &[Exact]) -> Result<Kernel<Exact>> {
    assert!(
        x < k.domain().card(),
        "with_column: column index {x} is not below the domain cardinality of {}",
        show(k)
    );
    let mut data = Vec::new();
    for i in 0..k.domain().card() {
        match k.column(i) {
            Some(_) if i == x => data.extend_from_slice(column),
            Some(current) => data.extend_from_slice(current),
            None => panic!("column {i} of {} is missing", show(k)),
        }
    }
    Kernel::new(k.domain().clone(), k.codomain().clone(), data)
}

/// `k₂`: `k₁` with the column at `(sunny, cold)` replaced by `(1/3, 2/3)` and
/// the column at `(rainy, hot)` replaced by `(2/3, 1/3)`.
fn k2() -> Result<Kernel<Exact>> {
    let sunny_cold = with_column(&k1()?, 1, &[r(1, 3), r(2, 3)])?;
    with_column(&sunny_cold, 4, &[r(2, 3), r(1, 3)])
}

/// `k₃`: `k₁` with the column at `(cloudy, cold)` replaced by `(0, 1)`.
fn k3() -> Result<Kernel<Exact>> {
    with_column(&k1()?, 3, &[r(0, 1), r(1, 1)])
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.isConditional_unique_as
#[test]
fn witness_is_conditional_unique_as() -> Result<()> {
    let (t, w, sp, f) = (obj_t()?, obj_w()?, obj_s()?, f()?);
    let (k1, k2, k3) = (k1()?, k2()?, k3()?);
    assert_differs("k₂ against k₁", &k2, &k1);
    assert_differs("k₃ against k₁", &k3, &k1);
    assert_kernel(
        "Def. 11.5 composite of k₁",
        &conditional_composite(&f, &w, &sp, &k1)?,
        &f,
    );
    assert_kernel(
        "Def. 11.5 composite of k₂",
        &conditional_composite(&f, &w, &sp, &k2)?,
        &f,
    );
    let p = Kernel::copy(&t)?.compose(&Kernel::whisker_right(&f.marginal_fst(&w, &sp)?, &t)?)?;
    let unreached: Vec<usize> = (0..k1.domain().card())
        .filter(|&x| {
            (0..p.domain().card()).all(|a| p.column(a).is_some_and(|col| col[x] == Exact::zero()))
        })
        .collect();
    let names: Vec<String> = unreached.iter().map(|&x| input_name(&k1, x)).collect();
    assert_eq!(
        names,
        ["(sunny, cold)", "(rainy, hot)"],
        "inputs of W ⊗ T that p reaches from no input: expected (sunny, cold), (rainy, hot), \
         observed {names:?} at {unreached:?}"
    );
    let half = [r(1, 2), r(1, 2)];
    for &x in &unreached {
        assert!(
            k1.column(x) == Some(&half[..]),
            "k₁ at {}: expected (1/2, 1/2), observed {}",
            input_name(&k1, x),
            show(&k1)
        );
    }
    for x in 0..k1.domain().card() {
        let changed = k1.column(x) != k2.column(x);
        let expected = unreached.contains(&x);
        assert_eq!(
            changed,
            expected,
            "k₂ against k₁ at {}: expected changed = {expected}, observed {changed}; k₂ = {}",
            input_name(&k1, x),
            show(&k2)
        );
    }
    assert_as_equal("as_equal(p, k₁, k₂)", &p, &k1, &k2, true);

    assert_differs(
        "control: Def. 11.5 composite of k₃",
        &conditional_composite(&f, &w, &sp, &k3)?,
        &f,
    );
    assert_as_equal("control: as_equal(p, k₁, k₃)", &p, &k1, &k3, false);
    let third = r(1, 3);
    let uniform = [third.clone(), third.clone(), third];
    let u = lit(t.clone(), w, &[&uniform, &uniform])?;
    let p_u = Kernel::copy(&t)?.compose(&Kernel::whisker_right(&u, &t)?)?;
    assert_as_equal("control: as_equal(p_u, k₁, k₂)", &p_u, &k1, &k2, false);
    Ok(())
}

/// The input `x` of `k : W ⊗ T → _` as `(w, t)`, from the labels of the
/// domain of `k`.
fn input_name(k: &Kernel<Exact>, x: usize) -> String {
    let factors = k.domain().factors();
    let label = |i: usize, j: usize| {
        factors
            .get(i)
            .and_then(|factor| factor.labels())
            .and_then(|labels| labels.get(j))
            .cloned()
            .unwrap_or_else(|| panic!("factor {i} of {} has no label {j}", show(k)))
    };
    let inner = factors.get(1).map_or(1, |factor| factor.card());
    format!("({}, {})", label(0, x / inner), label(1, x % inner))
}

/// `ψ = cold ≫ f : I → W ⊗ S`, `g₁ = conditional(ψ, W, S) : W → S` (the
/// engine's `W ⊗ I` is `W`), `g₂` and `g₃` are `g₁` with the column at sunny
/// and at cloudy replaced. Each `gᵢ` enters the Def. 11.5 composite as
/// `ρ_W ≫ gᵢ`.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.isConditional_unique_as_unit
#[test]
fn witness_is_conditional_unique_as_unit() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let psi = Kernel::state(t, vec![r(0, 1), r(1, 1)])?.compose(&f()?)?;
    let g1 = conditional(&psi, &w, &sp)?;
    let g2 = with_column(&g1, 0, &[r(1, 1), r(0, 1)])?;
    let g3 = with_column(&g1, 1, &[r(0, 1), r(1, 1)])?;
    assert_differs("g₂ against g₁", &g2, &g1);
    assert_differs("g₃ against g₁", &g3, &g1);
    let rho = Kernel::right_unitor(&w)?;
    assert_kernel(
        "Def. 11.5 composite of ρ_W ≫ g₁ for ψ",
        &conditional_composite(&psi, &w, &sp, &rho.compose(&g1)?)?,
        &psi,
    );
    assert_kernel(
        "Def. 11.5 composite of ρ_W ≫ g₂ for ψ",
        &conditional_composite(&psi, &w, &sp, &rho.compose(&g2)?)?,
        &psi,
    );
    let p = psi.marginal_fst(&w, &sp)?;
    assert_as_equal("as_equal(marginalFst ψ, g₁, g₂)", &p, &g1, &g2, true);

    assert_differs(
        "control: Def. 11.5 composite of ρ_W ≫ g₃ for ψ",
        &conditional_composite(&psi, &w, &sp, &rho.compose(&g3)?)?,
        &psi,
    );
    assert_as_equal(
        "control: as_equal(marginalFst ψ, g₁, g₃)",
        &p,
        &g1,
        &g3,
        false,
    );
    Ok(())
}

/// `F = Δ[T] ≫ (h ▷ T) ≫ (S ◁ (f ≫ swap)) : T → S ⊗ (S ⊗ W)`, `k` its
/// conditional on `S`, `n` the conditional of `k` on `S`.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsConditional.nest
#[test]
fn witness_is_conditional_nest() -> Result<()> {
    let (t, w, sp, f) = (obj_t()?, obj_w()?, obj_s()?, f()?);
    let (sw, ss) = (sp.tensor(&w)?, sp.tensor(&sp)?);
    let big_f = Kernel::copy(&t)?
        .compose(&Kernel::whisker_right(&h()?, &t)?)?
        .compose(&Kernel::whisker_left(
            &sp,
            &f.compose(&Kernel::swap(&w, &sp)?)?,
        )?)?;
    let k = conditional(&big_f, &sp, &sw)?;
    let n = conditional(&k, &sp, &w)?;
    assert_kernel(
        "hk: Def. 11.5 composite of k for F",
        &conditional_composite(&big_f, &sp, &sw, &k)?,
        &big_f,
    );
    assert_kernel(
        "hh: Def. 11.5 composite of n for k",
        &conditional_composite(&k, &sp, &w, &n)?,
        &k,
    );
    let lhs = big_f.compose(&Kernel::associator(&sp, &sp, &w)?)?;
    let nested = Kernel::whisker_right(&Kernel::swap(&sp, &sp)?, &t)?
        .compose(&Kernel::associator(&sp, &sp, &t)?)?
        .compose(&n)?;
    assert_kernel(
        "Def. 11.5 composite of (swap ▷ T) ≫ α ≫ n for F ≫ α⁻¹",
        &conditional_composite(&lhs, &ss, &w, &nested)?,
        &lhs,
    );

    let unswapped = Kernel::associator(&sp, &sp, &t)?.compose(&n)?;
    assert_differs(
        "control: Def. 11.5 composite of α ≫ n for F ≫ α⁻¹",
        &conditional_composite(&lhs, &ss, &w, &unswapped)?,
        &lhs,
    );
    Ok(())
}

/// `g : S ⊗ T → S` sends `(on, hot)` and `(off, cold)` to on, `(on, cold)`
/// and `(off, hot)` to off.
/// THEOREM_MAP: CategoryTheory.MarkovCategory.IsConditional.comp_whiskerLeft
#[test]
fn witness_is_conditional_comp_whisker_left() -> Result<()> {
    let (t, w, sp, f) = (obj_t()?, obj_w()?, obj_s()?, f()?);
    let g = points(sp.tensor(&t)?, sp.clone(), &[0, 1, 1, 0])?;
    let lhs = Kernel::whisker_right(&f, &t)?
        .compose(&Kernel::associator(&w, &sp, &t)?)?
        .compose(&Kernel::whisker_left(&w, &g)?)?;
    let candidate = |k: &Kernel<Exact>| -> Result<Kernel<Exact>> {
        Kernel::associator(&w, &t, &t)?
            .compose(&Kernel::whisker_right(k, &t)?)?
            .compose(&g)
    };
    let (k1, k3) = (k1()?, k3()?);
    assert_kernel(
        "Def. 11.5 composite of α⁻¹ ≫ (k₁ ▷ T) ≫ g for (f ▷ T) ≫ α ≫ (W ◁ g)",
        &conditional_composite(&lhs, &w, &sp, &candidate(&k1)?)?,
        &lhs,
    );

    assert_differs(
        "control: Def. 11.5 composite of α⁻¹ ≫ (k₃ ▷ T) ≫ g for (f ▷ T) ≫ α ≫ (W ◁ g)",
        &conditional_composite(&lhs, &w, &sp, &candidate(&k3)?)?,
        &lhs,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsConditional.deterministic_comp
#[test]
fn witness_is_conditional_deterministic_comp() -> Result<()> {
    let (w, sp) = (obj_w()?, obj_s()?);
    for (name, g) in [("e", e()?), ("d ≫ e", d()?.compose(&e()?)?)] {
        assert_deterministic(name, &g, true);
        let gf = g.compose(&f()?)?;
        let candidate = Kernel::whisker_left(&w, &g)?.compose(&k1()?)?;
        assert_kernel(
            &format!("Def. 11.5 composite of (W ◁ g) ≫ k₁ for g ≫ f, g = {name}"),
            &conditional_composite(&gf, &w, &sp, &candidate)?,
            &gf,
        );
    }

    assert_deterministic("coin", &coin()?, false);
    Ok(())
}

/// `f = Δ[B]`, `k = snd`, `g = coin`.
/// THEOREM_MAP: FinStoch.not_isConditional_comp_of_coin
#[test]
fn witness_not_is_conditional_comp_of_coin() -> Result<()> {
    let (b, coin, snd) = (obj_b()?, coin()?, snd()?);
    assert_deterministic("coin", &coin, false);
    let copy = Kernel::copy(&b)?;
    assert_kernel("Δ[B]", &copy, &points(b.clone(), b.tensor(&b)?, &[0, 3])?);
    assert_kernel(
        "Def. 11.5 composite of snd for Δ[B]",
        &conditional_composite(&copy, &b, &b, &snd)?,
        &copy,
    );
    let coin_copy = coin.compose(&copy)?;
    assert_kernel(
        "coin ≫ Δ[B]",
        &coin_copy,
        &Kernel::state(b.tensor(&b)?, vec![r(1, 2), r(0, 1), r(0, 1), r(1, 2)])?,
    );
    let candidate = Kernel::whisker_left(&b, &coin)?.compose(&snd)?;
    let composite = conditional_composite(&coin_copy, &b, &b, &candidate)?;
    assert_kernel(
        "Def. 11.5 composite of (B ◁ coin) ≫ snd for coin ≫ Δ[B]",
        &composite,
        &quarters()?,
    );
    Ok(())
}
