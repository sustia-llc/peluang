//! Witnesses of the independence theorems of `Peluang.Independence` and of
//! the countermodel of `Peluang.Instances.FinStoch.Independence`, at the
//! running example, at the states `p_ind` and `p_brk` on `T ⊗ P`, and at the
//! two-element object `B`. The engine is strict: `Kernel::associator` stands
//! for both `α` and `α⁻¹`, and `Kernel::left_unitor`, `Kernel::right_unitor`
//! stand for the unitors and their inverses. Because the engine's associator is
//! the identity on the flattened object, these witnesses do not tell one
//! associator from another.

use peluang::conditional::conditional;
use peluang::error::Result;
use peluang::finset::FinObj;
use peluang::independence::cond_indep_form;
use peluang::kernel::Kernel;
use peluang::markov::{Compose, Tensor};
use peluang::prob::Exact;

use crate::fixtures::{
    assert_as_equal, assert_differs, assert_independent, assert_kernel, c, coin,
    conditional_composite, f, h, j, lit, obj_b, obj_p, obj_s, obj_t, obj_w, p_brk, p_ind, psi_t, r,
};

/// THEOREM_MAP: CategoryTheory.MarkovCategory.displaysIndep_iff_exists
#[test]
fn witness_displays_indep_iff_exists() -> Result<()> {
    let (t, w, sp, pp) = (obj_t()?, obj_w()?, obj_s()?, obj_p()?);
    let (f, j, c, h) = (f()?, j()?, c()?, h()?);
    assert_independent("j", &j, &w, &sp, true);
    assert_kernel("marginalFst j", &j.marginal_fst(&w, &sp)?, &c);
    assert_kernel("marginalSnd j", &j.marginal_snd(&w, &sp)?, &h);
    let p_ind = p_ind()?;
    assert_independent("p_ind", &p_ind, &t, &pp, true);
    assert_kernel(
        "marginalFst p_ind",
        &p_ind.marginal_fst(&t, &pp)?,
        &Kernel::state(t.clone(), vec![r(4, 5), r(1, 5)])?,
    );
    assert_kernel(
        "marginalSnd p_ind",
        &p_ind.marginal_snd(&t, &pp)?,
        &Kernel::state(pp.clone(), vec![r(2, 5), r(3, 5)])?,
    );

    assert_independent("control: f", &f, &w, &sp, false);
    assert_kernel("control: marginalFst f", &f.marginal_fst(&w, &sp)?, &c);
    assert_kernel("control: marginalSnd f", &f.marginal_snd(&w, &sp)?, &h);
    let product = Kernel::copy(&t)?.compose(&c.tensor(&h)?)?;
    assert_kernel("control: Δ[T] ≫ (c ⊗ h)", &product, &j);
    assert_differs("control: Δ[T] ≫ (c ⊗ h) against f", &product, &f);
    assert_independent("control: p_brk", &p_brk()?, &t, &pp, false);
    Ok(())
}

/// The candidate conditional of `F : T → W ⊗ S` on `W` is
/// `(del_W ▷ T) ≫ λ_T ≫ marginalSnd F : W ⊗ T → S`. The engine's
/// `conditional(j, W, S)` is `Δ[T] ≫ (marginalFst j ▷ T)`-almost surely equal
/// to the candidate of `j`.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.displaysIndep_iff_isConditional
#[test]
fn witness_displays_indep_iff_is_conditional() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (f, j) = (f()?, j()?);
    let candidate = |k: &Kernel<Exact>| -> Result<Kernel<Exact>> {
        Kernel::whisker_right(&Kernel::del(&w)?, &t)?
            .compose(&Kernel::left_unitor(&t)?)?
            .compose(&k.marginal_snd(&w, &sp)?)
    };
    assert_kernel(
        "Def. 11.5 composite of (del_W ▷ T) ≫ λ_T ≫ marginalSnd j for j",
        &conditional_composite(&j, &w, &sp, &candidate(&j)?)?,
        &j,
    );
    let relativiser =
        Kernel::copy(&t)?.compose(&Kernel::whisker_right(&j.marginal_fst(&w, &sp)?, &t)?)?;
    let conditional_j = conditional(&j, &w, &sp)?;
    assert_as_equal(
        "as_equal(Δ[T] ≫ (marginalFst j ▷ T), conditional(j, W, S), (del_W ▷ T) ≫ λ_T ≫ marginalSnd j)",
        &relativiser,
        &conditional_j,
        &candidate(&j)?,
        true,
    );
    assert_differs(
        "control: conditional(j, W, S) against (del_W ▷ T) ≫ λ_T ≫ marginalSnd j",
        &conditional_j,
        &candidate(&j)?,
    );

    let composite_f = conditional_composite(&f, &w, &sp, &candidate(&f)?)?;
    assert_kernel(
        "control: Def. 11.5 composite of (del_W ▷ T) ≫ λ_T ≫ marginalSnd f for f",
        &composite_f,
        &j,
    );
    assert_differs(
        "control: Def. 11.5 composite of (del_W ▷ T) ≫ λ_T ≫ marginalSnd f against f",
        &composite_f,
        &f,
    );
    Ok(())
}

/// `condIndepForm` at `A = T`, `W = I`, `g = del_T`, `h = ρ_T ≫ c`,
/// `k = λ_T ≫ h`.
/// THEOREM_MAP: CategoryTheory.MarkovCategory.displaysCondIndep_unit_iff
#[test]
fn witness_displays_cond_indep_unit_iff() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let form = cond_indep_form(
        &Kernel::del(&t)?,
        &Kernel::right_unitor(&t)?.compose(&c()?)?,
        &Kernel::left_unitor(&t)?.compose(&h()?)?,
    )?;
    let lambda_inv = Kernel::whisker_left(&w, &Kernel::left_unitor(&sp)?)?;
    assert_kernel(
        "condIndepForm(del_T, ρ_T ≫ c, λ_T ≫ h) against j ≫ (W ◁ λ_S⁻¹)",
        &form,
        &j()?.compose(&lambda_inv)?,
    );

    assert_independent("control: f", &f()?, &w, &sp, false);
    Ok(())
}

/// `ψ : I → W ⊗ (T ⊗ S)` is `condIndepForm` at `A = I`, `g = psi_t`,
/// `h = λ_T ≫ c`, `k = ρ_T ≫ h`. `ψ_bad` is `psi_t ≫ Δ[T] ≫ (f ▷ T) ≫
/// (W ◁ swap(S, T))`.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.displaysCondIndep_iff_state
#[test]
fn witness_displays_cond_indep_iff_state() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (psi_t, c, h) = (psi_t()?, c()?, h()?);
    let wts = w.tensor(&t)?.tensor(&sp)?;
    let psi = Kernel::state(
        wts.clone(),
        vec![
            r(1, 15),
            r(1, 30),
            r(0, 1),
            r(0, 1),
            r(1, 15),
            r(1, 30),
            r(1, 20),
            r(3, 20),
            r(0, 1),
            r(0, 1),
            r(3, 20),
            r(9, 20),
        ],
    )?;
    let form = cond_indep_form(
        &psi_t,
        &Kernel::left_unitor(&t)?.compose(&c)?,
        &Kernel::right_unitor(&t)?.compose(&h)?,
    )?;
    assert_kernel("condIndepForm(psi_t, λ_T ≫ c, ρ_T ≫ h)", &form, &psi);
    let state_form = psi_t
        .compose(&Kernel::copy(&t)?)?
        .compose(&Kernel::whisker_left(&t, &Kernel::copy(&t)?)?)?
        .compose(&c.tensor(&Kernel::whisker_left(&t, &h)?)?)?;
    assert_kernel(
        "Def. 12.1 composite psi_t ≫ Δ[T] ≫ (T ◁ Δ[T]) ≫ (c ⊗ (T ◁ h))",
        &state_form,
        &psi,
    );

    let psi_bad = Kernel::state(
        wts,
        vec![
            r(1, 30),
            r(1, 15),
            r(0, 1),
            r(0, 1),
            r(1, 10),
            r(0, 1),
            r(1, 5),
            r(0, 1),
            r(0, 1),
            r(0, 1),
            r(0, 1),
            r(3, 5),
        ],
    )?;
    assert_kernel(
        "control: psi_t ≫ Δ[T] ≫ (f ▷ T) ≫ (W ◁ swap(S, T))",
        &psi_t
            .compose(&Kernel::copy(&t)?)?
            .compose(&Kernel::whisker_right(&f()?, &t)?)?
            .compose(&Kernel::whisker_left(&w, &Kernel::swap(&sp, &t)?)?)?,
        &psi_bad,
    );
    assert_differs("control: ψ_bad against ψ", &psi_bad, &psi);
    let wt = w.tensor(&t)?;
    let ts = t.tensor(&sp)?;
    let wt_marginal = Kernel::state(
        wt.clone(),
        vec![r(1, 10), r(0, 1), r(1, 10), r(1, 5), r(0, 1), r(3, 5)],
    )?;
    let ts_marginal = Kernel::state(ts.clone(), vec![r(2, 15), r(1, 15), r(1, 5), r(3, 5)])?;
    for (name, state) in [("ψ", &psi), ("ψ_bad", &psi_bad)] {
        assert_kernel(
            &format!("control: (W, T) marginal of {name}"),
            &state.marginal_fst(&wt, &sp)?,
            &wt_marginal,
        );
        assert_kernel(
            &format!("control: (T, S) marginal of {name}"),
            &state.marginal_snd(&w, &ts)?,
            &ts_marginal,
        );
    }
    Ok(())
}

/// `cond_indep_form` at `A = T`, `W = S`, `g = h`, `h' : T ⊗ S → W`,
/// `k' : S ⊗ T → S` equals the Def. 12.16 composite built from `copy`, the
/// whiskers, the associators, `tensor` and `compose`.
#[test]
fn cond_indep_form_is_the_def_12_16_composite() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let g = h()?;
    let h2 = lit(
        t.tensor(&sp)?,
        w.clone(),
        &[
            &[r(1, 2), r(1, 2), r(0, 1)],
            &[r(1, 3), r(1, 3), r(1, 3)],
            &[r(0, 1), r(1, 4), r(3, 4)],
            &[r(1, 1), r(0, 1), r(0, 1)],
        ],
    )?;
    let k2 = lit(
        sp.tensor(&t)?,
        sp.clone(),
        &[
            &[r(1, 5), r(4, 5)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 1), r(0, 1)],
            &[r(1, 3), r(2, 3)],
        ],
    )?;
    let (a, ws) = (&t, &sp);
    let ww = ws.tensor(ws)?;
    let wa = ws.tensor(a)?;
    let w_copy3 = Kernel::copy(ws)?.compose(&Kernel::whisker_left(ws, &Kernel::copy(ws)?)?)?;
    let composite = Kernel::copy(a)?
        .compose(&Kernel::whisker_left(a, &Kernel::copy(a)?)?)?
        .compose(&Kernel::whisker_left(a, &Kernel::whisker_right(&g, a)?)?)?
        .compose(&Kernel::whisker_left(
            a,
            &Kernel::whisker_right(&w_copy3, a)?,
        )?)?
        .compose(&Kernel::whisker_left(a, &Kernel::associator(ws, &ww, a)?)?)?
        .compose(&Kernel::whisker_left(
            a,
            &Kernel::whisker_left(ws, &Kernel::associator(ws, ws, a)?)?,
        )?)?
        .compose(&Kernel::associator(a, ws, &ws.tensor(&wa)?)?)?
        .compose(&h2.tensor(&Kernel::whisker_left(ws, &k2)?)?)?;
    assert_kernel(
        "cond_indep_form(h, h', k') against the Def. 12.16 composite",
        &cond_indep_form(&g, &h2, &k2)?,
        &composite,
    );
    Ok(())
}

/// THEOREM_MAP: FinStoch.not_displaysIndep_coin_copy
#[test]
fn witness_not_displays_indep_coin_copy() -> Result<()> {
    let (b, coin) = (obj_b()?, coin()?);
    let bb = b.tensor(&b)?;
    let coin_copy = coin.compose(&Kernel::copy(&b)?)?;
    assert_kernel(
        "coin ≫ Δ[B]",
        &coin_copy,
        &Kernel::state(bb.clone(), vec![r(1, 2), r(0, 1), r(0, 1), r(1, 2)])?,
    );
    assert_independent("coin ≫ Δ[B]", &coin_copy, &b, &b, false);
    assert_kernel(
        "marginalFst (coin ≫ Δ[B])",
        &coin_copy.marginal_fst(&b, &b)?,
        &coin,
    );
    assert_kernel(
        "marginalSnd (coin ≫ Δ[B])",
        &coin_copy.marginal_snd(&b, &b)?,
        &coin,
    );
    assert_kernel(
        "Δ[I] ≫ (coin ⊗ coin)",
        &Kernel::copy(&FinObj::unit())?.compose(&coin.tensor(&coin)?)?,
        &Kernel::state(bb, vec![r(1, 4), r(1, 4), r(1, 4), r(1, 4)])?,
    );
    Ok(())
}
