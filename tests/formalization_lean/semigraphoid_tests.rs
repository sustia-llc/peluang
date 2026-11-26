//! Witnesses of `marginalSnd_comp_braiding_hom`, `DisplaysIndep.symm`,
//! `DisplaysIndep.decomposition`, `DisplaysCondIndepState.symm`,
//! `DisplaysCondIndepState.decomposition`,
//! `DisplaysCondIndepState.contraction` and
//! `DisplaysCondIndepState.weak_union` at the running example: the reorder
//! kernels built from `Kernel::swap`, `Kernel::associator`,
//! `Kernel::whisker_left` and `Kernel::whisker_right`, `Kernel::marginal`,
//! `is_independent` and `is_cond_independent_state`. Also, untagged:
//! `Kernel::marginal` against `Kernel::marginal_fst`, `Kernel::marginal_snd`
//! and literals, with its `Error::NotAFactorList` and `Error::TooLarge` and
//! its results on an empty domain, and `is_cond_independent_state` on states
//! with a factor in no list and on states with a factor of `ws` between two
//! factors of `xs`, with its `Error::NotAState`, `Error::NotAFactorList` and
//! `Error::SharedFactorIndex`. The engine is strict:
//! `Kernel::associator` stands for both `α` and `α⁻¹`, and
//! `Kernel::right_unitor` for `ρ`.

use peluang::conditional::conditional_snd;
use peluang::error::{Error, Result};
use peluang::finset::FinObj;
use peluang::independence::is_cond_independent_state;
use peluang::kernel::Kernel;
use peluang::markov::{Compose, Tensor};
use peluang::prob::Exact;

use crate::fixtures::{
    assert_cond_independent_state, assert_differs, assert_independent, assert_kernel, c, f, h, j,
    k, lit, obj_b, obj_s, obj_t, obj_w, p_brk, p_ind, psi_t, r,
};

/// The state on `cod` whose weights in output order are the concatenation of
/// `groups`, through `Kernel::new`.
fn grouped(cod: FinObj, groups: &[&[Exact]]) -> Result<Kernel<Exact>> {
    lit(FinObj::unit(), cod, groups)
}

/// `(tensorRev₃ x w y).hom`: `σ[x, w ⊗ y] ≫ (σ[w, y] ▷ x) ≫ α[y, w, x]`.
fn rev3(x: &FinObj, w: &FinObj, y: &FinObj) -> Result<Kernel<Exact>> {
    Kernel::swap(x, &w.tensor(y)?)?
        .compose(&Kernel::whisker_right(&Kernel::swap(w, y)?, x)?)?
        .compose(&Kernel::associator(y, w, x)?)
}

/// `(tensorWeakUnionIso x1 x2 w y).hom`: `α[x1, x2, w ⊗ y] ≫
/// (x1 ◁ α⁻¹[x2, w, y]) ≫ (x1 ◁ (σ[x2, w] ▷ y))`.
fn weak_union(x1: &FinObj, x2: &FinObj, w: &FinObj, y: &FinObj) -> Result<Kernel<Exact>> {
    Kernel::associator(x1, x2, &w.tensor(y)?)?
        .compose(&Kernel::whisker_left(x1, &Kernel::associator(x2, w, y)?)?)?
        .compose(&Kernel::whisker_left(
            x1,
            &Kernel::whisker_right(&Kernel::swap(x2, w)?, y)?,
        )?)
}

/// The marginal `x1 ◁ ε[x2] ≫ ρ[x1] : x1 ⊗ x2 → x1`.
fn discard_snd(x1: &FinObj, x2: &FinObj) -> Result<Kernel<Exact>> {
    Kernel::whisker_left(x1, &Kernel::del(x2)?)?.compose(&Kernel::right_unitor(x1)?)
}

/// The Def. 12.1 composite `phi ≫ Δ[W] ≫ (W ◁ Δ[W]) ≫ (f ⊗ₘ (W ◁ g))` with
/// `W` the codomain of `phi`.
fn state_form(phi: &Kernel<Exact>, f: &Kernel<Exact>, g: &Kernel<Exact>) -> Result<Kernel<Exact>> {
    let w = phi.codomain();
    let copy = Kernel::copy(w)?;
    phi.compose(&copy)?
        .compose(&Kernel::whisker_left(w, &copy)?)?
        .compose(&f.tensor(&Kernel::whisker_left(w, g)?)?)
}

/// `W → S ⊗ S`: sunny to `(1/2, 1/4, 1/8, 1/8)`, cloudy to
/// `(1/10, 2/5, 3/10, 1/5)`, rainy to `(1/3, 1/6, 1/4, 1/4)`.
fn joint_ss() -> Result<Kernel<Exact>> {
    lit(
        obj_w()?,
        obj_s()?.tensor(&obj_s()?)?,
        &[
            &[r(1, 2), r(1, 4), r(1, 8), r(1, 8)],
            &[r(1, 10), r(2, 5), r(3, 10), r(1, 5)],
            &[r(1, 3), r(1, 6), r(1, 4), r(1, 4)],
        ],
    )
}

/// `k3 : T → (W ⊗ S) ⊗ S`, the literal of `Δ[T] ≫ (f ⊗ₘ h)`: weight
/// `f((w, s) | t) · h(y | t)` at output `(w, s, y)`.
fn k3() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_w()?.tensor(&obj_s()?)?.tensor(&obj_s()?)?,
        &[
            &[
                r(1, 9),
                r(1, 18),
                r(2, 9),
                r(1, 9),
                r(1, 3),
                r(1, 6),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(0, 1),
            ],
            &[
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(1, 16),
                r(3, 16),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(3, 16),
                r(9, 16),
            ],
        ],
    )
}

/// `k3_dep : T → (W ⊗ S) ⊗ S`, the literal of `Δ[T] ≫ (c ⊗ₘ (h ≫ Δ[S]))`:
/// weight `c(w | t) · h(s | t)` at output `(w, s, s)` and 0 at every other
/// output.
fn k3_dep() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_w()?.tensor(&obj_s()?)?.tensor(&obj_s()?)?,
        &[
            &[
                r(1, 3),
                r(0, 1),
                r(0, 1),
                r(1, 6),
                r(1, 3),
                r(0, 1),
                r(0, 1),
                r(1, 6),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(0, 1),
            ],
            &[
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(1, 16),
                r(0, 1),
                r(0, 1),
                r(3, 16),
                r(3, 16),
                r(0, 1),
                r(0, 1),
                r(9, 16),
            ],
        ],
    )
}

/// `ψ : I → W ⊗ (T ⊗ S)`, the literal of the Def. 12.1 composite of `psi_t`,
/// `c` and `h`: weight `psi_t(t) · c(w | t) · h(s | t)` at output `(w, t, s)`.
fn psi_wts() -> Result<Kernel<Exact>> {
    grouped(
        obj_w()?.tensor(&obj_t()?)?.tensor(&obj_s()?)?,
        &[
            &[r(1, 15), r(1, 30), r(0, 1), r(0, 1)],
            &[r(1, 15), r(1, 30), r(1, 20), r(3, 20)],
            &[r(0, 1), r(0, 1), r(3, 20), r(9, 20)],
        ],
    )
}

/// `ψ_bad : I → W ⊗ (T ⊗ S)`, the literal of `psi_t ≫ Δ[T] ≫ (f ▷ T) ≫
/// (W ◁ σ[S, T])`: weight `psi_t(t) · f((w, s) | t)` at output `(w, t, s)`.
fn psi_wts_bad() -> Result<Kernel<Exact>> {
    grouped(
        obj_w()?.tensor(&obj_t()?)?.tensor(&obj_s()?)?,
        &[
            &[r(1, 30), r(1, 15), r(0, 1), r(0, 1)],
            &[r(1, 10), r(0, 1), r(1, 5), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(3, 5)],
        ],
    )
}

/// The object `(W ⊗ S) ⊗ (T ⊗ S)`.
fn wsts() -> Result<FinObj> {
    obj_w()?
        .tensor(&obj_s()?)?
        .tensor(&obj_t()?)?
        .tensor(&obj_s()?)
}

/// `ψ5 : I → (W ⊗ S) ⊗ (T ⊗ S)`, the literal of the Def. 12.1 composite of
/// `psi_t`, `f` and `h`: weight `psi_t(t) · f((w, s) | t) · h(y | t)` at
/// output `(w, s, t, y)`.
fn psi5() -> Result<Kernel<Exact>> {
    grouped(
        wsts()?,
        &[
            &[r(1, 45), r(1, 90), r(0, 1), r(0, 1)],
            &[r(2, 45), r(1, 45), r(0, 1), r(0, 1)],
            &[r(1, 15), r(1, 30), r(1, 20), r(3, 20)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(3, 20), r(9, 20)],
        ],
    )
}

/// `ψ5_dep : I → (W ⊗ S) ⊗ (T ⊗ S)`: weight
/// `psi_t(t) · c(w | t) · h(s | t)` at output `(w, s, t, s)` and 0 at every
/// other output.
fn psi5_dep() -> Result<Kernel<Exact>> {
    grouped(
        wsts()?,
        &[
            &[r(1, 15), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(1, 30), r(0, 1), r(0, 1)],
            &[r(1, 15), r(0, 1), r(1, 20), r(0, 1)],
            &[r(0, 1), r(1, 30), r(0, 1), r(3, 20)],
            &[r(0, 1), r(0, 1), r(3, 20), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(9, 20)],
        ],
    )
}

/// `ψ_d : I → (W ⊗ S) ⊗ (T ⊗ S)`: weight
/// `psi_t(t) · f((w, y) | t) · h(s | t)` at output `(w, s, t, y)`.
fn psi_d() -> Result<Kernel<Exact>> {
    grouped(
        wsts()?,
        &[
            &[r(1, 45), r(2, 45), r(0, 1), r(0, 1)],
            &[r(1, 90), r(1, 45), r(0, 1), r(0, 1)],
            &[r(1, 15), r(0, 1), r(1, 20), r(0, 1)],
            &[r(1, 30), r(0, 1), r(3, 20), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(3, 20)],
            &[r(0, 1), r(0, 1), r(0, 1), r(9, 20)],
        ],
    )
}

/// `f0 : T → W ⊗ S`: hot to `(1/3, 0, 2/3, 0, 0, 0)`, with no mass at second
/// factor off, cold to `(0, 0, 1/4, 0, 0, 3/4)`.
fn f0() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_w()?.tensor(&obj_s()?)?,
        &[
            &[r(1, 3), r(0, 1), r(2, 3), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(1, 4), r(0, 1), r(0, 1), r(3, 4)],
        ],
    )
}

/// The kernel `S ⊗ T → W` with the columns `on_hot` at `(on, hot)`,
/// `(0, 1, 0)` at `(on, cold)`, `off_hot` at `(off, hot)` and `(0, 0, 1)` at
/// `(off, cold)`.
fn st_to_w(on_hot: [Exact; 3], off_hot: [Exact; 3]) -> Result<Kernel<Exact>> {
    lit(
        obj_s()?.tensor(&obj_t()?)?,
        obj_w()?,
        &[
            &on_hot,
            &[r(0, 1), r(1, 1), r(0, 1)],
            &off_hot,
            &[r(0, 1), r(0, 1), r(1, 1)],
        ],
    )
}

/// `ψ7 : I → (W ⊗ S) ⊗ (T ⊗ S)`, the literal of the Def. 12.1 composite of
/// `psi_t`, `f0` and `h`: weight `psi_t(t) · f0((w, s) | t) · h(y | t)` at
/// output `(w, s, t, y)`.
fn psi7() -> Result<Kernel<Exact>> {
    grouped(
        wsts()?,
        &[
            &[r(2, 45), r(1, 45), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(4, 45), r(2, 45), r(1, 20), r(3, 20)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(3, 20), r(9, 20)],
        ],
    )
}

/// `k_tb : T → B`: hot to `(1/2, 1/2)`, cold to `(1/4, 3/4)`.
fn k_tb() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_b()?,
        &[&[r(1, 2), r(1, 2)], &[r(1, 4), r(3, 4)]],
    )
}

/// `g6 : T ⊗ B → S`: `(hot, false)` to `(2/3, 1/3)`, `(hot, true)` to
/// `(1, 0)`, `(cold, false)` to `(1/4, 3/4)`, `(cold, true)` to `(1/2, 1/2)`.
fn g6() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?.tensor(&obj_b()?)?,
        obj_s()?,
        &[
            &[r(2, 3), r(1, 3)],
            &[r(1, 1), r(0, 1)],
            &[r(1, 4), r(3, 4)],
            &[r(1, 2), r(1, 2)],
        ],
    )
}

/// `ψ_A : I → W ⊗ ((T ⊗ B) ⊗ S)`, the Def. 12.1 composite of the state
/// `(1/10, 1/10, 1/5, 3/5)` on `T ⊗ B`, the kernel `T ⊗ B → W` with
/// `(hot, false)` to `(1/2, 1/2, 0)`, `(hot, true)` to `(0, 0, 1)` and
/// `(cold, false)`, `(cold, true)` to `(0, 1/4, 3/4)`, and `g6`.
fn psi_a() -> Result<Kernel<Exact>> {
    let tb = obj_t()?.tensor(&obj_b()?)?;
    let phi = Kernel::state(tb.clone(), vec![r(1, 10), r(1, 10), r(1, 5), r(3, 5)])?;
    let f_a = lit(
        tb,
        obj_w()?,
        &[
            &[r(1, 2), r(1, 2), r(0, 1)],
            &[r(0, 1), r(0, 1), r(1, 1)],
            &[r(0, 1), r(1, 4), r(3, 4)],
            &[r(0, 1), r(1, 4), r(3, 4)],
        ],
    )?;
    state_form(&phi, &f_a, &g6()?)
}

/// The object `W ⊗ (T ⊗ (S ⊗ B))`.
fn wtsb() -> Result<FinObj> {
    obj_w()?
        .tensor(&obj_t()?)?
        .tensor(&obj_s()?)?
        .tensor(&obj_b()?)
}

/// `ψ_i : I → W ⊗ (T ⊗ (S ⊗ B))`: weight
/// `psi_t(t) · f((w, s) | t) · k_tb(b | t)` at output `(w, t, s, b)`.
fn psi_wtsb() -> Result<Kernel<Exact>> {
    grouped(
        wtsb()?,
        &[
            &[r(1, 60), r(1, 60), r(1, 30), r(1, 30)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(1, 20), r(1, 20), r(0, 1), r(0, 1)],
            &[r(1, 20), r(3, 20), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(3, 20), r(9, 20)],
        ],
    )
}

/// `ψ_i' : I → W ⊗ (T ⊗ (S ⊗ B))`: weight `psi_t(t) · f((w, s) | t)` at the
/// outputs `(w, t, on, false)` and `(w, t, off, true)`, and 0 at every other
/// output.
fn psi_wtsb_dep() -> Result<Kernel<Exact>> {
    grouped(
        wtsb()?,
        &[
            &[r(1, 30), r(0, 1), r(0, 1), r(1, 15)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(1, 10), r(0, 1), r(0, 1), r(0, 1)],
            &[r(1, 5), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(3, 5)],
        ],
    )
}

/// Asserts that `got` is `Error::NotAFactorList` with `cod` and `list`,
/// naming `call`.
#[track_caller]
fn assert_not_a_factor_list<T: std::fmt::Debug>(
    call: &str,
    got: &Result<T>,
    cod: &FinObj,
    list: &[usize],
) {
    assert!(
        matches!(got, Err(Error::NotAFactorList { codomain, list: found })
            if codomain == cod && found == list),
        "{call}: expected NotAFactorList {{ codomain: {cod:?}, list: {list:?} }}, observed \
         {got:?}"
    );
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.marginalSnd_comp_braiding_hom
#[test]
fn witness_marginal_snd_comp_braiding_hom() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let joint = f()?;
    let literal = lit(
        t,
        w.clone(),
        &[&[r(1, 2), r(1, 2), r(0, 1)], &[r(0, 1), r(1, 4), r(3, 4)]],
    )?;
    let lhs = joint
        .compose(&Kernel::swap(&w, &sp)?)?
        .marginal_snd(&sp, &w)?;
    let rhs = joint.marginal_fst(&w, &sp)?;
    assert_kernel("marginalFst (f : T → W ⊗ S)", &rhs, &literal);
    assert_kernel("marginalSnd ((f : T → W ⊗ S) ≫ σ[W, S])", &lhs, &rhs);

    let joint = joint_ss()?;
    let literal = lit(
        w,
        sp.clone(),
        &[
            &[r(3, 4), r(1, 4)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 2), r(1, 2)],
        ],
    )?;
    let lhs = joint
        .compose(&Kernel::swap(&sp, &sp)?)?
        .marginal_snd(&sp, &sp)?;
    let rhs = joint.marginal_fst(&sp, &sp)?;
    assert_kernel("marginalFst (W → S ⊗ S)", &rhs, &literal);
    assert_kernel("marginalSnd ((W → S ⊗ S) ≫ σ[S, S])", &lhs, &rhs);
    assert_differs(
        "control: marginalSnd ((W → S ⊗ S) ≫ σ[S, S]) against marginalSnd (W → S ⊗ S)",
        &lhs,
        &joint.marginal_snd(&sp, &sp)?,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.DisplaysIndep.symm
#[test]
fn witness_displays_indep_symm() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (f, j) = (f()?, j()?);
    let sigma = Kernel::swap(&w, &sp)?;
    let sw = sp.tensor(&w)?;
    let j_swapped = j.compose(&sigma)?;
    assert_kernel(
        "j ≫ σ[W, S]",
        &j_swapped,
        &lit(
            t.clone(),
            sw.clone(),
            &[
                &[r(1, 3), r(1, 3), r(0, 1), r(1, 6), r(1, 6), r(0, 1)],
                &[r(0, 1), r(1, 16), r(3, 16), r(0, 1), r(3, 16), r(9, 16)],
            ],
        )?,
    );
    assert_independent("j", &j, &w, &sp, true);
    assert_independent("j ≫ σ[W, S]", &j_swapped, &sp, &w, true);

    let f_swapped = f.compose(&sigma)?;
    assert_kernel(
        "control: f ≫ σ[W, S]",
        &f_swapped,
        &lit(
            t,
            sw,
            &[
                &[r(1, 6), r(1, 2), r(0, 1), r(1, 3), r(0, 1), r(0, 1)],
                &[r(0, 1), r(1, 4), r(0, 1), r(0, 1), r(0, 1), r(3, 4)],
            ],
        )?,
    );
    assert_independent("control: f", &f, &w, &sp, false);
    assert_independent("control: f ≫ σ[W, S]", &f_swapped, &sp, &w, false);
    Ok(())
}

/// The theorem drops the second factor of the first place: here `S` of
/// `(W ⊗ S) ⊗ S`.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.DisplaysIndep.decomposition
#[test]
fn witness_displays_indep_decomposition() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let ws = w.tensor(&sp)?;
    let (c, h, j) = (c()?, h()?, j()?);
    let k = k3()?;
    assert_kernel(
        "Δ[T] ≫ (f ⊗ₘ h)",
        &Kernel::copy(&t)?.compose(&f()?.tensor(&h)?)?,
        &k,
    );
    assert_independent("k", &k, &ws, &sp, true);
    let marginal = k.marginal(&[0, 2])?;
    assert_kernel("k.marginal([0, 2])", &marginal, &j);
    let drop_snd = Kernel::whisker_right(&discard_snd(&w, &sp)?, &sp)?;
    assert_kernel(
        "k ≫ ((W ◁ ε[S] ≫ ρ) ▷ S)",
        &k.compose(&drop_snd)?,
        &marginal,
    );
    assert_independent("k.marginal([0, 2])", &marginal, &w, &sp, true);
    assert_differs(
        "control: k.marginal([0, 1]) against k.marginal([0, 2])",
        &k.marginal(&[0, 1])?,
        &marginal,
    );

    let k_dep = k3_dep()?;
    assert_kernel(
        "control: Δ[T] ≫ (c ⊗ₘ (h ≫ Δ[S]))",
        &Kernel::copy(&t)?.compose(&c.tensor(&h.compose(&Kernel::copy(&sp)?)?)?)?,
        &k_dep,
    );
    assert_independent("control: k'", &k_dep, &ws, &sp, false);
    let marginal_dep = k_dep.marginal(&[0, 2])?;
    assert_kernel("control: k'.marginal([0, 2])", &marginal_dep, &j);
    assert_kernel(
        "control: k' ≫ ((W ◁ ε[S] ≫ ρ) ▷ S)",
        &k_dep.compose(&drop_snd)?,
        &marginal_dep,
    );
    assert_independent("control: k'.marginal([0, 2])", &marginal_dep, &w, &sp, true);
    Ok(())
}

/// The `==` half compares `ψ ≫ tensorRev₃` with the Def. 12.1 composite of
/// `psi_t`, `h` and `c`.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.DisplaysCondIndepState.symm
#[test]
fn witness_displays_cond_indep_state_symm() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (psi_t, c, h) = (psi_t()?, c()?, h()?);
    let stw = sp.tensor(&t)?.tensor(&w)?;
    let psi = psi_wts()?;
    assert_kernel(
        "Def. 12.1 composite of psi_t, c, h",
        &state_form(&psi_t, &c, &h)?,
        &psi,
    );
    let rev = rev3(&w, &t, &sp)?;
    let reordered = grouped(
        stw.clone(),
        &[
            &[r(1, 15), r(1, 15), r(0, 1)],
            &[r(0, 1), r(1, 20), r(3, 20)],
            &[r(1, 30), r(1, 30), r(0, 1)],
            &[r(0, 1), r(3, 20), r(9, 20)],
        ],
    )?;
    let psi_rev = psi.compose(&rev)?;
    assert_kernel("ψ ≫ tensorRev₃ W T S", &psi_rev, &reordered);
    assert_kernel(
        "Def. 12.1 composite of psi_t, h, c",
        &state_form(&psi_t, &h, &c)?,
        &psi_rev,
    );
    assert_cond_independent_state("ψ", &psi, &[0], &[1], &[2], true);
    assert_cond_independent_state("ψ ≫ tensorRev₃ W T S", &psi_rev, &[0], &[1], &[2], true);

    let psi_bad = psi_wts_bad()?;
    assert_kernel(
        "control: psi_t ≫ Δ[T] ≫ (f ▷ T) ≫ (W ◁ σ[S, T])",
        &psi_t
            .compose(&Kernel::copy(&t)?)?
            .compose(&Kernel::whisker_right(&f()?, &t)?)?
            .compose(&Kernel::whisker_left(&w, &Kernel::swap(&sp, &t)?)?)?,
        &psi_bad,
    );
    let bad_rev = psi_bad.compose(&rev)?;
    assert_kernel(
        "control: ψ_bad ≫ tensorRev₃ W T S",
        &bad_rev,
        &grouped(
            stw,
            &[
                &[r(1, 30), r(1, 10), r(0, 1)],
                &[r(0, 1), r(1, 5), r(0, 1)],
                &[r(1, 15), r(0, 1), r(0, 1)],
                &[r(0, 1), r(0, 1), r(3, 5)],
            ],
        )?,
    );
    assert_cond_independent_state("control: ψ_bad", &psi_bad, &[0], &[1], &[2], false);
    assert_cond_independent_state(
        "control: ψ_bad ≫ tensorRev₃ W T S",
        &bad_rev,
        &[0],
        &[1],
        &[2],
        false,
    );
    assert_cond_independent_state("control: ψ given S", &psi, &[0], &[2], &[1], false);
    Ok(())
}

/// The theorem drops the second factor of the first place: here `S` of
/// `(W ⊗ S) ⊗ (T ⊗ S)`. The `==` half compares the marginal with the Def. 12.1
/// composite of `psi_t`, `f ≫ (W ◁ ε[S] ≫ ρ)` and `h`.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.DisplaysCondIndepState.decomposition
#[test]
fn witness_displays_cond_indep_state_decomposition() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (psi_t, c, f, h) = (psi_t()?, c()?, f()?, h()?);
    let psi = psi5()?;
    assert_kernel(
        "Def. 12.1 composite of psi_t, f, h",
        &state_form(&psi_t, &f, &h)?,
        &psi,
    );
    let m1 = discard_snd(&w, &sp)?;
    let drop_snd = Kernel::whisker_right(&m1, &t.tensor(&sp)?)?;
    let expected = psi_wts()?;
    let marginal = psi.marginal(&[0, 2, 3])?;
    assert_kernel("ψ.marginal([0, 2, 3])", &marginal, &expected);
    assert_kernel(
        "ψ ≫ ((W ◁ ε[S] ≫ ρ) ▷ (T ⊗ S))",
        &psi.compose(&drop_snd)?,
        &marginal,
    );
    assert_kernel(
        "Def. 12.1 composite of psi_t, f ≫ (W ◁ ε[S] ≫ ρ), h",
        &state_form(&psi_t, &f.compose(&m1)?, &h)?,
        &marginal,
    );
    assert_cond_independent_state("ψ", &psi, &[0, 1], &[2], &[3], true);
    assert_cond_independent_state("ψ.marginal([0, 2, 3])", &marginal, &[0], &[1], &[2], true);

    let psi_dep = psi5_dep()?;
    assert_kernel(
        "control: Def. 12.1 composite of psi_t, c, h ≫ Δ[S], then W ◁ (σ[T, S] ▷ S)",
        &state_form(&psi_t, &c, &h.compose(&Kernel::copy(&sp)?)?)?.compose(
            &Kernel::whisker_left(&w, &Kernel::whisker_right(&Kernel::swap(&t, &sp)?, &sp)?)?,
        )?,
        &psi_dep,
    );
    assert_cond_independent_state("control: ψ'", &psi_dep, &[0, 1], &[2], &[3], false);
    let marginal_dep = psi_dep.marginal(&[0, 2, 3])?;
    assert_kernel("control: ψ'.marginal([0, 2, 3])", &marginal_dep, &expected);
    assert_kernel(
        "control: ψ' ≫ ((W ◁ ε[S] ≫ ρ) ▷ (T ⊗ S))",
        &psi_dep.compose(&drop_snd)?,
        &marginal_dep,
    );
    assert_cond_independent_state(
        "control: ψ'.marginal([0, 2, 3])",
        &marginal_dep,
        &[0],
        &[1],
        &[2],
        true,
    );
    Ok(())
}

/// At `X = W`, `W = T`, `Z = B`, `Y = S` of the running example. The `==` half
/// compares `ψ ≫ (X ◁ α)` with the Def. 12.1 composite of `psi_t`, `c` and
/// `Δ[T] ≫ (T ◁ (k ≫ Δ[B])) ≫ α⁻¹ ≫ (σ[T, B] ▷ B) ≫ α ≫ (B ◁ g)`.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.DisplaysCondIndepState.contraction
#[test]
fn witness_displays_cond_indep_state_contraction() -> Result<()> {
    let (t, w, sp, b) = (obj_t()?, obj_w()?, obj_s()?, obj_b()?);
    let (psi_t, c, k, g) = (psi_t()?, c()?, k_tb()?, g6()?);
    let tb = t.tensor(&b)?;
    let wtb = w.tensor(&tb)?;
    let cod = wtb.tensor(&sp)?;
    let phi = psi_t
        .compose(&Kernel::copy(&t)?)?
        .compose(&Kernel::whisker_left(&t, &k)?)?;
    assert_kernel(
        "psi_t ≫ Δ[T] ≫ (T ◁ k)",
        &phi,
        &Kernel::state(tb.clone(), vec![r(1, 10), r(1, 10), r(1, 5), r(3, 5)])?,
    );
    let f_tb = discard_snd(&t, &b)?.compose(&c)?;
    let psi = grouped(
        cod.clone(),
        &[
            &[r(1, 30), r(1, 60), r(1, 20), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(1, 30), r(1, 60), r(1, 20), r(0, 1)],
            &[r(1, 80), r(3, 80), r(3, 40), r(3, 40)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(3, 80), r(9, 80), r(9, 40), r(9, 40)],
        ],
    )?;
    assert_kernel(
        "Def. 12.1 composite of psi_t ≫ Δ[T] ≫ (T ◁ k), (T ◁ ε[B] ≫ ρ) ≫ c, g",
        &state_form(&phi, &f_tb, &g)?,
        &psi,
    );
    let drop_y = Kernel::whisker_left(&w, &discard_snd(&tb, &sp)?)?;
    let marginal_literal = grouped(
        wtb,
        &[
            &[r(1, 20), r(1, 20), r(0, 1), r(0, 1)],
            &[r(1, 20), r(1, 20), r(1, 20), r(3, 20)],
            &[r(0, 1), r(0, 1), r(3, 20), r(9, 20)],
        ],
    )?;
    let marginal = psi.marginal(&[0, 1, 2])?;
    assert_kernel("ψ.marginal([0, 1, 2])", &marginal, &marginal_literal);
    assert_kernel(
        "ψ ≫ (W ◁ ((T ⊗ B) ◁ ε[S] ≫ ρ))",
        &psi.compose(&drop_y)?,
        &marginal,
    );
    assert_kernel(
        "Def. 12.1 composite of psi_t, c, k",
        &state_form(&psi_t, &c, &k)?,
        &marginal,
    );
    let third = Kernel::copy(&t)?
        .compose(&Kernel::whisker_left(&t, &k.compose(&Kernel::copy(&b)?)?)?)?
        .compose(&Kernel::associator(&t, &b, &b)?)?
        .compose(&Kernel::whisker_right(&Kernel::swap(&t, &b)?, &b)?)?
        .compose(&Kernel::associator(&b, &t, &b)?)?
        .compose(&Kernel::whisker_left(&b, &g)?)?;
    assert_kernel(
        "Δ[T] ≫ (T ◁ (k ≫ Δ[B])) ≫ α⁻¹ ≫ (σ[T, B] ▷ B) ≫ α ≫ (B ◁ g)",
        &third,
        &lit(
            t.clone(),
            b.tensor(&sp)?,
            &[
                &[r(1, 3), r(1, 6), r(1, 2), r(0, 1)],
                &[r(1, 16), r(3, 16), r(3, 8), r(3, 8)],
            ],
        )?,
    );
    let assoc = Kernel::whisker_left(&w, &Kernel::associator(&t, &b, &sp)?)?;
    let conclusion = psi.compose(&assoc)?;
    assert_kernel(
        "Def. 12.1 composite of psi_t, c and the third factor",
        &state_form(&psi_t, &c, &third)?,
        &conclusion,
    );
    assert_cond_independent_state("ψ", &psi, &[0], &[1, 2], &[3], true);
    assert_cond_independent_state("ψ.marginal([0, 1, 2])", &marginal, &[0], &[1], &[2], true);
    assert_cond_independent_state("ψ ≫ (W ◁ α)", &conclusion, &[0], &[1], &[2, 3], true);

    let psi_a = psi_a()?;
    assert_cond_independent_state("control A: ψ_A", &psi_a, &[0], &[1, 2], &[3], true);
    assert_cond_independent_state(
        "control A: ψ_A ≫ (W ◁ ((T ⊗ B) ◁ ε[S] ≫ ρ))",
        &psi_a.compose(&drop_y)?,
        &[0],
        &[1],
        &[2],
        false,
    );
    assert_cond_independent_state(
        "control A: ψ_A ≫ (W ◁ α)",
        &psi_a.compose(&assoc)?,
        &[0],
        &[1],
        &[2, 3],
        false,
    );
    assert_cond_independent_state(
        "control A: ψ_A given T alone",
        &psi_a,
        &[0],
        &[1],
        &[3],
        false,
    );

    let psi_b = grouped(
        cod,
        &[
            &[r(1, 60), r(1, 30), r(1, 60), r(1, 30)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(1, 20), r(0, 1), r(1, 20), r(0, 1)],
            &[r(1, 20), r(0, 1), r(3, 20), r(0, 1)],
            &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(3, 20), r(0, 1), r(9, 20)],
        ],
    )?;
    assert_kernel(
        "control B: Def. 12.1 composite of psi_t, f, k, then W ◁ σ[S, T ⊗ B]",
        &state_form(&psi_t, &f()?, &k)?
            .compose(&Kernel::whisker_left(&w, &Kernel::swap(&sp, &tb)?)?)?,
        &psi_b,
    );
    assert_cond_independent_state("control B: ψ_B", &psi_b, &[0], &[1, 2], &[3], false);
    let marginal_b = psi_b.compose(&drop_y)?;
    assert_kernel(
        "control B: ψ_B ≫ (W ◁ ((T ⊗ B) ◁ ε[S] ≫ ρ))",
        &marginal_b,
        &marginal_literal,
    );
    assert_cond_independent_state(
        "control B: ψ_B ≫ (W ◁ ((T ⊗ B) ◁ ε[S] ≫ ρ))",
        &marginal_b,
        &[0],
        &[1],
        &[2],
        true,
    );
    assert_cond_independent_state(
        "control B: ψ_B ≫ (W ◁ α)",
        &psi_b.compose(&assoc)?,
        &[0],
        &[1],
        &[2, 3],
        false,
    );
    Ok(())
}

/// The `==` half compares `ψ ≫ tensorWeakUnionIso` with the Def. 12.1
/// composite of `psi_t ≫ Δ[T] ≫ (T ◁ marginalSnd f0)`,
/// `σ[T, S] ≫ conditional_snd(f0, W, S)` and `(T ◁ ε[S] ≫ ρ) ≫ h`.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.DisplaysCondIndepState.weak_union
#[test]
fn witness_displays_cond_indep_state_weak_union() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (psi_t, f0, h) = (psi_t()?, f0()?, h()?);
    let ts = t.tensor(&sp)?;
    let cod = w.tensor(&ts)?.tensor(&sp)?;
    let psi = psi7()?;
    assert_kernel(
        "Def. 12.1 composite of psi_t, f0, h",
        &state_form(&psi_t, &f0, &h)?,
        &psi,
    );
    let wu = weak_union(&w, &sp, &t, &sp)?;
    let after = psi.compose(&wu)?;
    assert_kernel(
        "ψ ≫ tensorWeakUnionIso W S T S",
        &after,
        &grouped(
            cod,
            &[
                &[r(2, 45), r(1, 45), r(0, 1), r(0, 1)],
                &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
                &[r(4, 45), r(2, 45), r(0, 1), r(0, 1)],
                &[r(1, 20), r(3, 20), r(0, 1), r(0, 1)],
                &[r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
                &[r(0, 1), r(0, 1), r(3, 20), r(9, 20)],
            ],
        )?,
    );

    let marginal_snd = f0.marginal_snd(&w, &sp)?;
    assert_kernel("marginalSnd f0", &marginal_snd, &k()?);
    let got = conditional_snd(&f0, &w, &sp);
    let Ok(cond) = got else {
        panic!("conditional_snd(f0, W, S): expected Ok, observed {got:?}");
    };
    assert_kernel(
        "conditional_snd(f0, W, S)",
        &cond,
        &st_to_w([r(1, 3), r(2, 3), r(0, 1)], [r(1, 3), r(1, 3), r(1, 3)])?,
    );
    let phi = psi_t
        .compose(&Kernel::copy(&t)?)?
        .compose(&Kernel::whisker_left(&t, &marginal_snd)?)?;
    assert_kernel(
        "psi_t ≫ Δ[T] ≫ (T ◁ marginalSnd f0)",
        &phi,
        &Kernel::state(ts, vec![r(1, 5), r(0, 1), r(1, 5), r(3, 5)])?,
    );
    let sigma = Kernel::swap(&t, &sp)?;
    let g_ts = discard_snd(&t, &sp)?.compose(&h)?;
    assert_kernel(
        "Def. 12.1 composite of psi_t ≫ Δ[T] ≫ (T ◁ marginalSnd f0), σ[T, S] ≫ \
         conditional_snd(f0, W, S), (T ◁ ε[S] ≫ ρ) ≫ h",
        &state_form(&phi, &sigma.compose(&cond)?, &g_ts)?,
        &after,
    );
    let free = st_to_w([r(1, 3), r(2, 3), r(0, 1)], [r(1, 1), r(0, 1), r(0, 1)])?;
    assert_differs(
        "(off, hot) at (1, 0, 0) against (1/3, 1/3, 1/3)",
        &free,
        &cond,
    );
    assert_kernel(
        "the composite with (off, hot) at (1, 0, 0), a zero-mass input",
        &state_form(&phi, &sigma.compose(&free)?, &g_ts)?,
        &after,
    );
    let changed = st_to_w([r(2, 3), r(1, 3), r(0, 1)], [r(1, 3), r(1, 3), r(1, 3)])?;
    assert_differs(
        "control: the composite with (on, hot) at (2/3, 1/3, 0), an input with mass",
        &state_form(&phi, &sigma.compose(&changed)?, &g_ts)?,
        &after,
    );
    assert_cond_independent_state("ψ", &psi, &[0, 1], &[2], &[3], true);
    assert_cond_independent_state(
        "ψ ≫ tensorWeakUnionIso W S T S",
        &after,
        &[0],
        &[1, 2],
        &[3],
        true,
    );

    let psi_d = psi_d()?;
    assert_kernel(
        "control: Def. 12.1 composite of psi_t, f, h, then W ◁ tensorRev₃ S T S",
        &state_form(&psi_t, &f()?, &h)?
            .compose(&Kernel::whisker_left(&w, &rev3(&sp, &t, &sp)?)?)?,
        &psi_d,
    );
    assert_cond_independent_state("control: ψ_d", &psi_d, &[0, 1], &[2], &[3], false);
    assert_cond_independent_state(
        "control: ψ_d ≫ tensorWeakUnionIso W S T S",
        &psi_d.compose(&wu)?,
        &[0],
        &[1, 2],
        &[3],
        false,
    );
    Ok(())
}

#[test]
fn marginal_keeps_the_listed_factors() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (ws, ss) = (w.tensor(&sp)?, sp.tensor(&sp)?);
    let k = k3()?;
    let prefix = k.marginal(&[0, 1])?;
    assert_kernel("k.marginal([0, 1])", &prefix, &f()?);
    assert_kernel(
        "marginal_fst(k, W ⊗ S, S)",
        &k.marginal_fst(&ws, &sp)?,
        &prefix,
    );
    let first = k.marginal(&[0])?;
    assert_kernel("k.marginal([0])", &first, &c()?);
    assert_kernel(
        "marginal_fst(k, W, S ⊗ S)",
        &k.marginal_fst(&w, &ss)?,
        &first,
    );
    let suffix = k.marginal(&[1, 2])?;
    assert_kernel(
        "k.marginal([1, 2])",
        &suffix,
        &lit(
            t.clone(),
            ss.clone(),
            &[
                &[r(4, 9), r(2, 9), r(2, 9), r(1, 9)],
                &[r(1, 16), r(3, 16), r(3, 16), r(9, 16)],
            ],
        )?,
    );
    assert_kernel(
        "marginal_snd(k, W, S ⊗ S)",
        &k.marginal_snd(&w, &ss)?,
        &suffix,
    );
    let last = k.marginal(&[2])?;
    assert_kernel("k.marginal([2])", &last, &h()?);
    assert_kernel(
        "marginal_snd(k, W ⊗ S, S)",
        &k.marginal_snd(&ws, &sp)?,
        &last,
    );
    assert_kernel("k.marginal([1])", &k.marginal(&[1])?, &h()?);
    assert_kernel("k.marginal([])", &k.marginal(&[])?, &Kernel::del(&t)?);
    assert_kernel("k.marginal([0, 1, 2])", &k.marginal(&[0, 1, 2])?, &k);

    let psi = psi7()?;
    for (list, cod, weights) in [
        (&[1][..], sp.clone(), vec![r(2, 5), r(3, 5)]),
        (&[2][..], t.clone(), vec![r(1, 5), r(4, 5)]),
        (&[3][..], sp.clone(), vec![r(1, 3), r(2, 3)]),
        (
            &[1, 2][..],
            sp.tensor(&t)?,
            vec![r(1, 5), r(1, 5), r(0, 1), r(3, 5)],
        ),
        (
            &[0, 3][..],
            ws.clone(),
            vec![r(2, 45), r(1, 45), r(5, 36), r(7, 36), r(3, 20), r(9, 20)],
        ),
        (&[][..], FinObj::unit(), vec![r(1, 1)]),
    ] {
        assert_kernel(
            &format!("ψ7.marginal({list:?})"),
            &psi.marginal(list)?,
            &Kernel::state(cod, weights)?,
        );
    }
    assert_kernel(
        "ψ7.marginal([0, 1, 2, 3])",
        &psi.marginal(&[0, 1, 2, 3])?,
        &psi,
    );

    let cod = ws.tensor(&sp)?;
    for (name, list) in [
        ("decreasing", &[1, 0][..]),
        ("repeated", &[0, 0][..]),
        ("out of range", &[3][..]),
        ("last out of range", &[0, 3][..]),
        ("first out of range and decreasing", &[5, 1][..]),
    ] {
        assert_not_a_factor_list(
            &format!("k.marginal({list:?}), {name}"),
            &k.marginal(list),
            &cod,
            list,
        );
    }
    assert_not_a_factor_list(
        "ε[T].marginal([0]), a codomain with no factor",
        &Kernel::<Exact>::del(&t)?.marginal(&[0]),
        &FinObj::unit(),
        &[0],
    );

    let (empty, huge) = (FinObj::new(0), FinObj::new(usize::MAX));
    let wide = Kernel::<Exact>::new(
        empty.clone(),
        empty.tensor(&huge)?.tensor(&huge)?,
        Vec::new(),
    )?;
    let got = wide.marginal(&[1, 2]);
    assert!(
        matches!(&got, Err(Error::TooLarge { fst, snd, source: None })
            if *fst == usize::MAX && *snd == usize::MAX),
        "(0 → [0] ⊗ [usize::MAX] ⊗ [usize::MAX]).marginal([1, 2]): expected TooLarge {{ fst: \
         {max}, snd: {max}, source: None }}, observed {got:?}",
        max = usize::MAX
    );
    let narrow = Kernel::<Exact>::new(empty.clone(), empty.clone(), Vec::new())?;
    let tall = Kernel::<Exact>::new(empty, huge, Vec::new())?;
    let failed: Vec<String> = [
        (
            "(0 → [0] ⊗ [usize::MAX] ⊗ [usize::MAX]).marginal([0])",
            wide.marginal(&[0]),
            &narrow,
        ),
        (
            "(0 → [0] ⊗ [usize::MAX] ⊗ [usize::MAX]).marginal([0, 1, 2])",
            wide.marginal(&[0, 1, 2]),
            &wide,
        ),
        (
            "(0 → [usize::MAX]).marginal([0])",
            tall.marginal(&[0]),
            &tall,
        ),
    ]
    .into_iter()
    .filter(|(_, got, expected)| !got.as_ref().is_ok_and(|kernel| kernel == *expected))
    .map(|(call, got, expected)| format!("{call}: expected Ok({expected:?}), observed {got:?}"))
    .collect();
    assert!(
        failed.is_empty(),
        "marginal on an empty domain:\n{}",
        failed.join("\n")
    );
    Ok(())
}

/// On states with factors of 3, 2, 2 and 2 elements, with the factor 1
/// between the factors 0 and 2 of one list.
#[test]
fn is_cond_independent_state_reads_a_list_that_another_interleaves() -> Result<()> {
    let (t, w, sp, b) = (obj_t()?, obj_w()?, obj_s()?, obj_b()?);
    let psi = psi_wtsb()?;
    assert_kernel(
        "Def. 12.1 composite of psi_t, f, k_tb, then W ◁ (σ[S, T] ▷ B)",
        &state_form(&psi_t()?, &f()?, &k_tb()?)?.compose(&Kernel::whisker_left(
            &w,
            &Kernel::whisker_right(&Kernel::swap(&sp, &t)?, &b)?,
        )?)?,
        &psi,
    );
    assert_cond_independent_state("ψ_i", &psi, &[0, 2], &[1], &[3], true);
    assert_cond_independent_state("ψ_i", &psi, &[3], &[1], &[0, 2], true);
    let psi_dep = psi_wtsb_dep()?;
    assert_cond_independent_state("control: ψ_i'", &psi_dep, &[0, 2], &[1], &[3], false);
    assert_cond_independent_state("control: ψ_i'", &psi_dep, &[3], &[1], &[0, 2], false);
    Ok(())
}

#[test]
fn is_cond_independent_state_sums_out_a_factor_in_no_list() -> Result<()> {
    let t = obj_t()?;
    let (psi, psi_dep, psi_d) = (psi5()?, psi5_dep()?, psi_d()?);
    assert_cond_independent_state("ψ5", &psi, &[0], &[2], &[3], true);
    assert_cond_independent_state("ψ5_dep", &psi_dep, &[0], &[2], &[3], true);
    assert_cond_independent_state("control: ψ5_dep", &psi_dep, &[0, 1], &[2], &[3], false);
    assert_cond_independent_state("ψ_d", &psi_d, &[1], &[2], &[3], true);
    assert_cond_independent_state("ψ_d", &psi_d, &[0], &[2], &[1], true);
    assert_cond_independent_state("control: ψ_d", &psi_d, &[0], &[2], &[3], false);
    assert_cond_independent_state("p_ind", &p_ind()?, &[0], &[], &[1], true);
    assert_cond_independent_state("control: p_brk", &p_brk()?, &[0], &[], &[1], false);
    let psi_bad = psi_wts_bad()?;
    assert_cond_independent_state("control: ψ_bad", &psi_bad, &[0], &[], &[2], false);
    assert_cond_independent_state(
        "ψ_bad, pins only the Ok of the empty xs path",
        &psi_bad,
        &[],
        &[1],
        &[2],
        true,
    );
    let psi_a = psi_a()?;
    assert_cond_independent_state("ψ_A", &psi_a, &[0], &[1, 2], &[3], true);
    assert_cond_independent_state("control: ψ_A", &psi_a, &[0], &[1], &[3], false);

    let cod = wsts()?;
    for (name, xs, ws, ys, list) in [
        (
            "xs decreasing",
            &[1, 0][..],
            &[2][..],
            &[3][..],
            &[1, 0][..],
        ),
        ("ws out of range", &[0][..], &[4][..], &[3][..], &[4][..]),
        ("ys repeated", &[0][..], &[2][..], &[3, 3][..], &[3, 3][..]),
        (
            "xs decreasing before ws out of range",
            &[1, 0][..],
            &[4][..],
            &[3][..],
            &[1, 0][..],
        ),
        (
            "ws out of range before xs and ys share 0",
            &[0][..],
            &[4][..],
            &[0][..],
            &[4][..],
        ),
        (
            "ws out of range before ys repeated",
            &[0][..],
            &[4][..],
            &[3, 3][..],
            &[4][..],
        ),
        (
            "xs decreasing before ys repeated",
            &[1, 0][..],
            &[2][..],
            &[3, 3][..],
            &[1, 0][..],
        ),
    ] {
        assert_not_a_factor_list(
            &format!("is_cond_independent_state(ψ5, {xs:?}, {ws:?}, {ys:?}), {name}"),
            &is_cond_independent_state(&psi, xs, ws, ys),
            &cod,
            list,
        );
    }
    for (name, xs, ws, ys, fst, snd) in [
        (
            "xs and ws share 1",
            &[0, 1][..],
            &[1][..],
            &[3][..],
            &[0, 1][..],
            &[1][..],
        ),
        (
            "xs and ys share 0",
            &[0][..],
            &[2][..],
            &[0, 3][..],
            &[0][..],
            &[0, 3][..],
        ),
        (
            "ws and ys share 3",
            &[0][..],
            &[2, 3][..],
            &[3][..],
            &[2, 3][..],
            &[3][..],
        ),
        (
            "xs and ws share 0 before xs and ys share 0",
            &[0][..],
            &[0, 1][..],
            &[0, 2][..],
            &[0][..],
            &[0, 1][..],
        ),
        (
            "xs and ys share 0 before ws and ys share 2",
            &[0][..],
            &[2][..],
            &[0, 2][..],
            &[0][..],
            &[0, 2][..],
        ),
    ] {
        let got = is_cond_independent_state(&psi, xs, ws, ys);
        assert!(
            matches!(&got, Err(Error::SharedFactorIndex { codomain, fst: a, snd: b })
                if *codomain == cod && a == fst && b == snd),
            "is_cond_independent_state(ψ5, {xs:?}, {ws:?}, {ys:?}), {name}: expected \
             SharedFactorIndex {{ codomain: {cod:?}, fst: {fst:?}, snd: {snd:?} }}, observed \
             {got:?}"
        );
    }
    let unit = FinObj::unit();
    for (error, expected) in [
        (
            Error::NotAFactorList {
                codomain: unit.clone(),
                list: vec![1, 0],
            },
            "[1, 0] is not a strictly increasing list of indices into the factors of FinObj { \
             factors: [], card: 1 }",
        ),
        (
            Error::SharedFactorIndex {
                codomain: unit,
                fst: vec![0, 1],
                snd: vec![1],
            },
            "the lists [0, 1] and [1] of factor indices of FinObj { factors: [], card: 1 } share \
             an index",
        ),
    ] {
        let shown = error.to_string();
        assert_eq!(
            shown, expected,
            "Display of {error:?}: expected the text on the right, observed on the left"
        );
    }

    let c = c()?;
    for (name, xs) in [("lists in range", &[0][..]), ("xs decreasing", &[1, 0][..])] {
        let got = is_cond_independent_state(&c, xs, &[], &[]);
        assert!(
            matches!(&got, Err(Error::NotAState { domain }) if *domain == t),
            "is_cond_independent_state(c : T → W, {xs:?}, [], []), {name}: expected NotAState {{ \
             domain: {t:?} }}, observed {got:?}"
        );
    }
    Ok(())
}
