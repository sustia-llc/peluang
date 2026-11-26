//! Witnesses of `tensorRev₃_eq_tensorLeftComm`, `tensorRev₃_hom_naturality`,
//! `isConditionalSnd_iff`, `exists_isConditionalSnd` and
//! `marginalFst_comp_braiding_hom`: the reorder kernels built from
//! `Kernel::swap`, `Kernel::associator`, `Kernel::whisker_left` and
//! `Kernel::whisker_right`, and `conditional_snd`. Also, untagged:
//! `conditional_snd` against two literals with zero-mass columns and against
//! `conditional` after `Kernel::swap`, and the `Error::NotATensor` and
//! `Error::NoUniformWeight` of `conditional_snd`.

use peluang::conditional::{conditional, conditional_snd};
use peluang::error::{Error, Result};
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::{Compose, Tensor};
use peluang::prob::{Exact, Prob};

use crate::fixtures::{
    assert_differs, assert_kernel, c, conditional_composite, f, h, k, labels, lit, m, obj_s, obj_t,
    obj_w, points, r, s, show,
};

/// `(tensorLeftComm x y z).hom`: `α⁻¹[x, y, z] ≫ (σ[x, y] ▷ z) ≫ α[y, x, z]`.
fn left_comm(x: &FinObj, y: &FinObj, z: &FinObj) -> Result<Kernel<Exact>> {
    Kernel::associator(x, y, z)?
        .compose(&Kernel::whisker_right(&Kernel::swap(x, y)?, z)?)?
        .compose(&Kernel::associator(y, x, z)?)
}

/// `(tensorRev₃ x w y).hom`: `σ[x, w ⊗ y] ≫ (σ[w, y] ▷ x) ≫ α[y, w, x]`.
fn rev3(x: &FinObj, w: &FinObj, y: &FinObj) -> Result<Kernel<Exact>> {
    Kernel::swap(x, &w.tensor(y)?)?
        .compose(&Kernel::whisker_right(&Kernel::swap(w, y)?, x)?)?
        .compose(&Kernel::associator(y, w, x)?)
}

/// `tensorLeftComm x w y ≫ (w ◁ σ[x, y]) ≫ tensorLeftComm w y x`.
fn rev3_from_left_comm(x: &FinObj, w: &FinObj, y: &FinObj) -> Result<Kernel<Exact>> {
    left_comm(x, w, y)?
        .compose(&Kernel::whisker_left(w, &Kernel::swap(x, y)?)?)?
        .compose(&left_comm(w, y, x)?)
}

/// The state on `cod` with weight `weight` at each `(output, weight)` of
/// `atoms` and 0 at every other output, through `Kernel::state`.
fn sparse(cod: FinObj, atoms: &[(usize, Exact)]) -> Result<Kernel<Exact>> {
    let mut weights = vec![r(0, 1); cod.card()];
    for (output, weight) in atoms {
        weights[*output] = weight.clone();
    }
    Kernel::state(cod, weights)
}

/// The composite `Δ[A] ≫ (A ◁ (marginalSnd f ≫ Δ[y])) ≫ α⁻¹[A, y, y] ≫
/// (σ[A, y] ▷ y) ≫ (g ▷ y)` with `A` the domain of `f : A → x ⊗ y`.
fn conditional_snd_composite(
    f: &Kernel<Exact>,
    x: &FinObj,
    y: &FinObj,
    g: &Kernel<Exact>,
) -> Result<Kernel<Exact>> {
    let a = f.domain();
    let marginal_copy = f.marginal_snd(x, y)?.compose(&Kernel::copy(y)?)?;
    Kernel::copy(a)?
        .compose(&Kernel::whisker_left(a, &marginal_copy)?)?
        .compose(&Kernel::associator(a, y, y)?)?
        .compose(&Kernel::whisker_right(&Kernel::swap(a, y)?, y)?)?
        .compose(&Kernel::whisker_right(g, y)?)
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

/// `joint_ss` with sunny to `(3/4, 0, 1/4, 0)`: no mass at second factor off
/// on input sunny.
fn joint_ss_zero() -> Result<Kernel<Exact>> {
    lit(
        obj_w()?,
        obj_s()?.tensor(&obj_s()?)?,
        &[
            &[r(3, 4), r(0, 1), r(1, 4), r(0, 1)],
            &[r(1, 10), r(2, 5), r(3, 10), r(1, 5)],
            &[r(1, 3), r(1, 6), r(1, 4), r(1, 4)],
        ],
    )
}

/// The kernel `S ⊗ W → S` with the columns `on_sunny` at `(on, sunny)`,
/// `off_sunny` at `(off, sunny)`, `(1/4, 3/4)` at `(on, cloudy)`, `(4/7, 3/7)`
/// at `(on, rainy)`, `(2/3, 1/3)` at `(off, cloudy)` and `(2/5, 3/5)` at
/// `(off, rainy)`.
fn snd_conditional(on_sunny: [Exact; 2], off_sunny: [Exact; 2]) -> Result<Kernel<Exact>> {
    lit(
        obj_s()?.tensor(&obj_w()?)?,
        obj_s()?,
        &[
            &on_sunny,
            &[r(1, 4), r(3, 4)],
            &[r(4, 7), r(3, 7)],
            &off_sunny,
            &[r(2, 3), r(1, 3)],
            &[r(2, 5), r(3, 5)],
        ],
    )
}

/// `conditional_snd(f, x, y)`; panics with `call` and the error when the
/// engine returns an error.
#[track_caller]
fn snd(call: &str, f: &Kernel<Exact>, x: &FinObj, y: &FinObj) -> Kernel<Exact> {
    match conditional_snd(f, x, y) {
        Ok(g) => g,
        Err(e) => panic!("{call} on {}: expected Ok, observed Err({e:?})", show(f)),
    }
}

/// Asserts that `IsConditionalSnd f g`, unfolded to
/// `IsConditional (f ≫ σ[x, y]) g`, has the truth value `expected`: the
/// Def. 11.5 composite of `g` on `f ≫ σ[x, y] : A → y ⊗ x` equals
/// `f ≫ σ[x, y]`. `name` names `g`.
#[track_caller]
fn assert_is_conditional_snd(
    name: &str,
    f: &Kernel<Exact>,
    x: &FinObj,
    y: &FinObj,
    g: &Kernel<Exact>,
    expected: bool,
) {
    let got = Kernel::swap(x, y).and_then(|sigma| f.compose(&sigma));
    let Ok(fs) = got else {
        panic!("IsConditionalSnd f g at g = {name}: f ≫ σ: expected Ok, observed {got:?}");
    };
    let got = conditional_composite(&fs, y, x, g);
    let Ok(composite) = got else {
        panic!(
            "IsConditionalSnd f g at g = {name}: Def. 11.5 composite of g on f ≫ σ: expected \
             Ok(composite) with (composite == {}) == {expected}, observed {got:?}",
            show(&fs)
        );
    };
    let observed = composite == fs;
    assert_eq!(
        observed,
        expected,
        "IsConditionalSnd f g at g = {name}, the Def. 11.5 composite of g on f ≫ σ == f ≫ σ: \
         expected {expected}, the truth value of the right side of isConditionalSnd_iff at g, \
         observed {observed}; composite {}, f ≫ σ {}",
        show(&composite),
        show(&fs)
    );
}

/// Asserts that `g` has the domain `dom` and the codomain `cod`. `name` names
/// `g`.
#[track_caller]
fn assert_objects(name: &str, g: &Kernel<Exact>, dom: &FinObj, cod: &FinObj) {
    assert!(
        g.domain() == dom && g.codomain() == cod,
        "{name}: expected {dom:?} → {cod:?}, observed {:?} → {:?}",
        g.domain(),
        g.codomain()
    );
}

/// THEOREM_MAP: CategoryTheory.MonoidalCategory.tensorRev₃_eq_tensorLeftComm
#[test]
fn witness_tensor_rev3_eq_tensor_left_comm() -> Result<()> {
    let (t, w, d) = (
        obj_t()?,
        obj_w()?,
        labels(&["north", "east", "south", "west"])?,
    );
    let (dom, cod) = (t.tensor(&w)?.tensor(&d)?, d.tensor(&w)?.tensor(&t)?);
    let reversal = points(
        dom.clone(),
        cod.clone(),
        &[
            0, 6, 12, 18, 2, 8, 14, 20, 4, 10, 16, 22, 1, 7, 13, 19, 3, 9, 15, 21, 5, 11, 17, 23,
        ],
    )?;
    let lhs = rev3(&t, &w, &d)?;
    let rhs = rev3_from_left_comm(&t, &w, &d)?;
    assert_kernel("tensorRev₃ T W D", &lhs, &reversal);
    assert_kernel(
        "tensorLeftComm T W D ≫ (W ◁ σ[T, D]) ≫ tensorLeftComm W D T",
        &rhs,
        &lhs,
    );

    let psi = sparse(dom.clone(), &[(7, r(1, 2)), (14, r(1, 6)), (20, r(1, 3))])?;
    let image = sparse(cod.clone(), &[(5, r(1, 3)), (13, r(1, 6)), (20, r(1, 2))])?;
    assert_kernel("psi ≫ tensorRev₃ T W D", &psi.compose(&lhs)?, &image);
    assert_kernel(
        "psi ≫ tensorLeftComm T W D ≫ (W ◁ σ[T, D]) ≫ tensorLeftComm W D T",
        &psi.compose(&rhs)?,
        &image,
    );

    let flat = Kernel::from_fn(dom, cod, |i| i)?;
    assert_differs(
        "control: tensorRev₃ T W D against the identity on indices",
        &lhs,
        &flat,
    );

    let lhs = rev3(&t, &w, &t)?;
    assert_kernel(
        "tensorLeftComm T W T ≫ (W ◁ σ[T, T]) ≫ tensorLeftComm W T T",
        &rev3_from_left_comm(&t, &w, &t)?,
        &lhs,
    );
    let unbraided = left_comm(&t, &w, &t)?.compose(&left_comm(&w, &t, &t)?)?;
    assert_differs(
        "control: tensorLeftComm T W T ≫ tensorLeftComm W T T, without W ◁ σ[T, T]",
        &unbraided,
        &lhs,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.MonoidalCategory.tensorRev₃_hom_naturality
#[test]
fn witness_tensor_rev3_hom_naturality() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (c, s, m) = (c()?, s()?, m()?);
    let lhs = c.tensor(&s.tensor(&m)?)?.compose(&rev3(&w, &sp, &t)?)?;
    let rhs = rev3(&t, &w, &sp)?.compose(&m.tensor(&s.tensor(&c)?)?)?;
    assert_kernel(
        "(c ⊗ₘ (s ⊗ₘ m)) ≫ tensorRev₃ W S T against tensorRev₃ T W S ≫ (m ⊗ₘ (s ⊗ₘ c))",
        &lhs,
        &rhs,
    );

    let psi = sparse(t.tensor(&w)?.tensor(&sp)?, &[(0, r(1, 3)), (7, r(2, 3))])?;
    let image = Kernel::state(
        t.tensor(&sp)?.tensor(&w)?,
        vec![
            r(1, 18),
            r(1, 12),
            r(1, 12),
            r(1, 9),
            r(1, 6),
            r(1, 6),
            r(0, 1),
            r(1, 36),
            r(1, 12),
            r(0, 1),
            r(1, 18),
            r(1, 6),
        ],
    )?;
    assert_kernel(
        "psi ≫ (c ⊗ₘ (s ⊗ₘ m)) ≫ tensorRev₃ W S T",
        &psi.compose(&lhs)?,
        &image,
    );
    assert_kernel(
        "psi ≫ tensorRev₃ T W S ≫ (m ⊗ₘ (s ⊗ₘ c))",
        &psi.compose(&rhs)?,
        &image,
    );

    let (h, k) = (h()?, k()?);
    assert_differs("h against k", &h, &k);
    let lhs = h.tensor(&s.tensor(&k)?)?.compose(&rev3(&sp, &sp, &sp)?)?;
    let rhs = rev3(&t, &w, &t)?.compose(&k.tensor(&s.tensor(&h)?)?)?;
    assert_kernel(
        "(h ⊗ₘ (s ⊗ₘ k)) ≫ tensorRev₃ S S S against tensorRev₃ T W T ≫ (k ⊗ₘ (s ⊗ₘ h))",
        &lhs,
        &rhs,
    );
    let exchanged = rev3(&t, &w, &t)?.compose(&h.tensor(&s.tensor(&k)?)?)?;
    assert_differs(
        "control: tensorRev₃ T W T ≫ (h ⊗ₘ (s ⊗ₘ k)), h and k exchanged, against (h ⊗ₘ (s ⊗ₘ \
         k)) ≫ tensorRev₃ S S S",
        &exchanged,
        &lhs,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.isConditionalSnd_iff
#[test]
fn witness_is_conditional_snd_iff() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let f_ws = f()?;
    let f = joint_ss()?;
    let g = snd("conditional_snd(f, S, S)", &f, &sp, &sp);
    assert_kernel(
        "conditional_snd(f, S, S)",
        &g,
        &snd_conditional([r(4, 5), r(1, 5)], [r(2, 3), r(1, 3)])?,
    );
    assert_is_conditional_snd("conditional_snd(f, S, S)", &f, &sp, &sp, &g, true);
    assert_kernel(
        "Δ[W] ≫ (W ◁ (marginalSnd f ≫ Δ[S])) ≫ α⁻¹ ≫ (σ[W, S] ▷ S) ≫ (conditional_snd(f, S, S) \
         ▷ S)",
        &conditional_snd_composite(&f, &sp, &sp, &g)?,
        &f,
    );

    let got = conditional(&f, &sp, &sp);
    let Ok(on_fst) = got else {
        panic!("conditional(f, S, S): expected Ok, observed {got:?}");
    };
    assert_is_conditional_snd(
        "control: conditional(f, S, S), the conditional on the first factor",
        &f,
        &sp,
        &sp,
        &on_fst,
        false,
    );
    assert_differs(
        "control: Δ[W] ≫ (W ◁ (marginalSnd f ≫ Δ[S])) ≫ α⁻¹ ≫ (σ[W, S] ▷ S) ≫ (conditional(f, \
         S, S) ▷ S), the conditional on the first factor",
        &conditional_snd_composite(&f, &sp, &sp, &on_fst)?,
        &f,
    );

    let on_hot = |column: [Exact; 3]| {
        lit(
            sp.tensor(&t)?,
            w.clone(),
            &[
                &column,
                &[r(0, 1), r(1, 1), r(0, 1)],
                &[r(1, 1), r(0, 1), r(0, 1)],
                &[r(0, 1), r(0, 1), r(1, 1)],
            ],
        )
    };
    let g = snd("conditional_snd(f : T → W ⊗ S, W, S)", &f_ws, &w, &sp);
    assert_kernel(
        "conditional_snd(f : T → W ⊗ S, W, S)",
        &g,
        &on_hot([r(1, 4), r(3, 4), r(0, 1)])?,
    );
    assert_is_conditional_snd(
        "conditional_snd(f : T → W ⊗ S, W, S)",
        &f_ws,
        &w,
        &sp,
        &g,
        true,
    );
    assert_kernel(
        "Δ[T] ≫ (T ◁ (marginalSnd f ≫ Δ[S])) ≫ α⁻¹ ≫ (σ[T, S] ▷ S) ≫ (conditional_snd(f : T → W \
         ⊗ S, W, S) ▷ S)",
        &conditional_snd_composite(&f_ws, &w, &sp, &g)?,
        &f_ws,
    );
    let changed = on_hot([r(3, 4), r(1, 4), r(0, 1)])?;
    assert_is_conditional_snd(
        "control: the kernel S ⊗ T → W with (on, hot) at (3/4, 1/4, 0), an input with mass",
        &f_ws,
        &w,
        &sp,
        &changed,
        false,
    );
    assert_differs(
        "control: the composite of the kernel S ⊗ T → W with (on, hot) at (3/4, 1/4, 0), an \
         input with mass",
        &conditional_snd_composite(&f_ws, &w, &sp, &changed)?,
        &f_ws,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.exists_isConditionalSnd
#[test]
fn witness_exists_is_conditional_snd() -> Result<()> {
    let sp = obj_s()?;
    let f = joint_ss_zero()?;
    let literal = snd_conditional([r(3, 4), r(1, 4)], [r(1, 2), r(1, 2)])?;
    let g = snd("conditional_snd(f0, S, S)", &f, &sp, &sp);
    assert_kernel("conditional_snd(f0, S, S)", &g, &literal);
    assert_is_conditional_snd("conditional_snd(f0, S, S)", &f, &sp, &sp, &g, true);
    assert_kernel(
        "Δ[W] ≫ (W ◁ (marginalSnd f0 ≫ Δ[S])) ≫ α⁻¹ ≫ (σ[W, S] ▷ S) ≫ (conditional_snd(f0, S, \
         S) ▷ S)",
        &conditional_snd_composite(&f, &sp, &sp, &g)?,
        &f,
    );

    let free = snd_conditional([r(3, 4), r(1, 4)], [r(1, 1), r(0, 1)])?;
    assert_differs("(off, sunny) at (1, 0) against (1/2, 1/2)", &free, &literal);
    assert_is_conditional_snd(
        "the kernel with (off, sunny) at (1, 0), a zero-mass input",
        &f,
        &sp,
        &sp,
        &free,
        true,
    );
    assert_kernel(
        "the composite of the kernel with (off, sunny) at (1, 0), a zero-mass input",
        &conditional_snd_composite(&f, &sp, &sp, &free)?,
        &f,
    );
    let changed = snd_conditional([r(1, 4), r(3, 4)], [r(1, 2), r(1, 2)])?;
    assert_is_conditional_snd(
        "control: the kernel with (on, sunny) at (1/4, 3/4), an input with mass",
        &f,
        &sp,
        &sp,
        &changed,
        false,
    );
    assert_differs(
        "control: the composite of the kernel with (on, sunny) at (1/4, 3/4), an input with mass",
        &conditional_snd_composite(&f, &sp, &sp, &changed)?,
        &f,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.marginalFst_comp_braiding_hom
#[test]
fn witness_marginal_fst_comp_braiding_hom() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let joint = joint_ss()?;
    let literal = lit(
        w.clone(),
        sp.clone(),
        &[
            &[r(5, 8), r(3, 8)],
            &[r(2, 5), r(3, 5)],
            &[r(7, 12), r(5, 12)],
        ],
    )?;
    let lhs = joint
        .compose(&Kernel::swap(&sp, &sp)?)?
        .marginal_fst(&sp, &sp)?;
    let rhs = joint.marginal_snd(&sp, &sp)?;
    assert_kernel("marginalSnd f", &rhs, &literal);
    assert_kernel("marginalFst (f ≫ σ[S, S])", &lhs, &rhs);
    assert_differs(
        "control: marginalFst (f ≫ σ[S, S]) against marginalFst f",
        &lhs,
        &joint.marginal_fst(&sp, &sp)?,
    );

    let joint = f()?;
    let literal = lit(t, sp.clone(), &[&[r(2, 3), r(1, 3)], &[r(1, 4), r(3, 4)]])?;
    let lhs = joint
        .compose(&Kernel::swap(&w, &sp)?)?
        .marginal_fst(&sp, &w)?;
    let rhs = joint.marginal_snd(&w, &sp)?;
    assert_kernel("marginalSnd (f : T → W ⊗ S)", &rhs, &literal);
    assert_kernel("marginalFst ((f : T → W ⊗ S) ≫ σ[W, S])", &lhs, &rhs);
    Ok(())
}

#[test]
fn conditional_snd_equals_conditional_after_swap() -> Result<()> {
    let (t, w, sp, empty) = (obj_t()?, obj_w()?, obj_s()?, FinObj::new(0));
    let state = Kernel::state(
        t.tensor(&w)?,
        vec![r(1, 10), r(1, 10), r(0, 1), r(0, 1), r(1, 5), r(3, 5)],
    )?;
    let dry = Kernel::state(
        t.tensor(&w)?,
        vec![r(1, 2), r(1, 2), r(0, 1), r(0, 1), r(0, 1), r(0, 1)],
    )?;
    assert_kernel(
        "conditional_snd(I → T ⊗ W with no mass at rainy)",
        &snd(
            "conditional_snd(I → T ⊗ W with no mass at rainy)",
            &dry,
            &t,
            &w,
        ),
        &lit(
            w.clone(),
            t.clone(),
            &[
                &[r(1, 1), r(0, 1)],
                &[r(1, 1), r(0, 1)],
                &[r(1, 2), r(1, 2)],
            ],
        )?,
    );
    let arid = Kernel::state(
        t.tensor(&w)?,
        vec![r(1, 4), r(0, 1), r(0, 1), r(3, 4), r(0, 1), r(0, 1)],
    )?;
    assert_kernel(
        "conditional_snd(I → T ⊗ W with no mass at cloudy and at rainy)",
        &snd(
            "conditional_snd(I → T ⊗ W with no mass at cloudy and at rainy)",
            &arid,
            &t,
            &w,
        ),
        &lit(
            w.clone(),
            t.clone(),
            &[
                &[r(1, 4), r(3, 4)],
                &[r(1, 2), r(1, 2)],
                &[r(1, 2), r(1, 2)],
            ],
        )?,
    );
    let empty_s = Kernel::<Exact>::new(empty.clone(), w.tensor(&sp)?, Vec::new())?;
    let empty_empty = Kernel::<Exact>::new(empty.clone(), empty.tensor(&sp)?, Vec::new())?;
    let empty_snd = Kernel::<Exact>::new(empty.clone(), w.tensor(&empty)?, Vec::new())?;
    assert_objects(
        "conditional_snd(0 → W ⊗ S)",
        &snd("conditional_snd(0 → W ⊗ S)", &empty_s, &w, &sp),
        &sp.tensor(&empty)?,
        &w,
    );
    assert_objects(
        "conditional_snd(0 → 0 ⊗ S)",
        &snd("conditional_snd(0 → 0 ⊗ S)", &empty_empty, &empty, &sp),
        &sp.tensor(&empty)?,
        &empty,
    );
    assert_objects(
        "conditional_snd(0 → W ⊗ 0)",
        &snd("conditional_snd(0 → W ⊗ 0)", &empty_snd, &w, &empty),
        &empty.tensor(&empty)?,
        &w,
    );
    for (name, k, x, y) in [
        ("I → T ⊗ W with no mass at rainy", dry, &t, &w),
        ("f : T → W ⊗ S", f()?, &w, &sp),
        ("W → S ⊗ S", joint_ss()?, &sp, &sp),
        (
            "W → S ⊗ S with a zero-mass input",
            joint_ss_zero()?,
            &sp,
            &sp,
        ),
        ("I → T ⊗ W", state, &t, &w),
        ("0 → W ⊗ S", empty_s, &w, &sp),
        ("0 → 0 ⊗ S", empty_empty, &empty, &sp),
        ("0 → W ⊗ 0", empty_snd, &w, &empty),
    ] {
        let got = Kernel::swap(x, y)
            .and_then(|sigma| k.compose(&sigma))
            .and_then(|swapped| conditional(&swapped, y, x));
        let Ok(expected) = got else {
            panic!("{name}: conditional after σ: expected Ok, observed {got:?}");
        };
        let g = snd(&format!("conditional_snd({name})"), &k, x, y);
        assert_kernel(
            &format!("conditional_snd({name}) against conditional after σ"),
            &g,
            &expected,
        );
    }

    let joint = joint_ss()?;
    let got = conditional(&joint, &sp, &sp);
    let Ok(on_fst) = got else {
        panic!("control: conditional(W → S ⊗ S): expected Ok, observed {got:?}");
    };
    assert_differs(
        "control: conditional_snd(W → S ⊗ S) against conditional(W → S ⊗ S)",
        &snd("conditional_snd(W → S ⊗ S)", &joint, &sp, &sp),
        &on_fst,
    );
    Ok(())
}

#[test]
fn conditional_snd_rejects_a_wrong_split() -> Result<()> {
    let (w, sp) = (obj_w()?, obj_s()?);
    let f = f()?;
    let cod = w.tensor(&sp)?;
    for (name, x, y) in [
        ("factors swapped", &sp, &w),
        ("mismatch only on x", &sp, &sp),
        ("mismatch only on y", &w, &w),
        ("x is the whole codomain", &cod, &FinObj::new(1)),
    ] {
        let got = conditional_snd(&f, x, y);
        assert!(
            matches!(&got, Err(Error::NotATensor { codomain, fst, snd })
                if *codomain == cod && fst == x && snd == y),
            "{name}: expected NotATensor {{ codomain: {cod:?}, fst: {x:?}, snd: {y:?} }}, observed {got:?}"
        );
    }
    Ok(())
}

/// Exact weights whose `add` is left projection.
#[derive(Clone, Debug, PartialEq)]
struct LeftProj(Exact);

impl Prob for LeftProj {
    fn zero() -> Self {
        LeftProj(Exact::zero())
    }

    fn one() -> Self {
        LeftProj(Exact::one())
    }

    fn add(&self, _other: &Self) -> Self {
        self.clone()
    }

    fn mul(&self, other: &Self) -> Self {
        LeftProj(self.0.mul(&other.0))
    }

    fn div_checked(&self, other: &Self) -> Option<Self> {
        self.0.div_checked(&other.0).map(LeftProj)
    }

    fn is_nonneg(&self) -> bool {
        self.0.is_nonneg()
    }

    fn approx_eq(&self, other: &Self) -> bool {
        self.0.approx_eq(&other.0)
    }
}

/// On `LeftProj` weights, `conditional_snd` of the point state at 0 of
/// `[3] ⊗ [2]` on `[2]` returns `Error::NoUniformWeight { card: 3 }`.
#[test]
fn conditional_snd_reports_no_uniform_weight_on_left_projection_add() -> Result<()> {
    let (x, y) = (FinObj::new(3), FinObj::new(2));
    let f = Kernel::<LeftProj>::from_fn(FinObj::unit(), x.tensor(&y)?, |_| 0)?;
    let got = conditional_snd(&f, &x, &y);
    assert!(
        matches!(got, Err(Error::NoUniformWeight { card: 3 })),
        "conditional_snd(point at 0 of [3] ⊗ [2], [3], [2]) on left-projection add: expected \
         Err(NoUniformWeight {{ card: 3 }}), observed {got:?}"
    );
    Ok(())
}
