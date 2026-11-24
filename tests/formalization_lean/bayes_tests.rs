//! Witnesses of the theorems of `Peluang.BayesianInverse`,
//! `Peluang.AlmostSure.Deterministic`,
//! `Peluang.Instances.FinStoch.BayesianInverse` and
//! `Peluang.Instances.FinStoch.AlmostSureDeterministic` at the running example,
//! and the rejections of `bayesian_inverse`, `is_bayesian_inverse` and
//! `is_as_deterministic`.

use peluang::bayes::{bayesian_inverse, is_bayesian_inverse};
use peluang::conditional::conditional;
use peluang::deterministic::is_as_deterministic;
use peluang::error::{Error, Result};
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::{Compose, Tensor};
use peluang::prob::Exact;

use crate::fixtures::{
    assert_as_deterministic, assert_as_equal, assert_bayesian_inverse, assert_deterministic,
    assert_differs, assert_kernel, c, conditional_composite, d, e, hot, k, lit, obj_b, obj_s,
    obj_t, obj_w, point, points, psi_t, r, s, show,
};

/// `q : I → W`, `(1/10, 3/10, 3/5)`: the literal of `psi_t ≫ c`.
fn q() -> Result<Kernel<Exact>> {
    Kernel::state(obj_w()?, vec![r(1, 10), r(3, 10), r(3, 5)])
}

/// The kernel `W → T` with the columns `sunny`, `cloudy`, `rainy`.
fn w_to_t(sunny: [Exact; 2], cloudy: [Exact; 2], rainy: [Exact; 2]) -> Result<Kernel<Exact>> {
    lit(obj_w()?, obj_t()?, &[&sunny, &cloudy, &rainy])
}

/// `c† : W → T`, sunny `(1, 0)`, cloudy `(1/3, 2/3)`, rainy `(0, 1)`: the
/// literal of `bayesian_inverse(psi_t, c)`.
fn c_dagger() -> Result<Kernel<Exact>> {
    w_to_t([r(1, 1), r(0, 1)], [r(1, 3), r(2, 3)], [r(0, 1), r(1, 1)])
}

/// `c†` with the cloudy column `(2/3, 1/3)`.
fn c_dagger_flipped() -> Result<Kernel<Exact>> {
    w_to_t([r(1, 1), r(0, 1)], [r(2, 3), r(1, 3)], [r(0, 1), r(1, 1)])
}

/// `g₁ : W → T`, sunny `(1, 0)`, cloudy `(1, 0)`, rainy `(1/2, 1/2)`: the
/// literal of `bayesian_inverse(hot, c)`.
fn g_one() -> Result<Kernel<Exact>> {
    w_to_t([r(1, 1), r(0, 1)], [r(1, 1), r(0, 1)], [r(1, 2), r(1, 2)])
}

/// `g₂ : W → T`: `g₁` with the rainy column `(1, 0)`.
fn g_two() -> Result<Kernel<Exact>> {
    w_to_t([r(1, 1), r(0, 1)], [r(1, 1), r(0, 1)], [r(1, 1), r(0, 1)])
}

/// `hot ≫ c : I → W`, `(1/2, 1/2, 0)`, as a literal.
fn hot_c() -> Result<Kernel<Exact>> {
    Kernel::state(obj_w()?, vec![r(1, 2), r(1, 2), r(0, 1)])
}

/// `s† : S → W`, on `(1/10, 9/10, 0)`, off `(1/10, 0, 9/10)`: the literal of
/// `bayesian_inverse(q, s)`.
fn s_dagger() -> Result<Kernel<Exact>> {
    lit(
        obj_s()?,
        obj_w()?,
        &[
            &[r(1, 10), r(9, 10), r(0, 1)],
            &[r(1, 10), r(0, 1), r(9, 10)],
        ],
    )
}

/// `c' : T → W`: `c` with the cold column `(1/3, 1/3, 1/3)`.
fn c_prime() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_w()?,
        &[&[r(1, 2), r(1, 2), r(0, 1)], &[r(1, 3), r(1, 3), r(1, 3)]],
    )
}

/// `k' : T → S`: `k` with the cold column `(1/2, 1/2)`.
fn k_prime() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_s()?,
        &[&[r(1, 1), r(0, 1)], &[r(1, 2), r(1, 2)]],
    )
}

/// `bayesian_inverse(p, f)` after asserting that it equals `expected`; panics
/// with `name` and the error when the engine returns an error.
#[track_caller]
fn inverse(
    name: &str,
    p: &Kernel<Exact>,
    f: &Kernel<Exact>,
    expected: &Kernel<Exact>,
) -> Kernel<Exact> {
    let observed = match bayesian_inverse(p, f) {
        Ok(observed) => observed,
        Err(e) => panic!(
            "{name} with p = {}, f = {}: expected Ok({}), observed Err({e:?})",
            show(p),
            show(f),
            show(expected)
        ),
    };
    assert_kernel(name, &observed, expected);
    observed
}

/// Whether each weight of `column` is 0 or 1.
fn zero_one(column: &[Exact]) -> bool {
    column
        .iter()
        .all(|weight| *weight == r(0, 1) || *weight == r(1, 1))
}

/// THEOREM_MAP: FinStoch.isBayesianInverse_bayesInv
#[test]
fn witness_is_bayesian_inverse_bayes_inv() -> Result<()> {
    let (psi_t, c, hot) = (psi_t()?, c()?, hot()?);
    assert_kernel("psi_t ≫ c", &psi_t.compose(&c)?, &q()?);
    let dagger = inverse("bayesian_inverse(psi_t, c)", &psi_t, &c, &c_dagger()?);
    assert_bayesian_inverse(
        "is_bayesian_inverse(psi_t, c, bayesian_inverse(psi_t, c))",
        &psi_t,
        &c,
        &dagger,
        true,
    );
    assert_kernel("hot ≫ c", &hot.compose(&c)?, &hot_c()?);
    let filled = inverse("bayesian_inverse(hot, c)", &hot, &c, &g_one()?);
    assert_bayesian_inverse(
        "is_bayesian_inverse(hot, c, bayesian_inverse(hot, c))",
        &hot,
        &c,
        &filled,
        true,
    );
    assert_bayesian_inverse(
        "control: is_bayesian_inverse(psi_t, c, c† with cloudy (2/3, 1/3))",
        &psi_t,
        &c,
        &c_dagger_flipped()?,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsBayesianInverse.unique_as
#[test]
fn witness_is_bayesian_inverse_unique_as() -> Result<()> {
    let (hot, c, g1, g2) = (hot()?, c()?, g_one()?, g_two()?);
    assert_bayesian_inverse("h₁: is_bayesian_inverse(hot, c, g₁)", &hot, &c, &g1, true);
    assert_bayesian_inverse("h₂: is_bayesian_inverse(hot, c, g₂)", &hot, &c, &g2, true);
    let reached = hot.compose(&c)?;
    assert_kernel("hot ≫ c", &reached, &hot_c()?);
    assert_as_equal("as_equal(hot ≫ c, g₁, g₂)", &reached, &g1, &g2, true);
    assert_as_equal(
        "control: as_equal(psi_t ≫ c, g₁, g₂), rainy reached",
        &q()?,
        &g1,
        &g2,
        false,
    );
    Ok(())
}

/// The running example, and the instance of the Lean proof with `B` the
/// object labeled `["false", "true"]`: index 0 is Lean's `false` and index 1
/// is Lean's `true`, `p` is the point at `true`, `f = g₁ = 𝟙 B` and `g₂`
/// sends every input to `true`.
/// THEOREM_MAP: FinStoch.isBayesianInverse_not_unique
#[test]
fn witness_is_bayesian_inverse_not_unique() -> Result<()> {
    let (hot, c, g2) = (hot()?, c()?, g_two()?);
    let g1 = inverse("g₁ = bayesian_inverse(hot, c)", &hot, &c, &g_one()?);
    assert_bayesian_inverse("is_bayesian_inverse(hot, c, g₁)", &hot, &c, &g1, true);
    assert_bayesian_inverse("is_bayesian_inverse(hot, c, g₂)", &hot, &c, &g2, true);
    assert_as_equal(
        "as_equal(hot ≫ c, g₁, g₂)",
        &hot.compose(&c)?,
        &g1,
        &g2,
        true,
    );
    assert_differs("g₁ against g₂", &g1, &g2);

    let b = obj_b()?;
    let p = point(b.clone(), 1)?;
    let id = points(b.clone(), b.clone(), &[0, 1])?;
    assert_kernel("𝟙 B", &Kernel::identity(&b)?, &id);
    let constant = points(b.clone(), b, &[1, 1])?;
    assert_bayesian_inverse("is_bayesian_inverse(true, 𝟙 B, 𝟙 B)", &p, &id, &id, true);
    assert_bayesian_inverse(
        "is_bayesian_inverse(true, 𝟙 B, constant true)",
        &p,
        &id,
        &constant,
        true,
    );
    assert_differs("𝟙 B against constant true", &id, &constant);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.isBayesianInverse_id
#[test]
fn witness_is_bayesian_inverse_id() -> Result<()> {
    let (t, psi_t) = (obj_t()?, psi_t()?);
    let id = points(t.clone(), t.clone(), &[0, 1])?;
    assert_kernel("𝟙 T", &Kernel::identity(&t)?, &id);
    assert_bayesian_inverse(
        "is_bayesian_inverse(psi_t, 𝟙 T, 𝟙 T)",
        &psi_t,
        &id,
        &id,
        true,
    );
    assert_bayesian_inverse(
        "is_bayesian_inverse(c, 𝟙 W, 𝟙 W)",
        &c()?,
        &points(obj_w()?, obj_w()?, &[0, 1, 2])?,
        &points(obj_w()?, obj_w()?, &[0, 1, 2])?,
        true,
    );
    assert_bayesian_inverse(
        "control: is_bayesian_inverse(psi_t, 𝟙 T, hot and cold exchanged)",
        &psi_t,
        &id,
        &points(t.clone(), t, &[1, 0])?,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsBayesianInverse.comp_eq
#[test]
fn witness_is_bayesian_inverse_comp_eq() -> Result<()> {
    let (psi_t, c) = (psi_t()?, c()?);
    let literal = Kernel::state(obj_t()?, vec![r(1, 5), r(4, 5)])?;
    let dagger = inverse("bayesian_inverse(psi_t, c)", &psi_t, &c, &c_dagger()?);
    assert_bayesian_inverse(
        "h: is_bayesian_inverse(psi_t, c, c†)",
        &psi_t,
        &c,
        &dagger,
        true,
    );
    assert_kernel(
        "psi_t ≫ c ≫ c†",
        &psi_t.compose(&c)?.compose(&dagger)?,
        &literal,
    );
    let flipped = c_dagger_flipped()?;
    assert_bayesian_inverse(
        "control: is_bayesian_inverse(psi_t, c, c† with cloudy (2/3, 1/3))",
        &psi_t,
        &c,
        &flipped,
        false,
    );
    assert_kernel(
        "control: psi_t ≫ c ≫ (c† with cloudy (2/3, 1/3))",
        &psi_t.compose(&c)?.compose(&flipped)?,
        &Kernel::state(obj_t()?, vec![r(3, 10), r(7, 10)])?,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsBayesianInverse.symm
#[test]
fn witness_is_bayesian_inverse_symm() -> Result<()> {
    let (psi_t, c, q) = (psi_t()?, c()?, q()?);
    let dagger = inverse("bayesian_inverse(psi_t, c)", &psi_t, &c, &c_dagger()?);
    assert_bayesian_inverse(
        "h: is_bayesian_inverse(psi_t, c, c†)",
        &psi_t,
        &c,
        &dagger,
        true,
    );
    assert_kernel("psi_t ≫ c", &psi_t.compose(&c)?, &q);
    assert_bayesian_inverse(
        "is_bayesian_inverse(psi_t ≫ c, c†, c)",
        &q,
        &dagger,
        &c,
        true,
    );
    let literal = lit(
        obj_t()?,
        obj_w()?,
        &[&[r(1, 2), r(1, 2), r(0, 1)], &[r(0, 1), r(1, 4), r(3, 4)]],
    )?;
    let back = inverse("bayesian_inverse(psi_t ≫ c, c†)", &q, &dagger, &literal);
    assert_as_equal(
        "as_equal(psi_t, bayesian_inverse(psi_t ≫ c, c†), c)",
        &psi_t,
        &back,
        &c,
        true,
    );
    assert_bayesian_inverse(
        "control: is_bayesian_inverse(hot ≫ c, c†, c)",
        &hot_c()?,
        &dagger,
        &c,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsBayesianInverse.comp
#[test]
fn witness_is_bayesian_inverse_comp() -> Result<()> {
    let (psi_t, c, s, q) = (psi_t()?, c()?, s()?, q()?);
    assert_kernel("psi_t ≫ c", &psi_t.compose(&c)?, &q);
    let c_dagger = inverse("c† = bayesian_inverse(psi_t, c)", &psi_t, &c, &c_dagger()?);
    let s_dagger = inverse("s† = bayesian_inverse(psi_t ≫ c, s)", &q, &s, &s_dagger()?);
    assert_bayesian_inverse(
        "hf: is_bayesian_inverse(psi_t, c, c†)",
        &psi_t,
        &c,
        &c_dagger,
        true,
    );
    assert_bayesian_inverse(
        "hg: is_bayesian_inverse(psi_t ≫ c, s, s†)",
        &q,
        &s,
        &s_dagger,
        true,
    );

    let cs = c.compose(&s)?;
    assert_kernel(
        "c ≫ s",
        &cs,
        &lit(
            obj_t()?,
            obj_s()?,
            &[&[r(2, 3), r(1, 3)], &[r(1, 4), r(3, 4)]],
        )?,
    );
    let literal = lit(
        obj_s()?,
        obj_t()?,
        &[&[r(2, 5), r(3, 5)], &[r(1, 10), r(9, 10)]],
    )?;
    let composite = s_dagger.compose(&c_dagger)?;
    assert_kernel("s† ≫ c†", &composite, &literal);
    assert_bayesian_inverse(
        "is_bayesian_inverse(psi_t, c ≫ s, s† ≫ c†)",
        &psi_t,
        &cs,
        &composite,
        true,
    );
    let whole = inverse("bayesian_inverse(psi_t, c ≫ s)", &psi_t, &cs, &literal);
    let reached = psi_t.compose(&cs)?;
    assert_kernel(
        "psi_t ≫ c ≫ s",
        &reached,
        &Kernel::state(obj_s()?, vec![r(1, 3), r(2, 3)])?,
    );
    assert_as_equal(
        "as_equal(psi_t ≫ c ≫ s, bayesian_inverse(psi_t, c ≫ s), s† ≫ c†)",
        &reached,
        &whole,
        &composite,
        true,
    );
    assert_bayesian_inverse(
        "control: is_bayesian_inverse(psi_t, c ≫ s, e)",
        &psi_t,
        &cs,
        &e()?,
        false,
    );

    let (hot, g2, reached) = (hot()?, g_two()?, hot_c()?);
    assert_kernel("hot ≫ c", &hot.compose(&c)?, &reached);
    let g = points(obj_w()?, obj_s()?, &[0, 0, 1])?;
    let g_inverse = inverse(
        "g' = bayesian_inverse(hot ≫ c, g), g sunny and cloudy to on, rainy to off",
        &reached,
        &g,
        &lit(
            obj_s()?,
            obj_w()?,
            &[&[r(1, 2), r(1, 2), r(0, 1)], &[r(1, 3), r(1, 3), r(1, 3)]],
        )?,
    );
    assert_bayesian_inverse("hf: is_bayesian_inverse(hot, c, g₂)", &hot, &c, &g2, true);
    assert_bayesian_inverse(
        "hg: is_bayesian_inverse(hot ≫ c, g, g')",
        &reached,
        &g,
        &g_inverse,
        true,
    );
    let cg = c.compose(&g)?;
    assert_kernel(
        "c ≫ g",
        &cg,
        &lit(
            obj_t()?,
            obj_s()?,
            &[&[r(1, 1), r(0, 1)], &[r(1, 4), r(3, 4)]],
        )?,
    );
    let composite = g_inverse.compose(&g2)?;
    assert_kernel("g' ≫ g₂", &composite, &points(obj_s()?, obj_t()?, &[0, 0])?);
    assert_bayesian_inverse(
        "is_bayesian_inverse(hot, c ≫ g, g' ≫ g₂)",
        &hot,
        &cg,
        &composite,
        true,
    );
    let canonical = inverse(
        "bayesian_inverse(hot, c ≫ g)",
        &hot,
        &cg,
        &lit(
            obj_s()?,
            obj_t()?,
            &[&[r(1, 1), r(0, 1)], &[r(1, 2), r(1, 2)]],
        )?,
    );
    assert_differs(
        "g' ≫ g₂ against bayesian_inverse(hot, c ≫ g)",
        &composite,
        &canonical,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsBayesianInverse.congr
#[test]
fn witness_is_bayesian_inverse_congr() -> Result<()> {
    let (hot, c, c1, g1, g2) = (hot()?, c()?, c_prime()?, g_one()?, g_two()?);
    assert_differs("c against c'", &c, &c1);
    assert_as_equal("hf: as_equal(hot, c, c')", &hot, &c, &c1, true);
    assert_as_equal(
        "hg: as_equal(hot ≫ c, g₁, g₂)",
        &hot.compose(&c)?,
        &g1,
        &g2,
        true,
    );
    assert_bayesian_inverse("h: is_bayesian_inverse(hot, c, g₁)", &hot, &c, &g1, true);
    assert_bayesian_inverse("is_bayesian_inverse(hot, c', g₂)", &hot, &c1, &g2, true);

    let psi_t = psi_t()?;
    assert_as_equal(
        "control: as_equal(psi_t, c, c'), cold reached",
        &psi_t,
        &c,
        &c1,
        false,
    );
    assert_bayesian_inverse(
        "control: is_bayesian_inverse(psi_t, c', c†)",
        &psi_t,
        &c1,
        &c_dagger()?,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.isBayesianInverse_iff_isConditional
#[test]
fn witness_is_bayesian_inverse_iff_is_conditional() -> Result<()> {
    let (t, w, psi_t, c) = (obj_t()?, obj_w()?, psi_t()?, c()?);
    let joint = psi_t
        .compose(&Kernel::copy(&t)?)?
        .compose(&Kernel::whisker_right(&c, &t)?)?;
    let joint_literal = Kernel::state(
        w.tensor(&t)?,
        vec![r(1, 10), r(0, 1), r(1, 10), r(1, 5), r(0, 1), r(3, 5)],
    )?;
    assert_kernel("psi_t ≫ Δ[T] ≫ (c ▷ T)", &joint, &joint_literal);

    let literal = c_dagger()?;
    let dagger = inverse("bayesian_inverse(psi_t, c)", &psi_t, &c, &literal);
    let rho = Kernel::right_unitor(&w)?;
    let got = conditional(&joint, &w, &t);
    let Ok(cond) = got else {
        panic!(
            "conditional(psi_t ≫ Δ[T] ≫ (c ▷ T), W, T): expected Ok({}), observed {got:?}",
            show(&literal)
        );
    };
    assert_kernel("conditional(psi_t ≫ Δ[T] ≫ (c ▷ T), W, T)", &cond, &literal);
    assert_kernel("ρ_ W ≫ c†", &rho.compose(&dagger)?, &literal);

    for (name, g, expected) in [
        ("c†", &dagger, true),
        ("c† with cloudy (2/3, 1/3)", &c_dagger_flipped()?, false),
    ] {
        assert_bayesian_inverse(
            &format!("is_bayesian_inverse(psi_t, c, {name})"),
            &psi_t,
            &c,
            g,
            expected,
        );
        let got = rho
            .compose(g)
            .and_then(|k| conditional_composite(&joint, &w, &t, &k));
        let Ok(composite) = got else {
            panic!(
                "Def. 11.5 composite of ρ_ W ≫ {name}: expected Ok of a kernel == {} is \
                 {expected}, observed {got:?}",
                show(&joint_literal)
            );
        };
        let observed = composite == joint_literal;
        assert_eq!(
            observed,
            expected,
            "Def. 11.5 composite of ρ_ W ≫ {name} == psi_t ≫ Δ[T] ≫ (c ▷ T): expected \
             {expected}, observed {observed}: {} vs {}",
            show(&composite),
            show(&joint_literal)
        );
    }
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsBayesianInverse.tensor
#[test]
fn witness_is_bayesian_inverse_tensor() -> Result<()> {
    let (psi_t, c, s, q) = (psi_t()?, c()?, s()?, q()?);
    let c_dagger = inverse("c† = bayesian_inverse(psi_t, c)", &psi_t, &c, &c_dagger()?);
    let s_dagger = inverse("s† = bayesian_inverse(q, s)", &q, &s, &s_dagger()?);
    assert_bayesian_inverse(
        "hf: is_bayesian_inverse(psi_t, c, c†)",
        &psi_t,
        &c,
        &c_dagger,
        true,
    );
    assert_bayesian_inverse("hk: is_bayesian_inverse(q, s, s†)", &q, &s, &s_dagger, true);

    let state = psi_t.tensor(&q)?;
    assert_kernel(
        "psi_t ⊗ₘ q",
        &state,
        &Kernel::state(
            obj_t()?.tensor(&obj_w()?)?,
            vec![r(1, 50), r(3, 50), r(3, 25), r(2, 25), r(6, 25), r(12, 25)],
        )?,
    );
    let f = c.tensor(&s)?;
    assert_bayesian_inverse(
        "is_bayesian_inverse(psi_t ⊗ₘ q, c ⊗ₘ s, c† ⊗ₘ s†)",
        &state,
        &f,
        &c_dagger.tensor(&s_dagger)?,
        true,
    );
    assert_bayesian_inverse(
        "control: is_bayesian_inverse(psi_t ⊗ₘ q, c ⊗ₘ s, (c† with cloudy (2/3, 1/3)) ⊗ₘ s†)",
        &state,
        &f,
        &c_dagger_flipped()?.tensor(&s_dagger)?,
        false,
    );
    let got = is_bayesian_inverse(&state, &f, &s_dagger.tensor(&c_dagger)?);
    let (cod, dom) = (obj_w()?.tensor(&obj_s()?)?, obj_s()?.tensor(&obj_w()?)?);
    assert!(
        matches!(&got, Err(Error::NotComposable { codomain, domain })
            if *codomain == cod && *domain == dom),
        "factors exchanged, is_bayesian_inverse(psi_t ⊗ₘ q, c ⊗ₘ s, s† ⊗ₘ c†): expected \
         NotComposable {{ codomain: {cod:?}, domain: {dom:?} }}, observed {got:?}"
    );
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.isAlmostSurelyDeterministic_of_deterministic
#[test]
fn witness_is_almost_surely_deterministic_of_deterministic() -> Result<()> {
    let (q, d) = (q()?, d()?);
    assert_kernel("d", &d, &points(obj_w()?, obj_s()?, &[0, 1, 1])?);
    assert_deterministic("d", &d, true);
    assert_as_deterministic("is_as_deterministic(q, d)", &q, &d, true);
    assert_as_deterministic("is_as_deterministic(c, d)", &c()?, &d, true);
    let s = s()?;
    assert_deterministic("control: s", &s, false);
    assert_as_deterministic("control: is_as_deterministic(q, s)", &q, &s, false);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsAlmostSurelyDeterministic.comp_deterministic
#[test]
fn witness_is_almost_surely_deterministic_comp_deterministic() -> Result<()> {
    let (q, d, e) = (q()?, d()?, e()?);
    assert_as_deterministic("hf: is_as_deterministic(q, d)", &q, &d, true);
    assert_deterministic("e", &e, true);
    let de = d.compose(&e)?;
    assert_kernel("d ≫ e", &de, &points(obj_w()?, obj_t()?, &[0, 1, 1])?);
    assert_as_deterministic("is_as_deterministic(q, d ≫ e)", &q, &de, true);

    let (hot, k) = (hot()?, k()?);
    assert_deterministic("k", &k, false);
    assert_as_deterministic("hf: is_as_deterministic(hot, k)", &hot, &k, true);
    let ke = k.compose(&e)?;
    assert_kernel(
        "k ≫ e",
        &ke,
        &lit(
            obj_t()?,
            obj_t()?,
            &[&[r(1, 1), r(0, 1)], &[r(1, 4), r(3, 4)]],
        )?,
    );
    assert_as_deterministic("is_as_deterministic(hot, k ≫ e)", &hot, &ke, true);
    assert_as_deterministic(
        "control: is_as_deterministic(psi_t, k ≫ e)",
        &psi_t()?,
        &ke,
        false,
    );
    Ok(())
}

/// THEOREM_MAP: FinStoch.isAlmostSurelyDeterministic_iff
#[test]
fn witness_is_almost_surely_deterministic_iff() -> Result<()> {
    let (t, k) = (obj_t()?, k()?);
    let columns = [[r(1, 1), r(0, 1)], [r(1, 4), r(3, 4)]];
    assert_kernel(
        "k",
        &k,
        &lit(obj_t()?, obj_s()?, &[&columns[0], &columns[1]])?,
    );
    for (x, name, expected) in [(0, "hot", true), (1, "cold", false)] {
        let observed = zero_one(&columns[x]);
        assert_eq!(
            observed, expected,
            "each weight of the column of k at {name} is 0 or 1: expected {expected}, observed \
             {observed} on {:?}",
            columns[x]
        );
    }
    for (name, p, weights, expected) in [
        ("hot", hot()?, [r(1, 1), r(0, 1)], true),
        ("psi_t", psi_t()?, [r(1, 5), r(4, 5)], false),
    ] {
        let got = Kernel::state(t.clone(), weights.to_vec());
        let Ok(literal) = got else {
            panic!("the literal of {name} = {weights:?}: expected Ok, observed {got:?}");
        };
        assert_kernel(name, &p, &literal);
        let right = (0..columns.len()).all(|x| weights[x] == r(0, 1) || zero_one(&columns[x]));
        assert_eq!(
            right, expected,
            "each column of k at an input with a nonzero weight of {name} = {weights:?} holds \
             only 0 and 1: expected {expected}, observed {right} on {columns:?}"
        );
        assert_as_deterministic(&format!("is_as_deterministic({name}, k)"), &p, &k, expected);
    }
    Ok(())
}

/// The running example, and the instance of the Lean proof with `B` the
/// object labeled `["false", "true"]`: index 0 is Lean's `false` and index 1
/// is Lean's `true`, `p` is the point at `true` and `halfDet` has the columns
/// `(1/2, 1/2)` at `false` and `(0, 1)` at `true`.
/// THEOREM_MAP: FinStoch.exists_isAlmostSurelyDeterministic_not_deterministic
#[test]
fn witness_exists_is_almost_surely_deterministic_not_deterministic() -> Result<()> {
    let (hot, k) = (hot()?, k()?);
    assert_as_deterministic("is_as_deterministic(hot, k)", &hot, &k, true);
    assert_deterministic("k", &k, false);

    let b = obj_b()?;
    let p = point(b.clone(), 1)?;
    let half_det = lit(b.clone(), b, &[&[r(1, 2), r(1, 2)], &[r(0, 1), r(1, 1)]])?;
    assert_as_deterministic("is_as_deterministic(true, halfDet)", &p, &half_det, true);
    assert_deterministic("halfDet", &half_det, false);
    Ok(())
}

/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsAlmostSurelyDeterministic.congr
#[test]
fn witness_is_almost_surely_deterministic_congr() -> Result<()> {
    let (hot, k, k1) = (hot()?, k()?, k_prime()?);
    assert_differs("k against k'", &k, &k1);
    assert_as_equal("h: as_equal(hot, k, k')", &hot, &k, &k1, true);
    assert_as_deterministic("hf: is_as_deterministic(hot, k)", &hot, &k, true);
    assert_as_deterministic("is_as_deterministic(hot, k')", &hot, &k1, true);

    let cold = point(obj_t()?, 1)?;
    assert_as_equal("control: as_equal(cold, k, k')", &cold, &k, &k1, false);
    assert_as_deterministic("control: is_as_deterministic(cold, k')", &cold, &k1, false);
    Ok(())
}

#[test]
fn bayesian_inverse_rejects_a_non_state_then_a_non_composable_pair() -> Result<()> {
    let (t, w, c) = (obj_t()?, obj_w()?, c()?);
    for (name, f) in [("composable s", s()?), ("non-composable e", e()?)] {
        let got = bayesian_inverse(&c, &f);
        assert!(
            matches!(&got, Err(Error::NotAState { domain }) if *domain == t),
            "bayesian_inverse(c, {name}): expected NotAState {{ domain: {t:?} }}, observed {got:?}"
        );
    }
    let got = bayesian_inverse(&hot()?, &s()?);
    assert!(
        matches!(&got, Err(Error::NotComposable { codomain, domain })
            if *codomain == t && *domain == w),
        "bayesian_inverse(hot, s): expected NotComposable {{ codomain: {t:?}, domain: {w:?} }}, \
         observed {got:?}"
    );
    Ok(())
}

#[test]
fn bayesian_inverse_rejects_a_one_element_domain_that_is_not_the_unit() -> Result<()> {
    let one = FinObj::new(1);
    let p = Kernel::new(one.clone(), obj_t()?, vec![r(1, 5), r(4, 5)])?;
    let got = bayesian_inverse(&p, &c()?);
    assert!(
        matches!(&got, Err(Error::NotAState { domain }) if *domain == one),
        "bayesian_inverse(p, c) with p : [1] → T: expected NotAState {{ domain: {one:?} }}, \
         observed {got:?}"
    );
    Ok(())
}

/// `[2^19]`, where `Kernel::copy` returns `Error::TooLarge` for `2^19 * 2^38`
/// weights.
fn wide() -> FinObj {
    FinObj::new(1 << 19)
}

#[test]
fn bayesian_inverse_rejects_before_it_builds_a_kernel() -> Result<()> {
    let (t, wide) = (obj_t()?, wide());
    let f = Kernel::<Exact>::del(&wide)?;
    let got = bayesian_inverse(&c()?, &f);
    assert!(
        matches!(&got, Err(Error::NotAState { domain }) if *domain == t),
        "bayesian_inverse(c, ε[2^19]): expected NotAState {{ domain: {t:?} }}, observed {got:?}"
    );
    let got = bayesian_inverse(&hot()?, &f);
    assert!(
        matches!(&got, Err(Error::NotComposable { codomain, domain })
            if *codomain == t && *domain == wide),
        "bayesian_inverse(hot, ε[2^19]): expected NotComposable {{ codomain: {t:?}, domain: \
         [2^19] }}, observed {got:?}"
    );
    Ok(())
}

#[test]
fn is_bayesian_inverse_rejects_before_it_builds_a_kernel() -> Result<()> {
    let (t, wide, unit) = (obj_t()?, wide(), FinObj::unit());
    let (hot, c) = (hot()?, c()?);
    let into_wide = Kernel::<Exact>::from_fn(unit.clone(), wide.clone(), |_| 0)?;
    let del = Kernel::<Exact>::del(&wide)?;
    for (name, p, g, codomain, domain) in [
        (
            "(hot, ε[2^19], I → [2^19]), p into f fails",
            &hot,
            &into_wide,
            &t,
            &wide,
        ),
        (
            "(I → [2^19], ε[2^19], c), f into g fails",
            &into_wide,
            &c,
            &unit,
            &t,
        ),
        (
            "(I → [2^19], ε[2^19], hot), g into f fails",
            &into_wide,
            &hot,
            &t,
            &wide,
        ),
    ] {
        let got = is_bayesian_inverse(p, &del, g);
        assert!(
            matches!(&got, Err(Error::NotComposable { codomain: fst, domain: snd })
                if fst == codomain && snd == domain),
            "is_bayesian_inverse{name}: expected NotComposable {{ codomain: {codomain:?}, \
             domain: {domain:?} }}, observed {got:?}"
        );
    }
    Ok(())
}

#[test]
fn is_as_deterministic_rejects_before_it_builds_a_kernel() -> Result<()> {
    let (t, w) = (obj_t()?, obj_w()?);
    let f = Kernel::<Exact>::from_fn(t.clone(), wide(), |_| 0)?;
    let got = is_as_deterministic(&q()?, &f);
    assert!(
        matches!(&got, Err(Error::NotComposable { codomain, domain })
            if *codomain == w && *domain == t),
        "is_as_deterministic(q, T → [2^19]): expected NotComposable {{ codomain: {w:?}, domain: \
         {t:?} }}, observed {got:?}"
    );
    Ok(())
}

#[test]
fn is_as_deterministic_on_an_empty_domain_builds_no_kernel() -> Result<()> {
    let empty = FinObj::new(0);
    let p = Kernel::<Exact>::new(empty.clone(), empty.clone(), Vec::new())?;
    let f = Kernel::<Exact>::new(empty, wide(), Vec::new())?;
    let got = is_as_deterministic(&p, &f);
    assert!(
        matches!(got, Ok(true)),
        "is_as_deterministic(0 → 0, 0 → [2^19]): expected Ok(true), observed {got:?}"
    );
    Ok(())
}

#[test]
fn is_as_deterministic_rejects_a_non_composable_pair_on_an_empty_domain() -> Result<()> {
    let (empty, t) = (FinObj::new(0), obj_t()?);
    let p = Kernel::<Exact>::new(empty.clone(), t.clone(), Vec::new())?;
    let f = Kernel::<Exact>::new(empty.clone(), obj_s()?, Vec::new())?;
    let got = is_as_deterministic(&p, &f);
    assert!(
        matches!(&got, Err(Error::NotComposable { codomain, domain })
            if *codomain == t && *domain == empty),
        "is_as_deterministic(0 → T, 0 → S): expected NotComposable {{ codomain: {t:?}, domain: \
         {empty:?} }}, observed {got:?}"
    );
    Ok(())
}

#[test]
fn is_as_deterministic_on_a_one_element_domain_reads_its_row() -> Result<()> {
    let unit = FinObj::unit();
    let id = Kernel::new(unit.clone(), unit, vec![r(1, 1)])?;
    assert_as_deterministic("is_as_deterministic(𝟙 I, psi_t)", &id, &psi_t()?, false);
    assert_as_deterministic("is_as_deterministic(𝟙 I, hot)", &id, &hot()?, true);
    Ok(())
}

#[test]
fn is_bayesian_inverse_rejects_mismatched_shapes_in_order() -> Result<()> {
    let (t, w, sp) = (obj_t()?, obj_w()?, obj_s()?);
    let (hot, c, s) = (hot()?, c()?, s()?);
    let id_s = Kernel::<Exact>::identity(&sp)?;
    for (name, f, g, codomain, domain) in [
        ("(hot, s, c), p into f and f into g fail", &s, &c, &t, &w),
        (
            "(hot, c, 𝟙 S), f into g and g into f fail",
            &c,
            &id_s,
            &w,
            &sp,
        ),
        ("(hot, c, s), g into f fails", &c, &s, &sp, &t),
    ] {
        let got = is_bayesian_inverse(&hot, f, g);
        assert!(
            matches!(&got, Err(Error::NotComposable { codomain: fst, domain: snd })
                if fst == codomain && snd == domain),
            "is_bayesian_inverse{name}: expected NotComposable {{ codomain: {codomain:?}, \
             domain: {domain:?} }}, observed {got:?}"
        );
    }
    Ok(())
}

#[test]
fn is_as_deterministic_rejects_a_non_composable_pair_and_holds_on_an_empty_domain() -> Result<()> {
    let (t, w) = (obj_t()?, obj_w()?);
    let got = is_as_deterministic(&hot()?, &s()?);
    assert!(
        matches!(&got, Err(Error::NotComposable { codomain, domain })
            if *codomain == t && *domain == w),
        "is_as_deterministic(hot, s): expected NotComposable {{ codomain: {t:?}, domain: {w:?} }}, \
         observed {got:?}"
    );
    let empty = FinObj::new(0);
    let p = Kernel::<Exact>::new(empty.clone(), empty.clone(), Vec::new())?;
    let f = Kernel::<Exact>::new(empty, obj_s()?, Vec::new())?;
    assert_as_deterministic("is_as_deterministic(0 → 0, 0 → S)", &p, &f, true);
    Ok(())
}
