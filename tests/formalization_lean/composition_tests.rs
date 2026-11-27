//! Witnesses of `DisplaysCondIndep.tensor`, `DisplaysCondIndep.comp`,
//! `DisplaysCondIndep.comp_tensorHom`, `IsConditional.condIndepForm`,
//! `DisplaysCondIndep.exists_isConditional` and
//! `tensorTripleInterchange_hom_natural` on kernels with literal factors: the
//! composites of Fritz 2020, Prop. 12.18, built from `Kernel::tensor`,
//! `Kernel::copy`, `Kernel::del`, `Kernel::swap`, `Kernel::associator`, the
//! unitors and the two whiskers, compared with `==` to `cond_indep_form` of
//! the factors of each conclusion and to literals, `conditional` with the
//! Def. 11.5 composite `conditional_composite`, and
//! `cond_independent_at_each_input`, which runs `is_cond_independent_state`
//! on the state at each input of a kernel. A literal of a kernel with more
//! than 64 weights gives the columns of two inputs. Also, untagged: the
//! helpers `mu` and `delta` against point literals and against each other,
//! and `copy_pair` against a literal. The engine is strict:
//! `Kernel::associator` stands for both `α` and `α⁻¹`, `Kernel::swap` for both
//! `β` and `β⁻¹`, `Kernel::left_unitor` for `λ` and `Kernel::right_unitor` for
//! `ρ`.

use peluang::conditional::conditional;
use peluang::error::Result;
use peluang::finset::FinObj;
use peluang::independence::cond_indep_form;
use peluang::kernel::Kernel;
use peluang::markov::{Compose, Tensor};
use peluang::prob::Exact;

use crate::fixtures::{
    assert_differs, assert_kernel, c, conditional_composite, h, j, k, labels, lit, m, obj_b, obj_p,
    obj_s, obj_t, obj_w, points, r, show,
};
use crate::semigraphoid_tests::{
    assert_cond_independent_at_each_input, cond_independent_at_each_input, replace_column,
};

/// `L`: `{low, mid, high}`.
fn obj_l() -> Result<FinObj> {
    labels(&["low", "mid", "high"])
}

/// `C`: `{red, blue}`.
fn obj_c() -> Result<FinObj> {
    labels(&["red", "blue"])
}

/// `D`: `{left, right}`.
fn obj_d() -> Result<FinObj> {
    labels(&["left", "right"])
}

/// `U`: `{u}`.
fn obj_u() -> Result<FinObj> {
    labels(&["u"])
}

/// `Z`: `{z}`.
fn obj_z() -> Result<FinObj> {
    labels(&["z"])
}

/// `f` followed by each kernel of `steps` in order.
fn then(f: &Kernel<Exact>, steps: &[Kernel<Exact>]) -> Result<Kernel<Exact>> {
    steps
        .iter()
        .try_fold(f.clone(), |acc, step| acc.compose(step))
}

/// The composite of the kernels of `steps` in order, for a list with at least
/// one kernel; panics on the empty list.
fn chain(steps: &[Kernel<Exact>]) -> Result<Kernel<Exact>> {
    let (first, rest) = steps
        .split_first()
        .expect("invariant: a reorder map has a first factor");
    then(first, rest)
}

/// The factors of `(tensorCompAssoc a x1 w y1 a2).hom` in order:
/// `a ◁ α[x1, w ⊗ y1, a2]`, `a ◁ (x1 ◁ α[w, y1, a2])`,
/// `α⁻¹[a, x1, w ⊗ (y1 ⊗ a2)]`.
fn comp_assoc(
    a: &FinObj,
    x1: &FinObj,
    w: &FinObj,
    y1: &FinObj,
    a2: &FinObj,
) -> Result<Vec<Kernel<Exact>>> {
    Ok(vec![
        Kernel::whisker_left(a, &Kernel::associator(x1, &w.tensor(y1)?, a2)?)?,
        Kernel::whisker_left(
            a,
            &Kernel::whisker_left(x1, &Kernel::associator(w, y1, a2)?)?,
        )?,
        Kernel::associator(a, x1, &w.tensor(&y1.tensor(a2)?)?)?,
    ])
}

/// The factors of `(tensorLeftComm x y z).hom` in order: `α⁻¹[x, y, z]`,
/// `σ[x, y] ▷ z`, `α[y, x, z]`.
fn left_comm(x: &FinObj, y: &FinObj, z: &FinObj) -> Result<Vec<Kernel<Exact>>> {
    Ok(vec![
        Kernel::associator(x, y, z)?,
        Kernel::whisker_right(&Kernel::swap(x, y)?, z)?,
        Kernel::associator(y, x, z)?,
    ])
}

/// The factors of `(tensorμIso x1 x2 y1 y2).hom` in order:
/// `α[x1, x2, y1 ⊗ y2]`, `x1 ◁ α⁻¹[x2, y1, y2]`, `x1 ◁ (σ[x2, y1] ▷ y2)`,
/// `x1 ◁ α[y1, x2, y2]`, `α⁻¹[x1, y1, x2 ⊗ y2]`. Their composite is the kernel
/// `(x1 ⊗ x2) ⊗ (y1 ⊗ y2) → (x1 ⊗ y1) ⊗ (x2 ⊗ y2)`.
fn mu(x1: &FinObj, x2: &FinObj, y1: &FinObj, y2: &FinObj) -> Result<Vec<Kernel<Exact>>> {
    Ok(vec![
        Kernel::associator(x1, x2, &y1.tensor(y2)?)?,
        Kernel::whisker_left(x1, &Kernel::associator(x2, y1, y2)?)?,
        Kernel::whisker_left(x1, &Kernel::whisker_right(&Kernel::swap(x2, y1)?, y2)?)?,
        Kernel::whisker_left(x1, &Kernel::associator(y1, x2, y2)?)?,
        Kernel::associator(x1, y1, &x2.tensor(y2)?)?,
    ])
}

/// The factors of Mathlib's `tensorδ x1 x2 y1 y2`
/// (`Mathlib/CategoryTheory/Monoidal/Braided/Basic.lean`, line 608 at the tag
/// `v4.36.0`) in order: `α[x1, y1, x2 ⊗ y2]`, `x1 ◁ α⁻¹[y1, x2, y2]`,
/// `x1 ◁ (σ[y1, x2] ▷ y2)`, `x1 ◁ α[x2, y1, y2]`, `α⁻¹[x1, x2, y1 ⊗ y2]`.
/// Their composite is the kernel
/// `(x1 ⊗ y1) ⊗ (x2 ⊗ y2) → (x1 ⊗ x2) ⊗ (y1 ⊗ y2)`.
fn delta(x1: &FinObj, x2: &FinObj, y1: &FinObj, y2: &FinObj) -> Result<Vec<Kernel<Exact>>> {
    Ok(vec![
        Kernel::associator(x1, y1, &x2.tensor(y2)?)?,
        Kernel::whisker_left(x1, &Kernel::associator(y1, x2, y2)?)?,
        Kernel::whisker_left(x1, &Kernel::whisker_right(&Kernel::swap(y1, x2)?, y2)?)?,
        Kernel::whisker_left(x1, &Kernel::associator(x2, y1, y2)?)?,
        Kernel::associator(x1, x2, &y1.tensor(y2)?)?,
    ])
}

/// The factors of `(tensorTripleInterchange x1 w1 y1 x2 w2 y2).hom` in order:
/// the five of `mu(x1, w1 ⊗ y1, x2, w2 ⊗ y2)`, then
/// `(x1 ⊗ x2) ◁ m` with `m` the composite of `mu(w1, y1, w2, y2)`.
fn interchange(
    x1: &FinObj,
    w1: &FinObj,
    y1: &FinObj,
    x2: &FinObj,
    w2: &FinObj,
    y2: &FinObj,
) -> Result<Vec<Kernel<Exact>>> {
    let mut steps = mu(x1, &w1.tensor(y1)?, x2, &w2.tensor(y2)?)?;
    steps.push(Kernel::whisker_left(
        &x1.tensor(x2)?,
        &chain(&mu(w1, y1, w2, y2)?)?,
    )?);
    Ok(steps)
}

/// The factors of `(tensorCondReorder x v w y).hom` in order:
/// `x ◁ α[v, w, y]`, then the three of `left_comm(x, v, w ⊗ y)`.
fn cond_reorder(x: &FinObj, v: &FinObj, w: &FinObj, y: &FinObj) -> Result<Vec<Kernel<Exact>>> {
    let mut steps = vec![Kernel::whisker_left(x, &Kernel::associator(v, w, y)?)?];
    steps.extend(left_comm(x, v, &w.tensor(y)?)?);
    Ok(steps)
}

/// The factors of `(tensorCompReorder x1 v x2 w y2 y1).hom` in order:
/// `x1 ◁ (c ▷ y1)` with `c` the composite of `left_comm(v, x2, w ⊗ y2)`,
/// `x1 ◁ α[x2, v ⊗ (w ⊗ y2), y1]`, `α⁻¹[x1, x2, (v ⊗ (w ⊗ y2)) ⊗ y1]`,
/// `(x1 ⊗ x2) ◁ (α⁻¹[v, w, y2] ▷ y1)`, `(x1 ⊗ x2) ◁ α[v ⊗ w, y2, y1]`.
fn comp_reorder(
    x1: &FinObj,
    v: &FinObj,
    x2: &FinObj,
    w: &FinObj,
    y2: &FinObj,
    y1: &FinObj,
) -> Result<Vec<Kernel<Exact>>> {
    let wy2 = w.tensor(y2)?;
    let inner = v.tensor(&wy2)?;
    let x12 = x1.tensor(x2)?;
    Ok(vec![
        Kernel::whisker_left(
            x1,
            &Kernel::whisker_right(&chain(&left_comm(v, x2, &wy2)?)?, y1)?,
        )?,
        Kernel::whisker_left(x1, &Kernel::associator(x2, &inner, y1)?)?,
        Kernel::associator(x1, x2, &inner.tensor(y1)?)?,
        Kernel::whisker_left(
            &x12,
            &Kernel::whisker_right(&Kernel::associator(v, w, y2)?, y1)?,
        )?,
        Kernel::whisker_left(&x12, &Kernel::associator(&v.tensor(w)?, y2, y1)?)?,
    ])
}

/// `copyPair x y`: `Δ[Z] ≫ (x ⊗ₘ y)` with `Z` the domain of `x`.
fn copy_pair(x: &Kernel<Exact>, y: &Kernel<Exact>) -> Result<Kernel<Exact>> {
    Kernel::copy(x.domain())?.compose(&x.tensor(y)?)
}

/// The composite of `DisplaysCondIndep.comp_tensorHom`, `Δ[A] ≫ (A ◁ Δ[A]) ≫
/// (A ◁ (f ▷ A)) ≫ tensorCompAssoc A x1 w y1 A ≫ (u ⊗ₘ (w ◁ v))`, with `A` the
/// domain of `f : A → x1 ⊗ (w ⊗ y1)`.
fn comp_tensor_hom(
    f: &Kernel<Exact>,
    x1: &FinObj,
    w: &FinObj,
    y1: &FinObj,
    u: &Kernel<Exact>,
    v: &Kernel<Exact>,
) -> Result<Kernel<Exact>> {
    let a = f.domain();
    let copy = Kernel::copy(a)?;
    let copies = copy
        .compose(&Kernel::whisker_left(a, &copy)?)?
        .compose(&Kernel::whisker_left(a, &Kernel::whisker_right(f, a)?)?)?;
    then(&copies, &comp_assoc(a, x1, w, y1, a)?)?.compose(&u.tensor(&Kernel::whisker_left(w, v)?)?)
}

/// The conditional of `IsConditional.condIndepForm`:
/// `cond_indep_form(g_cond, (σ[v, a] ▷ w) ≫ α[a, v, w] ≫ h,
/// α⁻¹[w, v, a] ≫ (σ[w, v] ▷ a) ≫ k)`, for `g_cond : v ⊗ a → w`,
/// `h : a ⊗ (v ⊗ w) → X` and `k : (v ⊗ w) ⊗ a → Y`.
fn cond_form(
    g_cond: &Kernel<Exact>,
    h: &Kernel<Exact>,
    k: &Kernel<Exact>,
    a: &FinObj,
    v: &FinObj,
    w: &FinObj,
) -> Result<Kernel<Exact>> {
    let first = Kernel::whisker_right(&Kernel::swap(v, a)?, w)?
        .compose(&Kernel::associator(a, v, w)?)?
        .compose(h)?;
    let second = Kernel::associator(w, v, a)?
        .compose(&Kernel::whisker_right(&Kernel::swap(w, v)?, a)?)?
        .compose(k)?;
    cond_indep_form(g_cond, &first, &second)
}

/// The column of `width` weights with `weight` at each `(output, weight)` of
/// `atoms` and 0 at every other output.
fn sparse_column(width: usize, atoms: &[(usize, Exact)]) -> Vec<Exact> {
    let mut column = vec![r(0, 1); width];
    for (output, weight) in atoms {
        column[*output] = weight.clone();
    }
    column
}

/// The outputs of `column` with a weight other than 0, each with its weight.
fn show_column(column: &[Exact]) -> String {
    let atoms: Vec<String> = column
        .iter()
        .enumerate()
        .filter(|(_, weight)| **weight != r(0, 1))
        .map(|(output, weight)| format!("{output}: {weight}"))
        .collect();
    format!("{{{}}} of {} outputs", atoms.join(", "), column.len())
}

/// Asserts that the column of `f` at input `a` equals `expected`, naming
/// `name`.
#[track_caller]
fn assert_column(name: &str, f: &Kernel<Exact>, a: usize, expected: &[Exact]) {
    let observed = f.column(a);
    assert!(
        observed == Some(expected),
        "{name}, column at input {a}: expected {}, observed {}",
        show_column(expected),
        observed.map_or_else(|| String::from("no column"), show_column)
    );
}

/// The kernel `dom → cod` with weight 1 at output 0 on every input other than
/// `at`, and the weights 1/2 at output 0 and 1/2 at output `other` on input
/// `at`, through `Kernel::new`, for `at` below the number of inputs and
/// `other` an output that is not 0; panics otherwise.
fn two_point(dom: FinObj, cod: FinObj, at: usize, other: usize) -> Result<Kernel<Exact>> {
    let width = cod.card();
    assert!(
        at < dom.card() && other != 0 && other < width,
        "two_point: expected at below {} and other in 1..{width}, observed at = {at}, other = \
         {other}",
        dom.card()
    );
    let data = (0..dom.card())
        .flat_map(|a| {
            if a == at {
                sparse_column(width, &[(0, r(1, 2)), (other, r(1, 2))])
            } else {
                sparse_column(width, &[(0, r(1, 1))])
            }
        })
        .collect();
    Kernel::new(dom, cod, data)
}

/// Asserts that `cond_independent_at_each_input` on `f` gives `with_full` with
/// the lists `full` and `with_other` with the lists `other`, for two expected
/// results that differ, naming `name`; panics with `name`, the lists, the
/// input and the error when the engine returns an error.
#[track_caller]
fn assert_list_control(
    name: &str,
    f: &Kernel<Exact>,
    full: [&[usize]; 3],
    with_full: &[bool],
    other: [&[usize]; 3],
    with_other: &[bool],
) {
    assert_ne!(
        with_full, with_other,
        "list control {name}: the two expected results are equal"
    );
    let run = |lists: [&[usize]; 3]| match cond_independent_at_each_input(
        f, lists[0], lists[1], lists[2],
    ) {
        Ok(observed) => observed,
        Err((a, e)) => panic!(
            "list control {name}, lists {lists:?} on {}: expected Ok, observed Err({e:?}) at \
             input {a}",
            show(f)
        ),
    };
    let observed = (run(full), run(other));
    assert!(
        observed.0 == with_full && observed.1 == with_other,
        "list control {name} on {}: expected {with_full:?} with {full:?} and {with_other:?} with \
         {other:?}, observed {:?} and {:?}",
        show(f),
        observed.0,
        observed.1
    );
}

/// `g_tb : T → B`: hot to `(1/2, 1/2)`, cold to `(1/4, 3/4)`.
fn g_tb() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_b()?,
        &[&[r(1, 2), r(1, 2)], &[r(1, 4), r(3, 4)]],
    )
}

/// `h_tb_s : T ⊗ B → S`: `(hot, false)` to `(1, 0)`, `(hot, true)` to
/// `(0, 1)`, `(cold, false)` to `(1/2, 1/2)`, `(cold, true)` to `(1/3, 2/3)`.
fn h_tb_s() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?.tensor(&obj_b()?)?,
        obj_s()?,
        &[
            &[r(1, 1), r(0, 1)],
            &[r(0, 1), r(1, 1)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 3), r(2, 3)],
        ],
    )
}

/// `k_bt_p : B ⊗ T → P`: `(false, hot)` to `(1, 0)`, `(false, cold)` to
/// `(1/2, 1/2)`, `(true, hot)` to `(1/2, 1/2)`, `(true, cold)` to
/// `(1/4, 3/4)`.
fn k_bt_p() -> Result<Kernel<Exact>> {
    lit(
        obj_b()?.tensor(&obj_t()?)?,
        obj_p()?,
        &[
            &[r(1, 1), r(0, 1)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 4), r(3, 4)],
        ],
    )
}

/// `f_t : T → S ⊗ (B ⊗ P)`, the literal of
/// `cond_indep_form(g_tb, h_tb_s, k_bt_p)`: weight
/// `g_tb(b | t) · h_tb_s(s | (t, b)) · k_bt_p(p | (b, t))` at output
/// `(s, b, p)`.
fn f_t() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_s()?.tensor(&obj_b()?)?.tensor(&obj_p()?)?,
        &[
            &[
                r(1, 2),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(1, 4),
                r(1, 4),
            ],
            &[
                r(1, 16),
                r(1, 16),
                r(1, 16),
                r(3, 16),
                r(1, 16),
                r(1, 16),
                r(1, 8),
                r(3, 8),
            ],
        ],
    )
}

/// `f_t` with cold to the weights 1/2 at `(on, false, high)` and 1/2 at
/// `(off, false, low)`.
fn f_t_bad() -> Result<Kernel<Exact>> {
    replace_column(&f_t()?, 1, &sparse_column(8, &[(0, r(1, 2)), (5, r(1, 2))]))
}

/// `g_lw : L → W`: low to `(1/3, 0, 2/3)`, mid to `(1/2, 1/4, 1/4)`, high to
/// `(0, 1, 0)`.
fn g_lw() -> Result<Kernel<Exact>> {
    lit(
        obj_l()?,
        obj_w()?,
        &[
            &[r(1, 3), r(0, 1), r(2, 3)],
            &[r(1, 2), r(1, 4), r(1, 4)],
            &[r(0, 1), r(1, 1), r(0, 1)],
        ],
    )
}

/// `h_lw_c : L ⊗ W → C`: `(low, sunny)` to `(1, 0)`, `(low, cloudy)` to
/// `(1/2, 1/2)`, `(low, rainy)` to `(0, 1)`, `(mid, sunny)` to `(1/2, 1/2)`,
/// `(mid, cloudy)` to `(1/4, 3/4)`, `(mid, rainy)` to `(1, 0)`,
/// `(high, sunny)` to `(1/3, 2/3)`, `(high, cloudy)` to `(1/2, 1/2)`,
/// `(high, rainy)` to `(0, 1)`.
fn h_lw_c() -> Result<Kernel<Exact>> {
    lit(
        obj_l()?.tensor(&obj_w()?)?,
        obj_c()?,
        &[
            &[r(1, 1), r(0, 1)],
            &[r(1, 2), r(1, 2)],
            &[r(0, 1), r(1, 1)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 4), r(3, 4)],
            &[r(1, 1), r(0, 1)],
            &[r(1, 3), r(2, 3)],
            &[r(1, 2), r(1, 2)],
            &[r(0, 1), r(1, 1)],
        ],
    )
}

/// `k_wl_d : W ⊗ L → D`: `(sunny, low)` to `(1, 0)`, `(sunny, mid)` to
/// `(1/2, 1/2)`, `(sunny, high)` to `(1/4, 3/4)`, `(cloudy, low)` to
/// `(1/3, 2/3)`, `(cloudy, mid)` to `(0, 1)`, `(cloudy, high)` to
/// `(1/2, 1/2)`, `(rainy, low)` to `(0, 1)`, `(rainy, mid)` to `(1/3, 2/3)`,
/// `(rainy, high)` to `(1, 0)`.
fn k_wl_d() -> Result<Kernel<Exact>> {
    lit(
        obj_w()?.tensor(&obj_l()?)?,
        obj_d()?,
        &[
            &[r(1, 1), r(0, 1)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 4), r(3, 4)],
            &[r(1, 3), r(2, 3)],
            &[r(0, 1), r(1, 1)],
            &[r(1, 2), r(1, 2)],
            &[r(0, 1), r(1, 1)],
            &[r(1, 3), r(2, 3)],
            &[r(1, 1), r(0, 1)],
        ],
    )
}

/// `f_l : L → C ⊗ (W ⊗ D)`, the literal of
/// `cond_indep_form(g_lw, h_lw_c, k_wl_d)`: weight
/// `g_lw(w | l) · h_lw_c(c | (l, w)) · k_wl_d(d | (w, l))` at output
/// `(c, w, d)`.
fn f_l() -> Result<Kernel<Exact>> {
    lit(
        obj_l()?,
        obj_c()?.tensor(&obj_w()?)?.tensor(&obj_d()?)?,
        &[
            &sparse_column(12, &[(0, r(1, 3)), (11, r(2, 3))]),
            &[
                r(1, 8),
                r(1, 8),
                r(0, 1),
                r(1, 16),
                r(1, 12),
                r(1, 6),
                r(1, 8),
                r(1, 8),
                r(0, 1),
                r(3, 16),
                r(0, 1),
                r(0, 1),
            ],
            &[
                r(0, 1),
                r(0, 1),
                r(1, 4),
                r(1, 4),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(0, 1),
                r(1, 4),
                r(1, 4),
                r(0, 1),
                r(0, 1),
            ],
        ],
    )
}

/// `g_tl : T → L`: hot to `(1/2, 0, 1/2)`, cold to `(1/4, 3/4, 0)`.
fn g_tl() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_l()?,
        &[&[r(1, 2), r(0, 1), r(1, 2)], &[r(1, 4), r(3, 4), r(0, 1)]],
    )
}

/// `h_tl_s : T ⊗ L → S`: `(hot, low)` to `(1, 0)`, `(hot, mid)` to
/// `(1/2, 1/2)`, `(hot, high)` to `(1/3, 2/3)`, `(cold, low)` to `(0, 1)`,
/// `(cold, mid)` to `(1, 0)`, `(cold, high)` to `(1/2, 1/2)`.
fn h_tl_s() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?.tensor(&obj_l()?)?,
        obj_s()?,
        &[
            &[r(1, 1), r(0, 1)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 3), r(2, 3)],
            &[r(0, 1), r(1, 1)],
            &[r(1, 1), r(0, 1)],
            &[r(1, 2), r(1, 2)],
        ],
    )
}

/// `k_lt_p : L ⊗ T → P`: `(low, hot)` to `(1, 0)`, `(low, cold)` to
/// `(1/2, 1/2)`, `(mid, hot)` to `(1/2, 1/2)`, `(mid, cold)` to `(0, 1)`,
/// `(high, hot)` to `(0, 1)`, `(high, cold)` to `(1/2, 1/2)`.
fn k_lt_p() -> Result<Kernel<Exact>> {
    lit(
        obj_l()?.tensor(&obj_t()?)?,
        obj_p()?,
        &[
            &[r(1, 1), r(0, 1)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 2), r(1, 2)],
            &[r(0, 1), r(1, 1)],
            &[r(0, 1), r(1, 1)],
            &[r(1, 2), r(1, 2)],
        ],
    )
}

/// `f_t_slp : T → S ⊗ (L ⊗ P)`, the literal of
/// `cond_indep_form(g_tl, h_tl_s, k_lt_p)`: weight
/// `g_tl(l | t) · h_tl_s(s | (t, l)) · k_lt_p(p | (l, t))` at output
/// `(s, l, p)`.
fn f_t_slp() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_s()?.tensor(&obj_l()?)?.tensor(&obj_p()?)?,
        &[
            &sparse_column(12, &[(0, r(1, 2)), (5, r(1, 6)), (11, r(1, 3))]),
            &sparse_column(12, &[(3, r(3, 4)), (6, r(1, 8)), (7, r(1, 8))]),
        ],
    )
}

/// `u_ts_l : T ⊗ S → L`: `(hot, on)` to `(1/2, 1/2, 0)`, `(hot, off)` to
/// `(0, 1/3, 2/3)`, `(cold, on)` to `(1, 0, 0)`, `(cold, off)` to
/// `(1/4, 1/4, 1/2)`.
fn u_ts_l() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?.tensor(&obj_s()?)?,
        obj_l()?,
        &[
            &[r(1, 2), r(1, 2), r(0, 1)],
            &[r(0, 1), r(1, 3), r(2, 3)],
            &[r(1, 1), r(0, 1), r(0, 1)],
            &[r(1, 4), r(1, 4), r(1, 2)],
        ],
    )
}

/// `v_pt_c : P ⊗ T → C`: `(high, hot)` to `(1, 0)`, `(high, cold)` to
/// `(1/2, 1/2)`, `(low, hot)` to `(1/3, 2/3)`, `(low, cold)` to `(0, 1)`.
fn v_pt_c() -> Result<Kernel<Exact>> {
    lit(
        obj_p()?.tensor(&obj_t()?)?,
        obj_c()?,
        &[
            &[r(1, 1), r(0, 1)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 3), r(2, 3)],
            &[r(0, 1), r(1, 1)],
        ],
    )
}

/// `g_t_bs : T → B ⊗ S`: hot to `(1/3, 2/3, 0, 0)`, with no mass at first
/// factor true, cold to `(1/8, 1/8, 1/4, 1/2)`.
fn g_t_bs() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_b()?.tensor(&obj_s()?)?,
        &[
            &[r(1, 3), r(2, 3), r(0, 1), r(0, 1)],
            &[r(1, 8), r(1, 8), r(1, 4), r(1, 2)],
        ],
    )
}

/// The kernel `B ⊗ T → S` with `(false, hot)` to `(1/3, 2/3)`,
/// `(false, cold)` to `(1/2, 1/2)`, `(true, hot)` to `true_hot` and
/// `(true, cold)` to `true_cold`.
fn bt_to_s(true_hot: [Exact; 2], true_cold: [Exact; 2]) -> Result<Kernel<Exact>> {
    lit(
        obj_b()?.tensor(&obj_t()?)?,
        obj_s()?,
        &[
            &[r(1, 3), r(2, 3)],
            &[r(1, 2), r(1, 2)],
            &true_hot,
            &true_cold,
        ],
    )
}

/// `h_tbs_l : T ⊗ (B ⊗ S) → L`: `(hot, false, on)` to `(1, 0, 0)`,
/// `(hot, false, off)` to `(0, 1/2, 1/2)`, `(hot, true, on)` to
/// `(1/3, 1/3, 1/3)`, `(hot, true, off)` to `(0, 0, 1)`, `(cold, false, on)`
/// to `(1/2, 1/2, 0)`, `(cold, false, off)` to `(0, 1, 0)`,
/// `(cold, true, on)` to `(0, 0, 1)`, `(cold, true, off)` to
/// `(1/4, 1/4, 1/2)`.
fn h_tbs_l() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?.tensor(&obj_b()?)?.tensor(&obj_s()?)?,
        obj_l()?,
        &[
            &[r(1, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(1, 2), r(1, 2)],
            &[r(1, 3), r(1, 3), r(1, 3)],
            &[r(0, 1), r(0, 1), r(1, 1)],
            &[r(1, 2), r(1, 2), r(0, 1)],
            &[r(0, 1), r(1, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(1, 1)],
            &[r(1, 4), r(1, 4), r(1, 2)],
        ],
    )
}

/// `k_bst_p : (B ⊗ S) ⊗ T → P`: `(false, on, hot)` to `(1, 0)`,
/// `(false, on, cold)` to `(1/2, 1/2)`, `(false, off, hot)` to `(1/4, 3/4)`,
/// `(false, off, cold)` to `(0, 1)`, `(true, on, hot)` to `(1/2, 1/2)`,
/// `(true, on, cold)` to `(1, 0)`, `(true, off, hot)` to `(0, 1)`,
/// `(true, off, cold)` to `(1/3, 2/3)`.
fn k_bst_p() -> Result<Kernel<Exact>> {
    lit(
        obj_b()?.tensor(&obj_s()?)?.tensor(&obj_t()?)?,
        obj_p()?,
        &[
            &[r(1, 1), r(0, 1)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 4), r(3, 4)],
            &[r(0, 1), r(1, 1)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 1), r(0, 1)],
            &[r(0, 1), r(1, 1)],
            &[r(1, 3), r(2, 3)],
        ],
    )
}

/// `f_l_bsp : T → L ⊗ ((B ⊗ S) ⊗ P)`, the literal of
/// `cond_indep_form(g_t_bs, h_tbs_l, k_bst_p)`: weight
/// `g_t_bs((b, s) | t) · h_tbs_l(l | (t, b, s)) · k_bst_p(p | (b, s, t))` at
/// output `(l, b, s, p)`.
fn f_l_bsp() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_l()?
            .tensor(&obj_b()?)?
            .tensor(&obj_s()?)?
            .tensor(&obj_p()?)?,
        &[
            &sparse_column(
                24,
                &[
                    (0, r(1, 3)),
                    (10, r(1, 12)),
                    (11, r(1, 4)),
                    (18, r(1, 12)),
                    (19, r(1, 4)),
                ],
            ),
            &sparse_column(
                24,
                &[
                    (0, r(1, 32)),
                    (1, r(1, 32)),
                    (6, r(1, 24)),
                    (7, r(1, 12)),
                    (8, r(1, 32)),
                    (9, r(1, 32)),
                    (11, r(1, 8)),
                    (14, r(1, 24)),
                    (15, r(1, 12)),
                    (20, r(1, 4)),
                    (22, r(1, 12)),
                    (23, r(1, 6)),
                ],
            ),
        ],
    )
}

/// `f_b_lsp : T → B ⊗ (L ⊗ (S ⊗ P))`, the literal of
/// `f_l_bsp ≫ tensorCondReorder L B S P`: weight
/// `f_l_bsp((l, b, s, p) | t)` at output `(b, l, s, p)`.
fn f_b_lsp() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_b()?
            .tensor(&obj_l()?)?
            .tensor(&obj_s()?)?
            .tensor(&obj_p()?)?,
        &[
            &sparse_column(
                24,
                &[
                    (0, r(1, 3)),
                    (6, r(1, 12)),
                    (7, r(1, 4)),
                    (10, r(1, 12)),
                    (11, r(1, 4)),
                ],
            ),
            &sparse_column(
                24,
                &[
                    (0, r(1, 32)),
                    (1, r(1, 32)),
                    (4, r(1, 32)),
                    (5, r(1, 32)),
                    (7, r(1, 8)),
                    (14, r(1, 24)),
                    (15, r(1, 12)),
                    (18, r(1, 24)),
                    (19, r(1, 12)),
                    (20, r(1, 4)),
                    (22, r(1, 12)),
                    (23, r(1, 6)),
                ],
            ),
        ],
    )
}

/// `c_bt_lsp : B ⊗ T → L ⊗ (S ⊗ P)`: weight
/// `g'(s | (b, t)) · h_tbs_l(l | (t, b, s)) · k_bst_p(p | (b, s, t))` at
/// output `(l, s, p)`, with `g'` the kernel
/// `bt_to_s((1/2, 1/2), (1/3, 2/3))`.
fn c_bt_lsp() -> Result<Kernel<Exact>> {
    lit(
        obj_b()?.tensor(&obj_t()?)?,
        obj_l()?.tensor(&obj_s()?)?.tensor(&obj_p()?)?,
        &[
            &sparse_column(
                12,
                &[
                    (0, r(1, 3)),
                    (6, r(1, 12)),
                    (7, r(1, 4)),
                    (10, r(1, 12)),
                    (11, r(1, 4)),
                ],
            ),
            &sparse_column(
                12,
                &[
                    (0, r(1, 8)),
                    (1, r(1, 8)),
                    (4, r(1, 8)),
                    (5, r(1, 8)),
                    (7, r(1, 2)),
                ],
            ),
            &sparse_column(
                12,
                &[
                    (0, r(1, 12)),
                    (1, r(1, 12)),
                    (4, r(1, 12)),
                    (5, r(1, 12)),
                    (8, r(1, 12)),
                    (9, r(1, 12)),
                    (11, r(1, 2)),
                ],
            ),
            &sparse_column(
                12,
                &[
                    (2, r(1, 18)),
                    (3, r(1, 9)),
                    (6, r(1, 18)),
                    (7, r(1, 9)),
                    (8, r(1, 3)),
                    (10, r(1, 9)),
                    (11, r(2, 9)),
                ],
            ),
        ],
    )
}

/// `a_u_p : U → P`: `u` to `(1/3, 2/3)`.
fn a_u_p() -> Result<Kernel<Exact>> {
    lit(obj_u()?, obj_p()?, &[&[r(1, 3), r(2, 3)]])
}

/// `c_w_b : W → B`: sunny to `(1, 0)`, cloudy to `(1/2, 1/2)`, rainy to
/// `(1/4, 3/4)`.
fn c_w_b() -> Result<Kernel<Exact>> {
    lit(
        obj_w()?,
        obj_b()?,
        &[
            &[r(1, 1), r(0, 1)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 4), r(3, 4)],
        ],
    )
}

/// `b_ts : T → S`: hot to `(2/3, 1/3)`, cold to `(0, 1)`.
fn b_ts() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_s()?,
        &[&[r(2, 3), r(1, 3)], &[r(0, 1), r(1, 1)]],
    )
}

/// `c_z_c : Z → C`: `z` to `(3/4, 1/4)`.
fn c_z_c() -> Result<Kernel<Exact>> {
    lit(obj_z()?, obj_c()?, &[&[r(3, 4), r(1, 4)]])
}

/// At `A₁ = T`, `X₁ = S`, `W₁ = B`, `Y₁ = P`, `A₂ = L`, `X₂ = C`, `W₂ = W`,
/// `Y₂ = D`, with `f₁ = cond_indep_form(g₁, h₁, k₁)` for `g₁ = g_tb`,
/// `h₁ = h_tb_s` and `k₁ = k_bt_p`, and `f₂ = cond_indep_form(g₂, h₂, k₂)` for
/// `g₂ = g_lw`, `h₂ = h_lw_c` and `k₂ = k_wl_d`. The `==` half compares
/// `(f₁ ⊗ₘ f₂) ≫ tensorTripleInterchange S B P C W D` with two literal columns
/// and with `cond_indep_form` of `g₁ ⊗ₘ g₂`, `tensorδ T B L W ≫ (h₁ ⊗ₘ h₂)` and
/// `σ[B ⊗ W, T ⊗ L] ≫ tensorδ T B L W ≫ ((σ[T, B] ≫ k₁) ⊗ₘ (σ[L, W] ≫ k₂))`.
/// The result of `is_cond_independent_state` on the state at each input is a
/// claim of this test; its lists take each of the six objects as one factor.
/// The control tensors `f_t_bad`, which fails at cold, with `f₂`. Each list
/// control is a `two_point` kernel on the codomain of the composite.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.DisplaysCondIndep.tensor
#[test]
fn witness_displays_cond_indep_tensor() -> Result<()> {
    let (t, l) = (obj_t()?, obj_l()?);
    let (sp, b, p) = (obj_s()?, obj_b()?, obj_p()?);
    let (cc, w, d) = (obj_c()?, obj_w()?, obj_d()?);
    let (g1, h1, k1) = (g_tb()?, h_tb_s()?, k_bt_p()?);
    let (g2, h2, k2) = (g_lw()?, h_lw_c()?, k_wl_d()?);
    let f1 = cond_indep_form(&g1, &h1, &k1)?;
    let f2 = cond_indep_form(&g2, &h2, &k2)?;
    assert_kernel("f₁ = cond_indep_form(g_tb, h_tb_s, k_bt_p)", &f1, &f_t()?);
    assert_kernel("f₂ = cond_indep_form(g_lw, h_lw_c, k_wl_d)", &f2, &f_l()?);

    let reorder = interchange(&sp, &b, &p, &cc, &w, &d)?;
    let composite = then(&f1.tensor(&f2)?, &reorder)?;
    assert_column(
        "(f₁ ⊗ₘ f₂) ≫ tensorTripleInterchange S B P C W D",
        &composite,
        0,
        &sparse_column(
            96,
            &[
                (0, r(1, 6)),
                (33, r(1, 3)),
                (60, r(1, 12)),
                (62, r(1, 12)),
                (93, r(1, 6)),
                (95, r(1, 6)),
            ],
        ),
    );
    assert_column(
        "(f₁ ⊗ₘ f₂) ≫ tensorTripleInterchange S B P C W D",
        &composite,
        5,
        &sparse_column(
            96,
            &[
                (4, r(1, 64)),
                (5, r(1, 64)),
                (6, r(1, 64)),
                (7, r(1, 64)),
                (16, r(1, 64)),
                (17, r(1, 64)),
                (18, r(3, 64)),
                (19, r(3, 64)),
                (28, r(1, 64)),
                (29, r(1, 64)),
                (30, r(1, 64)),
                (31, r(1, 64)),
                (40, r(1, 64)),
                (41, r(1, 64)),
                (42, r(3, 64)),
                (43, r(3, 64)),
                (52, r(1, 64)),
                (53, r(1, 64)),
                (54, r(1, 64)),
                (55, r(1, 64)),
                (64, r(1, 32)),
                (65, r(1, 32)),
                (66, r(3, 32)),
                (67, r(3, 32)),
                (76, r(1, 64)),
                (77, r(1, 64)),
                (78, r(1, 64)),
                (79, r(1, 64)),
                (88, r(1, 32)),
                (89, r(1, 32)),
                (90, r(3, 32)),
                (91, r(3, 32)),
            ],
        ),
    );

    let (tl, bw) = (t.tensor(&l)?, b.tensor(&w)?);
    let first = g1.tensor(&g2)?;
    assert_kernel(
        "g₁ ⊗ₘ g₂",
        &first,
        &lit(
            tl.clone(),
            bw.clone(),
            &[
                &[r(1, 6), r(0, 1), r(1, 3), r(1, 6), r(0, 1), r(1, 3)],
                &[r(1, 4), r(1, 8), r(1, 8), r(1, 4), r(1, 8), r(1, 8)],
                &[r(0, 1), r(1, 2), r(0, 1), r(0, 1), r(1, 2), r(0, 1)],
                &[r(1, 12), r(0, 1), r(1, 6), r(1, 4), r(0, 1), r(1, 2)],
                &[r(1, 8), r(1, 16), r(1, 16), r(3, 8), r(3, 16), r(3, 16)],
                &[r(0, 1), r(1, 4), r(0, 1), r(0, 1), r(3, 4), r(0, 1)],
            ],
        )?,
    );
    let unshuffle = chain(&delta(&t, &b, &l, &w)?)?;
    let second = unshuffle.compose(&h1.tensor(&h2)?)?;
    assert_column(
        "tensorδ T B L W ≫ (h₁ ⊗ₘ h₂)",
        &second,
        12,
        &[r(1, 3), r(2, 3), r(0, 1), r(0, 1)],
    );
    assert_column(
        "tensorδ T B L W ≫ (h₁ ⊗ₘ h₂)",
        &second,
        28,
        &[r(1, 12), r(1, 4), r(1, 6), r(1, 2)],
    );
    let third = Kernel::swap(&bw, &tl)?.compose(&unshuffle)?.compose(
        &Kernel::swap(&t, &b)?
            .compose(&k1)?
            .tensor(&Kernel::swap(&l, &w)?.compose(&k2)?)?,
    )?;
    assert_column(
        "σ[B ⊗ W, T ⊗ L] ≫ tensorδ T B L W ≫ ((σ[T, B] ≫ k₁) ⊗ₘ (σ[L, W] ≫ k₂))",
        &third,
        6,
        &[r(1, 3), r(2, 3), r(0, 1), r(0, 1)],
    );
    assert_column(
        "σ[B ⊗ W, T ⊗ L] ≫ tensorδ T B L W ≫ ((σ[T, B] ≫ k₁) ⊗ₘ (σ[L, W] ≫ k₂))",
        &third,
        34,
        &[r(1, 12), r(1, 6), r(1, 4), r(1, 2)],
    );
    assert_kernel(
        "cond_indep_form(g₁ ⊗ₘ g₂, tensorδ T B L W ≫ (h₁ ⊗ₘ h₂), σ[B ⊗ W, T ⊗ L] ≫ tensorδ T B L \
         W ≫ ((σ[T, B] ≫ k₁) ⊗ₘ (σ[L, W] ≫ k₂)))",
        &cond_indep_form(&first, &second, &third)?,
        &composite,
    );
    assert_cond_independent_at_each_input("f₁", &f1, &[0], &[1], &[2], &[true, true]);
    assert_cond_independent_at_each_input("f₂", &f2, &[0], &[1], &[2], &[true, true, true]);
    assert_cond_independent_at_each_input(
        "(f₁ ⊗ₘ f₂) ≫ tensorTripleInterchange S B P C W D",
        &composite,
        &[0, 1],
        &[2, 3],
        &[4, 5],
        &[true, true, true, true, true, true],
    );

    let bad = f_t_bad()?;
    assert_cond_independent_at_each_input(
        "control: f_t_bad",
        &bad,
        &[0],
        &[1],
        &[2],
        &[true, false],
    );
    assert_cond_independent_at_each_input(
        "control: (f_t_bad ⊗ₘ f₂) ≫ tensorTripleInterchange S B P C W D",
        &then(&bad.tensor(&f2)?, &reorder)?,
        &[0, 1],
        &[2, 3],
        &[4, 5],
        &[true, true, true, false, false, false],
    );

    let cod = composite.codomain().clone();
    assert_list_control(
        "xs: second factor of xs equal to first factor of ys",
        &two_point(t.clone(), cod.clone(), 1, 26)?,
        [&[0, 1], &[2, 3], &[4, 5]],
        &[true, false],
        [&[0], &[2, 3], &[4, 5]],
        &[true, true],
    );
    assert_list_control(
        "ws: first factors of xs and ys equal to second factor of ws",
        &two_point(t.clone(), cod.clone(), 1, 54)?,
        [&[0, 1], &[2, 3], &[4, 5]],
        &[true, true],
        [&[0, 1], &[2], &[4, 5]],
        &[true, false],
    );
    assert_list_control(
        "ys: second factor of ys equal to first factor of xs",
        &two_point(t, cod, 1, 49)?,
        [&[0, 1], &[2, 3], &[4, 5]],
        &[true, false],
        [&[0, 1], &[2, 3], &[4]],
        &[true, true],
    );
    Ok(())
}

/// At `A = T`, `X₁ = S`, `V = L`, `Y₁ = P`, `X₂ = C`, `W = W`, `Y₂ = D`, with
/// `f = cond_indep_form(g₁, h₁, k₁)` for `g₁ = g_tl`, `h₁ = h_tl_s` and
/// `k₁ = k_lt_p`, and `g = cond_indep_form(g₂, h₂, k₂)` for `g₂ = g_lw`,
/// `h₂ = h_lw_c` and `k₂ = k_wl_d`. The `==` half compares
/// `f ≫ (S ◁ ((Δ[L] ≫ (L ◁ g)) ▷ P)) ≫ tensorCompReorder S L C W D P` with two
/// literal columns and with `cond_indep_form` of
/// `g₁ ≫ copyPair(𝟙 L, g₂)`,
/// `copyPair((T ◁ (L ◁ ε[W] ≫ ρ)) ≫ h₁, (ε[T] ▷ (L ⊗ W)) ≫ λ ≫ h₂)` and
/// `σ[L ⊗ W, T] ≫ copyPair((ε[T] ▷ (L ⊗ W)) ≫ λ ≫ σ[L, W] ≫ k₂,
/// (T ◁ (L ◁ ε[W] ≫ ρ)) ≫ σ[T, L] ≫ k₁)`. The result of
/// `is_cond_independent_state` on the state at each input is a claim of this
/// test; its lists take each of the six objects as one factor. The control
/// replaces the column of `g` at mid, which has mass under `f` at cold and
/// none at hot. Each list control is a `two_point` kernel on the codomain of
/// the composite.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.DisplaysCondIndep.comp
#[test]
fn witness_displays_cond_indep_comp() -> Result<()> {
    let (t, l, w) = (obj_t()?, obj_l()?, obj_w()?);
    let (sp, p) = (obj_s()?, obj_p()?);
    let (cc, d) = (obj_c()?, obj_d()?);
    let (g1, h1, k1) = (g_tl()?, h_tl_s()?, k_lt_p()?);
    let (g2, h2, k2) = (g_lw()?, h_lw_c()?, k_wl_d()?);
    let f = cond_indep_form(&g1, &h1, &k1)?;
    let g = cond_indep_form(&g2, &h2, &k2)?;
    assert_kernel("f = cond_indep_form(g_tl, h_tl_s, k_lt_p)", &f, &f_t_slp()?);
    assert_kernel("g = cond_indep_form(g_lw, h_lw_c, k_wl_d)", &g, &f_l()?);

    let copy = Kernel::copy(&l)?;
    let through = |g: &Kernel<Exact>| -> Result<Kernel<Exact>> {
        let on_copy = copy.compose(&Kernel::whisker_left(&l, g)?)?;
        Kernel::whisker_left(&sp, &Kernel::whisker_right(&on_copy, &p)?)
    };
    let reorder = comp_reorder(&sp, &l, &cc, &w, &d, &p)?;
    let composite = then(&f.compose(&through(&g)?)?, &reorder)?;
    assert_column(
        "f ≫ (S ◁ ((Δ[L] ≫ (L ◁ g)) ▷ P)) ≫ tensorCompReorder S L C W D P",
        &composite,
        0,
        &sparse_column(
            144,
            &[
                (0, r(1, 6)),
                (29, r(1, 24)),
                (31, r(1, 24)),
                (46, r(1, 3)),
                (65, r(1, 24)),
                (67, r(1, 24)),
                (101, r(1, 12)),
                (103, r(1, 12)),
                (137, r(1, 12)),
                (139, r(1, 12)),
            ],
        ),
    );
    assert_column(
        "f ≫ (S ◁ ((Δ[L] ≫ (L ◁ g)) ▷ P)) ≫ tensorCompReorder S L C W D P",
        &composite,
        1,
        &sparse_column(
            144,
            &[
                (13, r(3, 32)),
                (15, r(3, 32)),
                (19, r(3, 64)),
                (21, r(1, 16)),
                (23, r(1, 8)),
                (49, r(3, 32)),
                (51, r(3, 32)),
                (55, r(9, 64)),
                (72, r(1, 24)),
                (73, r(1, 24)),
                (118, r(1, 12)),
                (119, r(1, 12)),
            ],
        ),
    );

    let lw = l.tensor(&w)?;
    let drop_w =
        Kernel::whisker_left(&l, &Kernel::del(&w)?)?.compose(&Kernel::right_unitor(&l)?)?;
    let keep_tl = Kernel::whisker_left(&t, &drop_w)?;
    let keep_lw =
        Kernel::whisker_right(&Kernel::del(&t)?, &lw)?.compose(&Kernel::left_unitor(&lw)?)?;
    let first = g1.compose(&copy_pair(&Kernel::identity(&l)?, &g2)?)?;
    assert_kernel(
        "g₁ ≫ copyPair(𝟙 L, g₂)",
        &first,
        &lit(
            t.clone(),
            lw.clone(),
            &[
                &sparse_column(9, &[(0, r(1, 6)), (2, r(1, 3)), (7, r(1, 2))]),
                &sparse_column(
                    9,
                    &[
                        (0, r(1, 12)),
                        (2, r(1, 6)),
                        (3, r(3, 8)),
                        (4, r(3, 16)),
                        (5, r(3, 16)),
                    ],
                ),
            ],
        )?,
    );
    let second = copy_pair(&keep_tl.compose(&h1)?, &keep_lw.compose(&h2)?)?;
    assert_column(
        "copyPair((T ◁ (L ◁ ε[W] ≫ ρ)) ≫ h₁, (ε[T] ▷ (L ⊗ W)) ≫ λ ≫ h₂)",
        &second,
        7,
        &[r(1, 6), r(1, 6), r(1, 3), r(1, 3)],
    );
    assert_column(
        "copyPair((T ◁ (L ◁ ε[W] ≫ ρ)) ≫ h₁, (ε[T] ▷ (L ⊗ W)) ≫ λ ≫ h₂)",
        &second,
        13,
        &[r(1, 4), r(3, 4), r(0, 1), r(0, 1)],
    );
    let third = Kernel::swap(&lw, &t)?.compose(&copy_pair(
        &keep_lw.compose(&Kernel::swap(&l, &w)?)?.compose(&k2)?,
        &keep_tl.compose(&Kernel::swap(&t, &l)?)?.compose(&k1)?,
    )?)?;
    assert_column(
        "σ[L ⊗ W, T] ≫ copyPair((ε[T] ▷ (L ⊗ W)) ≫ λ ≫ σ[L, W] ≫ k₂, (T ◁ (L ◁ ε[W] ≫ ρ)) ≫ σ[T, \
         L] ≫ k₁)",
        &third,
        5,
        &[r(0, 1), r(0, 1), r(1, 2), r(1, 2)],
    );
    assert_column(
        "σ[L ⊗ W, T] ≫ copyPair((ε[T] ▷ (L ⊗ W)) ≫ λ ≫ σ[L, W] ≫ k₂, (T ◁ (L ◁ ε[W] ≫ ρ)) ≫ σ[T, \
         L] ≫ k₁)",
        &third,
        12,
        &[r(0, 1), r(1, 4), r(0, 1), r(3, 4)],
    );
    assert_kernel(
        "cond_indep_form of the three factors of DisplaysCondIndep.comp",
        &cond_indep_form(&first, &second, &third)?,
        &composite,
    );
    assert_cond_independent_at_each_input("f", &f, &[0], &[1], &[2], &[true, true]);
    assert_cond_independent_at_each_input("g", &g, &[0], &[1], &[2], &[true, true, true]);
    assert_cond_independent_at_each_input(
        "f ≫ (S ◁ ((Δ[L] ≫ (L ◁ g)) ▷ P)) ≫ tensorCompReorder S L C W D P",
        &composite,
        &[0, 1],
        &[2, 3],
        &[4, 5],
        &[true, true],
    );

    let bad = replace_column(
        &f_l()?,
        1,
        &sparse_column(12, &[(0, r(1, 2)), (7, r(1, 2))]),
    )?;
    assert_cond_independent_at_each_input(
        "control: g_bad",
        &bad,
        &[0],
        &[1],
        &[2],
        &[true, false, true],
    );
    assert_cond_independent_at_each_input(
        "control: f ≫ (S ◁ ((Δ[L] ≫ (L ◁ g_bad)) ▷ P)) ≫ tensorCompReorder S L C W D P",
        &then(&f.compose(&through(&bad)?)?, &reorder)?,
        &[0, 1],
        &[2, 3],
        &[4, 5],
        &[true, false],
    );

    let cod = composite.codomain().clone();
    assert_list_control(
        "xs: second factor of xs equal to first factor of ys",
        &two_point(t.clone(), cod.clone(), 1, 38)?,
        [&[0, 1], &[2, 3], &[4, 5]],
        &[true, false],
        [&[0], &[2, 3], &[4, 5]],
        &[true, true],
    );
    assert_list_control(
        "ws: first factors of xs and ys equal to second factor of ws",
        &two_point(t.clone(), cod.clone(), 1, 78)?,
        [&[0, 1], &[2, 3], &[4, 5]],
        &[true, true],
        [&[0, 1], &[2], &[4, 5]],
        &[true, false],
    );
    assert_list_control(
        "ys: second factor of ys equal to first factor of xs",
        &two_point(t, cod, 1, 73)?,
        [&[0, 1], &[2, 3], &[4, 5]],
        &[true, false],
        [&[0, 1], &[2, 3], &[4]],
        &[true, true],
    );
    Ok(())
}

/// At `A = T`, `X₁ = S`, `W = B`, `Y₁ = P`, `X₂ = L`, `Y₂ = C`, with
/// `f = cond_indep_form(g_tb, h, k)` for `h = h_tb_s` and `k = k_bt_p`,
/// `u = u_ts_l` and `v = v_pt_c`. The `==` half compares `Δ[T] ≫ (T ◁ Δ[T]) ≫ (T ◁ (f ▷ T)) ≫
/// tensorCompAssoc T S B P T ≫ (u ⊗ₘ (B ◁ v))` with a literal and with
/// `cond_indep_form(g_tb, (Δ[T] ▷ B) ≫ α ≫ (T ◁ h) ≫ u,
/// (B ◁ Δ[T]) ≫ α⁻¹ ≫ (k ▷ T) ≫ v)`. The result of
/// `is_cond_independent_state` on the state at each input is a claim of this
/// test. The control takes `f_t_bad`, which fails at cold, with
/// `u = (ε[T] ▷ S) ≫ λ` and `v = (P ◁ ε[T]) ≫ ρ`. Each list control is a
/// `two_point` kernel on `L ⊗ (B ⊗ C)`, with one list in place of the empty
/// list.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.DisplaysCondIndep.comp_tensorHom
#[test]
fn witness_displays_cond_indep_comp_tensor_hom() -> Result<()> {
    let (t, sp, b, p) = (obj_t()?, obj_s()?, obj_b()?, obj_p()?);
    let (l, cc) = (obj_l()?, obj_c()?);
    let (g1, h1, k1) = (g_tb()?, h_tb_s()?, k_bt_p()?);
    let (u, v) = (u_ts_l()?, v_pt_c()?);
    let f = cond_indep_form(&g1, &h1, &k1)?;
    assert_kernel("f = cond_indep_form(g_tb, h_tb_s, k_bt_p)", &f, &f_t()?);

    let cod = l.tensor(&b)?.tensor(&cc)?;
    let composite = comp_tensor_hom(&f, &sp, &b, &p, &u, &v)?;
    assert_kernel(
        "Δ[T] ≫ (T ◁ Δ[T]) ≫ (T ◁ (f ▷ T)) ≫ tensorCompAssoc T S B P T ≫ (u ⊗ₘ (B ◁ v))",
        &composite,
        &lit(
            t.clone(),
            cod.clone(),
            &[
                &[
                    r(1, 4),
                    r(0, 1),
                    r(0, 1),
                    r(0, 1),
                    r(1, 4),
                    r(0, 1),
                    r(1, 9),
                    r(1, 18),
                    r(0, 1),
                    r(0, 1),
                    r(2, 9),
                    r(1, 9),
                ],
                &[
                    r(5, 128),
                    r(15, 128),
                    r(3, 64),
                    r(21, 64),
                    r(1, 128),
                    r(3, 128),
                    r(1, 64),
                    r(7, 64),
                    r(1, 64),
                    r(3, 64),
                    r(1, 32),
                    r(7, 32),
                ],
            ],
        )?,
    );
    let second = Kernel::whisker_right(&Kernel::copy(&t)?, &b)?
        .compose(&Kernel::associator(&t, &t, &b)?)?
        .compose(&Kernel::whisker_left(&t, &h1)?)?
        .compose(&u)?;
    assert_kernel(
        "(Δ[T] ▷ B) ≫ α ≫ (T ◁ h) ≫ u",
        &second,
        &lit(
            t.tensor(&b)?,
            l.clone(),
            &[
                &[r(1, 2), r(1, 2), r(0, 1)],
                &[r(0, 1), r(1, 3), r(2, 3)],
                &[r(5, 8), r(1, 8), r(1, 4)],
                &[r(1, 2), r(1, 6), r(1, 3)],
            ],
        )?,
    );
    let third = Kernel::whisker_left(&b, &Kernel::copy(&t)?)?
        .compose(&Kernel::associator(&b, &t, &t)?)?
        .compose(&Kernel::whisker_right(&k1, &t)?)?
        .compose(&v)?;
    assert_kernel(
        "(B ◁ Δ[T]) ≫ α⁻¹ ≫ (k ▷ T) ≫ v",
        &third,
        &lit(
            b.tensor(&t)?,
            cc,
            &[
                &[r(1, 1), r(0, 1)],
                &[r(1, 4), r(3, 4)],
                &[r(2, 3), r(1, 3)],
                &[r(1, 8), r(7, 8)],
            ],
        )?,
    );
    assert_kernel(
        "cond_indep_form(g_tb, (Δ[T] ▷ B) ≫ α ≫ (T ◁ h) ≫ u, (B ◁ Δ[T]) ≫ α⁻¹ ≫ (k ▷ T) ≫ v)",
        &cond_indep_form(&g1, &second, &third)?,
        &composite,
    );
    assert_cond_independent_at_each_input(
        "Δ[T] ≫ (T ◁ Δ[T]) ≫ (T ◁ (f ▷ T)) ≫ tensorCompAssoc T S B P T ≫ (u ⊗ₘ (B ◁ v))",
        &composite,
        &[0],
        &[1],
        &[2],
        &[true, true],
    );
    assert_cond_independent_at_each_input("f", &f, &[0], &[1], &[2], &[true, true]);

    let bad = f_t_bad()?;
    let fst = Kernel::whisker_right(&Kernel::del(&t)?, &sp)?.compose(&Kernel::left_unitor(&sp)?)?;
    let snd = Kernel::whisker_left(&p, &Kernel::del(&t)?)?.compose(&Kernel::right_unitor(&p)?)?;
    let projected = comp_tensor_hom(&bad, &sp, &b, &p, &fst, &snd)?;
    assert_kernel(
        "control: the composite of f_t_bad with u = (ε[T] ▷ S) ≫ λ and v = (P ◁ ε[T]) ≫ ρ",
        &projected,
        &bad,
    );
    assert_cond_independent_at_each_input(
        "control: the composite of f_t_bad with u = (ε[T] ▷ S) ≫ λ and v = (P ◁ ε[T]) ≫ ρ",
        &projected,
        &[0],
        &[1],
        &[2],
        &[true, false],
    );

    assert_list_control(
        "xs: the factor of xs equal to the factor of ys",
        &two_point(t.clone(), cod.clone(), 1, 5)?,
        [&[0], &[1], &[2]],
        &[true, false],
        [&[], &[1], &[2]],
        &[true, true],
    );
    assert_list_control(
        "ws: the factors of xs and ys equal to the factor of ws",
        &two_point(t.clone(), cod.clone(), 1, 7)?,
        [&[0], &[1], &[2]],
        &[true, true],
        [&[0], &[], &[2]],
        &[true, false],
    );
    assert_list_control(
        "ys: the factor of ys equal to the factor of xs",
        &two_point(t, cod, 0, 9)?,
        [&[0], &[1], &[2]],
        &[false, true],
        [&[0], &[1], &[]],
        &[true, true],
    );
    Ok(())
}

/// At `A = T`, `X = L`, `V = B`, `W = S`, `Y = P`, with
/// `f = cond_indep_form(g, h, k)` for `g = g_t_bs`, `h = h_tbs_l` and
/// `k = k_bst_p`, and with `g' = conditional(g, B, S)`. The input hot gives
/// no mass to `V` true. The `==` half compares the Def. 11.5 composite of
/// `c = cond_indep_form(g', (σ[B, T] ▷ S) ≫ α ≫ h, α⁻¹ ≫ (σ[S, B] ▷ T) ≫ k)`
/// on `f ≫ tensorCondReorder L B S P` with `f ≫ tensorCondReorder L B S P`,
/// and each of `f`, `f ≫ tensorCondReorder L B S P`, `g'` and `c` with a
/// literal. The control replaces the column of `g'` at `(true, cold)`, an
/// input with mass.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.IsConditional.condIndepForm
#[test]
fn witness_is_conditional_cond_indep_form() -> Result<()> {
    let (t, l, b, sp, p) = (obj_t()?, obj_l()?, obj_b()?, obj_s()?, obj_p()?);
    let rest = l.tensor(&sp)?.tensor(&p)?;
    let (g, h1, k1) = (g_t_bs()?, h_tbs_l()?, k_bst_p()?);
    let f = cond_indep_form(&g, &h1, &k1)?;
    assert_kernel(
        "f = cond_indep_form(g_t_bs, h_tbs_l, k_bst_p)",
        &f,
        &f_l_bsp()?,
    );
    let reordered = then(&f, &cond_reorder(&l, &b, &sp, &p)?)?;
    assert_kernel("f ≫ tensorCondReorder L B S P", &reordered, &f_b_lsp()?);

    let cond_literal = bt_to_s([r(1, 2), r(1, 2)], [r(1, 3), r(2, 3)])?;
    let cond = conditional(&g, &b, &sp)?;
    assert_kernel("conditional(g_t_bs, B, S)", &cond, &cond_literal);
    let composed = cond_form(&cond, &h1, &k1, &t, &b, &sp)?;
    assert_kernel(
        "c = cond_indep_form(g', (σ[B, T] ▷ S) ≫ α ≫ h, α⁻¹ ≫ (σ[S, B] ▷ T) ≫ k)",
        &composed,
        &c_bt_lsp()?,
    );
    assert_kernel(
        "the Def. 11.5 composite of c on f ≫ tensorCondReorder L B S P",
        &conditional_composite(&reordered, &b, &rest, &composed)?,
        &reordered,
    );

    let free = bt_to_s([r(1, 1), r(0, 1)], [r(1, 3), r(2, 3)])?;
    assert_differs("(true, hot) at (1, 0) against (1/2, 1/2)", &free, &cond);
    assert_kernel(
        "the Def. 11.5 composite of c from the kernel with (true, hot) at (1, 0), a zero-mass \
         input",
        &conditional_composite(
            &reordered,
            &b,
            &rest,
            &cond_form(&free, &h1, &k1, &t, &b, &sp)?,
        )?,
        &reordered,
    );
    let changed = bt_to_s([r(1, 2), r(1, 2)], [r(2, 3), r(1, 3)])?;
    assert_differs(
        "control: the Def. 11.5 composite of c from the kernel with (true, cold) at (2/3, 1/3), \
         an input with mass",
        &conditional_composite(
            &reordered,
            &b,
            &rest,
            &cond_form(&changed, &h1, &k1, &t, &b, &sp)?,
        )?,
        &reordered,
    );
    Ok(())
}

/// At the objects, the `f` and the `c` of
/// `witness_is_conditional_cond_indep_form`. The `==` half compares the
/// Def. 11.5 composite of `c` on `f ≫ tensorCondReorder L B S P` with
/// `f ≫ tensorCondReorder L B S P`, and each of
/// `f ≫ tensorCondReorder L B S P` and `c` with a literal. The result of
/// `is_cond_independent_state` on the state at each input of `c`, in the
/// order `(false, hot)`, `(false, cold)`, `(true, hot)`, `(true, cold)` of
/// `B ⊗ T`, is a claim of this test. The control replaces the column of the
/// literal of `c` at `(false, cold)`. Each list control is a `two_point`
/// kernel `B ⊗ T → L ⊗ (S ⊗ P)`, with one list in place of the empty list.
/// THEOREM_MAP: CategoryTheory.CopyDiscardCategory.DisplaysCondIndep.exists_isConditional
#[test]
fn witness_displays_cond_indep_exists_is_conditional() -> Result<()> {
    let (t, l, b, sp, p) = (obj_t()?, obj_l()?, obj_b()?, obj_s()?, obj_p()?);
    let rest = l.tensor(&sp)?.tensor(&p)?;
    let (g, h1, k1) = (g_t_bs()?, h_tbs_l()?, k_bst_p()?);
    let f = cond_indep_form(&g, &h1, &k1)?;
    let reordered = then(&f, &cond_reorder(&l, &b, &sp, &p)?)?;
    assert_kernel("f ≫ tensorCondReorder L B S P", &reordered, &f_b_lsp()?);
    let literal = c_bt_lsp()?;
    let composed = cond_form(&conditional(&g, &b, &sp)?, &h1, &k1, &t, &b, &sp)?;
    assert_kernel(
        "c = cond_indep_form(g', (σ[B, T] ▷ S) ≫ α ≫ h, α⁻¹ ≫ (σ[S, B] ▷ T) ≫ k)",
        &composed,
        &literal,
    );
    assert_kernel(
        "the Def. 11.5 composite of c on f ≫ tensorCondReorder L B S P",
        &conditional_composite(&reordered, &b, &rest, &composed)?,
        &reordered,
    );
    assert_cond_independent_at_each_input(
        "c",
        &composed,
        &[0],
        &[1],
        &[2],
        &[true, true, true, true],
    );
    assert_cond_independent_at_each_input("f", &f, &[0], &[1, 2], &[3], &[true, true]);

    let dep = replace_column(
        &literal,
        1,
        &sparse_column(12, &[(0, r(1, 2)), (5, r(1, 2))]),
    )?;
    assert_cond_independent_at_each_input(
        "control: c_dep",
        &dep,
        &[0],
        &[1],
        &[2],
        &[true, false, true, true],
    );

    let bt = b.tensor(&t)?;
    assert_list_control(
        "xs: the factor of xs equal to the factor of ys",
        &two_point(bt.clone(), rest.clone(), 2, 5)?,
        [&[0], &[1], &[2]],
        &[true, true, false, true],
        [&[], &[1], &[2]],
        &[true, true, true, true],
    );
    assert_list_control(
        "ws: the factors of xs and ys equal to the factor of ws",
        &two_point(bt.clone(), rest.clone(), 3, 7)?,
        [&[0], &[1], &[2]],
        &[true, true, true, true],
        [&[0], &[], &[2]],
        &[true, true, true, false],
    );
    assert_list_control(
        "ys: the factor of ys equal to the factor of xs",
        &two_point(bt, rest, 1, 9)?,
        [&[0], &[1], &[2]],
        &[true, false, true, true],
        [&[0], &[1], &[]],
        &[true, true, true, true],
    );
    Ok(())
}

/// At `a₁ = a_u_p : U → P`, `b₁ = k : T → S`, `c₁ = c_w_b : W → B`,
/// `a₂ = m : S → T`, `b₂ = b_ts : T → S` and `c₂ = c_z_c : Z → C`. The `==`
/// half compares
/// `((a₁ ⊗ₘ (b₁ ⊗ₘ c₁)) ⊗ₘ (a₂ ⊗ₘ (b₂ ⊗ₘ c₂))) ≫ tensorTripleInterchange P S B T S C`
/// with two literal columns and with
/// `tensorTripleInterchange U T W S T Z ≫ ((a₁ ⊗ₘ a₂) ⊗ₘ ((b₁ ⊗ₘ b₂) ⊗ₘ (c₁ ⊗ₘ c₂)))`.
/// The control exchanges `b₁` and `b₂` on the right side.
/// THEOREM_MAP: CategoryTheory.MonoidalCategory.tensorTripleInterchange_hom_natural
#[test]
fn witness_tensor_triple_interchange_hom_natural() -> Result<()> {
    let (u, t, w, sp, z) = (obj_u()?, obj_t()?, obj_w()?, obj_s()?, obj_z()?);
    let (p, b, cc) = (obj_p()?, obj_b()?, obj_c()?);
    let (a1, b1, c1) = (a_u_p()?, k()?, c_w_b()?);
    let (a2, b2, c2) = (m()?, b_ts()?, c_z_c()?);
    assert_differs("b₁ against b₂", &b1, &b2);

    let grouped = a1
        .tensor(&b1.tensor(&c1)?)?
        .tensor(&a2.tensor(&b2.tensor(&c2)?)?)?;
    let lhs = then(&grouped, &interchange(&p, &sp, &b, &t, &sp, &cc)?)?;
    assert_column(
        "((a₁ ⊗ₘ (b₁ ⊗ₘ c₁)) ⊗ₘ (a₂ ⊗ₘ (b₂ ⊗ₘ c₂))) ≫ tensorTripleInterchange P S B T S C",
        &lhs,
        0,
        &sparse_column(
            64,
            &[
                (0, r(1, 6)),
                (1, r(1, 18)),
                (4, r(1, 12)),
                (5, r(1, 36)),
                (32, r(1, 3)),
                (33, r(1, 9)),
                (36, r(1, 6)),
                (37, r(1, 18)),
            ],
        ),
    );
    assert_column(
        "((a₁ ⊗ₘ (b₁ ⊗ₘ c₁)) ⊗ₘ (a₂ ⊗ₘ (b₂ ⊗ₘ c₂))) ≫ tensorTripleInterchange P S B T S C",
        &lhs,
        7,
        &sparse_column(
            64,
            &[
                (4, r(1, 16)),
                (5, r(1, 48)),
                (6, r(1, 16)),
                (7, r(1, 48)),
                (20, r(1, 16)),
                (21, r(1, 48)),
                (22, r(1, 16)),
                (23, r(1, 48)),
                (36, r(1, 8)),
                (37, r(1, 24)),
                (38, r(1, 8)),
                (39, r(1, 24)),
                (52, r(1, 8)),
                (53, r(1, 24)),
                (54, r(1, 8)),
                (55, r(1, 24)),
            ],
        ),
    );

    let regrouped = |first: &Kernel<Exact>, second: &Kernel<Exact>| -> Result<Kernel<Exact>> {
        a1.tensor(&a2)?
            .tensor(&first.tensor(second)?.tensor(&c1.tensor(&c2)?)?)
    };
    let reorder = chain(&interchange(&u, &t, &w, &sp, &t, &z)?)?;
    assert_kernel(
        "((a₁ ⊗ₘ (b₁ ⊗ₘ c₁)) ⊗ₘ (a₂ ⊗ₘ (b₂ ⊗ₘ c₂))) ≫ tensorTripleInterchange P S B T S C \
         against tensorTripleInterchange U T W S T Z ≫ ((a₁ ⊗ₘ a₂) ⊗ₘ ((b₁ ⊗ₘ b₂) ⊗ₘ (c₁ ⊗ₘ c₂)))",
        &lhs,
        &reorder.compose(&regrouped(&b1, &b2)?)?,
    );
    assert_differs(
        "control: tensorTripleInterchange U T W S T Z ≫ ((a₁ ⊗ₘ a₂) ⊗ₘ ((b₂ ⊗ₘ b₁) ⊗ₘ (c₁ ⊗ₘ \
         c₂))), b₁ and b₂ exchanged, against the left side",
        &reorder.compose(&regrouped(&b2, &b1)?)?,
        &lhs,
    );
    Ok(())
}

/// At `x1 = T`, `x2 = W`, `y1 = S`, `y2 = L`, of 2, 3, 2 and 3 elements: the
/// composite of `mu` sends `(t, w, s, l)` to `(t, s, w, l)`, the composite of
/// `delta` sends `(t, s, w, l)` to `(t, w, s, l)`, and each of the two
/// composites of the two is an identity.
#[test]
fn delta_inverts_mu() -> Result<()> {
    let (t, w, sp, l) = (obj_t()?, obj_w()?, obj_s()?, obj_l()?);
    let (dom, cod) = (
        t.tensor(&w)?.tensor(&sp)?.tensor(&l)?,
        t.tensor(&sp)?.tensor(&w)?.tensor(&l)?,
    );
    let shuffle = chain(&mu(&t, &w, &sp, &l)?)?;
    let unshuffle = chain(&delta(&t, &w, &sp, &l)?)?;
    assert_kernel(
        "tensorμ T W S L",
        &shuffle,
        &points(
            dom.clone(),
            cod.clone(),
            &[
                0, 1, 2, 9, 10, 11, 3, 4, 5, 12, 13, 14, 6, 7, 8, 15, 16, 17, 18, 19, 20, 27, 28,
                29, 21, 22, 23, 30, 31, 32, 24, 25, 26, 33, 34, 35,
            ],
        )?,
    );
    assert_kernel(
        "tensorδ T W S L",
        &unshuffle,
        &points(
            cod.clone(),
            dom.clone(),
            &[
                0, 1, 2, 6, 7, 8, 12, 13, 14, 3, 4, 5, 9, 10, 11, 15, 16, 17, 18, 19, 20, 24, 25,
                26, 30, 31, 32, 21, 22, 23, 27, 28, 29, 33, 34, 35,
            ],
        )?,
    );
    assert_kernel(
        "tensorμ T W S L ≫ tensorδ T W S L",
        &shuffle.compose(&unshuffle)?,
        &Kernel::identity(&dom)?,
    );
    assert_kernel(
        "tensorδ T W S L ≫ tensorμ T W S L",
        &unshuffle.compose(&shuffle)?,
        &Kernel::identity(&cod)?,
    );
    Ok(())
}

/// `copy_pair(c, h)` equals the literal `j : T → W ⊗ S`, and
/// `copy_pair(h, c) ≫ σ[S, W]` equals `copy_pair(c, h)`.
#[test]
fn copy_pair_matches_the_literal_j() -> Result<()> {
    let (w, sp) = (obj_w()?, obj_s()?);
    let (first, second) = (c()?, h()?);
    let pair = copy_pair(&first, &second)?;
    assert_kernel("copyPair(c, h)", &pair, &j()?);
    assert_kernel(
        "copyPair(h, c) ≫ σ[S, W]",
        &copy_pair(&second, &first)?.compose(&Kernel::swap(&sp, &w)?)?,
        &pair,
    );
    Ok(())
}
