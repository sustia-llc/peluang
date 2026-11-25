//! The running example as exact literals built with `Kernel::new`: the objects
//! `W`, `T`, `S`, `P`, `B`, the kernels `psi_t`, `c`, `s`, `h`, `k`, `hot`,
//! `f`, `j`, `d`, `e`, `coin`, `p_ind`, `p_brk`, `s2`, `dd`, `g2`, `g0`, `c2`,
//! `m`, `e_inv`, `c3`, `on_b`, `const_b`, `not_b`, `q`, `hot_c`, `c_dagger`,
//! the constructors `r`, `labels`, `lit`, `points`, `point`, `w_to_t`, the
//! composites `conditional_composite` and `copy_whisker`, the printer `show`,
//! and the comparisons that report observed and expected values:
//! `assert_kernel`, `assert_differs`, `assert_as_equal`, `assert_independent`,
//! `assert_bayesian_inverse`, `assert_state_preserving`,
//! `assert_as_deterministic`, `assert_copy_comp_natural`,
//! `assert_copy_comp_natural_as`, `deterministic`, `assert_deterministic` and
//! `inverse`.

#![allow(dead_code)]

use peluang::almost_sure::as_equal;
use peluang::bayes::{bayesian_inverse, is_bayesian_inverse};
use peluang::deterministic::{is_as_deterministic, is_deterministic};
use peluang::error::Result;
use peluang::finset::FinObj;
use peluang::independence::is_independent;
use peluang::information_flow::{copy_comp_natural, copy_comp_natural_as};
use peluang::kernel::Kernel;
use peluang::markov::Compose;
use peluang::prob::{Exact, Prob};
use peluang::prob_space::is_state_preserving;

pub fn r(n: i64, d: i64) -> Exact {
    Exact::new(n.into(), d.into())
}

/// The object with one factor whose elements are `names` in order.
pub fn labels(names: &[&str]) -> Result<FinObj> {
    FinObj::labeled(names.iter().map(|&name| name.to_owned()).collect())
}

/// `W`: `{sunny, cloudy, rainy}`.
pub fn obj_w() -> Result<FinObj> {
    labels(&["sunny", "cloudy", "rainy"])
}

/// `T`: `{hot, cold}`.
pub fn obj_t() -> Result<FinObj> {
    labels(&["hot", "cold"])
}

/// `S`: `{on, off}`.
pub fn obj_s() -> Result<FinObj> {
    labels(&["on", "off"])
}

/// `P`: `{high, low}`.
pub fn obj_p() -> Result<FinObj> {
    labels(&["high", "low"])
}

/// The kernel `dom → cod` with `columns` in input order, through `Kernel::new`.
pub fn lit(dom: FinObj, cod: FinObj, columns: &[&[Exact]]) -> Result<Kernel<Exact>> {
    Kernel::new(dom, cod, columns.concat())
}

/// The deterministic kernel `dom → cod` with output `outputs[x]` on input `x`,
/// through `Kernel::new`.
pub fn points(dom: FinObj, cod: FinObj, outputs: &[usize]) -> Result<Kernel<Exact>> {
    let mut data = Vec::new();
    for &output in outputs {
        for y in 0..cod.card() {
            data.push(if y == output {
                Exact::one()
            } else {
                Exact::zero()
            });
        }
    }
    Kernel::new(dom, cod, data)
}

/// `psi_t : I → T`.
pub fn psi_t() -> Result<Kernel<Exact>> {
    Kernel::state(obj_t()?, vec![r(1, 5), r(4, 5)])
}

/// `c : T → W`.
pub fn c() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_w()?,
        &[&[r(1, 2), r(1, 2), r(0, 1)], &[r(0, 1), r(1, 4), r(3, 4)]],
    )
}

/// `s : W → S`.
pub fn s() -> Result<Kernel<Exact>> {
    lit(
        obj_w()?,
        obj_s()?,
        &[
            &[r(1, 3), r(2, 3)],
            &[r(1, 1), r(0, 1)],
            &[r(0, 1), r(1, 1)],
        ],
    )
}

/// `h : T → S`.
pub fn h() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_s()?,
        &[&[r(2, 3), r(1, 3)], &[r(1, 4), r(3, 4)]],
    )
}

/// `k : T → S`: hot to `(1, 0)`, cold to `(1/4, 3/4)`.
pub fn k() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_s()?,
        &[&[r(1, 1), r(0, 1)], &[r(1, 4), r(3, 4)]],
    )
}

/// The state `I → cod` with weight 1 at output `at`, through `Kernel::new`.
pub fn point(cod: FinObj, at: usize) -> Result<Kernel<Exact>> {
    points(FinObj::unit(), cod, &[at])
}

/// `hot : I → T`, `(1, 0)`.
pub fn hot() -> Result<Kernel<Exact>> {
    point(obj_t()?, 0)
}

/// `f : T → W ⊗ S`.
pub fn f() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_w()?.tensor(&obj_s()?)?,
        &[
            &[r(1, 6), r(1, 3), r(1, 2), r(0, 1), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(1, 4), r(0, 1), r(0, 1), r(3, 4)],
        ],
    )
}

/// `j : T → W ⊗ S`, the literal of `Δ[T] ≫ (c ⊗ₘ h)`.
pub fn j() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_w()?.tensor(&obj_s()?)?,
        &[
            &[r(1, 3), r(1, 6), r(1, 3), r(1, 6), r(0, 1), r(0, 1)],
            &[r(0, 1), r(0, 1), r(1, 16), r(3, 16), r(3, 16), r(9, 16)],
        ],
    )
}

/// `p_ind : I → T ⊗ P`, `(8/25, 12/25, 2/25, 3/25)`.
pub fn p_ind() -> Result<Kernel<Exact>> {
    Kernel::state(
        obj_t()?.tensor(&obj_p()?)?,
        vec![r(8, 25), r(12, 25), r(2, 25), r(3, 25)],
    )
}

/// `p_brk : I → T ⊗ P`, `(31/100, 49/100, 2/25, 3/25)`.
pub fn p_brk() -> Result<Kernel<Exact>> {
    Kernel::state(
        obj_t()?.tensor(&obj_p()?)?,
        vec![r(31, 100), r(49, 100), r(2, 25), r(3, 25)],
    )
}

/// `d : W → S`: sunny to on, cloudy and rainy to off.
pub fn d() -> Result<Kernel<Exact>> {
    points(obj_w()?, obj_s()?, &[0, 1, 1])
}

/// `e : S → T`: on to hot, off to cold.
pub fn e() -> Result<Kernel<Exact>> {
    points(obj_s()?, obj_t()?, &[0, 1])
}

/// `B`: `{false, true}`.
pub fn obj_b() -> Result<FinObj> {
    labels(&["false", "true"])
}

/// `coin : I → B`, `(1/2, 1/2)`.
pub fn coin() -> Result<Kernel<Exact>> {
    Kernel::state(obj_b()?, vec![r(1, 2), r(1, 2)])
}

/// `s2 : W → S`: sunny to `(1/3, 2/3)`, cloudy to `(1, 0)`, rainy to
/// `(1/2, 1/2)`.
pub fn s2() -> Result<Kernel<Exact>> {
    lit(
        obj_w()?,
        obj_s()?,
        &[
            &[r(1, 3), r(2, 3)],
            &[r(1, 1), r(0, 1)],
            &[r(1, 2), r(1, 2)],
        ],
    )
}

/// `dd : W → S`: sunny and cloudy to on, rainy to off.
pub fn dd() -> Result<Kernel<Exact>> {
    points(obj_w()?, obj_s()?, &[0, 0, 1])
}

/// `g2 : W → S`: sunny and cloudy to `(1, 0)`, rainy to `(1/2, 1/2)`.
pub fn g2() -> Result<Kernel<Exact>> {
    lit(
        obj_w()?,
        obj_s()?,
        &[
            &[r(1, 1), r(0, 1)],
            &[r(1, 1), r(0, 1)],
            &[r(1, 2), r(1, 2)],
        ],
    )
}

/// `g0 : W → S`: sunny, cloudy and rainy to `(1/2, 1/2)`.
pub fn g0() -> Result<Kernel<Exact>> {
    lit(
        obj_w()?,
        obj_s()?,
        &[
            &[r(1, 2), r(1, 2)],
            &[r(1, 2), r(1, 2)],
            &[r(1, 2), r(1, 2)],
        ],
    )
}

/// `c2 : T → W`: hot to `(1/2, 1/2, 0)`, cold to `(0, 0, 1)`.
pub fn c2() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_w()?,
        &[&[r(1, 2), r(1, 2), r(0, 1)], &[r(0, 1), r(0, 1), r(1, 1)]],
    )
}

/// `m : S → T`: on to `(1, 0)`, off to `(1/2, 1/2)`.
pub fn m() -> Result<Kernel<Exact>> {
    lit(
        obj_s()?,
        obj_t()?,
        &[&[r(1, 1), r(0, 1)], &[r(1, 2), r(1, 2)]],
    )
}

/// `e_inv : T → S`: hot to on, cold to off.
pub fn e_inv() -> Result<Kernel<Exact>> {
    points(obj_t()?, obj_s()?, &[0, 1])
}

/// `c3 : T → W`: hot to `(1/2, 1/2, 0)`, cold to `(1/3, 1/3, 1/3)`.
pub fn c3() -> Result<Kernel<Exact>> {
    lit(
        obj_t()?,
        obj_w()?,
        &[&[r(1, 2), r(1, 2), r(0, 1)], &[r(1, 3), r(1, 3), r(1, 3)]],
    )
}

/// `on_b : I → B`, `(0, 1)`: the point at `true`.
pub fn on_b() -> Result<Kernel<Exact>> {
    point(obj_b()?, 1)
}

/// `const_b : B → B`: false and true to `(0, 1)`, the point at `true`.
pub fn const_b() -> Result<Kernel<Exact>> {
    lit(
        obj_b()?,
        obj_b()?,
        &[&[r(0, 1), r(1, 1)], &[r(0, 1), r(1, 1)]],
    )
}

/// `not_b : B → B`: false to `(0, 1)`, true to `(1, 0)`.
pub fn not_b() -> Result<Kernel<Exact>> {
    lit(
        obj_b()?,
        obj_b()?,
        &[&[r(0, 1), r(1, 1)], &[r(1, 1), r(0, 1)]],
    )
}

/// `q : I → W`, `(1/10, 3/10, 3/5)`: the literal of `psi_t ≫ c`.
pub fn q() -> Result<Kernel<Exact>> {
    Kernel::state(obj_w()?, vec![r(1, 10), r(3, 10), r(3, 5)])
}

/// `hot ≫ c : I → W`, `(1/2, 1/2, 0)`, as a literal.
pub fn hot_c() -> Result<Kernel<Exact>> {
    Kernel::state(obj_w()?, vec![r(1, 2), r(1, 2), r(0, 1)])
}

/// The kernel `W → T` with the columns `sunny`, `cloudy`, `rainy`.
pub fn w_to_t(sunny: [Exact; 2], cloudy: [Exact; 2], rainy: [Exact; 2]) -> Result<Kernel<Exact>> {
    lit(obj_w()?, obj_t()?, &[&sunny, &cloudy, &rainy])
}

/// `c† : W → T`, sunny `(1, 0)`, cloudy `(1/3, 2/3)`, rainy `(0, 1)`: the
/// literal of `bayesian_inverse(psi_t, c)`.
pub fn c_dagger() -> Result<Kernel<Exact>> {
    w_to_t([r(1, 1), r(0, 1)], [r(1, 3), r(2, 3)], [r(0, 1), r(1, 1)])
}

/// The Def. 11.5 composite `Δ[A] ≫ (marginalFst f ▷ A) ≫ (Δ[x] ▷ A) ≫
/// α[x, x, A] ≫ (x ◁ k)` with `A` the domain of `f : A → x ⊗ y`.
pub fn conditional_composite(
    f: &Kernel<Exact>,
    x: &FinObj,
    y: &FinObj,
    k: &Kernel<Exact>,
) -> Result<Kernel<Exact>> {
    let a = f.domain();
    Kernel::copy(a)?
        .compose(&Kernel::whisker_right(&f.marginal_fst(x, y)?, a)?)?
        .compose(&Kernel::whisker_right(&Kernel::copy(x)?, a)?)?
        .compose(&Kernel::associator(x, x, a)?)?
        .compose(&Kernel::whisker_left(x, k)?)
}

/// The Def. 13.1 composite `p ≫ Δ[W] ≫ (f ▷ W)` with `W` the domain of `f`.
pub fn copy_whisker(p: &Kernel<Exact>, f: &Kernel<Exact>) -> Result<Kernel<Exact>> {
    let w = f.domain();
    p.compose(&Kernel::copy(w)?)?
        .compose(&Kernel::whisker_right(f, w)?)
}

fn show_obj(x: &FinObj) -> String {
    let factors: Vec<String> = x
        .factors()
        .iter()
        .map(|factor| match factor.labels() {
            Some(labels) => format!("{{{}}}", labels.join(",")),
            None => factor.card().to_string(),
        })
        .collect();
    format!("[{}]", factors.join(" ⊗ "))
}

/// The largest `dom.card() · cod.card()` that `show` prints in full.
const SHOW_LIMIT: usize = 4096;

/// The number of weights `show` prints for a kernel above `SHOW_LIMIT`.
const SHOW_HEAD: usize = 16;

/// The text `show` prints in place of the column at input `x` when
/// `Kernel::column` returns `None` for it.
fn missing_column(x: usize) -> String {
    format!("<column {x} missing>")
}

/// `dom → cod`, then the columns in input order. Above `SHOW_LIMIT` weights:
/// `dom → cod`, the dimensions, the first `SHOW_HEAD` entries in input order
/// and `dom.card() · cod.card()` minus the number of entries printed, or
/// `overflow` in place of that number when `dom.card() · cod.card()`
/// overflows `usize`. An entry is a weight or,
/// for an input whose column `Kernel::column` does not return, the text
/// `<column x missing>`, which stands in that column's place in both forms.
pub fn show(k: &Kernel<Exact>) -> String {
    let (dom, cod) = (k.domain().card(), k.codomain().card());
    let total = dom.checked_mul(cod);
    if total.is_none_or(|total| total > SHOW_LIMIT) {
        let head: Vec<String> = (0..dom)
            .flat_map(|x| match k.column(x) {
                Some(column) => column.iter().map(ToString::to_string).collect(),
                None => vec![missing_column(x)],
            })
            .take(SHOW_HEAD)
            .collect();
        let rest = total.map_or_else(
            || String::from("overflow"),
            |total| format!("{} more", total - head.len()),
        );
        return format!(
            "{} → {}: {dom}×{cod} weights, first {}: ({}) … {rest}",
            show_obj(k.domain()),
            show_obj(k.codomain()),
            head.len(),
            head.join(", "),
        );
    }
    let columns: Vec<String> = (0..dom)
        .map(|x| match k.column(x) {
            Some(column) => {
                let weights: Vec<String> = column.iter().map(ToString::to_string).collect();
                format!("({})", weights.join(", "))
            }
            None => missing_column(x),
        })
        .collect();
    format!(
        "{} → {}: {}",
        show_obj(k.domain()),
        show_obj(k.codomain()),
        columns.join(" ")
    )
}

/// Asserts `observed == expected`, naming `side`.
#[track_caller]
pub fn assert_kernel(side: &str, observed: &Kernel<Exact>, expected: &Kernel<Exact>) {
    assert!(
        observed == expected,
        "{side}: expected {}, observed {}",
        show(expected),
        show(observed)
    );
}

/// Asserts `observed != unexpected`, naming `side`.
#[track_caller]
pub fn assert_differs(side: &str, observed: &Kernel<Exact>, unexpected: &Kernel<Exact>) {
    assert!(
        observed != unexpected,
        "{side}: expected a kernel != {}, observed {}",
        show(unexpected),
        show(observed)
    );
}

/// Asserts `as_equal(p, f, g) == Ok(expected)`, naming the call `name`; panics
/// with `name` and the error when the engine returns an error.
#[track_caller]
pub fn assert_as_equal(
    name: &str,
    p: &Kernel<Exact>,
    f: &Kernel<Exact>,
    g: &Kernel<Exact>,
    expected: bool,
) {
    let observed = match as_equal(p, f, g) {
        Ok(observed) => observed,
        Err(e) => panic!(
            "{name} with p = {}, f = {}, g = {}: expected Ok({expected}), observed Err({e:?})",
            show(p),
            show(f),
            show(g)
        ),
    };
    assert_eq!(
        observed,
        expected,
        "{name} with p = {}, f = {}, g = {}: expected {expected}, observed {observed}",
        show(p),
        show(f),
        show(g)
    );
}

/// Asserts `is_independent(k, x, y) == Ok(expected)`, naming `name`; panics
/// with `name` and the error when the engine returns an error.
#[track_caller]
pub fn assert_independent(name: &str, k: &Kernel<Exact>, x: &FinObj, y: &FinObj, expected: bool) {
    let observed = match is_independent(k, x, y) {
        Ok(observed) => observed,
        Err(e) => panic!(
            "is_independent({name}) on {}: expected Ok({expected}), observed Err({e:?})",
            show(k)
        ),
    };
    assert_eq!(
        observed,
        expected,
        "is_independent({name}) on {}: expected {expected}, observed {observed}",
        show(k)
    );
}

/// Asserts `is_bayesian_inverse(p, f, g) == Ok(expected)`, naming the call
/// `name`; panics with `name` and the error when the engine returns an error.
#[track_caller]
pub fn assert_bayesian_inverse(
    name: &str,
    p: &Kernel<Exact>,
    f: &Kernel<Exact>,
    g: &Kernel<Exact>,
    expected: bool,
) {
    let observed = match is_bayesian_inverse(p, f, g) {
        Ok(observed) => observed,
        Err(e) => panic!(
            "{name} with p = {}, f = {}, g = {}: expected Ok({expected}), observed Err({e:?})",
            show(p),
            show(f),
            show(g)
        ),
    };
    assert_eq!(
        observed,
        expected,
        "{name} with p = {}, f = {}, g = {}: expected {expected}, observed {observed}",
        show(p),
        show(f),
        show(g)
    );
}

/// `bayesian_inverse(p, f)` after asserting that it equals `expected`; panics
/// with `name` and the error when the engine returns an error.
#[track_caller]
pub fn inverse(
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

/// Asserts `is_state_preserving(psi, f, phi) == Ok(expected)`, naming the call
/// `name`; panics with `name` and the error when the engine returns an error.
#[track_caller]
pub fn assert_state_preserving(
    name: &str,
    psi: &Kernel<Exact>,
    f: &Kernel<Exact>,
    phi: &Kernel<Exact>,
    expected: bool,
) {
    let observed = match is_state_preserving(psi, f, phi) {
        Ok(observed) => observed,
        Err(e) => panic!(
            "{name} with psi = {}, f = {}, phi = {}: expected Ok({expected}), observed Err({e:?})",
            show(psi),
            show(f),
            show(phi)
        ),
    };
    assert_eq!(
        observed,
        expected,
        "{name} with psi = {}, f = {}, phi = {}: expected {expected}, observed {observed}",
        show(psi),
        show(f),
        show(phi)
    );
}

/// Asserts `is_as_deterministic(p, f) == Ok(expected)`, naming the call
/// `name`; panics with `name` and the error when the engine returns an error.
#[track_caller]
pub fn assert_as_deterministic(name: &str, p: &Kernel<Exact>, f: &Kernel<Exact>, expected: bool) {
    let observed = match is_as_deterministic(p, f) {
        Ok(observed) => observed,
        Err(e) => panic!(
            "{name} with p = {}, f = {}: expected Ok({expected}), observed Err({e:?})",
            show(p),
            show(f)
        ),
    };
    assert_eq!(
        observed,
        expected,
        "{name} with p = {}, f = {}: expected {expected}, observed {observed}",
        show(p),
        show(f)
    );
}

/// Asserts `copy_comp_natural(f, g) == Ok(expected)`, naming the call `name`;
/// panics with `name` and the error when the engine returns an error.
#[track_caller]
pub fn assert_copy_comp_natural(name: &str, f: &Kernel<Exact>, g: &Kernel<Exact>, expected: bool) {
    let observed = match copy_comp_natural(f, g) {
        Ok(observed) => observed,
        Err(e) => panic!(
            "{name} with f = {}, g = {}: expected Ok({expected}), observed Err({e:?})",
            show(f),
            show(g)
        ),
    };
    assert_eq!(
        observed,
        expected,
        "{name} with f = {}, g = {}: expected {expected}, observed {observed}",
        show(f),
        show(g)
    );
}

/// Asserts `copy_comp_natural_as(p, f, g) == Ok(expected)`, naming the call
/// `name`; panics with `name` and the error when the engine returns an error.
#[track_caller]
pub fn assert_copy_comp_natural_as(
    name: &str,
    p: &Kernel<Exact>,
    f: &Kernel<Exact>,
    g: &Kernel<Exact>,
    expected: bool,
) {
    let observed = match copy_comp_natural_as(p, f, g) {
        Ok(observed) => observed,
        Err(e) => panic!(
            "{name} with p = {}, f = {}, g = {}: expected Ok({expected}), observed Err({e:?})",
            show(p),
            show(f),
            show(g)
        ),
    };
    assert_eq!(
        observed,
        expected,
        "{name} with p = {}, f = {}, g = {}: expected {expected}, observed {observed}",
        show(p),
        show(f),
        show(g)
    );
}

/// `is_deterministic(k)`; panics with `name`, `expected` (the text inside
/// `Ok(…)`) and the error when the engine returns an error.
#[track_caller]
fn deterministic_or_panic(name: &str, k: &Kernel<Exact>, expected: &str) -> bool {
    match is_deterministic(k) {
        Ok(observed) => observed,
        Err(e) => panic!(
            "is_deterministic({name}) on {}: expected Ok({expected}), observed Err({e:?})",
            show(k)
        ),
    }
}

/// `is_deterministic(k)`; panics with `name` and the error when the engine
/// returns an error.
#[track_caller]
pub fn deterministic(name: &str, k: &Kernel<Exact>) -> bool {
    deterministic_or_panic(name, k, "_")
}

/// Asserts `is_deterministic(k) == Ok(expected)`, naming `name`; panics with
/// `name`, `expected` and the error when the engine returns an error.
#[track_caller]
pub fn assert_deterministic(name: &str, k: &Kernel<Exact>, expected: bool) {
    let observed = deterministic_or_panic(name, k, &expected.to_string());
    assert_eq!(
        observed,
        expected,
        "is_deterministic({name}) on {}: expected {expected}, observed {observed}",
        show(k)
    );
}
