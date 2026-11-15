//! The running example as exact literals built with `Kernel::new`: the objects
//! `W`, `T`, `S`, `P`, `B`, the kernels `psi_t`, `c`, `s`, `h`, `f`, `j`, `d`,
//! `e`, `coin`, `p_ind`, `p_brk`, and the comparisons that report observed and
//! expected values.

#![allow(dead_code)]

use peluang::almost_sure::as_equal;
use peluang::deterministic::is_deterministic;
use peluang::error::Result;
use peluang::finset::FinObj;
use peluang::independence::is_independent;
use peluang::kernel::Kernel;
use peluang::markov::Compose;
use peluang::prob::{Exact, Prob};

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

/// `dom → cod`, then the columns in input order.
pub fn show(k: &Kernel<Exact>) -> String {
    let columns: Vec<String> = (0..k.domain().card())
        .filter_map(|x| k.column(x))
        .map(|column| {
            let weights: Vec<String> = column.iter().map(ToString::to_string).collect();
            format!("({})", weights.join(", "))
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
