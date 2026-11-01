//! The running example as exact literals built with `Kernel::new`: the objects
//! `W`, `T`, `S`, the kernels `psi_t`, `c`, `s`, `h`, `f`, `j`, `d`, `e`, and
//! the comparison that reports observed and expected values.

#![allow(dead_code)]

use peluang::error::Result;
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::prob::{Exact, Prob};

pub fn r(n: i64, d: i64) -> Exact {
    Exact::new(n.into(), d.into())
}

fn labels(names: &[&str]) -> Result<FinObj> {
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

/// `d : W → S`: sunny to on, cloudy and rainy to off.
pub fn d() -> Result<Kernel<Exact>> {
    points(obj_w()?, obj_s()?, &[0, 1, 1])
}

/// `e : S → T`: on to hot, off to cold.
pub fn e() -> Result<Kernel<Exact>> {
    points(obj_s()?, obj_t()?, &[0, 1])
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
    use peluang::markov::Compose;

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
