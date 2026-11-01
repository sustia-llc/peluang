//! Shared fixtures on `Exact` weights; each test binary uses a subset.

#![allow(dead_code)]

use peluang::prob::{Exact, Prob};

/// Terms `1/((i+1)(i+2))` for `i < n`, summing to `closed_form(n)`.
pub fn telescoping(n: usize) -> Vec<Exact> {
    (0..n)
        .map(|i| {
            let i = i64::try_from(i).expect("invariant: test sizes fit in i64");
            Exact::new(1.into(), ((i + 1) * (i + 2)).into())
        })
        .collect()
}

/// `1 - 1/(n+1)`.
pub fn closed_form(n: usize) -> Exact {
    let n = i64::try_from(n).expect("invariant: test sizes fit in i64");
    Exact::one().add(&Exact::new((-1).into(), (n + 1).into()))
}
