//! `prob::sum_with`: the parallel and sequential branches agree on exact
//! rational term vectors across the `PAR_THRESHOLD` boundary.

#![cfg(feature = "parallel")]

#[cfg(not(feature = "f64-prob"))]
mod exact {
    use peluang::prob::{Exact, PAR_THRESHOLD, Prob, sum, sum_with};

    /// Terms `1/((i+1)(i+2))` for `i < n`, telescoping to `1 - 1/(n+1)`.
    fn telescoping(n: usize) -> Vec<Exact> {
        (0..n)
            .map(|i| {
                let i = i as i64;
                Exact::new(1.into(), ((i + 1) * (i + 2)).into())
            })
            .collect()
    }

    fn closed_form(n: usize) -> Exact {
        Exact::one().add(&Exact::new((-1).into(), (n as i64 + 1).into()))
    }

    #[test]
    fn sum_with_branches_agree_with_closed_form() {
        for n in [
            0,
            1,
            PAR_THRESHOLD - 1,
            PAR_THRESHOLD,
            3 * PAR_THRESHOLD + 7,
        ] {
            let terms = telescoping(n);
            let want = closed_form(n);
            let par = sum_with(&terms, true);
            let seq = sum_with(&terms, false);
            assert_eq!(
                par, seq,
                "n = {n}: parallel sum {par} != sequential sum {seq}"
            );
            assert_eq!(
                par, want,
                "n = {n}: parallel sum {par} != closed form 1 - 1/(n+1) = {want}"
            );
            assert_eq!(
                seq, want,
                "n = {n}: sequential sum {seq} != closed form 1 - 1/(n+1) = {want}"
            );
            let auto = sum(&terms);
            assert_eq!(
                auto, want,
                "n = {n}: sum {auto} != closed form 1 - 1/(n+1) = {want}"
            );
        }
    }

    #[test]
    fn sum_with_empty_is_zero() {
        let par = sum_with::<Exact>(&[], true);
        let seq = sum_with::<Exact>(&[], false);
        assert_eq!(par, Exact::zero(), "parallel sum of [] = {par}, expected 0");
        assert_eq!(
            seq,
            Exact::zero(),
            "sequential sum of [] = {seq}, expected 0"
        );
    }
}
