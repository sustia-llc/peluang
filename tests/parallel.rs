//! `prob::sum_with`: the parallel and sequential branches agree on exact
//! rational term vectors across the `PAR_THRESHOLD` boundary; `prob::sum`
//! runs on rayon workers exactly at or above `PAR_THRESHOLD` terms.

#![cfg(feature = "parallel")]

#[cfg(not(feature = "f64-prob"))]
mod common;

#[cfg(not(feature = "f64-prob"))]
mod exact {
    use crate::common::telescoping;
    use peluang::prob::{Exact, PAR_THRESHOLD, Prob, sum_with};

    #[test]
    fn sum_with_branches_agree() {
        for n in [
            0,
            1,
            PAR_THRESHOLD - 1,
            PAR_THRESHOLD,
            3 * PAR_THRESHOLD + 7,
        ] {
            let terms = telescoping(n);
            let par = sum_with(&terms, true);
            let seq = sum_with(&terms, false);
            assert_eq!(
                par, seq,
                "n = {n}: parallel sum {par} != sequential sum {seq}"
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

mod dispatch {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};

    use peluang::prob::{PAR_THRESHOLD, Prob, sum};

    /// Natural-number weights whose `add` sets `on_worker` when it runs on a
    /// rayon worker thread.
    #[derive(Clone, Debug)]
    struct Probe {
        n: u64,
        on_worker: Option<Arc<AtomicBool>>,
    }

    impl Probe {
        fn merge(&self, other: &Self, n: u64) -> Self {
            Probe {
                n,
                on_worker: self.on_worker.clone().or_else(|| other.on_worker.clone()),
            }
        }
    }

    impl PartialEq for Probe {
        fn eq(&self, other: &Self) -> bool {
            self.n == other.n
        }
    }

    impl Prob for Probe {
        fn zero() -> Self {
            Probe {
                n: 0,
                on_worker: None,
            }
        }

        fn one() -> Self {
            Probe {
                n: 1,
                on_worker: None,
            }
        }

        fn add(&self, other: &Self) -> Self {
            let out = self.merge(other, self.n + other.n);
            if let Some(flag) = &out.on_worker
                && rayon::current_thread_index().is_some()
            {
                flag.store(true, Ordering::SeqCst);
            }
            out
        }

        fn mul(&self, other: &Self) -> Self {
            self.merge(other, self.n * other.n)
        }

        fn div_checked(&self, other: &Self) -> Option<Self> {
            self.n.checked_div(other.n).map(|n| self.merge(other, n))
        }

        fn is_nonneg(&self) -> bool {
            true
        }

        fn approx_eq(&self, other: &Self) -> bool {
            self == other
        }
    }

    /// Runs `sum` over `len` unit terms; whether any `add` ran on a rayon
    /// worker.
    fn sum_ran_on_worker(len: usize) -> bool {
        let flag = Arc::new(AtomicBool::new(false));
        let terms = vec![
            Probe {
                n: 1,
                on_worker: Some(Arc::clone(&flag)),
            };
            len
        ];
        let total = sum(&terms).n;
        let want = u64::try_from(len).expect("invariant: test sizes fit in u64");
        assert_eq!(total, want, "sum of {len} unit terms = {total}");
        flag.load(Ordering::SeqCst)
    }

    #[test]
    fn sum_below_threshold_runs_sequentially() {
        let len = PAR_THRESHOLD - 1;
        let on_worker = sum_ran_on_worker(len);
        assert!(
            !on_worker,
            "sum over {len} terms (< PAR_THRESHOLD = {PAR_THRESHOLD}): expected no add on a rayon worker, observed on_worker = {on_worker}"
        );
    }

    #[test]
    fn sum_at_threshold_runs_on_rayon() {
        let len = PAR_THRESHOLD;
        let on_worker = sum_ran_on_worker(len);
        assert!(
            on_worker,
            "sum over {len} terms (= PAR_THRESHOLD): expected an add on a rayon worker, observed on_worker = {on_worker}"
        );
    }
}
