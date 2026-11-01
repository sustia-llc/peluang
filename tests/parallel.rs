//! `prob::sum_with`: the parallel and sequential branches agree on exact
//! rational term vectors across the `PAR_THRESHOLD` boundary. `prob::sum`
//! over unit terms runs no add on a rayon worker at `PAR_THRESHOLD - 1` terms
//! and at least one at `PAR_THRESHOLD`. Outside a rayon pool, `prob::sum` and
//! `prob::sum_with(_, true)` at `PAR_THRESHOLD` terms and
//! `prob::sum_with(_, true)` at 2 terms run exactly one add off a worker, the
//! last add, on the calling thread; `prob::sum_with(_, true)` at 1 term runs
//! every add on the calling thread. `Compose::compose`, `Kernel::marginal_fst`
//! and `Kernel::marginal_snd` run no add on a rayon worker when the summed
//! object has `PAR_THRESHOLD - 1` elements and at least one at `PAR_THRESHOLD`.

#![cfg(feature = "parallel")]

mod common;
mod probe;

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
    use std::collections::BTreeSet;

    use peluang::error::Result;
    use peluang::finset::FinObj;
    use peluang::kernel::Kernel;
    use peluang::markov::Compose;
    use peluang::prob::{PAR_THRESHOLD, sum, sum_with};

    use crate::probe::{
        AddLog, Probe, ROUTES, add_sites, names, off_worker, point_mass, thread_name, unit_terms,
    };

    /// Runs `sum` over `len` unit terms; whether any `add` ran on a rayon
    /// worker.
    fn sum_ran_on_worker(len: usize) -> bool {
        add_sites(len, sum).iter().any(|site| site.on_worker)
    }

    /// Clears `log`, runs `op`; whether any `add` ran on a rayon worker.
    fn ran_on_worker(log: &AddLog, op: impl FnOnce() -> Result<Kernel<Probe>>) -> Result<bool> {
        log.lock().unwrap().clear();
        op()?;
        let sites = log.lock().unwrap();
        assert!(
            !sites.is_empty(),
            "expected a non-empty record, observed {sites:?}"
        );
        Ok(sites.iter().any(|site| site.on_worker))
    }

    /// `(on a worker below PAR_THRESHOLD, on a worker at PAR_THRESHOLD)`.
    fn dispatch(op: impl Fn(&AddLog, usize) -> Result<bool>) -> Result<(bool, bool)> {
        let log = AddLog::default();
        Ok((op(&log, PAR_THRESHOLD - 1)?, op(&log, PAR_THRESHOLD)?))
    }

    #[test]
    fn compose_dispatches_at_threshold() -> Result<()> {
        let observed = dispatch(|log, m| {
            let middle = FinObj::new(m);
            let f = point_mass(log, middle.clone())?;
            let (units, _) = unit_terms(log, m);
            let g = Kernel::new(middle, FinObj::unit(), units)?;
            ran_on_worker(log, || f.compose(&g))
        })?;
        assert_eq!(
            observed,
            (false, true),
            "expected no worker add below PAR_THRESHOLD and one at it, observed on the left"
        );
        Ok(())
    }

    #[test]
    fn marginal_fst_dispatches_at_threshold() -> Result<()> {
        let observed = dispatch(|log, m| {
            let (x, y) = (FinObj::new(2), FinObj::new(m));
            let joint = point_mass(log, x.tensor(&y)?)?;
            ran_on_worker(log, || joint.marginal_fst(&x, &y))
        })?;
        assert_eq!(
            observed,
            (false, true),
            "expected no worker add below PAR_THRESHOLD and one at it, observed on the left"
        );
        Ok(())
    }

    #[test]
    fn marginal_snd_dispatches_at_threshold() -> Result<()> {
        let observed = dispatch(|log, m| {
            let (x, y) = (FinObj::new(m), FinObj::new(2));
            let joint = point_mass(log, x.tensor(&y)?)?;
            ran_on_worker(log, || joint.marginal_snd(&x, &y))
        })?;
        assert_eq!(
            observed,
            (false, true),
            "expected no worker add below PAR_THRESHOLD and one at it, observed on the left"
        );
        Ok(())
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

    #[test]
    fn sum_outside_pool_combines_on_caller() {
        for (route, reduce) in ROUTES {
            let observed = off_worker(&add_sites(PAR_THRESHOLD, reduce));
            assert_eq!(
                observed,
                (1, BTreeSet::from([thread_name()]), true),
                "{route} over {PAR_THRESHOLD} terms: expected one add off a worker, on the calling thread, as the last record, observed (adds off a worker, their thread names, last record off a worker) on the left"
            );
        }
    }

    #[test]
    fn sum_with_two_terms_combines_on_caller() {
        let sites = add_sites(2, |terms| sum_with(terms, true));
        assert!(
            sites.iter().any(|site| site.on_worker),
            "sum_with over 2 terms: expected at least one add on a worker, observed {sites:?}"
        );
        assert_eq!(
            off_worker(&sites),
            (1, BTreeSet::from([thread_name()]), true),
            "sum_with over 2 terms: expected one add off a worker, on the calling thread, as the last record, observed (adds off a worker, their thread names, last record off a worker) on the left"
        );
    }

    #[test]
    fn sum_with_one_term_stays_on_caller() {
        let sites = add_sites(1, |terms| sum_with(terms, true));
        let on_worker = sites.iter().filter(|site| site.on_worker).count();
        let all_names = names(&sites, |_| true);
        assert!(
            !sites.is_empty(),
            "sum_with over 1 term: expected a non-empty record, observed {sites:?}"
        );
        assert_eq!(
            (on_worker, all_names),
            (0, BTreeSet::from([thread_name()])),
            "sum_with over 1 term: expected no add on a worker and every name the caller, observed (adds on a worker, thread names) on the left"
        );
    }
}
