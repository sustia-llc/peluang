//! `exec::Executor`: closures resolve to their value, run on threads named
//! `peluang-exec-*`, run on a pool of the configured size (rayon's default
//! for `0`), and resume their panics on the awaiting task. Over
//! `PAR_THRESHOLD` unit terms inside `Executor::run`, `prob::sum` and
//! `prob::sum_with(_, true)` record more adds than a sequential run, each on
//! a `peluang-exec-*` thread that reports the executor's pool size. Over the
//! same terms outside it, they run no add on `peluang-exec-*`, the last add on
//! the calling thread, and every other add on a worker that reports the global
//! pool size. Inside `Executor::run`, `prob::sum_with(_, true)` over 1 and 2
//! terms runs every add on `peluang-exec-*`. `Executor` supports `#[derive(Debug)]` on a struct that holds
//! it. `Compose::compose` inside `Executor::run` with a middle object of
//! `PAR_THRESHOLD` elements records more adds than a sequential run, each on a
//! `peluang-exec-*` thread that reports the executor's pool size.

#![cfg(feature = "async")]

mod probe;

use std::collections::BTreeSet;
use std::sync::Arc;

use peluang::error::Result;
use peluang::exec::Executor;
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::Compose;
use peluang::prob::{PAR_THRESHOLD, Prob, sum_with};
use probe::{AddLog, Probe, ROUTES, add_sites, names, off_worker, thread_name, unit_terms};
use tokio_rayon::rayon;

fn on_exec_thread(name: Option<&str>) -> bool {
    name.is_some_and(|n| n.starts_with("peluang-exec-"))
}

#[tokio::test]
async fn run_returns_value_on_exec_thread() -> Result<()> {
    let exec = Executor::new()?;
    let (value, name) = exec.run(|| (6 * 7, thread_name())).await;
    assert_eq!(value, 42, "expected the closure's value 42, got {value}");
    assert!(
        on_exec_thread(name.as_deref()),
        "expected a thread named peluang-exec-*, observed {name:?}"
    );
    Ok(())
}

#[tokio::test]
async fn run_uses_the_configured_pool() -> Result<()> {
    let exec = Executor::with_num_threads(2)?;
    let threads = exec.run(rayon::current_num_threads).await;
    assert_eq!(
        threads, 2,
        "expected the executor's 2-thread pool, observed {threads}"
    );
    Ok(())
}

#[tokio::test]
async fn zero_threads_is_rayon_default() -> Result<()> {
    let default = Executor::new()?.run(rayon::current_num_threads).await;
    let zero = Executor::with_num_threads(0)?
        .run(rayon::current_num_threads)
        .await;
    assert_eq!(
        zero, default,
        "expected with_num_threads(0) to match Executor::new()'s {default} threads, observed {zero}"
    );
    Ok(())
}

#[tokio::test]
#[should_panic(expected = "peluang-exec job panicked")]
async fn run_resumes_panic_on_awaiting_task() {
    let exec = Executor::new().expect("pool builds");
    exec.run(|| panic!("peluang-exec job panicked")).await;
}

#[tokio::test]
async fn sum_inside_run_stays_on_executor_pool() -> Result<()> {
    let exec_size = rayon::current_num_threads() + 1;
    let exec = Executor::with_num_threads(exec_size)?;
    let mut observed = Vec::new();
    for (route, reduce) in ROUTES {
        let log = AddLog::default();
        let (terms, want) = unit_terms(&log, PAR_THRESHOLD);
        let total = exec.run(move || reduce(&terms).n).await;
        let sites = log.lock().unwrap();
        let off_pool = names(&sites, |site| !on_exec_thread(site.name.as_deref()));
        let sizes: BTreeSet<usize> = sites.iter().map(|site| site.pool_size).collect();
        let held = total == want
            && sites.len() > PAR_THRESHOLD + 1
            && off_pool.is_empty()
            && sizes == BTreeSet::from([exec_size]);
        observed.push((held, route, total, sites.len(), off_pool, sizes));
    }
    assert!(
        observed.iter().all(|(held, ..)| *held),
        "expected total = {PAR_THRESHOLD}, more than {} records (a sequential run records exactly that many), every add on peluang-exec-* and every add seeing the executor size {exec_size}, observed (held, route, total, records, off-pool names, pool sizes): {observed:?}",
        PAR_THRESHOLD + 1
    );
    Ok(())
}

#[tokio::test]
async fn compose_inside_run_stays_on_executor_pool() -> Result<()> {
    let exec_size = rayon::current_num_threads() + 1;
    let exec = Executor::with_num_threads(exec_size)?;
    let log = AddLog::default();
    let middle = FinObj::new(PAR_THRESHOLD);
    let (units, _) = unit_terms(&log, PAR_THRESHOLD);
    let point_mass: Vec<Probe> = units
        .iter()
        .enumerate()
        .map(|(y, unit)| {
            if y == 0 {
                unit.clone()
            } else {
                unit.mul(&Probe::zero())
            }
        })
        .collect();
    let f = Kernel::state(middle.clone(), point_mass)?;
    let g = Kernel::new(middle, FinObj::unit(), units)?;
    log.lock().unwrap().clear();

    let composite = exec.run(move || f.compose(&g)).await?;

    let total = composite.column(0).map(|column| column[0].n);
    let sites = log.lock().unwrap();
    let off_pool = names(&sites, |site| !on_exec_thread(site.name.as_deref()));
    let sizes: BTreeSet<usize> = sites.iter().map(|site| site.pool_size).collect();
    assert!(
        total == Some(1)
            && sites.len() > PAR_THRESHOLD + 1
            && off_pool.is_empty()
            && sizes == BTreeSet::from([exec_size]),
        "expected weight 1, more than {} records (a sequential run records at most that many), every add on peluang-exec-* and every add seeing the executor size {exec_size}, observed (weight, records, off-pool names, pool sizes): {:?}",
        PAR_THRESHOLD + 1,
        (total, sites.len(), &off_pool, &sizes)
    );
    Ok(())
}

#[tokio::test]
async fn sum_with_short_slices_inside_run_stay_on_executor_pool() -> Result<()> {
    let exec = Executor::new()?;
    for len in [1, 2] {
        let sites = exec
            .run(move || add_sites(len, |terms| sum_with(terms, true)))
            .await;
        let off_pool = names(&sites, |site| !on_exec_thread(site.name.as_deref()));
        assert!(
            !sites.is_empty(),
            "sum_with over {len} terms inside run: expected a non-empty record, observed {sites:?}"
        );
        assert!(
            off_pool.is_empty(),
            "sum_with over {len} terms inside run: expected every add on peluang-exec-*, observed adds on {off_pool:?}"
        );
    }
    Ok(())
}

#[test]
fn sum_outside_run_uses_global_pool() -> Result<()> {
    let global_size = rayon::current_num_threads();
    let exec_size = global_size + 1;
    let _exec = Executor::with_num_threads(exec_size)?;
    for (route, reduce) in ROUTES {
        let sites = add_sites(PAR_THRESHOLD, reduce);
        let on_exec = names(&sites, |site| on_exec_thread(site.name.as_deref()));
        let worker_sizes: BTreeSet<usize> = sites
            .iter()
            .filter(|site| site.on_worker)
            .map(|site| site.pool_size)
            .collect();
        assert!(
            on_exec.is_empty(),
            "{route}: expected no add on peluang-exec-*, observed adds on {on_exec:?}"
        );
        assert_eq!(
            worker_sizes,
            BTreeSet::from([global_size]),
            "{route}: expected every worker add to see the global size {global_size}, not the executor size {exec_size}, observed worker pool sizes on the left"
        );
        assert_eq!(
            off_worker(&sites),
            (1, BTreeSet::from([thread_name()]), true),
            "{route}: expected every add on a rayon worker except the one top-level combine on the calling thread, as the last record, observed (adds off a worker, their thread names, last record off a worker) on the left"
        );
    }
    Ok(())
}

#[test]
fn executor_debug_supports_derive_in_holder() -> Result<()> {
    #[derive(Debug)]
    struct Holder {
        #[expect(dead_code, reason = "read only through Debug")]
        pool: Arc<Executor>,
    }

    let holder = Holder {
        pool: Arc::new(Executor::with_num_threads(1)?),
    };
    let debug = format!("{holder:?}");
    assert!(
        debug.contains("Executor"),
        "expected the Debug output to name Executor, observed {debug}"
    );
    Ok(())
}
