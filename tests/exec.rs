//! `exec::Executor`: closures resolve to their value, run on threads named
//! `peluang-exec-*`, run on a pool of the configured size (rayon's default
//! for `0`), and resume their panics on the awaiting task. Over
//! `PAR_THRESHOLD` unit terms inside `Executor::run`, `prob::sum` and
//! `prob::sum_with(_, true)` record more adds than a sequential run, each on
//! a `peluang-exec-*` thread that reports the executor's pool size, on an
//! executor of 1 thread and of the global pool size plus 1. Over the
//! same terms outside it, they run no add on `peluang-exec-*`, the last add on
//! the calling thread, and every other add on a worker that reports the global
//! pool size. Inside `Executor::run`, `prob::sum_with(_, true)` over 1 and 2
//! terms runs every add on `peluang-exec-*`. `Executor` supports `#[derive(Debug)]` on a struct that holds
//! it. `Compose::compose` inside `Executor::run` with a middle object of
//! `PAR_THRESHOLD` elements records more adds than a sequential run, each on a
//! `peluang-exec-*` thread that reports the executor's pool size. On `Exact`
//! weights inside `Executor::run`, `prob::sum` and `prob::sum_with(_, true)`
//! over the telescoping terms of `PAR_THRESHOLD - 1`, `PAR_THRESHOLD` and
//! `3 * PAR_THRESHOLD + 7` elements equal their closed form, and a state on
//! such an object composed with `Kernel::del` is the weight 1. On a 1-thread
//! executor, a future of `Executor::run` dropped unpolled does not run its
//! closure before a later `run` on the same executor completes; one dropped
//! after one `Pending` poll runs its closure and drops the return value on
//! `peluang-exec-0`; and a panic of the closure of such a future reaches the
//! panic hook on `peluang-exec-0` and does not unwind the thread that dropped
//! it.

#![cfg(feature = "async")]

mod common;
mod probe;

use std::any::Any;
use std::collections::BTreeSet;
use std::future::Future;
use std::panic::{self, AssertUnwindSafe};
use std::pin::{Pin, pin};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, mpsc};
use std::task::{Context, Poll, Waker};
use std::time::Duration;

use common::{closed_form, telescoping};
use peluang::error::Result;
use peluang::exec::Executor;
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::Compose;
use peluang::prob::{Exact, PAR_THRESHOLD, Prob, sum, sum_with};
use probe::{AddLog, ROUTES, add_sites, names, off_worker, point_mass, thread_name, unit_terms};
use tokio_rayon::rayon;

fn on_exec_thread(name: Option<&str>) -> bool {
    name.is_some_and(|n| n.starts_with("peluang-exec-"))
}

/// How long a test waits for a pool thread before it reports a timeout.
const WAIT: Duration = Duration::from_secs(10);

/// Polls `fut` once with a waker that does nothing, discarding a ready value.
fn poll_once<F: Future>(fut: Pin<&mut F>) -> Poll<()> {
    fut.poll(&mut Context::from_waker(Waker::noop())).map(drop)
}

/// The text of a `&str` or `String` panic payload.
fn payload_text(payload: &(dyn Any + Send)) -> String {
    payload
        .downcast_ref::<&str>()
        .map(|s| (*s).to_owned())
        .or_else(|| payload.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "<non-string payload>".to_owned())
}

/// A return value that sends the name of the thread that drops it.
struct DropProbe(mpsc::Sender<Option<String>>);

impl Drop for DropProbe {
    fn drop(&mut self) {
        let _sent = self.0.send(thread_name());
    }
}

#[tokio::test]
async fn future_dropped_unpolled_does_not_run_f() -> Result<()> {
    let exec = Executor::with_num_threads(1)?;
    let ran = Arc::new(AtomicBool::new(false));
    let flag = Arc::clone(&ran);
    drop(exec.run(move || flag.store(true, Ordering::SeqCst)));
    let barrier = exec.run(|| 7).await;
    let observed = ran.load(Ordering::SeqCst);
    assert!(
        barrier == 7 && !observed,
        "expected the later run to return 7 and the dropped future's closure not to have run, observed (later run, closure ran) = ({barrier}, {observed})"
    );
    Ok(())
}

#[test]
fn future_dropped_after_first_poll_runs_f_and_drops_its_value_on_the_pool() -> Result<()> {
    let exec = Executor::with_num_threads(1)?;
    let (go_tx, go_rx) = mpsc::channel::<()>();
    let (drop_tx, drop_rx) = mpsc::channel();
    let polled = {
        let mut fut = pin!(exec.run(move || {
            let _gate = go_rx.recv_timeout(WAIT);
            DropProbe(drop_tx)
        }));
        poll_once(fut.as_mut())
    };
    let released = go_tx.send(()).is_ok();
    let dropped_on = drop_rx.recv_timeout(WAIT);
    assert_eq!(
        (polled, released, dropped_on.clone()),
        (Poll::Pending, true, Ok(Some("peluang-exec-0".to_owned()))),
        "expected the first poll Pending, the closure still waiting after the future was dropped, and its return value dropped on peluang-exec-0, observed (first poll, closure still waiting, dropping thread) = {:?}",
        (polled, released, dropped_on)
    );
    Ok(())
}

#[test]
fn panic_after_drop_reaches_only_the_panic_hook() -> Result<()> {
    const MESSAGE: &str = "peluang-exec orphaned panic";
    let (seen_tx, seen_rx) = mpsc::channel::<String>();
    let seen_tx = Mutex::new(seen_tx);
    let previous = Arc::new(panic::take_hook());
    let chained = Arc::clone(&previous);
    panic::set_hook(Box::new(move |info| {
        let text = payload_text(info.payload());
        if text == MESSAGE {
            if let Ok(tx) = seen_tx.lock() {
                let _sent = tx.send(format!("{}: {text}", thread_name().unwrap_or_default()));
            }
        } else {
            chained(info);
        }
    }));

    let exec = Executor::with_num_threads(1)?;
    let (go_tx, go_rx) = mpsc::channel::<()>();
    let outcome = panic::catch_unwind(AssertUnwindSafe(|| {
        let mut fut = pin!(exec.run(move || {
            let _gate = go_rx.recv_timeout(WAIT);
            panic!("{MESSAGE}");
        }));
        let polled = poll_once(fut.as_mut());
        go_tx
            .send(())
            .expect("the closure holds the receiver until it runs");
        polled
    }))
    .map_err(|payload| payload_text(&*payload));
    let seen = seen_rx.recv_timeout(WAIT);

    drop(panic::take_hook());
    panic::set_hook(Box::new(move |info| previous(info)));
    assert_eq!(
        (outcome.clone(), seen.clone()),
        (Ok(Poll::Pending), Ok(format!("peluang-exec-0: {MESSAGE}"))),
        "expected the dropping thread not to unwind after a Pending first poll and the hook to see the panic on peluang-exec-0, observed (dropping thread, hook) = {:?}",
        (outcome, seen)
    );
    Ok(())
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

/// Asserts that `prob::sum` and `prob::sum_with(_, true)` over `PAR_THRESHOLD`
/// unit terms inside `Executor::run` on an executor of `exec_size` threads
/// total `PAR_THRESHOLD`, record more adds than a sequential run, and run each
/// add on `peluang-exec-*` seeing the pool size `exec_size`.
async fn assert_sum_inside_run_stays_on_pool(exec_size: usize) -> Result<()> {
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
async fn sum_inside_run_stays_on_executor_pool() -> Result<()> {
    assert_sum_inside_run_stays_on_pool(rayon::current_num_threads() + 1).await
}

#[tokio::test]
async fn sum_inside_run_on_one_thread_executor_stays_on_it() -> Result<()> {
    assert_sum_inside_run_stays_on_pool(1).await
}

#[tokio::test]
async fn exact_sums_inside_run_are_exact() -> Result<()> {
    let exec = Executor::new()?;
    type ExactRoute = fn(&[Exact]) -> Exact;
    let routes: [(&str, ExactRoute); 2] =
        [("sum", sum), ("sum_with", |terms| sum_with(terms, true))];
    for n in [PAR_THRESHOLD - 1, PAR_THRESHOLD, 3 * PAR_THRESHOLD + 7] {
        let want = closed_form(n);
        for (route, reduce) in routes {
            let terms = telescoping(n);
            let total = exec.run(move || reduce(&terms)).await;
            assert_eq!(
                total, want,
                "{route} over {n} telescoping terms inside run: expected {want}, observed {total}"
            );
        }
        let mut weights = telescoping(n - 1);
        weights.push(Exact::new(1.into(), n.into()));
        let state = Kernel::state(FinObj::new(n), weights)?;
        let discarded = exec
            .run(move || state.compose(&Kernel::del(state.codomain())?))
            .await?;
        let weight = discarded.column(0).map(<[Exact]>::to_vec);
        assert_eq!(
            weight,
            Some(vec![Exact::one()]),
            "state on {n} elements composed with del inside run: expected the column [1], observed {weight:?}"
        );
    }
    Ok(())
}

#[tokio::test]
async fn compose_inside_run_stays_on_executor_pool() -> Result<()> {
    let exec_size = rayon::current_num_threads() + 1;
    let exec = Executor::with_num_threads(exec_size)?;
    let log = AddLog::default();
    let middle = FinObj::new(PAR_THRESHOLD);
    let f = point_mass(&log, middle.clone())?;
    let (units, _) = unit_terms(&log, PAR_THRESHOLD);
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
