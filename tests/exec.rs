//! `exec::Executor`: closures resolve to their value, run on threads named
//! `peluang-exec-*`, run on a pool of the configured size (rayon's default
//! for `0`), and resume their panics on the awaiting task. `prob::sum` and
//! `prob::sum_with` stay on the executor pool inside `Executor::run`, and
//! `prob::sum` uses the global pool outside it, except for the last combining
//! `add` on the calling thread. `Executor` supports `#[derive(Debug)]` on a
//! struct that holds it.

#![cfg(feature = "async")]

use std::collections::BTreeSet;
use std::sync::{Arc, Mutex};

use peluang::error::Result;
use peluang::exec::Executor;
use peluang::prob::{PAR_THRESHOLD, Prob, sum, sum_with};
use tokio_rayon::rayon;

fn thread_name() -> Option<String> {
    std::thread::current().name().map(str::to_owned)
}

fn on_exec_thread(name: Option<&str>) -> bool {
    name.is_some_and(|n| n.starts_with("peluang-exec-"))
}

/// The thread that ran one `Probe::add`.
#[derive(Clone, Debug)]
struct AddSite {
    name: Option<String>,
    on_worker: bool,
}

type AddLog = Arc<Mutex<Vec<AddSite>>>;

/// Natural-number weights whose `add` appends its `AddSite` to `log`.
#[derive(Clone, Debug)]
struct Probe {
    n: u64,
    log: Option<AddLog>,
}

impl Probe {
    fn merge(&self, other: &Self, n: u64) -> Self {
        Probe {
            n,
            log: self.log.clone().or_else(|| other.log.clone()),
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
        Probe { n: 0, log: None }
    }

    fn one() -> Self {
        Probe { n: 1, log: None }
    }

    fn add(&self, other: &Self) -> Self {
        let out = self.merge(other, self.n + other.n);
        if let Some(log) = &out.log {
            log.lock().unwrap().push(AddSite {
                name: thread_name(),
                on_worker: rayon::current_thread_index().is_some(),
            });
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

/// `PAR_THRESHOLD` unit terms that record into `log`, and their sum.
fn unit_terms(log: &AddLog) -> (Vec<Probe>, u64) {
    let term = Probe {
        n: 1,
        log: Some(Arc::clone(log)),
    };
    let want = u64::try_from(PAR_THRESHOLD).expect("invariant: PAR_THRESHOLD fits in u64");
    (vec![term; PAR_THRESHOLD], want)
}

/// The distinct thread names in `sites` that `keep` selects.
fn names(sites: &[AddSite], keep: impl Fn(&AddSite) -> bool) -> BTreeSet<Option<String>> {
    sites
        .iter()
        .filter(|site| keep(site))
        .map(|site| site.name.clone())
        .collect()
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
    type Route = fn(&[Probe]) -> Probe;
    let routes: [(&str, Route); 2] = [("sum", sum), ("sum_with", |terms| sum_with(terms, true))];
    let exec = Executor::with_num_threads(2)?;
    let mut observed = Vec::new();
    for (route, reduce) in routes {
        let log = AddLog::default();
        let (terms, want) = unit_terms(&log);
        let total = exec.run(move || reduce(&terms).n).await;
        let sites = log.lock().unwrap();
        let off_pool = names(&sites, |site| !on_exec_thread(site.name.as_deref()));
        let held = total == want && !sites.is_empty() && off_pool.is_empty();
        observed.push((held, route, total, sites.len(), off_pool));
    }
    assert!(
        observed.iter().all(|(held, ..)| *held),
        "expected total = {PAR_THRESHOLD}, a non-empty record and every add on peluang-exec-*, observed (held, route, total, records, off-pool names): {observed:?}"
    );
    Ok(())
}

#[test]
fn sum_outside_run_uses_global_pool() -> Result<()> {
    let _exec = Executor::with_num_threads(2)?;
    let log = AddLog::default();
    let (terms, want) = unit_terms(&log);
    let total = sum(&terms).n;
    let sites = log.lock().unwrap();
    let off_worker = sites.iter().filter(|site| !site.on_worker).count();
    let off_worker_names = names(&sites, |site| !site.on_worker);
    let on_exec = names(&sites, |site| on_exec_thread(site.name.as_deref()));
    assert_eq!(total, want, "sum of {want} unit terms = {total}");
    assert!(
        sites.len() > 1,
        "expected adds beyond the top-level combine, observed {} records",
        sites.len()
    );
    assert!(
        on_exec.is_empty(),
        "expected no add on peluang-exec-*, observed adds on {on_exec:?}"
    );
    assert_eq!(
        (off_worker, off_worker_names),
        (1, BTreeSet::from([thread_name()])),
        "expected every add on a rayon worker except the one top-level combine on the calling thread, observed (adds off a worker, their thread names) on the left"
    );
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
