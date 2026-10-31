//! Shared `Prob` probe: weights that record the thread and pool of each `add`.

use std::collections::BTreeSet;
use std::sync::{Arc, Mutex};

use peluang::prob::Prob;

/// The name of the current thread.
pub fn thread_name() -> Option<String> {
    std::thread::current().name().map(str::to_owned)
}

/// The thread that ran one `Probe::add`, and the size of the rayon pool that
/// `rayon::current_num_threads` reported there.
#[derive(Clone, Debug)]
pub struct AddSite {
    pub name: Option<String>,
    pub on_worker: bool,
    #[allow(dead_code, reason = "read only by tests/exec.rs")]
    pub pool_size: usize,
}

pub type AddLog = Arc<Mutex<Vec<AddSite>>>;

/// Natural-number weights whose `add` appends its `AddSite` to `log`.
#[derive(Clone, Debug)]
pub struct Probe {
    pub n: u64,
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
                pool_size: rayon::current_num_threads(),
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

/// `len` unit terms that record into `log`, and their sum.
pub fn unit_terms(log: &AddLog, len: usize) -> (Vec<Probe>, u64) {
    let term = Probe {
        n: 1,
        log: Some(Arc::clone(log)),
    };
    let want = u64::try_from(len).expect("invariant: test sizes fit in u64");
    (vec![term; len], want)
}

/// The distinct thread names in `sites` that `keep` selects.
pub fn names(sites: &[AddSite], keep: impl Fn(&AddSite) -> bool) -> BTreeSet<Option<String>> {
    sites
        .iter()
        .filter(|site| keep(site))
        .map(|site| site.name.clone())
        .collect()
}
