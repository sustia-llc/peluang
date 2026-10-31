//! Caller-owned rayon thread pool whose jobs are awaited from async code.

use tokio_rayon::AsyncThreadPool;
use tokio_rayon::rayon;

use crate::error::{Error, Result};

/// A rayon thread pool with threads named `peluang-exec-{i}`, running each
/// submitted closure on the pool and resolving to its value.
#[derive(Debug)]
pub struct Executor {
    pool: rayon::ThreadPool,
}

impl Executor {
    /// Builds an executor with rayon's default thread count, or
    /// `Error::ThreadPool` when the pool cannot be built.
    pub fn new() -> Result<Self> {
        Self::build(rayon::ThreadPoolBuilder::new())
    }

    /// Builds an executor with `num_threads` threads (rayon's default count
    /// when `0`), or `Error::ThreadPool` when the pool cannot be built.
    pub fn with_num_threads(num_threads: usize) -> Result<Self> {
        Self::build(rayon::ThreadPoolBuilder::new().num_threads(num_threads))
    }

    fn build(builder: rayon::ThreadPoolBuilder) -> Result<Self> {
        let pool = builder
            .thread_name(|i| format!("peluang-exec-{i}"))
            .build()
            .map_err(|source| Error::ThreadPool { source })?;
        Ok(Self { pool })
    }

    /// Runs `f` on the pool and resolves to its return value; a panic in `f`
    /// resumes on the awaiting task.
    pub async fn run<F, R>(&self, f: F) -> R
    where
        F: FnOnce() -> R + Send + 'static,
        R: Send + 'static,
    {
        self.pool.spawn_async(f).await
    }
}
