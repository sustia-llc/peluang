//! `exec::Executor`: closures resolve to their value, run on threads named
//! `peluang-exec-*`, and run on a pool of the configured size.

#![cfg(feature = "async")]

use peluang::error::Result;
use peluang::exec::Executor;
use tokio_rayon::rayon;

fn thread_name() -> Option<String> {
    std::thread::current().name().map(str::to_owned)
}

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
