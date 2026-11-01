//! `Compose::compose`, `Kernel::marginal_fst` and `Kernel::marginal_snd` under
//! an allocator that refuses the reservation of 64 weights: each returns
//! `Error::TooLarge` with the sizes of that reservation and a
//! `TryReserveError` source, for the buffer of the result and for the buffer of
//! the terms.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::collections::TryReserveError;
use std::error::Error as StdError;
use std::ptr;

use peluang::error::{Error, Result};
use peluang::finset::FinObj;
use peluang::kernel::Kernel;
use peluang::markov::Compose;
use peluang::prob::Exact;

const REFUSED: usize = 64;

thread_local! {
    /// The allocation size in bytes at or above which this thread's allocations
    /// return null.
    static LIMIT: Cell<usize> = const { Cell::new(usize::MAX) };
}

/// The system allocator, refusing allocations at or above `LIMIT`.
struct Refusing;

// SAFETY: `alloc` returns null or the result of `System.alloc` for the same
// layout, and `dealloc` passes a pointer from `System.alloc` back to `System`
// with its layout. `LIMIT` is a const-initialized `Cell<usize>`, so reading it
// allocates nothing.
unsafe impl GlobalAlloc for Refusing {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if layout.size() >= LIMIT.get() {
            ptr::null_mut()
        } else {
            // SAFETY: the caller of `alloc` guarantees a layout of non-zero
            // size, the one precondition of `System.alloc`.
            unsafe { System.alloc(layout) }
        }
    }

    unsafe fn dealloc(&self, block: *mut u8, layout: Layout) {
        // SAFETY: the caller passes a block of `layout` from `alloc`, which got
        // it from `System.alloc`.
        unsafe { System.dealloc(block, layout) }
    }
}

#[global_allocator]
static ALLOCATOR: Refusing = Refusing;

/// Runs `op` while this thread's allocations of `REFUSED` weights or more fail.
fn refusing(op: impl FnOnce() -> Result<Kernel<Exact>>) -> Result<Kernel<Exact>> {
    LIMIT.set(REFUSED * size_of::<Exact>());
    let got = op();
    LIMIT.set(usize::MAX);
    got
}

/// Asserts `got` is `Error::TooLarge` for `rows * cols` with a
/// `TryReserveError` source, naming `route`.
#[track_caller]
fn assert_refused(route: &str, got: &Result<Kernel<Exact>>, rows: usize, cols: usize) {
    let source = got.as_ref().err().and_then(StdError::source);
    assert!(
        matches!(got, Err(Error::TooLarge { fst, snd, source: Some(_) }) if *fst == rows && *snd == cols)
            && source.is_some_and(|source| source.is::<TryReserveError>()),
        "{route}: expected TooLarge {{ fst: {rows}, snd: {cols} }} with a TryReserveError source, observed {got:?}"
    );
}

/// The state on `cod` with weight 1 at output 0.
fn point_mass(cod: FinObj) -> Result<Kernel<Exact>> {
    Kernel::from_fn(FinObj::unit(), cod, |_| 0)
}

#[test]
fn compose_reports_a_refused_reservation() -> Result<()> {
    let wide = FinObj::new(REFUSED);

    let f = point_mass(FinObj::new(2))?;
    let g = Kernel::from_fn(FinObj::new(2), wide.clone(), |x| x)?;
    assert_refused("result buffer", &refusing(|| f.compose(&g)), 1, REFUSED);

    let f = point_mass(wide.clone())?;
    let g = Kernel::del(&wide)?;
    assert_refused("terms buffer", &refusing(|| f.compose(&g)), REFUSED, 1);
    Ok(())
}

#[test]
fn marginals_report_a_refused_reservation() -> Result<()> {
    let (one, wide) = (FinObj::new(1), FinObj::new(REFUSED));
    let wide_first = point_mass(wide.tensor(&one)?)?;
    let wide_last = point_mass(one.tensor(&wide)?)?;
    for (route, got, rows, cols) in [
        (
            "marginal_fst, result buffer",
            refusing(|| wide_first.marginal_fst(&wide, &one)),
            1,
            REFUSED,
        ),
        (
            "marginal_fst, terms buffer",
            refusing(|| wide_last.marginal_fst(&one, &wide)),
            REFUSED,
            1,
        ),
        (
            "marginal_snd, result buffer",
            refusing(|| wide_last.marginal_snd(&one, &wide)),
            1,
            REFUSED,
        ),
        (
            "marginal_snd, terms buffer",
            refusing(|| wide_first.marginal_snd(&wide, &one)),
            REFUSED,
            1,
        ),
    ] {
        assert_refused(route, &got, rows, cols);
    }
    Ok(())
}
