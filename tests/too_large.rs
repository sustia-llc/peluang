//! `Compose::compose`, `Tensor::tensor`, `FinObj::tensor`,
//! `Kernel::marginal_fst` and `Kernel::marginal_snd`, on `Exact` weights, under
//! an allocator that refuses allocations of at least the bytes of 64 `Exact`
//! weights: each returns `Error::TooLarge` with the sizes of the refused
//! reservation and a `TryReserveError` source, for the buffer of the result,
//! the buffer of the terms of `compose` and `marginal_snd`, and the three factor
//! list routes, the factor list of `FinObj::tensor` and the domain and codomain
//! factor lists of `Tensor::tensor`, which reserve `Factor`s of that byte size. `compose` on
//! an empty domain and `marginal_fst` reserve no terms under it. Under it,
//! `prob_space::coupling` and `prob_space::is_state_preserving` return their
//! `Error::NotAState`, `Error::NotComposable` and, for `is_state_preserving`,
//! `Error::NotParallel` on kernels whose result buffer it refuses, each before
//! a reservation of that buffer, and `Error::TooLarge` for that buffer on the
//! same kernels with no rejection. Under it, `coupling` returns the
//! `Error::TooLarge` of the factor list of `X ⊗ Y` on an `f : X → Y` whose
//! `X.card() * Y.card()` weights it does not refuse. Under it,
//! `conditional::conditional_snd` returns `Error::TooLarge` for the buffer of
//! the result on an `f : I → [2] ⊗ Y`, and the `Error::TooLarge` of the factor
//! list of `Y ⊗ A` on an `f : A → [2] ⊗ Y` whose result buffer it does not
//! refuse.
//! `refusing` restores the limit when `op` panics.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::collections::TryReserveError;
use std::error::Error as StdError;
use std::fmt::Debug;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::ptr;

use peluang::conditional::conditional_snd;
use peluang::error::{Error, Result};
use peluang::finset::{Factor, FinObj};
use peluang::kernel::Kernel;
use peluang::markov::{Compose, Tensor};
use peluang::prob::Exact;
use peluang::prob_space::{coupling, is_state_preserving};

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

/// Sets `LIMIT` to `usize::MAX` when dropped.
struct LimitReset;

impl Drop for LimitReset {
    fn drop(&mut self) {
        LIMIT.set(usize::MAX);
    }
}

/// Runs `op` while this thread's allocations of `REFUSED` weights or more fail.
fn refusing<T>(op: impl FnOnce() -> Result<T>) -> Result<T> {
    let _reset = LimitReset;
    LIMIT.set(REFUSED * size_of::<Exact>());
    op()
}

/// Asserts `got` is `Error::TooLarge` for `rows * cols` with a
/// `TryReserveError` source, naming `route`.
#[track_caller]
fn assert_refused<T: Debug>(route: &str, got: &Result<T>, rows: usize, cols: usize) {
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
fn compose_of_an_empty_domain_computes_no_terms() -> Result<()> {
    let (empty, wide) = (FinObj::new(0), FinObj::new(REFUSED));
    let f = Kernel::<Exact>::new(empty.clone(), wide.clone(), Vec::new())?;
    let g = Kernel::del(&wide)?;
    let expected = Kernel::new(empty, FinObj::unit(), Vec::new())?;
    let got = refusing(|| f.compose(&g));
    assert!(
        got.as_ref().is_ok_and(|kernel| *kernel == expected),
        "compose over a middle object of {REFUSED} elements: expected {expected:?}, observed {got:?}"
    );
    Ok(())
}

#[test]
fn tensors_report_a_refused_reservation() -> Result<()> {
    let (one, wide) = (FinObj::new(1), FinObj::new(REFUSED));

    let f = point_mass(wide)?;
    let g = point_mass(one.clone())?;
    assert_refused(
        "Tensor::tensor, result buffer",
        &refusing(|| f.tensor(&g)),
        1,
        REFUSED,
    );

    let factors = (REFUSED * size_of::<Exact>()).div_ceil(size_of::<Factor>());
    let list = (1..factors).try_fold(one.clone(), |list, _| list.tensor(&one))?;
    assert_refused(
        "FinObj::tensor, factor list",
        &refusing(|| list.tensor(&FinObj::unit())),
        factors,
        1,
    );

    let f = Kernel::del(&list)?;
    let g = point_mass(FinObj::unit())?;
    assert_refused(
        "Tensor::tensor, domain factor list",
        &refusing(|| f.tensor(&g)),
        factors,
        1,
    );

    let f = point_mass(list)?;
    let g = point_mass(FinObj::unit())?;
    assert_refused(
        "Tensor::tensor, codomain factor list",
        &refusing(|| f.tensor(&g)),
        factors,
        1,
    );
    Ok(())
}

/// Asserts `got` is `Error::NotAState` with `expected`, naming `call`.
#[track_caller]
fn assert_not_a_state<T: Debug>(call: &str, got: &Result<T>, expected: &FinObj) {
    assert!(
        matches!(got, Err(Error::NotAState { domain }) if domain == expected),
        "{call}: expected NotAState {{ domain: {expected:?} }}, observed {got:?}"
    );
}

/// Asserts `got` is `Error::NotComposable` with `cod` and `dom`, naming `call`.
#[track_caller]
fn assert_not_composable<T: Debug>(call: &str, got: &Result<T>, cod: &FinObj, dom: &FinObj) {
    assert!(
        matches!(got, Err(Error::NotComposable { codomain, domain })
            if codomain == cod && domain == dom),
        "{call}: expected NotComposable {{ codomain: {cod:?}, domain: {dom:?} }}, observed {got:?}"
    );
}

/// With `f : [2] → [REFUSED]`, whose coupling holds `2 * REFUSED` weights:
/// `coupling` returns `Error::NotAState` on `(𝟙 [2], f)`,
/// `Error::NotComposable` on `(I → [3], f)` and `Error::TooLarge` for
/// `1 * (2 * REFUSED)` on `(I → [2], f)`.
#[test]
fn coupling_rejects_before_it_reserves_and_reports_a_refused_reservation() -> Result<()> {
    let (two, three) = (FinObj::new(2), FinObj::new(3));
    let f = Kernel::<Exact>::from_fn(two.clone(), FinObj::new(REFUSED), |x| x)?;
    let id = Kernel::<Exact>::identity(&two)?;
    let (on_two, on_three) = (point_mass(two.clone())?, point_mass(three.clone())?);
    assert_not_a_state("coupling(𝟙 [2], f)", &refusing(|| coupling(&id, &f)), &two);
    assert_not_composable(
        "coupling(I → [3], f)",
        &refusing(|| coupling(&on_three, &f)),
        &three,
        &two,
    );
    assert_refused(
        "coupling(I → [2], f), result buffer",
        &refusing(|| coupling(&on_two, &f)),
        1,
        2 * REFUSED,
    );
    Ok(())
}

/// With `f : [2] → [REFUSED]` and `phi : I → [REFUSED]`: `is_state_preserving`
/// returns `Error::NotAState` on `(𝟙 [2], f, phi)`, `Error::NotComposable` on
/// `(I → [3], f, phi)` and `Error::NotParallel` on `(I → [2], f, I → [2])`,
/// each before a reservation of `1 * REFUSED` weights, and `Error::TooLarge`
/// for `1 * REFUSED` on `(I → [2], f, phi)`.
#[test]
fn is_state_preserving_rejects_before_it_reserves_and_reports_a_refused_reservation() -> Result<()>
{
    let (unit, two, wide) = (FinObj::unit(), FinObj::new(2), FinObj::new(REFUSED));
    let three = FinObj::new(3);
    let f = Kernel::<Exact>::from_fn(two.clone(), wide.clone(), |x| x)?;
    let phi = point_mass(wide.clone())?;
    let id = Kernel::<Exact>::identity(&two)?;
    let (on_two, on_three) = (point_mass(two.clone())?, point_mass(three.clone())?);
    assert_not_a_state(
        "is_state_preserving(𝟙 [2], f, phi)",
        &refusing(|| is_state_preserving(&id, &f, &phi)),
        &two,
    );
    assert_not_composable(
        "is_state_preserving(I → [3], f, phi)",
        &refusing(|| is_state_preserving(&on_three, &f, &phi)),
        &three,
        &two,
    );
    let got = refusing(|| is_state_preserving(&on_two, &f, &on_two));
    let (fst, snd) = ((&unit, &wide), (&unit, &two));
    assert!(
        matches!(&got, Err(Error::NotParallel { fst: a, snd: b })
            if (&a.0, &a.1) == fst && (&b.0, &b.1) == snd),
        "is_state_preserving(I → [2], f, I → [2]): expected NotParallel {{ fst: {fst:?}, snd: \
         {snd:?} }}, observed {got:?}"
    );
    assert_refused(
        "is_state_preserving(I → [2], f, phi), result buffer",
        &refusing(|| is_state_preserving(&on_two, &f, &phi)),
        1,
        REFUSED,
    );
    Ok(())
}

/// With `X` of `factors` factors of one element, `factors * size_of::<Factor>()`
/// at or above the refused byte size, and `f : X → [2]`, whose coupling holds
/// `1 * 2` weights: `coupling` returns the `Error::TooLarge` of the factor list
/// of `X ⊗ [2]`, for `(factors + 1) * 1`, on `(I → X, f)`.
#[test]
fn coupling_reports_a_refused_factor_list_reservation() -> Result<()> {
    let (one, two) = (FinObj::new(1), FinObj::new(2));
    let factors = (REFUSED * size_of::<Exact>()).div_ceil(size_of::<Factor>());
    let list = (1..factors).try_fold(one.clone(), |list, _| list.tensor(&one))?;
    let psi = point_mass(list.clone())?;
    let f = Kernel::<Exact>::from_fn(list, two, |_| 0)?;
    assert_refused(
        "coupling(I → X, f), factor list of X ⊗ [2]",
        &refusing(|| coupling(&psi, &f)),
        factors + 1,
        1,
    );
    Ok(())
}

/// With `f : I → [2] ⊗ [REFUSED]`, whose conditional on `[REFUSED]` holds
/// `REFUSED * 2` weights: `conditional_snd` returns `Error::TooLarge` for
/// `REFUSED * 2`. With `Y` of `factors` factors of one element,
/// `factors * size_of::<Factor>()` at or above the refused byte size, and
/// `f : [1] → [2] ⊗ Y`, whose conditional on `Y` holds `1 * 2` weights:
/// `conditional_snd` returns the `Error::TooLarge` of the factor list of
/// `Y ⊗ [1]`, for `(factors + 1) * 1`.
#[test]
fn conditional_snd_reports_a_refused_reservation() -> Result<()> {
    let (one, two, wide) = (FinObj::new(1), FinObj::new(2), FinObj::new(REFUSED));
    let f = point_mass(two.tensor(&wide)?)?;
    assert_refused(
        "conditional_snd(I → [2] ⊗ [REFUSED]), result buffer",
        &refusing(|| conditional_snd(&f, &two, &wide)),
        REFUSED,
        2,
    );

    let factors = (REFUSED * size_of::<Exact>()).div_ceil(size_of::<Factor>());
    let list = (1..factors).try_fold(one.clone(), |list, _| list.tensor(&one))?;
    let f = Kernel::<Exact>::from_fn(one, two.tensor(&list)?, |_| 0)?;
    assert_refused(
        "conditional_snd([1] → [2] ⊗ Y), factor list of Y ⊗ [1]",
        &refusing(|| conditional_snd(&f, &two, &list)),
        factors + 1,
        1,
    );
    Ok(())
}

#[test]
fn refusing_restores_the_limit_when_op_panics() {
    let armed = Cell::new(0);
    let got = catch_unwind(AssertUnwindSafe(|| {
        refusing(|| -> Result<()> {
            armed.set(LIMIT.get());
            resume_unwind(Box::new("op panics"))
        })
    }));
    let restored = LIMIT.replace(usize::MAX);
    assert!(got.is_err(), "expected op to panic, observed {got:?}");
    assert_eq!(
        (armed.get(), restored),
        (REFUSED * size_of::<Exact>(), usize::MAX),
        "expected the limit armed during op and usize::MAX after its panic, observed on the left"
    );
}

#[test]
fn marginal_fst_reserves_no_terms() -> Result<()> {
    let (one, wide) = (FinObj::new(1), FinObj::new(REFUSED));
    let joint = point_mass(one.tensor(&wide)?)?;
    let expected = point_mass(one.clone())?;
    let got = refusing(|| joint.marginal_fst(&one, &wide));
    assert!(
        got.as_ref().is_ok_and(|kernel| *kernel == expected),
        "marginal_fst summing {REFUSED} terms: expected {expected:?}, observed {got:?}"
    );
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
