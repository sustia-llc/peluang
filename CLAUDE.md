# CLAUDE.md

`peluang` is a library-first crate (`src/lib.rs`) implementing finite
categorical probability — Markov-category structure on finite stochastic
kernels — beside a Lean 4 library under `lean/` that proves the statements
the crate's witness tests pin. `THEOREM_MAP.md` is the bridge.

## Build & Test

- Rust gates, each in its own shell call with output to a file:
  `cargo metadata --locked`, `cargo fmt --all --check`,
  `cargo clippy --all-targets -- -D warnings` (also with
  `--features f64-prob`), `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps`,
  ``rg -n '^\s*(///|//!).*`{3}' src/`` (must print nothing),
  `cargo nextest run`, `cargo nextest run --features f64-prob`.
- Bridge gate: `python3 -I scripts/test_check_theorem_map.py`, then
  `python3 -I scripts/check_theorem_map.py`.
- Lean gates (from Phase 1b): `lake -d lean exe cache get` (fail closed),
  `lake -d lean build` (warning-free), the `sorry`/`axiom` greps, the
  `#print axioms` probe with allowlist `{propext, Classical.choice,
  Quot.sound}`.
- Witness tests compile only in the exact lane
  (`#[cfg(not(feature = "f64-prob"))]`); the `f64-prob` lane runs law tests
  with declared tolerances only.

## Lifecycle of a proof + witness change

1. Lean statement and proof under `lean/Peluang/`.
2. A `THEOREM_MAP.md` row: fully qualified Lean id → `tests/formalization_lean/<file>.rs::<fn>` → anchor.
3. The Rust test carrying `/// THEOREM_MAP: <id>` directly above `#[test]`;
   a.s.-equality theorems compare with `as_equal`, equalities with `==`.
4. Falsify the witness: perturb the engine, see the test fail with observed vs
   expected in the message, restore.
5. `scripts/check_theorem_map.py` green.

## Conventions

- Library code returns `crate::error::Error` (`thiserror`); `anyhow` only in
  examples and tests. No `unwrap()` in `src/`; `expect("invariant: …")` only
  where a precondition makes the other branch unreachable.
- No code blocks in docstrings while the repo is private (`[lib] doctest =
  false`); usage lives in `examples/` and `tests/`.
- Lean/Mathlib move together as a pair, pinned in `lean/lean-toolchain`,
  `lean/lakefile.lean` and `lean/lake-manifest.json`; never `lake update`.
- Anchors cite Fritz 2020 (arXiv:1908.07021) by definition/theorem number.
- PR per phase; tags `vX.Y.Z` are pins; `CHANGELOG.md` follows Keep a
  Changelog.

## Gotchas (do not regress)

None recorded yet.
