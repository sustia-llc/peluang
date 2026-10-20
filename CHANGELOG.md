# Changelog

All notable changes to this project are documented in this file. The format
follows [Keep a Changelog 1.1.0](https://keepachangelog.com/en/1.1.0/); the
git tag is the authoritative pin.

## [Unreleased]

### Added

- Features `parallel` (`rayon-cond`) and `async` (`tokio-rayon`), both off
  by default.
- `prob::sum` and `prob::PAR_THRESHOLD`; `prob::sum_with` under `parallel`.
- `exec::Executor` (`new`, `with_num_threads`, `run`) under `async`;
  `Error::ThreadPool`.
- CI: clippy and nextest over the feature matrix; `wasm-check` job
  (`wasm32-wasip1`, `wasm32-wasip1-threads`, `wasm32-unknown-unknown`,
  `cargo check --lib`).

### Changed

- `Prob` requires `Send + Sync`.
- Rust 1.99.1.

## [0.1.0] - 2026-10-17

### Added

- Crate scaffold: `error.rs` (`thiserror` enum, `Result<T>`), `prob.rs`
  (`Prob` trait, exact `Ratio<BigInt>` carrier, `f64` behind `f64-prob`,
  `verify_prob_axioms`), `tests/canonical.rs`.
- `THEOREM_MAP.md` schema and `scripts/check_theorem_map.py`.
- CI: `rust.yml`, `theorem-map.yml`.
- Lake project `lean/` pinned to `leanprover/lean4:v4.35.0` + Mathlib
  `v4.35.0`; root `Peluang.lean` imports
  `Mathlib.CategoryTheory.MarkovCategory.Basic` and
  `Mathlib.Probability.Kernel.Category.Stoch`.
- `scripts/print_axioms.py` (axioms of every constant in `Peluang.*`
  modules, allowlist `propext`, `Classical.choice`, `Quot.sound`; orphan
  files; scanned theorem names against the environment's source theorems;
  refuses a stale build)
  with `scripts/test_print_axioms.py` and the end-to-end
  `scripts/probe_selftest.py`.
- `scripts/check_lean_source.py` (`sorry`/`admit`/`axiom` scan outside
  comments and literals) with `scripts/test_check_lean_source.py`.
- CI: `lean.yml` (pinned elan, fail-closed cache fetch checked with
  `lake build --no-build Mathlib`, cached `~/.elan` and
  `lean/.lake/packages`, warning-free build, axioms probe and its
  self-test); `theorem-map.yml` runs the source scan, the THEOREM_MAP check
  and all script tests.
- `CLAUDE.md` (build and gate commands, gotchas), `README.md`, `LICENSE`
  (MIT), `THIRD-PARTY.md`, `rust-toolchain.toml`.

[Unreleased]: https://github.com/sustia-llc/peluang/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/sustia-llc/peluang/releases/tag/v0.1.0
