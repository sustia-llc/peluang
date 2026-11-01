# Changelog

All notable changes to this project are documented in this file. The format
follows [Keep a Changelog 1.1.0](https://keepachangelog.com/en/1.1.0/); the
git tag is the authoritative pin.

## [Unreleased]

## [0.2.3] - 2026-11-01

### Added

- `exec::Executor` implements `Debug`.
- `finset::FinObj`: a finite object as an ordered list of factors, each a
  cardinality with optional labels. `tensor` concatenates the lists, and
  `unit` is the empty list.
- `kernel::Kernel<P>`: a stochastic matrix stored by input. `Kernel::new`
  tests the data length, the sign of each entry and the sum of each column.
- `markov::Compose` and `markov::Tensor`, implemented by `Kernel<P>`, with
  `identity`, `copy`, `del`, `swap`, `associator`, `left_unitor`,
  `right_unitor`, `whisker_left`, `whisker_right`, `marginal_fst` and
  `marginal_snd`.
- `deterministic::is_deterministic`: Fritz 2020 Def. 10.1.
- `error::Error` variants `DataLength`, `NegativeWeight`, `NotNormalized`,
  `NotComposable`, `NotATensor`, `DuplicateLabel`, `TooLarge`, `NotAFunction`.
- `tests/formalization_lean/` with 21 witness tests and `THEOREM_MAP.md` rows.

### Removed

- The 12 `-- WITNESS: none (Phase 2R witness)` opt-outs in
  `lean/Peluang/Markov/Derived.lean`.

### Changed

- `prob::sum`, `prob::sum_with` and the README `parallel` entry state which
  rayon pool a parallel run uses.
- `prob::sum` and `prob::sum_with` state the effect of a parallel run on `f64`
  weights.

## [0.2.2] - 2026-10-25

### Added

- `lean/PeluangLint.lean` (`lean_lib PeluangLint`): command linters that
  run in every `PeluangTest` module that imports the module. A hidden
  constant with an axiom outside `{propext, Classical.choice, Quot.sound}`
  is an error. A hidden constant without an `_example` name component is
  an error. A command that adds a constant to the module is an error. The
  option `linter.peluangTest.verbose` logs each inspected hidden constant.
- `#peluang_test_audit`, run by `lean/PeluangTest/Audit.lean`. Each
  `.lean` file of `PeluangTest` is imported and imports `PeluangLint`
  directly. Each test module holds no constant and has entries only in
  four allowed environment extensions. The modules of the plant list are
  the only exception, and each file under `lean/PeluangTest/Plant/` is a
  listed plant. `Audit.lean` holds only its header, its module docstring
  and one audit command.
- In a `PeluangTest` module outside the plant list of `PeluangLint`,
  `#guard_msgs` and `#guard_panic` are build errors.
- Plants under `lean/PeluangTest/Plant/`: a `sorryAx` example in term form
  and in tactic form, an `#eval`, and a `theorem` in a `module` file and
  in a plain file. Each holds its linter error under `#guard_msgs`.

### Changed

- `scripts/print_axioms.py` reads the axiom allowlist from
  `Peluang.Linter.allowedAxioms` through its probe, which imports
  `PeluangLint`. It requires current builds of `Peluang` and
  `PeluangLint`.
- `scripts/probe_selftest.py` builds `PeluangLint` before it plants its
  module.
- Lean gate 2 removes `Audit.trace` before `lake build` and requires one
  `peluangTest audit:` line in the build log.

### Removed

- `scripts/check_peluangtest.py`, `scripts/test_check_peluangtest.py`,
  `scripts/lean/ExampleCheck.lean` and `scripts/lean/ImportCheck.lean`.

## [0.2.1] - 2026-10-24

### Added

- `scripts/check_peluangtest.py`, with `scripts/lean/ImportCheck.lean` and
  `scripts/lean/ExampleCheck.lean`, checks `lean/PeluangTest` in Lean. An
  import check finds constants and extension entries outside a baseline
  set. A per-file re-elaboration check finds disallowed axioms in
  examples and lakefile options that the file's imports do not register.
  It also counts examples and reports a planted `native_decide` example
  and a planted `theorem` in a `module` file and in a plain file. If the
  lakefile sets `moreLeanArgs`, `weakLeanArgs`, `moreServerOptions` or
  `moreServerArgs`, the check fails.
- `scripts/test_check_peluangtest.py`.
- `scripts/test_probe_selftest.py`: a unit test that pins the build
  target of `scripts/probe_selftest.py`.
- Lean `Peluang.Markov.Derived`: `@[simp]` lemmas
  `CopyDiscardCategory.marginalFst_whiskerRight`, `marginalSnd_whiskerLeft`
  and `MarkovCategory.marginalSnd_whiskerRight`, `marginalFst_whiskerLeft`
  (Fritz 2020 Notation 2.8).

### Changed

- `scripts/check_lean_source.py` no longer scans `lean/PeluangTest` for
  declarations.
- `scripts/check_theorem_map.py` accepts a `/// THEOREM_MAP:` tag only on
  the line directly above `#[test]` or `#[<path>::test]`. Between that
  line and the `fn`, only blank lines, comments other than a tag, and
  single-line attributes are allowed. `#[ignore]`, `#[should_panic]` and a
  `cfg` that enables `f64-prob` are not allowed. Every other tag is
  reported with its file and line.
- Lean `Peluang.Markov.Derived`: `marginalFst_comp`, `marginalSnd_comp`,
  `marginalFst_tensorHom` and `marginalSnd_tensorHom` are `@[simp]`. The
  `_copy_comp_tensorHom` lemmas are no longer `@[simp]`.

## [0.2.0] - 2026-10-20

### Added

- Lean `Peluang.Markov.Derived`: `CopyDiscardCategory.comonObj_tensor`,
  `MarkovCategory.discard_natural_tensor`,
  `MarkovCategory.comp_tensorHom_leftUnitor_hom_eq_discard`;
  `CopyDiscardCategory.marginalFst`/`marginalSnd` with `_comp` and
  `@[simp]` `_copy` lemmas; `MarkovCategory.marginalFst`/`Snd` `_tensorHom`
  and `@[simp]` `_copy_comp_tensorHom` lemmas (Fritz 2020 Notation 2.8).
- Lean `Peluang.Markov.Cartesian`: `MarkovCategory.ofCartesianMonoidalCategory`
  (Remark 2.4).
- Lean `Peluang.Deterministic.Lemmas`: `Deterministic` instances for `Δ`,
  `ε`, `⊗ₘ`, `▷`, `◁`, `α`, `λ`, `ρ`, `β` in any `CopyDiscardCategory`
  (Def. 10.1, Remark 10.2, Lemma 10.12); an `IsComonHom` instance at the
  tensor-product comonoid structure for `α`;
  `Comon.instIsComonHomTensorHom`, `Comon.instIsComonHomWhiskerRight`/`Left`
  for `⊗ₘ`, `▷`, `◁` at any comonoid structures in a braided monoidal
  category; `Deterministic.instIsComonHomOfTensorObjSource`/`…Target`
  (low priority).
- Lean `Peluang.Deterministic.Wide`: `MorphismProperty.deterministic`, its
  braiding and comonoid stability, and
  `WideSubcategory.instMarkovCategory` (Remark 10.13).
- Lean test library `PeluangTest` (a default target of `lean/lakefile.lean`),
  including `PeluangTest/Lint.lean` (`#lint in Peluang`).

### Changed

- `lake build` runs Mathlib's style linters
  (`weak.linter.mathlibStandardSet`, header linter off), whose findings
  are warnings, and `#lint in Peluang`, whose findings are build errors.
- `scripts/print_axioms.py` checks freshness with
  `lake build --no-build Peluang`; `scripts/probe_selftest.py` builds only
  the `Peluang` target, with its fixture and after restoring.
- `scripts/check_lean_source.py` also rejects `native_decide` and any
  standalone `native` word (`decide +native`, `native := true`) anywhere
  under `lean/`, and every declaration other than `example` under
  `lean/PeluangTest`.

## [0.1.1] - 2026-10-20

### Added

- Features `parallel` (`rayon-cond`) and `async` (`tokio-rayon`), both off
  by default.
- `prob::sum` and `prob::PAR_THRESHOLD`; `prob::sum_with` under `parallel`.
- `exec::Executor` (`new`, `with_num_threads`, `run`) under `async`;
  `Error::ThreadPool`.
- CI: clippy and nextest over the feature matrix; `wasm-check` job
  (`wasm32-wasip1`, `wasm32-wasip1-threads`, `wasm32-unknown-unknown`,
  `cargo check --lib`); `cargo tree --duplicates` guard.

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

[Unreleased]: https://github.com/sustia-llc/peluang/compare/v0.2.3...HEAD
[0.2.3]: https://github.com/sustia-llc/peluang/compare/v0.2.2...v0.2.3
[0.2.2]: https://github.com/sustia-llc/peluang/compare/v0.2.1...v0.2.2
[0.2.1]: https://github.com/sustia-llc/peluang/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/sustia-llc/peluang/compare/v0.1.1...v0.2.0
[0.1.1]: https://github.com/sustia-llc/peluang/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/sustia-llc/peluang/releases/tag/v0.1.0
