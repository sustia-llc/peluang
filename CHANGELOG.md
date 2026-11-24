# Changelog

All notable changes to this project are documented in this file. The format
follows [Keep a Changelog 1.1.0](https://keepachangelog.com/en/1.1.0/); the
git tag is the authoritative pin.

## [Unreleased]

## [0.5.3] - 2026-11-24

### Added

- `lean/Peluang/Causal.lean`: the class `CausalCategory`, which extends
  `MarkovCategory` with the causality axiom (Fritz 2020 Def. 11.31). The file
  adds `CausalCategory.causal_eq`, `AlmostSurelyEq.of_comp`,
  `IsAlmostSurelyDeterministic.comp` (Remark 13.14),
  `almostSurelyEq_copy_whiskerRight_of_hasConditionals` and the `abbrev`
  `CausalCategory.ofHasConditionals` (Prop. 11.34). Its helpers are
  `AlmostSurelyEq.comp_eq_comp`, `AlmostSurelyEq.precomp` and
  `copy_comp_fst_tensorHom_snd`.
- `lean/Peluang/Positive.lean`: the class `RelativelyPositiveCategory`
  (Fritz 2020 Def. 13.16; arXiv:2211.02507, equation (78)). The file adds the
  instances `instRelativelyPositiveCategoryOfCausalCategory` and
  `instPositiveCategoryOfRelativelyPositiveCategory`,
  `copy_comp_natural_of_relativelyPositive` and
  `IsAlmostSurelyDeterministic.of_comp` (Remark 13.17 (b)). Its helpers are
  `AlmostSurelyEq.copy_comp_tensorHom`, `AlmostSurelyEq.copy_comp_tensorHom'`,
  `almostSurelyEq_copy_fst_snd`, `copy_comp_whiskerRight_comp_whiskerLeft` and
  `copy_comp_copy_tensorHom_tensorHom`.
- `lean/Peluang/Markov/Fox.lean`: the definitions
  `cartesianMonoidalCategoryOfDeterministic` (Heunen–Vicary Theorem 4.28) and
  `cartesianMonoidalCategoryDeterministic` (Fritz 2020 Remark 10.13), and the
  helper `eq_copy_comp_tensorHom_of_deterministic`.
- `lean/Peluang/Instances/FinStoch/InformationFlow.lean`:
  `FinStoch.instCausalCategory`,
  `exists_deterministic_comp_not_deterministic` and
  `exists_almostSurelyEq_comp_ne`.
- `information_flow::copy_then`, `information_flow::copy_comp_natural` and
  `information_flow::copy_comp_natural_as`.
- `tests/formalization_lean/information_flow_tests.rs`: 17 tests, 9 of them
  with a `THEOREM_MAP` tag. `THEOREM_MAP.md` goes from 67 to 76 rows. One new
  row has the `mathlib:` prefix.

### Changed

- `docs/diagrams/lean-1-classes.svg`: the diagram shows `CausalCategory` and
  `RelativelyPositiveCategory`.

## [0.5.2] - 2026-11-24

### Added

- `lean/Peluang/BayesianInverse.lean`: `IsBayesianInverse p f g` for
  `p : A ⟶ X` in a copy-discard category (Fritz 2020 Remark 13.10, equation
  (13.2)). The file adds `unique_as`, `isBayesianInverse_id`, `comp`,
  `congr`, `tensor`, `isBayesianInverse_iff_isConditional` and
  `exists_isBayesianInverse`. In a Markov category, it adds `comp_eq` and
  `symm`. Its helpers are `copy_comp_whiskerLeft_eq`,
  `copy_comp_whiskerRight_eq` and `marginalFst_comp_copy_whiskerRight`.
- `lean/Peluang/AlmostSure/Deterministic.lean`:
  `IsAlmostSurelyDeterministic p f` (Def. 13.11). The file adds
  `isAlmostSurelyDeterministic_of_deterministic`, `congr` (Lemma 13.12),
  `comp_deterministic` and the helper `copy_comp_copy_tensorHom_whiskerRight`.
- `lean/Peluang/Instances/FinStoch/BayesianInverse.lean`: `FinStoch.bayesInv`,
  `isBayesianInverse_bayesInv`, `isBayesianInverse_not_unique` and the helper
  `isBayesianInverse_id_ofFun_const`.
- `lean/Peluang/Instances/FinStoch/AlmostSureDeterministic.lean`:
  `isAlmostSurelyDeterministic_iff`,
  `exists_isAlmostSurelyDeterministic_not_deterministic` and `halfDet`.
- `lean/Peluang/Instances/FinStoch/Basic.lean`:
  `eq_of_ofFun_const_mass_ne_zero`.
- `bayes::bayesian_inverse`, `bayes::is_bayesian_inverse` and
  `deterministic::is_as_deterministic`.
- `Error::NotAState`: `bayes::bayesian_inverse` returns it for a `p` whose
  domain is not the unit object.
- `tests/formalization_lean/bayes_tests.rs`: 15 witness tests. `THEOREM_MAP.md`
  goes from 52 to 67 rows.

### Changed

- The Rust channel moves from `1.99.1` to `1.100.0`: `rust-toolchain.toml`,
  `rust-version` in `Cargo.toml`, and both jobs of
  `.github/workflows/rust.yml`.

## [0.5.1] - 2026-11-23

### Changed

- The Lean pin moves to `leanprover/lean4:v4.36.0` and Mathlib `v4.36.0`
  (rev `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`).
- `docs/diagrams/lean-1-classes.svg`: the description names
  `CopyDiscardCategory` as the hub. The file drops an unused style block and
  two unused markers.

## [0.5.0] - 2026-11-15

### Added

- `examples/weather_sprinkler.rs`: the running example composed and
  marginalized through the public API, and a README Examples section.
- `scripts/print_axioms.py` fails when the Lean id of a `THEOREM_MAP.md` row
  without the `mathlib:` prefix is not a constant of a `Peluang` /
  `Peluang.*` module.
- `scripts/check_theorem_map.py` fails when a `[[test]]` target with
  `required-features` holds a placed witness tag.
- `lean/PeluangTest/Markov/Derived.lean`: the generic `marginalFst` case at
  a nested tensor codomain `X ⊗ (Y₁ ⊗ Y₂)`.
- Pool tests: an `Exact` sum and compose inside `Executor::run`, and a sum
  at `PAR_THRESHOLD` on a 1-thread executor.
- Law tests: the associator law at cards `(2, 3, 4)`, and the `copy` and
  `del` laws at `FinObj::unit()`.
- `tests/too_large.rs`: the refused codomain reservation of
  `Tensor::tensor`.
- Witness test: same support with different weights at a reached input is
  not almost surely equal.
- Fixture tests: on an engine error, the assert helpers name the call and
  the expected value.
- `tests/formalization_lean/conditional_tests.rs`: `s_with_column` returns
  an error on an index outside the domain.
- Script tests: `#[path]` and `mod` inside an inline `mod` block resolve at
  the locations that rustc accepts; `print_axioms.py` reports a map with no
  `| Lean id` header.

### Changed

- Breaking: `Error` is `#[non_exhaustive]`. A downstream `match` on it
  needs a wildcard arm.
- `Kernel::approx_eq` returns `false` when the data lengths differ.
- The `Executor::run` docstring states that a future dropped before its
  first poll does not run `f`. A future dropped after its first poll
  discards the return value of `f`, and a panic of `f` then reaches only the
  panic hook.
- `Kernel` construction inside the crate checks the data length with
  `debug_assert_eq!`.
- `linter.peluangTest.verbose` turns on only when a top-level `set_option`
  sets it to `true`; `linter.all` does not set it. The `PeluangTest` audit names modules with
  `Lean.moduleNameOfFileName`.
- The CI Lean build step no longer removes `Audit.trace`.
- `docs/diagrams/lean-1-classes.svg`: `HasConditionals`, almost-sure
  equality and the independence definitions build on `CopyDiscardCategory`,
  which is now the hub. The badge counts match the arrows, and the legend
  has no "planned" entry.

## [0.4.2] - 2026-11-14

### Added

- `lean/Peluang/Independence.lean`: `DisplaysIndep` (Fritz 2020 Def. 12.12, in
  the form of Lemma 12.11 (a)), `DisplaysCondIndep` (Def. 12.16) and
  `DisplaysCondIndepState` (Def. 12.1), in a copy-discard category.
- `lean/Peluang/Independence.lean`: in a Markov category, `DisplaysIndep f`
  holds iff `f = Δ[A] ≫ (g ⊗ₘ h)` for some `g`, `h`
  (`MarkovCategory.displaysIndep_iff_exists`, Lemma 12.11), and Def. 12.16 at
  `W = 𝟙_ C` is Def. 12.12 (`MarkovCategory.displaysCondIndep_unit_iff`).
- `lean/Peluang/Independence.lean`: the Café post's D19 in a copy-discard
  category (`displaysIndep_iff_isConditional`). `DisplaysIndep f` holds iff
  `(ε[X] ▷ A) ≫ (λ_ A).hom ≫ marginalSnd f` is a conditional of `f` on `X`.
- `lean/Peluang/Independence.lean`: in a copy-discard category, Def. 12.16 at
  `A = 𝟙_ C` is Def. 12.1 (`displaysCondIndep_iff_state`).
- `lean/Peluang/Instances/FinStoch/Independence.lean`:
  `not_displaysIndep_coin_copy`: the copied fair coin does not display
  independence.
- `src/independence.rs`: `is_independent` and `cond_indep_form`.
- `tests/formalization_lean/independence_tests.rs` with 5 witness tests and
  `THEOREM_MAP.md` rows.

## [0.4.1] - 2026-11-14

### Added

- `lean/Peluang/Conditional.lean`: any two conditionals of `f : A ⟶ X ⊗ Y`
  are almost surely equal relative to `Δ[A] ≫ (marginalFst f ▷ A)`, in a
  copy-discard category (`isConditional_unique_as`). Its case `A = I`,
  `isConditional_unique_as_unit`, states Fritz 2020 Prop. 13.7: any two
  conditionals `X ⟶ Y` of `ψ : I ⟶ X ⊗ Y` are almost surely equal relative
  to the marginal of `ψ`.
- `lean/Peluang/Conditional.lean`: the three rewrite rules of conditionals.
  Nesting (`IsConditional.nest`, Lemma 11.11) and pre-composition by a
  deterministic morphism (`IsConditional.deterministic_comp`, the Café post's
  T16 and Def. 10.1) hold
  in a copy-discard category. Post-composition
  (`MarkovCategory.IsConditional.comp_whiskerLeft`, Lemma 11.12) holds in a
  Markov category.
- `lean/Peluang/Instances/FinStoch/Conditional.lean`:
  `not_isConditional_comp_of_coin`: pre-composition by the fair coin does not
  preserve a conditional.
- `tests/formalization_lean/conditional_rewrite_tests.rs` with 6 witness tests
  and `THEOREM_MAP.md` rows.

## [0.4.0] - 2026-11-13

### Added

- `lean/Peluang/AlmostSure.lean`: almost-sure equality in a copy-discard
  category (Fritz 2020 Def. 13.1), its equivalence relation, Lemma 13.4 and
  Lemma 13.5.
- `lean/Peluang/Conditional.lean`: `IsConditional` (Def. 11.5, input order
  `X ⊗ A`) and the class `HasConditionals`.
- `lean/Peluang/Instances/FinStoch/AlmostSure.lean`: almost-sure equality in
  FinStoch is equality of the rows that `p` reaches (Example 13.2).
- `lean/Peluang/Instances/FinStoch/Conditional.lean`: the computable
  conditional `FinStoch.cond`, uniform on rows of zero mass, with
  `isConditional_cond` and `instance : HasConditionals FinStoch`
  (Example 11.6), and `isConditional_not_unique`: one FinStoch morphism has
  two distinct conditionals (Prop. 11.15).
- `almost_sure::as_equal` and `conditional::conditional`.
- `tests/formalization_lean/conditional_tests.rs` with 9 witness tests and
  `THEOREM_MAP.md` rows.

### Changed

- `Error` has the new variants `NotParallel` and `NoUniformWeight`. A
  downstream exhaustive `match` on `Error` no longer compiles.

## [0.3.0] - 2026-11-01

### Added

- `lean/Peluang/Instances/FinStoch/`: the category of finite sets and
  stochastic matrices with entries in `ℚ≥0`, `instance : MarkovCategory
  FinStoch` (Fritz 2020 Example 2.5), the deterministic morphisms as functions
  (Example 10.3), and a Bernoulli state that is not deterministic.
- `tests/laws.rs`: law tests on `proptest` kernels and on each cardinality from
  0 to 4, in the `Exact` lane and under `f64-prob` in the `f64` lane.
- `tests/formalization_lean/finstoch_tests.rs` with 11 witness tests and
  `THEOREM_MAP.md` rows.

### Changed

- The witness tests in `tests/formalization_lean/` and the tests on `Exact`
  weights in `tests/canonical.rs` run in every feature lane, also under
  `f64-prob`. The tests on `Exact` weights in `tests/parallel.rs` run in each
  lane with `parallel`.
- If a `.rs` file under `tests/formalization_lean/` contains `f64-prob` or a
  word that starts with `cfg`, `scripts/check_theorem_map.py` fails.
- Tests pin the input order and the product of `tensor` on `f64` weights, the
  domain factor list of `Tensor::tensor`, and the reset of the test allocator
  limit after a panic.

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

[Unreleased]: https://github.com/sustia-llc/peluang/compare/v0.5.3...HEAD
[0.5.3]: https://github.com/sustia-llc/peluang/compare/v0.5.2...v0.5.3
[0.5.2]: https://github.com/sustia-llc/peluang/compare/v0.5.1...v0.5.2
[0.5.1]: https://github.com/sustia-llc/peluang/compare/v0.5.0...v0.5.1
[0.5.0]: https://github.com/sustia-llc/peluang/compare/v0.4.2...v0.5.0
[0.4.2]: https://github.com/sustia-llc/peluang/compare/v0.4.1...v0.4.2
[0.4.1]: https://github.com/sustia-llc/peluang/compare/v0.4.0...v0.4.1
[0.4.0]: https://github.com/sustia-llc/peluang/compare/v0.3.0...v0.4.0
[0.3.0]: https://github.com/sustia-llc/peluang/compare/v0.2.3...v0.3.0
[0.2.3]: https://github.com/sustia-llc/peluang/compare/v0.2.2...v0.2.3
[0.2.2]: https://github.com/sustia-llc/peluang/compare/v0.2.1...v0.2.2
[0.2.1]: https://github.com/sustia-llc/peluang/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/sustia-llc/peluang/compare/v0.1.1...v0.2.0
[0.1.1]: https://github.com/sustia-llc/peluang/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/sustia-llc/peluang/releases/tag/v0.1.0
