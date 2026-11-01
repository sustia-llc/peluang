# THEOREM_MAP

One row per Lean theorem under `lean/Peluang/`: the fully qualified Lean id,
the Rust witness test, and the anchor. Lean proves the universal statement.
The Rust test pins the engine at worked examples. `tests/laws.rs` pins identity,
associativity, interchange, naturality of `swap` and of the associator, and
naturality of `del` at property-generated inputs. It also tests the `copy` laws,
counit, `copy_tensor` and `discard_tensor` at each cardinality from 0 to 4.
`lean/Peluang/Instances/FinStoch/` proves the FinStoch instance of the abstract
statements in the `CategoryTheory.*` rows.
`scripts/check_theorem_map.py` enforces: every `theorem` or `lemma`
under `lean/Peluang/` has a row whose test exists (exactly one `#[test]` under
`tests/formalization_lean/` carrying `/// THEOREM_MAP: <id>`), or an opt-out
comment `-- WITNESS: none (<reason>)` separated from the declaration only by
blank lines, comments, docstrings and attributes.

Comparison rule: a theorem stated up to almost-sure equality is witnessed with
`as_equal`; an equality theorem with `==` on the exact carrier. Witness tests
use `Exact` weights and run in every feature lane.
If a `.rs` file under `tests/formalization_lean/` contains `f64-prob` or a word
that starts with `cfg`, `scripts/check_theorem_map.py` fails. Rows for Mathlib-owned theorems are
prefixed `mathlib:` and are optional.

Anchor format: `Fritz 2020 Def./Prop./Thm./Lemma/Remark/Notation/Example N.M`
(arXiv:1908.07021) and/or the Café post's `D`/`T` id. A row can name an
instance, and `check_theorem_map.py` does not test that a row's Lean id names
a declaration.

| Lean id | Rust test | anchor |
|---|---|---|
| CategoryTheory.CopyDiscardCategory.marginalFst_comp | tests/formalization_lean/marginal_tests.rs::witness_marginal_fst_comp | Fritz 2020 Notation 2.8 |
| CategoryTheory.CopyDiscardCategory.marginalSnd_comp | tests/formalization_lean/marginal_tests.rs::witness_marginal_snd_comp | Fritz 2020 Notation 2.8 |
| CategoryTheory.CopyDiscardCategory.marginalFst_copy | tests/formalization_lean/marginal_tests.rs::witness_marginal_fst_copy | Fritz 2020 Notation 2.8, Def. 2.1 |
| CategoryTheory.CopyDiscardCategory.marginalSnd_copy | tests/formalization_lean/marginal_tests.rs::witness_marginal_snd_copy | Fritz 2020 Notation 2.8, Def. 2.1 |
| CategoryTheory.CopyDiscardCategory.marginalFst_whiskerRight | tests/formalization_lean/marginal_tests.rs::witness_marginal_fst_whisker_right | Fritz 2020 Notation 2.8 |
| CategoryTheory.CopyDiscardCategory.marginalSnd_whiskerLeft | tests/formalization_lean/marginal_tests.rs::witness_marginal_snd_whisker_left | Fritz 2020 Notation 2.8 |
| CategoryTheory.MarkovCategory.marginalFst_copy_comp_tensorHom | tests/formalization_lean/marginal_tests.rs::witness_marginal_fst_copy_comp_tensor_hom | Fritz 2020 Notation 2.8 |
| CategoryTheory.MarkovCategory.marginalSnd_copy_comp_tensorHom | tests/formalization_lean/marginal_tests.rs::witness_marginal_snd_copy_comp_tensor_hom | Fritz 2020 Notation 2.8 |
| CategoryTheory.MarkovCategory.marginalFst_tensorHom | tests/formalization_lean/marginal_tests.rs::witness_marginal_fst_tensor_hom | Fritz 2020 Notation 2.8 |
| CategoryTheory.MarkovCategory.marginalSnd_tensorHom | tests/formalization_lean/marginal_tests.rs::witness_marginal_snd_tensor_hom | Fritz 2020 Notation 2.8 |
| CategoryTheory.MarkovCategory.marginalSnd_whiskerRight | tests/formalization_lean/marginal_tests.rs::witness_marginal_snd_whisker_right | Fritz 2020 Notation 2.8 |
| CategoryTheory.MarkovCategory.marginalFst_whiskerLeft | tests/formalization_lean/marginal_tests.rs::witness_marginal_fst_whisker_left | Fritz 2020 Notation 2.8 |
| CategoryTheory.Deterministic.instCopy | tests/formalization_lean/deterministic_tests.rs::witness_inst_copy | Fritz 2020 Remark 10.2 |
| CategoryTheory.Deterministic.instDiscard | tests/formalization_lean/deterministic_tests.rs::witness_inst_discard | Fritz 2020 Remark 10.2 |
| CategoryTheory.Deterministic.instTensorHom | tests/formalization_lean/deterministic_tests.rs::witness_inst_tensor_hom | Fritz 2020 Lemma 10.12 |
| CategoryTheory.Deterministic.instWhiskerRight | tests/formalization_lean/deterministic_tests.rs::witness_inst_whisker_right | Fritz 2020 Lemma 10.12 |
| CategoryTheory.Deterministic.instWhiskerLeft | tests/formalization_lean/deterministic_tests.rs::witness_inst_whisker_left | Fritz 2020 Lemma 10.12 |
| CategoryTheory.Deterministic.instAssociator | tests/formalization_lean/deterministic_tests.rs::witness_inst_associator | Fritz 2020 Lemma 10.12 |
| CategoryTheory.Deterministic.instLeftUnitor | tests/formalization_lean/deterministic_tests.rs::witness_inst_left_unitor | Fritz 2020 Lemma 10.12 |
| CategoryTheory.Deterministic.instRightUnitor | tests/formalization_lean/deterministic_tests.rs::witness_inst_right_unitor | Fritz 2020 Lemma 10.12 |
| CategoryTheory.Deterministic.instBraiding | tests/formalization_lean/deterministic_tests.rs::witness_inst_braiding | Fritz 2020 Lemma 10.12 |
| FinStoch.comp_mass | tests/formalization_lean/finstoch_tests.rs::witness_comp_mass | Fritz 2020 Example 2.5 |
| FinStoch.tensorHom_mass | tests/formalization_lean/finstoch_tests.rs::witness_tensor_hom_mass | Fritz 2020 Example 2.5 |
| FinStoch.ofFun_id | tests/formalization_lean/finstoch_tests.rs::witness_of_fun_id | Fritz 2020 Example 10.3 |
| FinStoch.ofFun_comp | tests/formalization_lean/finstoch_tests.rs::witness_of_fun_comp | Fritz 2020 Example 10.3 |
| FinStoch.copy_eq_ofFun | tests/formalization_lean/finstoch_tests.rs::witness_copy_eq_of_fun | Fritz 2020 Example 2.5 |
| FinStoch.discard_eq_ofFun | tests/formalization_lean/finstoch_tests.rs::witness_discard_eq_of_fun | Fritz 2020 Example 2.5 |
| FinStoch.braiding_eq_ofFun | tests/formalization_lean/finstoch_tests.rs::witness_braiding_eq_of_fun | Fritz 2020 Example 2.5 |
| FinStoch.deterministic_iff_mass | tests/formalization_lean/finstoch_tests.rs::witness_deterministic_iff_mass | Fritz 2020 Example 10.3, T12 |
| FinStoch.deterministic_iff_exists_ofFun | tests/formalization_lean/finstoch_tests.rs::witness_deterministic_iff_exists_of_fun | Fritz 2020 Example 10.3, T12 |
| FinStoch.not_deterministic_bernoulli | tests/formalization_lean/finstoch_tests.rs::witness_not_deterministic_bernoulli | Fritz 2020 Def. 10.1 |
| FinStoch.instMarkovCategory | tests/formalization_lean/finstoch_tests.rs::witness_markov_category | Fritz 2020 Example 2.5, T1 |
