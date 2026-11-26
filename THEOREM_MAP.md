# THEOREM_MAP

One row per Lean theorem under `lean/Peluang/`: the fully qualified Lean id,
the Rust witness test, and the anchor. Lean proves the universal statement.
The Rust test pins the engine at worked examples. `tests/laws.rs` pins identity,
associativity, interchange, naturality of `swap`, of the associator, of both
unitors and of `del` at property-generated inputs. It also tests the `copy` laws,
counit, `copy_tensor` and `discard_tensor` at each cardinality from 0 to 4.
It tests these five laws once at `FinObj::unit()`, the two tensor laws at the
pair of it with itself. It tests naturality of the associator at one fixed
triple of endomorphisms on the cardinalities (2, 3, 4).
`lean/Peluang/Instances/FinStoch/` proves the FinStoch instance of the abstract
statements in the `CategoryTheory.*` rows.
`scripts/check_theorem_map.py` enforces: every `theorem` or `lemma`
under `lean/Peluang/` has a row whose test exists (exactly one `#[test]` under
`tests/formalization_lean/` carrying `/// THEOREM_MAP: <id>`), or an opt-out
comment `-- WITNESS: none (<reason>)` separated from the declaration only by
blank lines, comments, docstrings and attributes. It also fails on a
malformed table line, and when a test target that holds a witness file has
`required-features`, `test = false` or `harness = false`. The module
docstring of the script states the full rule.

Comparison rule: a theorem stated up to almost-sure equality is witnessed with
`as_equal`; an equality theorem with `==` on the exact carrier. Witness tests
use `Exact` weights and run in every feature lane.
If a `.rs` file under `tests/formalization_lean/` contains `f64-prob` or a word
that starts with `cfg`, `scripts/check_theorem_map.py` fails. Rows for Mathlib-owned theorems are
prefixed `mathlib:` and are optional.

Anchor format: `Fritz 2020 Def./Prop./Thm./Lemma/Remark/Notation/Example N.M`
(arXiv:1908.07021), which can carry a part letter, a footnote number or "the
sentence after it", `Cho–Jacobs Example N.M`
(arXiv:1709.00322),
`arXiv:2211.02507 Remark N.M` and/or the
Café post's `D`/`T` id. A row can name an
instance. `scripts/print_axioms.py` fails when the Lean id of a row that is
not prefixed `mathlib:` is not a constant of a `Peluang` / `Peluang.*` module.

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
| CategoryTheory.CopyDiscardCategory.almostSurelyEq_equivalence | tests/formalization_lean/conditional_tests.rs::witness_almost_surely_eq_equivalence | Fritz 2020 Def. 13.1 |
| CategoryTheory.CopyDiscardCategory.AlmostSurelyEq.comp | tests/formalization_lean/conditional_tests.rs::witness_almost_surely_eq_comp | Fritz 2020 Lemma 13.4 |
| CategoryTheory.CopyDiscardCategory.AlmostSurelyEq.copy_tensorHom | tests/formalization_lean/conditional_tests.rs::witness_almost_surely_eq_copy_tensor_hom | Fritz 2020 Lemma 13.5 |
| FinStoch.almostSurelyEq_iff | tests/formalization_lean/conditional_tests.rs::witness_almost_surely_eq_iff | Fritz 2020 Example 13.2 |
| FinStoch.copy_comp_whiskerRight_mass | tests/formalization_lean/conditional_tests.rs::witness_copy_comp_whisker_right_mass | Fritz 2020 Def. 13.1 |
| FinStoch.marginalFst_mass | tests/formalization_lean/conditional_tests.rs::witness_marginal_fst_mass | Fritz 2020 Notation 2.8 |
| FinStoch.isConditional_cond | tests/formalization_lean/conditional_tests.rs::witness_is_conditional_cond | Fritz 2020 Def. 11.5, Example 11.6 |
| FinStoch.instHasConditionals | tests/formalization_lean/conditional_tests.rs::witness_has_conditionals | Fritz 2020 Example 11.6 |
| FinStoch.isConditional_not_unique | tests/formalization_lean/conditional_tests.rs::witness_is_conditional_not_unique | Fritz 2020 Prop. 11.15 |
| CategoryTheory.CopyDiscardCategory.isConditional_unique_as | tests/formalization_lean/conditional_rewrite_tests.rs::witness_is_conditional_unique_as | T13 |
| CategoryTheory.CopyDiscardCategory.isConditional_unique_as_unit | tests/formalization_lean/conditional_rewrite_tests.rs::witness_is_conditional_unique_as_unit | Fritz 2020 Prop. 13.7, T13 |
| CategoryTheory.CopyDiscardCategory.IsConditional.nest | tests/formalization_lean/conditional_rewrite_tests.rs::witness_is_conditional_nest | Fritz 2020 Lemma 11.11, T16 |
| CategoryTheory.MarkovCategory.IsConditional.comp_whiskerLeft | tests/formalization_lean/conditional_rewrite_tests.rs::witness_is_conditional_comp_whisker_left | Fritz 2020 Lemma 11.12, T16 |
| CategoryTheory.CopyDiscardCategory.IsConditional.deterministic_comp | tests/formalization_lean/conditional_rewrite_tests.rs::witness_is_conditional_deterministic_comp | T16; Fritz 2020 Def. 10.1, Def. 11.5 |
| FinStoch.not_isConditional_comp_of_coin | tests/formalization_lean/conditional_rewrite_tests.rs::witness_not_is_conditional_comp_of_coin | T16; Fritz 2020 Def. 10.1 |
| CategoryTheory.MarkovCategory.displaysIndep_iff_exists | tests/formalization_lean/independence_tests.rs::witness_displays_indep_iff_exists | Fritz 2020 Lemma 12.11, T17 |
| CategoryTheory.CopyDiscardCategory.displaysIndep_iff_isConditional | tests/formalization_lean/independence_tests.rs::witness_displays_indep_iff_is_conditional | D19; Fritz 2020 Def. 11.5 |
| CategoryTheory.MarkovCategory.displaysCondIndep_unit_iff | tests/formalization_lean/independence_tests.rs::witness_displays_cond_indep_unit_iff | Fritz 2020 Def. 12.16, Def. 12.12 |
| CategoryTheory.CopyDiscardCategory.displaysCondIndep_iff_state | tests/formalization_lean/independence_tests.rs::witness_displays_cond_indep_iff_state | Fritz 2020 Def. 12.16, Def. 12.1 |
| FinStoch.not_displaysIndep_coin_copy | tests/formalization_lean/independence_tests.rs::witness_not_displays_indep_coin_copy | Fritz 2020 Def. 12.12, Lemma 12.11 |
| CategoryTheory.CopyDiscardCategory.IsBayesianInverse.unique_as | tests/formalization_lean/bayes_tests.rs::witness_is_bayesian_inverse_unique_as | Fritz 2020 Remark 13.10 |
| CategoryTheory.CopyDiscardCategory.isBayesianInverse_id | tests/formalization_lean/bayes_tests.rs::witness_is_bayesian_inverse_id | Fritz 2020 Remark 13.10 |
| CategoryTheory.CopyDiscardCategory.IsBayesianInverse.comp | tests/formalization_lean/bayes_tests.rs::witness_is_bayesian_inverse_comp | Fritz 2020 Remark 13.10 |
| CategoryTheory.CopyDiscardCategory.IsBayesianInverse.congr | tests/formalization_lean/bayes_tests.rs::witness_is_bayesian_inverse_congr | Fritz 2020 Remark 13.10 |
| CategoryTheory.CopyDiscardCategory.isBayesianInverse_iff_isConditional | tests/formalization_lean/bayes_tests.rs::witness_is_bayesian_inverse_iff_is_conditional | Fritz 2020 Remark 13.10, Def. 11.5 |
| CategoryTheory.CopyDiscardCategory.IsBayesianInverse.tensor | tests/formalization_lean/bayes_tests.rs::witness_is_bayesian_inverse_tensor | Fritz 2020 Remark 13.10 |
| CategoryTheory.CopyDiscardCategory.IsBayesianInverse.comp_eq | tests/formalization_lean/bayes_tests.rs::witness_is_bayesian_inverse_comp_eq | Fritz 2020 Remark 13.10 |
| CategoryTheory.CopyDiscardCategory.IsBayesianInverse.symm | tests/formalization_lean/bayes_tests.rs::witness_is_bayesian_inverse_symm | Fritz 2020 Remark 13.10 |
| FinStoch.isBayesianInverse_bayesInv | tests/formalization_lean/bayes_tests.rs::witness_is_bayesian_inverse_bayes_inv | Fritz 2020 Remark 13.10; Cho–Jacobs Example 3.8 |
| FinStoch.isBayesianInverse_not_unique | tests/formalization_lean/bayes_tests.rs::witness_is_bayesian_inverse_not_unique | Fritz 2020 Remark 13.10 |
| CategoryTheory.CopyDiscardCategory.isAlmostSurelyDeterministic_of_deterministic | tests/formalization_lean/bayes_tests.rs::witness_is_almost_surely_deterministic_of_deterministic | Fritz 2020 Def. 13.11, Def. 10.1 |
| CategoryTheory.CopyDiscardCategory.IsAlmostSurelyDeterministic.congr | tests/formalization_lean/bayes_tests.rs::witness_is_almost_surely_deterministic_congr | Fritz 2020 Lemma 13.12 |
| CategoryTheory.CopyDiscardCategory.IsAlmostSurelyDeterministic.comp_deterministic | tests/formalization_lean/bayes_tests.rs::witness_is_almost_surely_deterministic_comp_deterministic | Fritz 2020 Def. 13.11, Def. 10.1 |
| FinStoch.isAlmostSurelyDeterministic_iff | tests/formalization_lean/bayes_tests.rs::witness_is_almost_surely_deterministic_iff | Fritz 2020 Def. 13.11 |
| FinStoch.exists_isAlmostSurelyDeterministic_not_deterministic | tests/formalization_lean/bayes_tests.rs::witness_exists_is_almost_surely_deterministic_not_deterministic | Fritz 2020 Def. 13.11, Def. 10.1 |
| CategoryTheory.CausalCategory.causal_eq | tests/formalization_lean/information_flow_tests.rs::witness_causal_eq | Fritz 2020 Def. 11.31 |
| CategoryTheory.CopyDiscardCategory.almostSurelyEq_copy_whiskerRight_of_hasConditionals | tests/formalization_lean/information_flow_tests.rs::witness_almost_surely_eq_copy_whisker_right_of_has_conditionals | Fritz 2020 Prop. 11.34 |
| CategoryTheory.CopyDiscardCategory.AlmostSurelyEq.of_comp | tests/formalization_lean/information_flow_tests.rs::witness_almost_surely_eq_of_comp | Fritz 2020 Def. 11.31 |
| CategoryTheory.CopyDiscardCategory.IsAlmostSurelyDeterministic.comp | tests/formalization_lean/information_flow_tests.rs::witness_is_almost_surely_deterministic_comp | Fritz 2020 Remark 13.14 |
| CategoryTheory.CopyDiscardCategory.copy_comp_natural_of_relativelyPositive | tests/formalization_lean/information_flow_tests.rs::witness_copy_comp_natural_of_relatively_positive | Fritz 2020 Def. 11.22; arXiv:2211.02507 Remark 2.27 |
| CategoryTheory.CopyDiscardCategory.IsAlmostSurelyDeterministic.of_comp | tests/formalization_lean/information_flow_tests.rs::witness_is_almost_surely_deterministic_of_comp | Fritz 2020 Remark 13.17 (b) |
| FinStoch.exists_deterministic_comp_not_deterministic | tests/formalization_lean/information_flow_tests.rs::witness_exists_deterministic_comp_not_deterministic | Fritz 2020 Def. 11.22 |
| FinStoch.exists_almostSurelyEq_comp_ne | tests/formalization_lean/information_flow_tests.rs::witness_exists_almost_surely_eq_comp_ne | Fritz 2020 Def. 11.31 |
| mathlib:CategoryTheory.PositiveCategory.instDeterministicOfIsIso | tests/formalization_lean/information_flow_tests.rs::mutually_inverse_kernels_are_deterministic | Fritz 2020 Remark 11.28 |
| CategoryTheory.CopyDiscardCategory.AlmostSurelyEq.tensorHom | tests/formalization_lean/prob_space_tests.rs::witness_almost_surely_eq_tensor_hom | Fritz 2020 Lemma 13.5, the sentence after it |
| CategoryTheory.ProbStoch.functor_map_eq_iff | tests/formalization_lean/prob_space_tests.rs::witness_prob_stoch_functor_map_eq_iff | Fritz 2020 Def. 13.8 |
| CategoryTheory.ProbStoch.functor_map_tensorHom | tests/formalization_lean/prob_space_tests.rs::witness_prob_stoch_functor_map_tensor_hom | Fritz 2020 Prop. 13.9 (a) |
| FinStoch.exists_ne_probStoch_map_eq | tests/formalization_lean/prob_space_tests.rs::witness_exists_ne_prob_stoch_map_eq | Fritz 2020 Def. 13.8 |
| FinStoch.exists_probStoch_map_ne | tests/formalization_lean/prob_space_tests.rs::witness_exists_prob_stoch_map_ne | Fritz 2020 Def. 13.8 |
| CategoryTheory.CopyDiscardCategory.IsBayesianInverse.almostSurelyEq_of_almostSurelyEq | tests/formalization_lean/prob_space_tests.rs::witness_is_bayesian_inverse_almost_surely_eq_of_almost_surely_eq | Fritz 2020 Remark 13.10 |
| CategoryTheory.ProbStoch.dagger_map | tests/formalization_lean/prob_space_tests.rs::witness_prob_stoch_dagger_map | Fritz 2020 Remark 13.10 |
| CategoryTheory.ProbStoch.dagger_id | tests/formalization_lean/prob_space_tests.rs::witness_prob_stoch_dagger_id | Fritz 2020 Remark 13.10, footnote 28 |
| CategoryTheory.ProbStoch.dagger_comp | tests/formalization_lean/prob_space_tests.rs::witness_prob_stoch_dagger_comp | Fritz 2020 Remark 13.10, footnote 28 |
| CategoryTheory.ProbStoch.dagger_dagger | tests/formalization_lean/prob_space_tests.rs::witness_prob_stoch_dagger_dagger | Fritz 2020 Remark 13.10, footnote 28 |
| CategoryTheory.ProbStoch.homEquivCoupling_map | tests/formalization_lean/prob_space_tests.rs::witness_prob_stoch_hom_equiv_coupling_map | Fritz 2020 Prop. 13.9 (b) |
| CategoryTheory.MonoidalCategory.tensorRev₃_eq_tensorLeftComm | tests/formalization_lean/reorder_tests.rs::witness_tensor_rev3_eq_tensor_left_comm | Fritz 2020 Lemma 12.5 (a), Prop. 12.17 (a) |
| CategoryTheory.MonoidalCategory.tensorRev₃_hom_naturality | tests/formalization_lean/reorder_tests.rs::witness_tensor_rev3_hom_naturality | Fritz 2020 Lemma 12.5 (a), Prop. 12.17 (a) |
| CategoryTheory.CopyDiscardCategory.isConditionalSnd_iff | tests/formalization_lean/reorder_tests.rs::witness_is_conditional_snd_iff | Fritz 2020 Def. 11.5 |
| CategoryTheory.CopyDiscardCategory.exists_isConditionalSnd | tests/formalization_lean/reorder_tests.rs::witness_exists_is_conditional_snd | Fritz 2020 Def. 11.5 |
| CategoryTheory.CopyDiscardCategory.marginalFst_comp_braiding_hom | tests/formalization_lean/reorder_tests.rs::witness_marginal_fst_comp_braiding_hom | Fritz 2020 Notation 2.8 |
