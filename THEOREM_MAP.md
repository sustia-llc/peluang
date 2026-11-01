# THEOREM_MAP

One row per Lean theorem under `lean/Peluang/`: the fully qualified Lean id,
the Rust witness test, and the anchor. Lean proves the universal statement;
the Rust test pins the engine at worked examples. Each row pins an abstract
statement, and Phase 3 proves its FinStoch instance.
`scripts/check_theorem_map.py` enforces: every `theorem` or `lemma`
under `lean/Peluang/` has a row whose test exists (exactly one `#[test]` under
`tests/formalization_lean/` carrying `/// THEOREM_MAP: <id>`), or an opt-out
comment `-- WITNESS: none (<reason>)` separated from the declaration only by
blank lines, comments, docstrings and attributes.

Comparison rule: a theorem stated up to almost-sure equality is witnessed with
`as_equal`; an equality theorem with `==` on the exact carrier. Witness tests
compile only in the exact lane (`#[cfg(not(feature = "f64-prob"))]`). Rows for
Mathlib-owned theorems are prefixed `mathlib:` and are optional.

Anchor format: `Fritz 2020 Def./Prop./Thm./Lemma/Remark/Notation N.M`
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
