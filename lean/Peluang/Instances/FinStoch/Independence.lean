/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Independence
public import Peluang.Instances.FinStoch.Deterministic
public import Peluang.Instances.FinStoch.Markov

/-!
# Independence in `FinStoch`

## Main results

* `FinStoch.not_displaysIndep_coin_copy` - the fair coin `bernoulli` copied does not display
  the independence of `boolObj` and `boolObj` given `𝟙_ FinStoch`.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020], Lemma 12.11, Def. 12.12.
-/

public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory
open scoped NNRat

namespace FinStoch

/-- In `FinStoch`, the fair coin `bernoulli` copied, `bernoulli ≫ Δ[boolObj]`, does not display
`boolObj ⊥ boolObj ‖ 𝟙_ FinStoch` (Fritz 2020, Def. 12.12, Lemma 12.11). -/
theorem not_displaysIndep_coin_copy : ¬ DisplaysIndep (bernoulli ≫ Δ[boolObj]) := by
  intro hc
  unfold DisplaysIndep at hc
  simp only [marginalFst_comp, marginalSnd_comp, marginalFst_copy, marginalSnd_copy,
    Category.comp_id] at hc
  have e := congrArg (fun k => k.mass PUnit.unit (true, false)) hc
  simp only [comp_mass, copy_eq_ofFun, ofFun_mass] at e
  simp [bernoulli, boolObj, Hom.tensor, MonoidalCategoryStruct.tensorHom,
    MonoidalCategoryStruct.tensorObj] at e

end FinStoch
