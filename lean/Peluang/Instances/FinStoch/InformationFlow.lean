/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Causal
public import Peluang.Instances.FinStoch.BayesianInverse
public import Peluang.Instances.FinStoch.Deterministic
public import Peluang.Positive

/-!
# Information flow axioms in `FinStoch`

## Main definitions

* `FinStoch.instCausalCategory` - `FinStoch` is a causal Markov category.

## Main results

* `FinStoch.exists_deterministic_comp_not_deterministic` - in `FinStoch`, some composite `f ≫ g`
  is deterministic with `f` not deterministic.
* `FinStoch.exists_almostSurelyEq_comp_ne` - in `FinStoch`, some `h₁ h₂ : X ⟶ Y` are
  `(f ≫ g)`-almost surely equal and distinct.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020], Def. 11.22, Def. 11.31 and Prop. 11.34.
-/

public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory
open scoped NNRat

namespace FinStoch

/-- `FinStoch` is a causal Markov category, with the Markov category structure
`FinStoch.instMarkovCategory` (Fritz 2020, Prop. 11.34 and Example 11.6). -/
instance instCausalCategory : CausalCategory FinStoch :=
  CausalCategory.ofHasConditionals

/-- In `FinStoch`, some `f : X ⟶ Y` and `g : Y ⟶ Z` have `f ≫ g` deterministic and `f` not
deterministic (Fritz 2020, Def. 11.22). -/
theorem exists_deterministic_comp_not_deterministic :
    ∃ (X Y Z : FinStoch) (f : X ⟶ Y) (g : Y ⟶ Z), Deterministic (f ≫ g) ∧ ¬ Deterministic f := by
  refine ⟨𝟙_ FinStoch, boolObj, 𝟙_ FinStoch, bernoulli, ε[boolObj], ?_,
    not_deterministic_bernoulli⟩
  have e : bernoulli ≫ ε[boolObj] = 𝟙 (𝟙_ FinStoch) := Subsingleton.elim _ _
  rw [e]
  infer_instance

/-- In `FinStoch`, some `f : A ⟶ W`, `g : W ⟶ X` and `h₁ h₂ : X ⟶ Y` have `h₁` and `h₂`
`(f ≫ g)`-almost surely equal and `h₁ ≠ h₂` (Fritz 2020, Def. 11.31). -/
theorem exists_almostSurelyEq_comp_ne :
    ∃ (A W X Y : FinStoch) (f : A ⟶ W) (g : W ⟶ X) (h₁ h₂ : X ⟶ Y),
      AlmostSurelyEq (f ≫ g) h₁ h₂ ∧ h₁ ≠ h₂ := by
  refine ⟨𝟙_ FinStoch, boolObj, boolObj, boolObj, Hom.ofFun fun _ => true, 𝟙 boolObj,
    𝟙 boolObj, Hom.ofFun fun _ => true, ?_, fun h => ?_⟩
  · exact (isBayesianInverse_id _).unique_as
      (isBayesianInverse_id_ofFun_const (X := boolObj) true)
  · have key := congrArg (fun k : boolObj ⟶ boolObj => k.mass false false) h
    change (1 : ℚ≥0) = 0 at key
    exact one_ne_zero key

end FinStoch
