/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Instances.FinStoch.AlmostSure
public import Peluang.Instances.FinStoch.Deterministic
public import Peluang.Instances.FinStoch.InformationFlow
public import Peluang.ProbStoch.Basic

/-!
# The category of probability spaces of `FinStoch`

## Main results

* `FinStoch.exists_ne_probStoch_map_eq` - some distinct morphisms `f g : X ⟶ Y` of
  `Under (𝟙_ FinStoch)` have the same image under `Quotient.functor (probStochRel FinStoch)`.
* `FinStoch.exists_probStoch_map_ne` - some morphisms `f g : X ⟶ Y` of `Under (𝟙_ FinStoch)`
  have distinct images under `Quotient.functor (probStochRel FinStoch)`.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020], Def. 13.8.
-/

public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory
open scoped NNRat

namespace FinStoch

/-- Some objects `X Y` of `Under (𝟙_ FinStoch)` and morphisms `f g : X ⟶ Y` have `f ≠ g` and
the same image under `Quotient.functor (probStochRel FinStoch)`, the functor to the quotient of
Fritz 2020, Def. 13.8. -/
theorem exists_ne_probStoch_map_eq :
    ∃ (X Y : Under (𝟙_ FinStoch)) (f g : X ⟶ Y), f ≠ g ∧
      (Quotient.functor (probStochRel FinStoch)).map f =
        (Quotient.functor (probStochRel FinStoch)).map g := by
  let p : 𝟙_ FinStoch ⟶ boolObj := Hom.ofFun fun _ => true
  let k : boolObj ⟶ boolObj := Hom.ofFun fun _ => true
  have hk : p ≫ k = p := ofFun_comp _ _
  refine ⟨Under.mk p, Under.mk p, 𝟙 _, Under.homMk k hk, fun h => ?_, ?_⟩
  · have key := congrArg (fun t : Under.mk p ⟶ Under.mk p => t.right.mass false false) h
    change (1 : ℚ≥0) = 0 at key
    exact one_ne_zero key
  · rw [ProbStoch.functor_map_eq_iff]
    change AlmostSurelyEq p (𝟙 boolObj) k
    rw [almostSurelyEq_iff]
    intro a x hp y
    have hx : true = x := eq_of_ofFun_const_mass_ne_zero (X := boolObj) hp
    subst hx
    rfl

/-- Some objects `X Y` of `Under (𝟙_ FinStoch)` and morphisms `f g : X ⟶ Y` have distinct images
under `Quotient.functor (probStochRel FinStoch)`, the functor to the quotient of Fritz 2020,
Def. 13.8. -/
theorem exists_probStoch_map_ne :
    ∃ (X Y : Under (𝟙_ FinStoch)) (f g : X ⟶ Y),
      (Quotient.functor (probStochRel FinStoch)).map f ≠
        (Quotient.functor (probStochRel FinStoch)).map g := by
  let k : boolObj ⟶ boolObj := Hom.ofFun (fun b : Bool => !b)
  have aux : ∀ y : Bool, (∑ b : Bool, (1 / 2 : ℚ≥0) * (if (!b) = y then 1 else 0)) = 1 / 2 := by
    intro y
    cases y <;> simp
  have hk : bernoulli ≫ k = bernoulli := hom_ext fun _ y => aux y
  refine ⟨Under.mk bernoulli, Under.mk bernoulli, 𝟙 _, Under.homMk k hk, fun h => ?_⟩
  rw [ProbStoch.functor_map_eq_iff] at h
  have h' : AlmostSurelyEq bernoulli (𝟙 boolObj) k := h
  rw [almostSurelyEq_iff] at h'
  have key := h' PUnit.unit true (by change (1 / 2 : ℚ≥0) ≠ 0; norm_num) true
  change (1 : ℚ≥0) = 0 at key
  exact one_ne_zero key

end FinStoch
