/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.BayesianInverse
public import Peluang.Instances.FinStoch.AlmostSureDeterministic
public import Peluang.Instances.FinStoch.Conditional

/-!
# Bayesian inverses in `FinStoch`

## Main definitions

* `FinStoch.bayesInv` - for a state `p : 𝟙_ FinStoch ⟶ X` and `f : X ⟶ Y`, the morphism
  `(ρ_ Y).inv ≫ cond (p ≫ Δ[X] ≫ (f ▷ X)) : Y ⟶ X` (Cho–Jacobs 2019, Example 3.8;
  Fritz 2020, Remark 13.10).

## Main results

* `FinStoch.isBayesianInverse_bayesInv` - `bayesInv p f` is a Bayesian inverse of `f` with
  respect to `p`.
* `FinStoch.isBayesianInverse_not_unique` - Bayesian inverses in `FinStoch` are not unique: some
  `f : boolObj ⟶ boolObj` has two distinct Bayesian inverses with respect to some state
  `p : 𝟙_ FinStoch ⟶ boolObj`.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020], Remark 13.10.
* [Cho and Jacobs, *Disintegration and Bayesian inversion via string
  diagrams*][cho_jacobs_2019], Example 3.8.
-/

@[expose] public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory
open scoped NNRat

namespace FinStoch

/-- For a state `p : 𝟙_ FinStoch ⟶ X` and `f : X ⟶ Y`, the morphism
`(ρ_ Y).inv ≫ cond (p ≫ Δ[X] ≫ (f ▷ X)) : Y ⟶ X` (Cho–Jacobs 2019, Example 3.8; Fritz 2020,
Remark 13.10). -/
def bayesInv {X Y : FinStoch} (p : 𝟙_ FinStoch ⟶ X) (f : X ⟶ Y) : Y ⟶ X :=
  (ρ_ Y).inv ≫ cond (p ≫ Δ[X] ≫ (f ▷ X))

/-- For a state `p : 𝟙_ FinStoch ⟶ X` and `f : X ⟶ Y`, `bayesInv p f` is a Bayesian inverse of
`f` with respect to `p` (Cho–Jacobs 2019, Example 3.8; Fritz 2020, Remark 13.10). -/
theorem isBayesianInverse_bayesInv {X Y : FinStoch} (p : 𝟙_ FinStoch ⟶ X) (f : X ⟶ Y) :
    IsBayesianInverse p f (bayesInv p f) := by
  refine (isBayesianInverse_iff_isConditional p f _).2 ?_
  unfold bayesInv
  rw [Iso.hom_inv_id_assoc]
  exact isConditional_cond _

-- WITNESS: none (step of isBayesianInverse_not_unique; witnessed through it)
/-- For `x₀ : X.carrier`, the constant `Hom.ofFun fun _ => x₀ : X ⟶ X` is a Bayesian inverse of
`𝟙 X` with respect to the constant state `Hom.ofFun fun _ => x₀ : 𝟙_ FinStoch ⟶ X`
(Fritz 2020, Remark 13.10). -/
theorem isBayesianInverse_id_ofFun_const {X : FinStoch} (x₀ : X.carrier) :
    IsBayesianInverse (Hom.ofFun (fun _ => x₀) : 𝟙_ FinStoch ⟶ X) (𝟙 X)
      (Hom.ofFun fun _ => x₀) := by
  refine IsBayesianInverse.congr (f₁ := 𝟙 X) (g₁ := 𝟙 X)
    ((almostSurelyEq_equivalence _).refl _) ?_ (isBayesianInverse_id _)
  rw [Category.comp_id, almostSurelyEq_iff]
  intro a x hp y
  have hx : x₀ = x := eq_of_ofFun_const_mass_ne_zero hp
  subst hx
  rw [id_mass, ofFun_mass]

/-- In `FinStoch`, Bayesian inverses are not unique: some `f : boolObj ⟶ boolObj` has two distinct
Bayesian inverses with respect to some state `p : 𝟙_ FinStoch ⟶ boolObj`
(Fritz 2020, Remark 13.10). -/
theorem isBayesianInverse_not_unique :
    ∃ (p : 𝟙_ FinStoch ⟶ boolObj) (f : boolObj ⟶ boolObj) (g₁ g₂ : boolObj ⟶ boolObj),
      IsBayesianInverse p f g₁ ∧ IsBayesianInverse p f g₂ ∧ g₁ ≠ g₂ := by
  refine ⟨Hom.ofFun fun _ => true, 𝟙 boolObj, 𝟙 boolObj, Hom.ofFun fun _ => true,
    isBayesianInverse_id _, isBayesianInverse_id_ofFun_const (X := boolObj) true, fun h => ?_⟩
  have key := congrArg (fun k : boolObj ⟶ boolObj => k.mass false false) h
  change (1 : ℚ≥0) = 0 at key
  exact one_ne_zero key

end FinStoch
