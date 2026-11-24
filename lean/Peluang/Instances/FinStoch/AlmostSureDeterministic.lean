/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.AlmostSure.Deterministic
public import Peluang.Instances.FinStoch.AlmostSure
public import Peluang.Instances.FinStoch.Deterministic
import Mathlib.Tactic.NormNum

/-!
# Almost surely deterministic morphisms in `FinStoch`

## Main definitions

* `FinStoch.halfDet` - the morphism `boolObj ⟶ boolObj` sending `true` to `true` and `false` to
  the distribution with mass `1/2` at each point.

## Main results

* `FinStoch.isAlmostSurelyDeterministic_iff` - `f : X ⟶ Y` is `p`-almost surely deterministic
  iff `f.mass x y` is `0` or `1` at every `x` with `p.mass a x ≠ 0` for some `a`.
* `FinStoch.exists_isAlmostSurelyDeterministic_not_deterministic` - almost surely deterministic
  morphisms of `FinStoch` are not all deterministic: some `f : boolObj ⟶ boolObj` is `p`-almost
  surely deterministic for some state `p : 𝟙_ FinStoch ⟶ boolObj` and is not deterministic.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020], Def. 13.11.
-/

@[expose] public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory
open scoped NNRat

namespace FinStoch

/-- In `FinStoch`, `f : X ⟶ Y` is `p`-almost surely deterministic for `p : A ⟶ X` iff
`f.mass x y` is `0` or `1` for every `y` at every `x` with `p.mass a x ≠ 0` for some `a`
(Fritz 2020, Def. 13.11). -/
theorem isAlmostSurelyDeterministic_iff {A X Y : FinStoch} (p : A ⟶ X) (f : X ⟶ Y) :
    IsAlmostSurelyDeterministic p f ↔
      ∀ a x, p.mass a x ≠ 0 → ∀ y, f.mass x y = 0 ∨ f.mass x y = 1 := by
  unfold IsAlmostSurelyDeterministic
  rw [almostSurelyEq_iff]
  have hL (x : X.carrier) (y₁ y₂ : Y.carrier) :
      (f ≫ Δ[Y]).mass x (y₁, y₂) = if y₁ = y₂ then f.mass x y₁ else 0 := by
    have e (y' : Y.carrier) : (((y', y') : (Y ⊗ Y).carrier) = (y₁, y₂)) ↔ y' = y₁ ∧ y' = y₂ :=
      Prod.mk_inj
    rw [copy_eq_ofFun, comp_mass]
    simp only [ofFun_mass, e, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · subst h
      simp
    · apply Finset.sum_eq_zero
      intro y' _
      rw [ite_eq_right]
      rintro ⟨rfl, rfl⟩
      exact h rfl
  have hR (x : X.carrier) (y₁ y₂ : Y.carrier) :
      (Δ[X] ≫ (f ⊗ₘ f)).mass x (y₁, y₂) = f.mass x y₁ * f.mass x y₂ := by
    rw [copy_eq_ofFun, ofFun_comp_mass, tensorHom_mass]
  constructor
  · intro h a x hp y
    have key := h a x hp (y, y)
    rw [hL, hR, ite_eq_left rfl] at key
    exact IsIdempotentElem.iff_eq_zero_or_one.1 key.symm
  · rintro h a x hp ⟨y₁, y₂⟩
    rw [hL, hR]
    split_ifs with e
    · subst e
      rcases h a x hp y₁ with h0 | h1
      · simp [h0]
      · simp [h1]
    · rcases h a x hp y₁ with h0 | h1
      · simp [h0]
      · rcases h a x hp y₂ with h0' | h1'
        · simp [h0']
        · have hle : ∑ z ∈ {y₁, y₂}, f.mass x z ≤ ∑ z, f.mass x z :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          rw [Finset.sum_pair e, f.sum_one, h1, h1'] at hle
          norm_num at hle

/-- The morphism `boolObj ⟶ boolObj` with mass `1` at output `true` and `0` at output `false`
for input `true`, and mass `1/2` at each output for input `false`. -/
def halfDet : boolObj ⟶ boolObj :=
  Hom.mk (fun (x y : Bool) => if x then (if y then 1 else 0) else 1 / 2)
    (show ∀ x : Bool, ∑ y : Bool, (if x then (if y then (1 : ℚ≥0) else 0) else 1 / 2) = 1 from by
      intro x
      rw [Fintype.sum_bool]
      cases x <;> norm_num)

/-- In `FinStoch`, almost surely deterministic morphisms are not all deterministic: some
`f : boolObj ⟶ boolObj` is `p`-almost surely deterministic for some state
`p : 𝟙_ FinStoch ⟶ boolObj` and is not deterministic (Fritz 2020, Def. 13.11). -/
theorem exists_isAlmostSurelyDeterministic_not_deterministic :
    ∃ (p : 𝟙_ FinStoch ⟶ boolObj) (f : boolObj ⟶ boolObj),
      IsAlmostSurelyDeterministic p f ∧ ¬ Deterministic f := by
  refine ⟨Hom.ofFun fun _ => true, halfDet, ?_, fun hd => ?_⟩
  · rw [isAlmostSurelyDeterministic_iff]
    intro a x hp y
    have hx : true = x := eq_of_ofFun_const_mass_ne_zero (X := boolObj) hp
    subst hx
    rcases y with _ | _
    · left
      rfl
    · right
      rfl
  · have key := (deterministic_iff_mass halfDet).1 hd false true
    change (1 / 2 : ℚ≥0) = 0 ∨ (1 / 2 : ℚ≥0) = 1 at key
    norm_num at key

end FinStoch
