/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Peluang.Conditional
public import Peluang.Instances.FinStoch.Deterministic
public import Peluang.Instances.FinStoch.Markov

/-!
# Conditionals in `FinStoch`

## Main definitions

* `FinStoch.cond` - the conditional of `f : A ⟶ X ⊗ Y` on `X`, with the uniform distribution
  on the rows `(x, a)` where `f` gives `x` mass zero.

## Main results

* `FinStoch.marginalFst_mass` - the entries of the first marginal of `f : A ⟶ X ⊗ Y`.
* `FinStoch.isConditional_cond` - `cond f` is a conditional of `f` on `X`.
* `FinStoch.instHasConditionals` - `FinStoch` has conditionals.
* `FinStoch.isConditional_not_unique` - conditionals in `FinStoch` are not unique: some
  `f : 𝟙_ FinStoch ⟶ boolObj ⊗ boolObj` has two distinct conditionals.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020], Notation 2.8, Def. 11.5, Example 11.6,
  Prop. 11.15.
-/

@[expose] public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory
open scoped NNRat

namespace FinStoch

variable {A X Y : FinStoch}

/-- For `f : A ⟶ X ⊗ Y`, the entry of the first marginal of `f` at input `a` and output `x` is
`∑ y, f.mass a (x, y)` (Fritz 2020, Notation 2.8). -/
theorem marginalFst_mass (f : A ⟶ X ⊗ Y) (a x) :
    (marginalFst f).mass a x = ∑ y, f.mass a (x, y) := by
  simp only [marginalFst, discard_eq_ofFun, whiskerLeft_ofFun, rightUnitor_hom_eq_ofFun,
    ofFun_comp, comp_mass, ofFun_mass, Function.comp_apply, Prod.map_fst, id_eq, mul_ite, mul_one,
    mul_zero, sum_tensor]
  rw [Finset.sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- For `f : A ⟶ X ⊗ Y`, the conditional of `f` on `X`, with inputs ordered `X ⊗ A`: the entry
at input `(x, a)` and output `y` is `f.mass a (x, y) / ∑ y', f.mass a (x, y')` when
`∑ y', f.mass a (x, y') ≠ 0`, and `1 / |Y|` otherwise (Fritz 2020, Example 11.6). -/
def cond (f : A ⟶ X ⊗ Y) : X ⊗ A ⟶ Y where
  mass p y :=
    if ∑ y', f.mass p.2 (p.1, y') = 0 then (Fintype.card Y.carrier : ℚ≥0)⁻¹
    else f.mass p.2 (p.1, y) / ∑ y', f.mass p.2 (p.1, y')
  sum_one p := by
    split_ifs with h
    · have hY : Fintype.card Y.carrier ≠ 0 := by
        intro h0
        have hE : IsEmpty Y.carrier := Fintype.card_eq_zero_iff.mp h0
        have := f.sum_one p.2
        rw [sum_tensor] at this
        simp at this
      have hY' : (Fintype.card Y.carrier : ℚ≥0) ≠ 0 := by exact_mod_cast hY
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hY']
    · rw [← Finset.sum_div, div_self h]

-- WITNESS: none (entry step; witnessed through isConditional_cond)
/-- For `m : A ⟶ X` and `g : X ⊗ A ⟶ Y`, the entry of
`Δ[A] ≫ (m ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ g)` at input `a` and output `(x, y)` is
`m.mass a x * g.mass (x, a) y` (Fritz 2020, Def. 11.5). -/
theorem conditional_form_mass (m : A ⟶ X) (g : X ⊗ A ⟶ Y) (a x y) :
    (Δ[A] ≫ (m ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ g)).mass a (x, y) =
      m.mass a x * g.mass (x, a) y := by
  have h1 : (Δ[X] ▷ A) ≫ (α_ X X A).hom =
      Hom.ofFun (fun p : X.carrier × A.carrier => (p.1, p.1, p.2)) := by
    rw [copy_eq_ofFun, whiskerRight_ofFun, associator_hom_eq_ofFun, ofFun_comp]
    rfl
  rw [reassoc_of% h1, copy_eq_ofFun, ofFun_comp_mass, comp_mass]
  simp only [ofFun_comp_mass, sum_tensor]
  change ∑ x₁, ∑ a₁, (m.mass a x₁ * (if a = a₁ then 1 else 0)) *
      ((if x₁ = x then 1 else 0) * g.mass (x₁, a₁) y) = _
  simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul]
  rw [Fintype.sum_eq_single x (fun b hb => by simp [hb])]
  simp

/-- For `f : A ⟶ X ⊗ Y`, `cond f` is a conditional of `f` on `X` (Fritz 2020, Def. 11.5,
Example 11.6). -/
theorem isConditional_cond (f : A ⟶ X ⊗ Y) : IsConditional f (cond f) := by
  unfold IsConditional
  ext a ⟨x, y⟩ : 1
  rw [conditional_form_mass, marginalFst_mass]
  simp only [cond]
  split_ifs with h
  · have := (Finset.sum_eq_zero_iff.mp h) y (Finset.mem_univ _)
    rw [h, zero_mul]
    exact this
  · exact (mul_div_cancel₀ _ h).symm

/-- `FinStoch` has conditionals, given by `cond` (Fritz 2020, Example 11.6). -/
instance : HasConditionals FinStoch := ⟨fun f => ⟨cond f, isConditional_cond f⟩⟩

/-- In `FinStoch`, conditionals are not unique: some `f : 𝟙_ FinStoch ⟶ boolObj ⊗ boolObj` has two
distinct conditionals on `boolObj` (Fritz 2020, Prop. 11.15). -/
theorem isConditional_not_unique :
    ∃ (f : 𝟙_ FinStoch ⟶ boolObj ⊗ boolObj) (g₁ g₂ : boolObj ⊗ 𝟙_ FinStoch ⟶ boolObj),
      IsConditional f g₁ ∧ IsConditional f g₂ ∧ g₁ ≠ g₂ := by
  refine ⟨Hom.ofFun fun _ => (true, true), cond _, Hom.ofFun fun _ => true,
    isConditional_cond _, ?_, fun h => ?_⟩
  · unfold IsConditional
    ext a ⟨x, y⟩ : 1
    rw [conditional_form_mass, marginalFst_mass]
    simp only [ofFun_mass]
    cases x <;> cases y <;> erw [Fintype.sum_bool] <;> simp +decide [boolObj]
  · have := congrArg (fun g : boolObj ⊗ 𝟙_ FinStoch ⟶ boolObj => g.mass (false, PUnit.unit) true) h
    simp only [cond, ofFun_mass] at this
    erw [Fintype.sum_bool] at this
    simp +decide [boolObj] at this

end FinStoch
