/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Instances.FinStoch.Conditional
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum.Inv
import PeluangLint

/-!
# Tests for `Peluang.Instances.FinStoch.Conditional`

`marginalFst_mass`, `conditional_form_mass` and `isConditional_cond` each applied once, the
instance `HasConditionals FinStoch` found by instance search, the entry `3 / 4` of `cond` on the
joint state of `FinStoch.mk (Fin 2) ⊗ FinStoch.mk (Fin 3)` with rows `(1/10, 1/10, 0)` and
`(0, 1/5, 3/5)`, and the entry `(Fintype.card Bool)⁻¹` of `cond` on a zero-mass row.
-/

public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory
open scoped NNRat

namespace FinStoch

variable {A X Y : FinStoch}

example (f : A ⟶ X ⊗ Y) (a x) : (marginalFst f).mass a x = ∑ y, f.mass a (x, y) :=
  marginalFst_mass f a x

example (m : A ⟶ X) (g : X ⊗ A ⟶ Y) (a x y) :
    (Δ[A] ≫ (m ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ g)).mass a (x, y) =
      m.mass a x * g.mass (x, a) y :=
  conditional_form_mass m g a x y

example (f : A ⟶ X ⊗ Y) : IsConditional f (cond f) :=
  isConditional_cond f

example : HasConditionals FinStoch := inferInstance

example (f : A ⟶ X ⊗ Y) : ∃ g, IsConditional f g :=
  HasConditionals.exists_isConditional f

example :
    (cond (⟨fun _ p => ![![1 / 10, 1 / 10, 0], ![0, 1 / 5, 3 / 5]] p.1 p.2, fun _ => by
        rw [sum_tensor]
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, one_div, Fin.sum_univ_two,
          Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Matrix.cons_val]
        rw [← NNRat.coe_inj]
        push_cast
        norm_num⟩ :
      𝟙_ FinStoch ⟶ FinStoch.mk (Fin 2) ⊗ FinStoch.mk (Fin 3))).mass
        ((1 : Fin 2), PUnit.unit) (2 : Fin 3) = 3 / 4 := by
  simp only [cond, Nat.succ_eq_add_one, Nat.reduceAdd, one_div, Fin.sum_univ_three, Fin.isValue,
    add_eq_zero, Fintype.card_fin, Nat.cast_ofNat, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, inv_eq_zero, OfNat.ofNat_ne_zero, and_false, Matrix.cons_val,
    div_eq_zero_iff, or_self, and_self, ↓reduceIte, zero_add]
  rw [← NNRat.coe_inj]
  push_cast
  norm_num

example :
    (cond (⟨fun _ p => if p.1 then 0 else if p.2 then 1 else 0, fun _ => by
        rw [sum_tensor]
        simp⟩ :
      𝟙_ FinStoch ⟶ FinStoch.mk Bool ⊗ FinStoch.mk Bool)).mass (true, PUnit.unit) false =
      (Fintype.card Bool : ℚ≥0)⁻¹ := by
  simp [cond]

end FinStoch
