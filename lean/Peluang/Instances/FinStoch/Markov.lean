/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.MarkovCategory.Basic
public import Peluang.Instances.FinStoch.Monoidal

/-!
# The Markov category `FinStoch`

## Main definitions

* `FinStoch.instComonObj`, `FinStoch.instIsCommComonObj` - each object is a commutative comonoid
  under `Hom.ofFun` of the diagonal and of the constant function.
* `FinStoch.instCopyDiscardCategory`, `FinStoch.instMarkovCategory` - `FinStoch` is a Markov
  category.

## Main results

* `FinStoch.copy_eq_ofFun` - `Δ[X]` is `Hom.ofFun` of the diagonal.
* `FinStoch.discard_eq_ofFun` - `ε[X]` is `Hom.ofFun` of the constant function.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020], Example 2.5.
-/

@[expose] public section

open CategoryTheory MonoidalCategory ComonObj

namespace FinStoch

variable {X : FinStoch}

/-- Each object of `FinStoch` is a comonoid with `comul = Hom.ofFun fun x => (x, x)` and
`counit = Hom.ofFun fun _ => PUnit.unit`. -/
instance instComonObj (X : FinStoch) : ComonObj X where
  counit := Hom.ofFun fun _ => PUnit.unit
  comul := Hom.ofFun fun x => (x, x)
  counit_comul := by
    simp only [whiskerRight_ofFun, ofFun_comp]
    rfl
  comul_counit := by
    simp only [whiskerLeft_ofFun, ofFun_comp]
    rfl
  comul_assoc := by
    simp only [whiskerLeft_ofFun, whiskerRight_ofFun, associator_hom_eq_ofFun, ofFun_comp]
    rfl

/-- `Δ[X]` is `Hom.ofFun` of the diagonal `x ↦ (x, x)`. -/
theorem copy_eq_ofFun : Δ[X] = Hom.ofFun fun x => (x, x) :=
  rfl

/-- `ε[X]` is `Hom.ofFun` of the constant function at `PUnit.unit`. -/
theorem discard_eq_ofFun : ε[X] = Hom.ofFun fun _ => PUnit.unit :=
  rfl

/-- The comonoid of each object of `FinStoch` is commutative. -/
instance instIsCommComonObj (X : FinStoch) : IsCommComonObj X where
  comul_comm := by
    simp only [copy_eq_ofFun, braiding_eq_ofFun, ofFun_comp]
    rfl

/-- `FinStoch` is a copy-discard category. -/
instance : CopyDiscardCategory FinStoch where
  copy_tensor X Y := by
    simp only [copy_eq_ofFun, tensorHom_ofFun, tensorμ, associator_hom_eq_ofFun,
      associator_inv_eq_ofFun, braiding_eq_ofFun, whiskerRight_ofFun, whiskerLeft_ofFun, ofFun_comp]
    rfl
  discard_tensor X Y := by
    simp only [discard_eq_ofFun, tensorHom_ofFun, leftUnitor_hom_eq_ofFun, ofFun_comp]
    rfl
  copy_unit := rfl
  discard_unit := by
    rw [discard_eq_ofFun, ← ofFun_id]
    rfl

/-- `FinStoch` is a Markov category. -/
instance : MarkovCategory FinStoch where
  discard_natural {X Y} f := by
    ext x ⟨⟩ : 1
    simp [discard_eq_ofFun, f.sum_one]

end FinStoch
