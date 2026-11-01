/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Deterministic.Lemmas
public import Peluang.Instances.FinStoch.Markov
public import Peluang.Markov.Derived
meta import Peluang.Instances.FinStoch.Markov
import PeluangLint

/-!
# Tests for `Peluang.Instances.FinStoch.Markov`

Instance search for the copy-discard and Markov classes and for the comonoid classes at tensor,
nested tensor and unit objects. The instance that `Δ[X ⊗ Y]` and `ε[X ⊗ Y]` elaborate to, its
relation to `CopyDiscardCategory.comonObj` and `Comon.instComonObjTensorObj`, and `copy_eq_ofFun`
and `discard_eq_ofFun` at tensor objects. The class laws at their `FinStoch` statements, `tensorμ`
as `Hom.ofFun`, instance search for `Deterministic` and `IsComonHom` at tensors, whiskers,
associators and `Δ[X ⊗ Y]`, and values of `Δ[X]` and `ε[X]` in `ℚ≥0` by `#guard`.
-/

public section

open CategoryTheory MonoidalCategory ComonObj
open scoped NNRat

namespace FinStoch

variable {A B X Y Z : FinStoch}

example : CopyDiscardCategory FinStoch := inferInstance

example : MarkovCategory FinStoch := inferInstance

example (X : FinStoch) : ComonObj X := inferInstance

example (X Y : FinStoch) : ComonObj (X ⊗ Y) := inferInstance

example (X Y Z : FinStoch) : ComonObj ((X ⊗ Y) ⊗ Z) := inferInstance

example (X Y Z : FinStoch) : ComonObj (X ⊗ Y ⊗ Z) := inferInstance

example : ComonObj (𝟙_ FinStoch) := inferInstance

example (X : FinStoch) : IsCommComonObj X := inferInstance

example (X Y : FinStoch) : IsCommComonObj (X ⊗ Y) := inferInstance

example (X Y Z : FinStoch) : IsCommComonObj ((X ⊗ Y) ⊗ Z) := inferInstance

example (X Y Z : FinStoch) : IsCommComonObj (X ⊗ Y ⊗ Z) := inferInstance

example : IsCommComonObj (𝟙_ FinStoch) := inferInstance

example : (Δ[X ⊗ Y] : _) = @comul _ _ _ _ (instComonObj (X ⊗ Y)) := by
  with_reducible rfl

example : (ε[X ⊗ Y] : _) = @counit _ _ _ _ (instComonObj (X ⊗ Y)) := by
  with_reducible rfl

example (X : FinStoch) : CopyDiscardCategory.comonObj X = instComonObj X := by
  with_reducible_and_instances rfl

example (X Y : FinStoch) : CopyDiscardCategory.comonObj (X ⊗ Y) = instComonObj (X ⊗ Y) := by
  with_reducible_and_instances rfl

example (X Y : FinStoch) : Comon.instComonObjTensorObj X Y = instComonObj (X ⊗ Y) :=
  CopyDiscardCategory.comonObj_tensor X Y |>.symm

example : True := by
  fail_if_success
    have (X Y : FinStoch) : Comon.instComonObjTensorObj X Y = instComonObj (X ⊗ Y) := rfl
  trivial

example : @comul _ _ _ _ (Comon.instComonObjTensorObj X Y) = Δ[X ⊗ Y] := by
  rw [← CopyDiscardCategory.comonObj_tensor]

example : @counit _ _ _ _ (Comon.instComonObjTensorObj X Y) = ε[X ⊗ Y] := by
  rw [← CopyDiscardCategory.comonObj_tensor]

example : Δ[X ⊗ Y] = Hom.ofFun fun x => (x, x) :=
  copy_eq_ofFun

example : ε[X ⊗ Y] = Hom.ofFun fun _ => PUnit.unit :=
  discard_eq_ofFun

example : Δ[(X ⊗ Y) ⊗ Z] = Hom.ofFun fun x => (x, x) :=
  copy_eq_ofFun

example : ε[(X ⊗ Y) ⊗ Z] = Hom.ofFun fun _ => PUnit.unit :=
  discard_eq_ofFun

example : @comul _ _ _ _ (Comon.instComonObjTensorObj X Y) = Hom.ofFun fun x => (x, x) := by
  rw [← CopyDiscardCategory.comonObj_tensor]
  rfl

example : @counit _ _ _ _ (Comon.instComonObjTensorObj X Y) = Hom.ofFun fun _ => PUnit.unit := by
  rw [← CopyDiscardCategory.comonObj_tensor]
  rfl

example (f : A ⟶ X ⊗ Y) : f ≫ ε[X ⊗ Y] = ε[A] := by
  fail_if_success exact MarkovCategory.discard_natural_tensor f
  exact MarkovCategory.discard_natural f

example : Δ[X ⊗ Y] = (Δ[X] ⊗ₘ Δ[Y]) ≫ tensorμ X X Y Y :=
  CopyDiscardCategory.copy_tensor X Y

example : ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ (λ_ (𝟙_ FinStoch)).hom :=
  CopyDiscardCategory.discard_tensor X Y

example : Δ[𝟙_ FinStoch] = (λ_ (𝟙_ FinStoch)).inv :=
  rfl

example : Δ[𝟙_ FinStoch] = (λ_ (𝟙_ FinStoch)).inv :=
  CopyDiscardCategory.copy_unit

example : ε[𝟙_ FinStoch] = 𝟙 (𝟙_ FinStoch) :=
  CopyDiscardCategory.discard_unit

example (f : X ⟶ Y) : f ≫ ε[Y] = ε[X] :=
  MarkovCategory.discard_natural f

example (f : X ⟶ 𝟙_ FinStoch) : f = ε[X] :=
  MarkovCategory.eq_discard X f

example : tensorμ X X Y Y =
    Hom.ofFun fun p : (X.carrier × X.carrier) × Y.carrier × Y.carrier =>
      ((p.1.1, p.2.1), p.1.2, p.2.2) := by
  simp only [tensorμ, associator_hom_eq_ofFun, associator_inv_eq_ofFun, braiding_eq_ofFun,
    whiskerRight_ofFun, whiskerLeft_ofFun, ofFun_comp]
  rfl

example (f : A ⟶ X ⊗ (Y ⊗ Z)) :
    CopyDiscardCategory.marginalFst f = f ≫ X ◁ ε[Y ⊗ Z] ≫ (ρ_ X).hom :=
  rfl

example (f : X ⟶ Y) (g : A ⟶ B) [Deterministic f] [Deterministic g] :
    Deterministic (f ⊗ₘ g) := inferInstance

example (f : X ⟶ Y) (g : A ⟶ B) [Deterministic f] [Deterministic g] :
    IsComonHom (f ⊗ₘ g) := inferInstance

example (f : X ⟶ Y) (g : A ⟶ B) [IsComonHom f] [IsComonHom g] :
    IsComonHom (f ⊗ₘ g) := inferInstance

example (f : A ⊗ B ⟶ Y) [IsComonHom f] (Z : FinStoch) : Deterministic (f ▷ Z) := inferInstance

example (f : A ⊗ B ⟶ Y) [IsComonHom f] (Z : FinStoch) : IsComonHom (f ▷ Z) := inferInstance

example (X Y Z : FinStoch) : IsComonHom (α_ (X ⊗ Y) Y Z).hom := inferInstance

example (X Y : FinStoch) : IsComonHom Δ[X ⊗ Y] := inferInstance

example (X Y : FinStoch) : Deterministic Δ[X ⊗ Y] := inferInstance

example (X Y : FinStoch) : Deterministic ε[X ⊗ Y] := inferInstance

set_option linter.hashCommand false in
#guard
  let X : FinStoch := ⟨Bool⟩
  (Δ[X]).mass true (true, true) == 1 &&
    (Δ[X]).mass true (false, false) == 0 &&
    (Δ[X]).mass true (true, false) == 0 &&
    (ε[X]).mass false PUnit.unit == 1

end FinStoch
