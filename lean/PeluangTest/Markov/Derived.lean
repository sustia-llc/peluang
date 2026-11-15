/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Markov.Derived
import PeluangLint

/-!
# Tests for `Peluang.Markov.Derived`

`simp` closes discard naturality into binary and nested tensor products, the marginals
of copying and of `Δ[A] ≫ (g ⊗ₘ h)`, the marginals of `k ≫ f`, of `f ⊗ₘ g`, of `f ▷ B` and
of `A ◁ g`, and `k ≫ marginalFst (f ⊗ₘ g) ≫ h` and `k ≫ marginalSnd (f ⊗ₘ g) ≫ h` for
arbitrary `k` and `h`.

For `f : A ⟶ X ⊗ (Y₁ ⊗ Y₂)`: `ε[Y₁ ⊗ Y₂]` elaborates at `Comon.instComonObjTensorObj`;
`marginalFst f = f ≫ X ◁ ε[Y₁ ⊗ Y₂] ≫ (ρ_ X).hom` fails by `rfl` and holds by
`rw [marginalFst, comonObj_tensor]`; `simp [marginalFst, comonObj_tensor]` and
`simp [marginalFst]` leave the same goal, whose left side keeps the counit at
`CopyDiscardCategory.comonObj (Y₁ ⊗ Y₂)`; `simp` closes `marginalFst f ≫ ε[X] = ε[A]`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory MarkovCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

example {A B X Y : C} (k : B ⟶ A) (f : A ⟶ X ⊗ Y) : k ≫ f ≫ ε[X ⊗ Y] = ε[B] := by
  simp

example {A X Y Z : C} (f : A ⟶ (X ⊗ Y) ⊗ Z) : f ≫ ε[(X ⊗ Y) ⊗ Z] = ε[A] := by
  simp

example {A X Y Z : C} (f : A ⟶ X ⊗ (Y ⊗ Z)) : f ≫ ε[X ⊗ (Y ⊗ Z)] = ε[A] := by
  simp

example {A B X Y Z W : C} (k : B ⟶ A) (f : A ⟶ (X ⊗ Y) ⊗ (Z ⊗ W)) :
    k ≫ f ≫ ε[(X ⊗ Y) ⊗ (Z ⊗ W)] = ε[B] := by
  simp

example {A X Y : C} (g : A ⟶ X) (h : A ⟶ Y) : marginalFst (Δ[A] ≫ (g ⊗ₘ h)) = g := by
  simp

example {A X Y : C} (g : A ⟶ X) (h : A ⟶ Y) : marginalSnd (Δ[A] ≫ (g ⊗ₘ h)) = h := by
  simp

example {A : C} : marginalFst Δ[A] = 𝟙 A := by
  simp

example {A : C} : marginalSnd Δ[A] = 𝟙 A := by
  simp

example {W A B X Y Z : C} (k : W ⟶ A ⊗ B) (f : A ⟶ X) (g : B ⟶ Y) (h : X ⟶ Z) :
    k ≫ marginalFst (f ⊗ₘ g) ≫ h = k ≫ A ◁ ε[B] ≫ (ρ_ A).hom ≫ f ≫ h := by
  simp

example {W A B X Y Z : C} (k : W ⟶ A ⊗ B) (f : A ⟶ X) (g : B ⟶ Y) (h : Y ⟶ Z) :
    k ≫ marginalSnd (f ⊗ₘ g) ≫ h = k ≫ ε[A] ▷ B ≫ (λ_ B).hom ≫ g ≫ h := by
  simp

example {A B X Y : C} (k : B ⟶ A) (f : A ⟶ X ⊗ Y) :
    marginalFst (k ≫ f) = k ≫ marginalFst f := by
  simp

example {A B X Y : C} (k : B ⟶ A) (f : A ⟶ X ⊗ Y) :
    marginalSnd (k ≫ f) = k ≫ marginalSnd f := by
  simp

example {A B X Y : C} (f : A ⟶ X) (g : B ⟶ Y) :
    marginalFst (f ⊗ₘ g) = A ◁ ε[B] ≫ (ρ_ A).hom ≫ f := by
  simp

example {A B X Y : C} (f : A ⟶ X) (g : B ⟶ Y) :
    marginalSnd (f ⊗ₘ g) = ε[A] ▷ B ≫ (λ_ B).hom ≫ g := by
  simp

example {A B X : C} (f : A ⟶ X) : marginalFst (f ▷ B) = A ◁ ε[B] ≫ (ρ_ A).hom ≫ f := by
  simp

example {A B X : C} (f : A ⟶ X) : marginalSnd (f ▷ B) = ε[A] ▷ B ≫ (λ_ B).hom := by
  simp

example {A B Y : C} (g : B ⟶ Y) : marginalFst (A ◁ g) = A ◁ ε[B] ≫ (ρ_ A).hom := by
  simp

example {A B Y : C} (g : B ⟶ Y) : marginalSnd (A ◁ g) = ε[A] ▷ B ≫ (λ_ B).hom ≫ g := by
  simp

example {A X Y₁ Y₂ : C} (f : A ⟶ X ⊗ (Y₁ ⊗ Y₂)) :
    marginalFst f = f ≫ X ◁ ε[Y₁ ⊗ Y₂] ≫ (ρ_ X).hom := by
  guard_target =ₛ marginalFst f =
    f ≫ X ◁ @ComonObj.counit C _ _ (Y₁ ⊗ Y₂) (Comon.instComonObjTensorObj Y₁ Y₂) ≫ (ρ_ X).hom
  fail_if_success rfl
  rw [marginalFst, comonObj_tensor]

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
example {A X Y₁ Y₂ : C} (f : A ⟶ X ⊗ (Y₁ ⊗ Y₂))
    (h : f ≫ X ◁ @ComonObj.counit C _ _ (Y₁ ⊗ Y₂) (comonObj (Y₁ ⊗ Y₂)) ≫ (ρ_ X).hom =
      f ≫ X ◁ (ε[Y₁] ⊗ₘ ε[Y₂]) ≫ X ◁ (λ_ (𝟙_ C)).hom ≫ (ρ_ X).hom) :
    marginalFst f = f ≫ X ◁ ε[Y₁ ⊗ Y₂] ≫ (ρ_ X).hom := by
  simp [marginalFst, comonObj_tensor]
  guard_target =ₛ f ≫ X ◁ @ComonObj.counit C _ _ (Y₁ ⊗ Y₂) (comonObj (Y₁ ⊗ Y₂)) ≫ (ρ_ X).hom =
    f ≫ X ◁ (ε[Y₁] ⊗ₘ ε[Y₂]) ≫ X ◁ (λ_ (𝟙_ C)).hom ≫ (ρ_ X).hom
  exact h

set_option linter.flexible false in
example {A X Y₁ Y₂ : C} (f : A ⟶ X ⊗ (Y₁ ⊗ Y₂))
    (h : f ≫ X ◁ @ComonObj.counit C _ _ (Y₁ ⊗ Y₂) (comonObj (Y₁ ⊗ Y₂)) ≫ (ρ_ X).hom =
      f ≫ X ◁ (ε[Y₁] ⊗ₘ ε[Y₂]) ≫ X ◁ (λ_ (𝟙_ C)).hom ≫ (ρ_ X).hom) :
    marginalFst f = f ≫ X ◁ ε[Y₁ ⊗ Y₂] ≫ (ρ_ X).hom := by
  simp [marginalFst]
  guard_target =ₛ f ≫ X ◁ @ComonObj.counit C _ _ (Y₁ ⊗ Y₂) (comonObj (Y₁ ⊗ Y₂)) ≫ (ρ_ X).hom =
    f ≫ X ◁ (ε[Y₁] ⊗ₘ ε[Y₂]) ≫ X ◁ (λ_ (𝟙_ C)).hom ≫ (ρ_ X).hom
  exact h

example {A X Y₁ Y₂ : C} (f : A ⟶ X ⊗ (Y₁ ⊗ Y₂)) : marginalFst f ≫ ε[X] = ε[A] := by
  simp

end CategoryTheory
