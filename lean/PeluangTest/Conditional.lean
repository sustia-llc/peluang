/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Conditional
import PeluangLint

/-!
# Tests for `Peluang.Conditional`

`IsConditional f g` unfolds to its equation, `HasConditionals.exists_isConditional` applied
once, and `IsConditional f g` at `f : A ⟶ (X₁ ⊗ X₂) ⊗ Y` from a hypothesis written with
`Δ[X₁ ⊗ X₂]`: `exact` fails, and closes after rewriting with
`CopyDiscardCategory.comonObj_tensor`. Dot notation `hk.nest hh` and
`h.deterministic_comp g` on `IsConditional` hypotheses, and `rw [CopyDiscardCategory.copy_tensor]`
failing at a user-written `Δ[X ⊗ A]`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

example {A X Y : C} (f : A ⟶ X ⊗ Y) (g : X ⊗ A ⟶ Y) :
    IsConditional f g ↔
      f = Δ[A] ≫ (marginalFst f ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ g) :=
  Iff.rfl

example [HasConditionals C] {A X Y : C} (f : A ⟶ X ⊗ Y) : ∃ g, IsConditional f g :=
  HasConditionals.exists_isConditional f

example {A X₁ X₂ Y : C} (f : A ⟶ (X₁ ⊗ X₂) ⊗ Y) (g : (X₁ ⊗ X₂) ⊗ A ⟶ Y)
    (h : f = Δ[A] ≫ (marginalFst f ▷ A) ≫ (Δ[X₁ ⊗ X₂] ▷ A) ≫ (α_ (X₁ ⊗ X₂) (X₁ ⊗ X₂) A).hom ≫
      ((X₁ ⊗ X₂) ◁ g)) :
    IsConditional f g := by
  fail_if_success exact h
  unfold IsConditional
  rw [CopyDiscardCategory.comonObj_tensor]
  exact h

example {A X Y Z : C} {f : A ⟶ X ⊗ (Y ⊗ Z)} {k : X ⊗ A ⟶ Y ⊗ Z} {h : Y ⊗ (X ⊗ A) ⟶ Z}
    (hk : IsConditional f k) (hh : IsConditional k h) :
    IsConditional (f ≫ (α_ X Y Z).inv) (((β_ X Y).hom ▷ A) ≫ (α_ Y X A).hom ≫ h) :=
  hk.nest hh

example {A A' X Y : C} {f : A' ⟶ X ⊗ Y} {k : X ⊗ A' ⟶ Y} (h : IsConditional f k)
    (g : A ⟶ A') [Deterministic g] :
    IsConditional (g ≫ f) ((X ◁ g) ≫ k) :=
  h.deterministic_comp g

example {A X : C} (g : (X ⊗ A) ⊗ (X ⊗ A) ⟶ X ⊗ A) :
    Δ[X ⊗ A] ≫ g = Δ[X ⊗ A] ≫ g := by
  fail_if_success rw [CopyDiscardCategory.copy_tensor]
  rfl

end CategoryTheory
