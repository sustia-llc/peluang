/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Conditional.Snd
import PeluangLint

/-!
# Tests for `Peluang.Conditional.Snd`

`IsConditionalSnd f g` unfolds to `IsConditional (f ≫ (β_ X Y).hom) g`. Each of
`marginalFst_comp_braiding_hom`, `conditional_form_comp_braiding_hom`, `isConditionalSnd_iff`
and `exists_isConditionalSnd` applied at variables. The equation of `isConditionalSnd_iff`
from a hypothesis `IsConditionalSnd f g` through `.mp`, and `IsConditionalSnd f g` from the
equation through `.mpr`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

example {A X Y : C} (f : A ⟶ X ⊗ Y) (g : Y ⊗ A ⟶ X) :
    IsConditionalSnd f g ↔ IsConditional (f ≫ (β_ X Y).hom) g :=
  Iff.rfl

example {A X Y : C} (f : A ⟶ X ⊗ Y) : marginalFst (f ≫ (β_ X Y).hom) = marginalSnd f :=
  marginalFst_comp_braiding_hom f

example {A X Y : C} (m : A ⟶ Y) (g : Y ⊗ A ⟶ X) :
    (Δ[A] ≫ (m ▷ A) ≫ (Δ[Y] ▷ A) ≫ (α_ Y Y A).hom ≫ (Y ◁ g)) ≫ (β_ Y X).hom =
      Δ[A] ≫ (A ◁ (m ≫ Δ[Y])) ≫ (α_ A Y Y).inv ≫ ((β_ A Y).hom ▷ Y) ≫ (g ▷ Y) :=
  conditional_form_comp_braiding_hom m g

example {A X Y : C} (f : A ⟶ X ⊗ Y) (g : Y ⊗ A ⟶ X) :
    IsConditionalSnd f g ↔
      f = Δ[A] ≫ (A ◁ (marginalSnd f ≫ Δ[Y])) ≫ (α_ A Y Y).inv ≫
        ((β_ A Y).hom ▷ Y) ≫ (g ▷ Y) :=
  isConditionalSnd_iff f g

example [HasConditionals C] {A X Y : C} (f : A ⟶ X ⊗ Y) : ∃ g, IsConditionalSnd f g :=
  exists_isConditionalSnd f

example {A X Y : C} (f : A ⟶ X ⊗ Y) (g : Y ⊗ A ⟶ X) (h : IsConditionalSnd f g) :
    f = Δ[A] ≫ (A ◁ (marginalSnd f ≫ Δ[Y])) ≫ (α_ A Y Y).inv ≫
      ((β_ A Y).hom ▷ Y) ≫ (g ▷ Y) :=
  (isConditionalSnd_iff f g).mp h

example {A X Y : C} (f : A ⟶ X ⊗ Y) (g : Y ⊗ A ⟶ X)
    (h : f = Δ[A] ≫ (A ◁ (marginalSnd f ≫ Δ[Y])) ≫ (α_ A Y Y).inv ≫
      ((β_ A Y).hom ▷ Y) ≫ (g ▷ Y)) :
    IsConditionalSnd f g :=
  (isConditionalSnd_iff f g).mpr h

end CategoryTheory
