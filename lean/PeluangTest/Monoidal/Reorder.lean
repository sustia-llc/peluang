/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Monoidal.Reorder
import PeluangLint

/-!
# Tests for `Peluang.Monoidal.Reorder`

For each of the eight isomorphisms of `Peluang.Monoidal.Reorder`, its `hom` as the composite
of its `_hom` theorem and the equation `hom ≫ inv = 𝟙 _`; `tensorCompAssoc` under
`[MonoidalCategory C]` with no braiding; and `tensorRev₃_eq_tensorLeftComm`,
`tensorRev₃_hom_naturality` and `tensorTripleInterchange_hom_natural` at variables.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

example (A X₁ W Y₁ A' : C) : A ⊗ ((X₁ ⊗ (W ⊗ Y₁)) ⊗ A') ≅ (A ⊗ X₁) ⊗ (W ⊗ (Y₁ ⊗ A')) :=
  tensorCompAssoc A X₁ W Y₁ A'

example (A X₁ W Y₁ A' : C) :
    (tensorCompAssoc A X₁ W Y₁ A').hom =
      A ◁ (α_ X₁ (W ⊗ Y₁) A').hom ≫ A ◁ X₁ ◁ (α_ W Y₁ A').hom ≫
        (α_ A X₁ (W ⊗ (Y₁ ⊗ A'))).inv :=
  tensorCompAssoc_hom A X₁ W Y₁ A'

example (A X₁ W Y₁ A' : C) :
    (tensorCompAssoc A X₁ W Y₁ A').hom ≫ (tensorCompAssoc A X₁ W Y₁ A').inv = 𝟙 _ :=
  Iso.hom_inv_id _

section Braided

variable [BraidedCategory C]

example (X Y Z : C) :
    (tensorLeftComm X Y Z).hom = (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom :=
  tensorLeftComm_hom X Y Z

example (X Y Z : C) : (tensorLeftComm X Y Z).hom ≫ (tensorLeftComm X Y Z).inv = 𝟙 _ :=
  Iso.hom_inv_id _

example (X₁ X₂ Y₁ Y₂ : C) :
    (tensorμIso X₁ X₂ Y₁ Y₂).hom =
      (α_ X₁ X₂ (Y₁ ⊗ Y₂)).hom ≫ X₁ ◁ (α_ X₂ Y₁ Y₂).inv ≫ X₁ ◁ (β_ X₂ Y₁).hom ▷ Y₂ ≫
        X₁ ◁ (α_ Y₁ X₂ Y₂).hom ≫ (α_ X₁ Y₁ (X₂ ⊗ Y₂)).inv :=
  tensorμIso_hom X₁ X₂ Y₁ Y₂

example (X₁ X₂ Y₁ Y₂ : C) :
    (tensorμIso X₁ X₂ Y₁ Y₂).hom ≫ (tensorμIso X₁ X₂ Y₁ Y₂).inv = 𝟙 _ :=
  Iso.hom_inv_id _

example (X W Y : C) :
    (tensorRev₃ X W Y).hom = (β_ X (W ⊗ Y)).hom ≫ (β_ W Y).hom ▷ X ≫ (α_ Y W X).hom :=
  tensorRev₃_hom X W Y

example (X W Y : C) : (tensorRev₃ X W Y).hom ≫ (tensorRev₃ X W Y).inv = 𝟙 _ :=
  Iso.hom_inv_id _

example (X₁ X₂ W Y : C) :
    (tensorWeakUnionIso X₁ X₂ W Y).hom =
      (α_ X₁ X₂ (W ⊗ Y)).hom ≫ X₁ ◁ (α_ X₂ W Y).inv ≫ X₁ ◁ (β_ X₂ W).hom ▷ Y :=
  tensorWeakUnionIso_hom X₁ X₂ W Y

example (X₁ X₂ W Y : C) :
    (tensorWeakUnionIso X₁ X₂ W Y).hom ≫ (tensorWeakUnionIso X₁ X₂ W Y).inv = 𝟙 _ :=
  Iso.hom_inv_id _

example (X₁ W₁ Y₁ X₂ W₂ Y₂ : C) :
    (tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom =
      ((α_ X₁ (W₁ ⊗ Y₁) (X₂ ⊗ (W₂ ⊗ Y₂))).hom ≫ X₁ ◁ (α_ (W₁ ⊗ Y₁) X₂ (W₂ ⊗ Y₂)).inv ≫
        X₁ ◁ (β_ (W₁ ⊗ Y₁) X₂).hom ▷ (W₂ ⊗ Y₂) ≫ X₁ ◁ (α_ X₂ (W₁ ⊗ Y₁) (W₂ ⊗ Y₂)).hom ≫
        (α_ X₁ X₂ ((W₁ ⊗ Y₁) ⊗ (W₂ ⊗ Y₂))).inv) ≫
      (X₁ ⊗ X₂) ◁ ((α_ W₁ Y₁ (W₂ ⊗ Y₂)).hom ≫ W₁ ◁ (α_ Y₁ W₂ Y₂).inv ≫
        W₁ ◁ (β_ Y₁ W₂).hom ▷ Y₂ ≫ W₁ ◁ (α_ W₂ Y₁ Y₂).hom ≫ (α_ W₁ W₂ (Y₁ ⊗ Y₂)).inv) :=
  tensorTripleInterchange_hom X₁ W₁ Y₁ X₂ W₂ Y₂

example (X₁ W₁ Y₁ X₂ W₂ Y₂ : C) :
    (tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom ≫
      (tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).inv = 𝟙 _ :=
  Iso.hom_inv_id _

example (X V W Y : C) :
    (tensorCondReorder X V W Y).hom =
      X ◁ (α_ V W Y).hom ≫ (α_ X V (W ⊗ Y)).inv ≫ (β_ X V).hom ▷ (W ⊗ Y) ≫
        (α_ V X (W ⊗ Y)).hom :=
  tensorCondReorder_hom X V W Y

example (X V W Y : C) :
    (tensorCondReorder X V W Y).hom ≫ (tensorCondReorder X V W Y).inv = 𝟙 _ :=
  Iso.hom_inv_id _

example (X₁ V X₂ W Y₂ Y₁ : C) :
    (tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom =
      X₁ ◁ ((α_ V X₂ (W ⊗ Y₂)).inv ≫ (β_ V X₂).hom ▷ (W ⊗ Y₂) ≫
        (α_ X₂ V (W ⊗ Y₂)).hom) ▷ Y₁ ≫
      X₁ ◁ (α_ X₂ (V ⊗ (W ⊗ Y₂)) Y₁).hom ≫ (α_ X₁ X₂ ((V ⊗ (W ⊗ Y₂)) ⊗ Y₁)).inv ≫
      (X₁ ⊗ X₂) ◁ (α_ V W Y₂).inv ▷ Y₁ ≫ (X₁ ⊗ X₂) ◁ (α_ (V ⊗ W) Y₂ Y₁).hom :=
  tensorCompReorder_hom X₁ V X₂ W Y₂ Y₁

example (X₁ V X₂ W Y₂ Y₁ : C) :
    (tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom ≫ (tensorCompReorder X₁ V X₂ W Y₂ Y₁).inv = 𝟙 _ :=
  Iso.hom_inv_id _

example (X W Y : C) :
    tensorRev₃ X W Y =
      tensorLeftComm X W Y ≪≫ whiskerLeftIso W (β_ X Y) ≪≫ tensorLeftComm W Y X :=
  tensorRev₃_eq_tensorLeftComm X W Y

example {X W Y X' W' Y' : C} (f : X ⟶ X') (g : W ⟶ W') (h : Y ⟶ Y') :
    (f ⊗ₘ (g ⊗ₘ h)) ≫ (tensorRev₃ X' W' Y').hom =
      (tensorRev₃ X W Y).hom ≫ (h ⊗ₘ (g ⊗ₘ f)) :=
  tensorRev₃_hom_naturality f g h

example {X₁ W₁ Y₁ X₂ W₂ Y₂ X₁' W₁' Y₁' X₂' W₂' Y₂' : C} (a₁ : X₁ ⟶ X₁') (b₁ : W₁ ⟶ W₁')
    (c₁ : Y₁ ⟶ Y₁') (a₂ : X₂ ⟶ X₂') (b₂ : W₂ ⟶ W₂') (c₂ : Y₂ ⟶ Y₂') :
    ((a₁ ⊗ₘ (b₁ ⊗ₘ c₁)) ⊗ₘ (a₂ ⊗ₘ (b₂ ⊗ₘ c₂))) ≫
        (tensorTripleInterchange X₁' W₁' Y₁' X₂' W₂' Y₂').hom =
      (tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom ≫
        ((a₁ ⊗ₘ a₂) ⊗ₘ ((b₁ ⊗ₘ b₂) ⊗ₘ (c₁ ⊗ₘ c₂))) :=
  tensorTripleInterchange_hom_natural a₁ b₁ c₁ a₂ b₂ c₂

end Braided

end CategoryTheory
