/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Independence
import PeluangLint

/-!
# Tests for `Peluang.Independence`

`DisplaysIndep f`, `DisplaysCondIndep f` and `DisplaysCondIndepState ψ` unfold to their
equation and existentials. In a Markov category, `Δ[A] ≫ (g ⊗ₘ h)` displays independence
through `MarkovCategory.displaysIndep_iff_exists`. Instance search finds the comonoid structure
of `X ⊗ (𝟙_ C ⊗ Y)`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section CopyDiscard

variable [CopyDiscardCategory C]

example {A X Y : C} (f : A ⟶ X ⊗ Y) :
    DisplaysIndep f ↔ f = Δ[A] ≫ (marginalFst f ⊗ₘ marginalSnd f) :=
  Iff.rfl

example {A X W Y : C} (f : A ⟶ X ⊗ (W ⊗ Y)) :
    DisplaysCondIndep f ↔
      ∃ (g : A ⟶ W) (h : A ⊗ W ⟶ X) (k : W ⊗ A ⟶ Y), f = condIndepForm g h k :=
  Iff.rfl

example {X W Y : C} (ψ : 𝟙_ C ⟶ X ⊗ (W ⊗ Y)) :
    DisplaysCondIndepState ψ ↔
      ∃ (φ : 𝟙_ C ⟶ W) (f : W ⟶ X) (g : W ⟶ Y),
        ψ = φ ≫ Δ[W] ≫ (W ◁ Δ[W]) ≫ (f ⊗ₘ (W ◁ g)) :=
  Iff.rfl

example {X Y : C} : ComonObj (X ⊗ (𝟙_ C ⊗ Y)) := inferInstance

end CopyDiscard

section Markov

variable [MarkovCategory C]

example {A X Y : C} (g : A ⟶ X) (h : A ⟶ Y) : DisplaysIndep (Δ[A] ≫ (g ⊗ₘ h)) :=
  (MarkovCategory.displaysIndep_iff_exists _).2 ⟨g, h, rfl⟩

end Markov

end CategoryTheory
