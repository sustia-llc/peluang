/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.BayesianInverse
import PeluangLint

/-!
# Tests for `Peluang.BayesianInverse`

`IsBayesianInverse p f g` unfolds to its equation, dot notation `h₁.unique_as h₂`,
`hf.comp hg`, `h.congr hf hg` and `hf.tensor hk` on `IsBayesianInverse` hypotheses,
`isBayesianInverse_id`, `isBayesianInverse_iff_isConditional` and `exists_isBayesianInverse`
applied once. For `h : IsBayesianInverse p f g`, dot notation `h.comp_eq`, `h.symm` and
`h.symm.symm` in a Markov category, and `h.symm` failing in a copy-discard category with no
`MarkovCategory` instance.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

section CopyDiscard

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

example {A X Y : C} (p : A ⟶ X) (f : X ⟶ Y) (g : Y ⟶ X) :
    IsBayesianInverse p f g ↔ p ≫ Δ[X] ≫ (X ◁ f) = (p ≫ f) ≫ Δ[Y] ≫ (g ▷ Y) :=
  Iff.rfl

example {A X Y : C} {p : A ⟶ X} {f : X ⟶ Y} {g₁ g₂ : Y ⟶ X}
    (h₁ : IsBayesianInverse p f g₁) (h₂ : IsBayesianInverse p f g₂) :
    AlmostSurelyEq (p ≫ f) g₁ g₂ :=
  h₁.unique_as h₂

example {A X : C} (p : A ⟶ X) : IsBayesianInverse p (𝟙 X) (𝟙 X) :=
  isBayesianInverse_id p

example {A X Y Z : C} {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : Y ⟶ X} {g' : Z ⟶ Y}
    (hf : IsBayesianInverse p f f') (hg : IsBayesianInverse (p ≫ f) g g') :
    IsBayesianInverse p (f ≫ g) (g' ≫ f') :=
  hf.comp hg

example {A X Y : C} {p : A ⟶ X} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : Y ⟶ X}
    (hf : AlmostSurelyEq p f₁ f₂) (hg : AlmostSurelyEq (p ≫ f₁) g₁ g₂)
    (h : IsBayesianInverse p f₁ g₁) : IsBayesianInverse p f₂ g₂ :=
  h.congr hf hg

example {X Y : C} (p : 𝟙_ C ⟶ X) (f : X ⟶ Y) (g : Y ⟶ X) (h : IsBayesianInverse p f g) :
    IsConditional (p ≫ Δ[X] ≫ (f ▷ X)) ((ρ_ Y).hom ≫ g) :=
  (isBayesianInverse_iff_isConditional p f g).1 h

example [HasConditionals C] {X Y : C} (p : 𝟙_ C ⟶ X) (f : X ⟶ Y) :
    ∃ g, IsBayesianInverse p f g :=
  exists_isBayesianInverse p f

example {A B X Y W Z : C} {p : A ⟶ X} {q : B ⟶ W} {f : X ⟶ Y} {k : W ⟶ Z} {f' : Y ⟶ X}
    {k' : Z ⟶ W} (hf : IsBayesianInverse p f f') (hk : IsBayesianInverse q k k') :
    IsBayesianInverse (p ⊗ₘ q) (f ⊗ₘ k) (f' ⊗ₘ k') :=
  hf.tensor hk

example {A X Y : C} {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ X} (h : IsBayesianInverse p f g) :
    IsBayesianInverse p f g := by
  fail_if_success have := h.symm
  exact h

end CopyDiscard

section Markov

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

example {A X Y : C} {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ X} (h : IsBayesianInverse p f g) :
    p ≫ f ≫ g = p :=
  h.comp_eq

example {A X Y : C} {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ X} (h : IsBayesianInverse p f g) :
    IsBayesianInverse (p ≫ f) g f :=
  h.symm

example {A X Y : C} {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ X} (h : IsBayesianInverse p f g) :
    IsBayesianInverse ((p ≫ f) ≫ g) f g :=
  h.symm.symm

end Markov

end CategoryTheory
