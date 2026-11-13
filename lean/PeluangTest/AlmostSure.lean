/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.AlmostSure
public import Peluang.Markov.Derived
import PeluangLint

/-!
# Tests for `Peluang.AlmostSure`

Each result of `Peluang.AlmostSure` applied once in a general copy-discard category, and
`AlmostSurelyEq p f g` at `p : B ⟶ X ⊗ A` from a hypothesis written with `Δ[X ⊗ A]`: `exact`
fails, and closes after rewriting with `CopyDiscardCategory.comonObj_tensor`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

example {A X Y : C} (p : A ⟶ X) (f g h : X ⟶ Y) (hfg : AlmostSurelyEq p f g)
    (hgh : AlmostSurelyEq p g h) : AlmostSurelyEq p h f :=
  (almostSurelyEq_equivalence p).symm ((almostSurelyEq_equivalence p).trans hfg hgh)

example {A X Y : C} (p : A ⟶ X) (f : X ⟶ Y) : AlmostSurelyEq p f f :=
  (almostSurelyEq_equivalence p).refl f

example {A X Y Z : C} {p : A ⟶ X} {f g : X ⟶ Y} (h : AlmostSurelyEq p f g) (k : Y ⟶ Z) :
    p ≫ Δ[X] ≫ ((f ≫ k) ▷ X) = p ≫ Δ[X] ≫ ((g ≫ k) ▷ X) :=
  h.comp k

example {A X Y Z : C} {p : A ⟶ X} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z}
    (hf : AlmostSurelyEq p f₁ f₂) (hg : AlmostSurelyEq p g₁ g₂) :
    p ≫ Δ[X] ≫ (Δ[X] ▷ X) ≫ ((f₁ ▷ X) ⊗ₘ g₁) = p ≫ Δ[X] ≫ (Δ[X] ▷ X) ≫ ((f₂ ▷ X) ⊗ₘ g₂) :=
  hf.copy_tensorHom hg

example {B X A Y : C} (p : B ⟶ X ⊗ A) (f g : X ⊗ A ⟶ Y)
    (h : p ≫ Δ[X ⊗ A] ≫ (f ▷ (X ⊗ A)) = p ≫ Δ[X ⊗ A] ≫ (g ▷ (X ⊗ A))) :
    AlmostSurelyEq p f g := by
  fail_if_success exact h
  unfold AlmostSurelyEq
  rw [CopyDiscardCategory.comonObj_tensor]
  exact h

end CategoryTheory
