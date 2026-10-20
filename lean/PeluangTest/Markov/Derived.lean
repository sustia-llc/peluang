/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Markov.Derived

/-!
# Tests for `Peluang.Markov.Derived`

`simp` closes discard naturality into binary and nested tensor products, and the marginals
of copying and of `Δ[A] ≫ (g ⊗ₘ h)`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj MarkovCategory

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

end CategoryTheory
