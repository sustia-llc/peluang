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

end CategoryTheory
