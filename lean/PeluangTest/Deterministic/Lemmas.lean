/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Deterministic.Lemmas

/-!
# Tests for `Peluang.Deterministic.Lemmas`

Instance synthesis of `IsComonHom` and `Deterministic` for the structure maps, tensor
products and whiskerings in a copy-discard category; `fail_if_success` pins the goals on
which synthesis fails.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

example (X Y : C) : IsComonHom (β_ X Y).hom := inferInstance

example (X Y : C) : IsComonHom (β_ X Y).inv := inferInstance

example (X Y Z : C) : IsComonHom (α_ X Y Z).hom := inferInstance

example (X Y Z : C) : IsComonHom (α_ X Y Z).inv := inferInstance

example (X : C) : IsComonHom (λ_ X).hom := inferInstance

example (X : C) : IsComonHom (λ_ X).inv := inferInstance

example (X : C) : IsComonHom (ρ_ X).hom := inferInstance

example (X : C) : IsComonHom (ρ_ X).inv := inferInstance

example (X : C) : IsComonHom Δ[X] := inferInstance

example {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') [Deterministic f] [Deterministic g] :
    IsComonHom (f ⊗ₘ g) := inferInstance

example (X : C) : IsComonHom (Δ[X] ≫ (β_ X X).hom) := inferInstance

section TensorSource

variable {X Y Z W V : C} (f : X ⊗ Y ⟶ Z) (g : W ⟶ V)

example [Deterministic f] [Deterministic g] : Deterministic (f ⊗ₘ g) := inferInstance

example [Deterministic f] [Deterministic g] : IsComonHom (f ⊗ₘ g) := inferInstance

example [IsComonHom f] [IsComonHom g] : IsComonHom (f ⊗ₘ g) := inferInstance

example [Deterministic f] : IsComonHom f := inferInstance

example [IsComonHom f] [IsComonHom g] : True := by
  fail_if_success have : Deterministic (f ⊗ₘ g) := inferInstance
  trivial

example [IsComonHom f] : True := by
  fail_if_success have : Deterministic f := inferInstance
  trivial

end TensorSource

example {X₁ X₂ Y Z W V : C} (f : (X₁ ⊗ X₂) ⊗ Y ⟶ Z) (g : W ⟶ V) [IsComonHom f]
    [IsComonHom g] : IsComonHom (f ⊗ₘ g) := inferInstance

example {X₁ X₂ Y Z : C} (f : (X₁ ⊗ X₂) ⊗ Y ⟶ Z) [Deterministic f] : True := by
  fail_if_success have : IsComonHom f := inferInstance
  trivial

example {A B Y : C} (f : A ⊗ B ⟶ Y) [IsComonHom f] (Z : C) : IsComonHom (f ▷ Z) :=
  inferInstance

example {A B Y : C} (f : A ⊗ B ⟶ Y) [IsComonHom f] (Z : C) : IsComonHom (Z ◁ f) :=
  inferInstance

example {A B Y : C} (f : A ⊗ B ⟶ Y) [IsComonHom f] (Z : C) : f ▷ Z = f ▷ Z := by
  fail_if_success have : Deterministic (f ▷ Z) := inferInstance
  rfl

example (A B Y Z : C) : (α_ (A ⊗ B) Y Z).hom = (α_ (A ⊗ B) Y Z).hom := by
  fail_if_success have : IsComonHom (α_ (A ⊗ B) Y Z).hom := inferInstance
  rfl

example (A B : C) : Δ[A ⊗ B] = Δ[A ⊗ B] := by
  fail_if_success have : IsComonHom Δ[A ⊗ B] := inferInstance
  rfl

example {X Y Z W : C} (f : X ⊗ Y ⟶ Z ⊗ W) [Deterministic f] : IsComonHom f := inferInstance

example {X Y Z : C} (f : Z ⟶ X ⊗ Y) [Deterministic f] : IsComonHom f := inferInstance

end CategoryTheory
