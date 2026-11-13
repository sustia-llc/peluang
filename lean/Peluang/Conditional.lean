/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
public import Peluang.Markov.Derived

/-!
# Conditionals

Conditionals of morphisms into a tensor product, in a copy-discard category.

## Main definitions

* `CopyDiscardCategory.IsConditional` - `g : X ⊗ A ⟶ Y` is a conditional of `f : A ⟶ X ⊗ Y`
  on `X` (Fritz 2020, Def. 11.5, equation (11.4)).
* `CopyDiscardCategory.HasConditionals` - every morphism into a tensor product has a
  conditional (Fritz 2020, Def. 11.5).

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace CopyDiscardCategory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

/-- For `f : A ⟶ X ⊗ Y` and `g : X ⊗ A ⟶ Y`, `g` is a conditional of `f` on `X`: `f` equals
copying `A`, applying the first marginal of `f` to the left copy, copying that `X`, and
applying `g` to the right `X` and `A` (Fritz 2020, Def. 11.5, equation (11.4)). The inputs
of `g` are ordered `X ⊗ A`. -/
def IsConditional {A X Y : C} (f : A ⟶ X ⊗ Y) (g : X ⊗ A ⟶ Y) : Prop :=
  f = Δ[A] ≫ (marginalFst f ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ g)

/-- A copy-discard category `C` has conditionals: every morphism `f : A ⟶ X ⊗ Y` of `C` has
a conditional `g : X ⊗ A ⟶ Y` on `X` (Fritz 2020, Def. 11.5). -/
class HasConditionals (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    [CopyDiscardCategory C] : Prop where
  /-- Every morphism `f : A ⟶ X ⊗ Y` has a conditional `g : X ⊗ A ⟶ Y` on `X`. -/
  exists_isConditional : ∀ {A X Y : C} (f : A ⟶ X ⊗ Y), ∃ g, IsConditional f g

end CopyDiscardCategory

end CategoryTheory
