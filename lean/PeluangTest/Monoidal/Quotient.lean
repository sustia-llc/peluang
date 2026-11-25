/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Monoidal.Quotient
import PeluangLint

/-!
# Tests for `Peluang.Monoidal.Quotient`

The definitional unfoldings of the tensor product of objects, of the whiskerings, of the unit,
of the associator and of the braiding of `Quotient r` on the image of `Quotient.functor r`, a
use of `Quotient.functor_map_tensorHom`, the `MonoidalCategory`, `BraidedCategory` and
`SymmetricCategory` instances that search finds on `Quotient r` under
`[HomRel.IsStableUnderWhisker r]`, and the `HomRel.IsStableUnderWhisker` instance of the
equality relation.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory

variable {D : Type u} [Category.{v} D] [MonoidalCategory.{v} D]

example : HomRel.IsStableUnderWhisker (fun (_ _ : D) f g => f = g) where
  whiskerLeft X _ _ _ _ h := congrArg (X ◁ ·) h
  whiskerRight Z h := congrArg (· ▷ Z) h

variable (r : HomRel D) [HomRel.IsStableUnderWhisker r]

example : MonoidalCategory (Quotient r) := inferInstance

example {X Y X' Y' : D} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (Quotient.functor r).map (f ⊗ₘ g) = (Quotient.functor r).map f ⊗ₘ (Quotient.functor r).map g :=
  Quotient.functor_map_tensorHom r f g

example (X Y : D) :
    (Quotient.functor r).obj X ⊗ (Quotient.functor r).obj Y = (Quotient.functor r).obj (X ⊗ Y) :=
  rfl

example (X : D) {Y Z : D} (f : Y ⟶ Z) :
    (Quotient.functor r).obj X ◁ (Quotient.functor r).map f =
      (Quotient.functor r).map (X ◁ f) := rfl

example {X Z : D} (f : X ⟶ Z) (Y : D) :
    (Quotient.functor r).map f ▷ (Quotient.functor r).obj Y =
      (Quotient.functor r).map (f ▷ Y) := rfl

example : 𝟙_ (Quotient r) = (Quotient.functor r).obj (𝟙_ D) := rfl

example (X Y Z : D) :
    (α_ ((Quotient.functor r).obj X) ((Quotient.functor r).obj Y)
      ((Quotient.functor r).obj Z)).hom = (Quotient.functor r).map (α_ X Y Z).hom := rfl

section Braided

variable [BraidedCategory D]

example : BraidedCategory (Quotient r) := inferInstance

example (X Y : D) :
    (β_ ((Quotient.functor r).obj X) ((Quotient.functor r).obj Y)).hom =
      (Quotient.functor r).map (β_ X Y).hom := rfl

end Braided

section Symmetric

variable [SymmetricCategory D]

example : SymmetricCategory (Quotient r) := inferInstance

end Symmetric

end CategoryTheory
