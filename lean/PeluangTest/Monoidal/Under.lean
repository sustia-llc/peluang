/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Monoidal.Under
import PeluangLint

/-!
# Tests for `Peluang.Monoidal.Under`

The definitional unfoldings of the tensor product of objects and of morphisms, of the unit and
of the braiding of `Under (𝟙_ C)`, and the `MonoidalCategory`, `BraidedCategory` and
`SymmetricCategory` instances that search finds on `Under (𝟙_ C)` under `[MonoidalCategory C]`,
`[BraidedCategory C]` and `[SymmetricCategory C]`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

example (X Y : Under (𝟙_ C)) : (X ⊗ Y).right = X.right ⊗ Y.right := rfl

example (X Y : Under (𝟙_ C)) : (X ⊗ Y).hom = (λ_ (𝟙_ C)).inv ≫ (X.hom ⊗ₘ Y.hom) := rfl

example {X Y X' Y' : Under (𝟙_ C)} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g).right = f.right ⊗ₘ g.right := rfl

example : (𝟙_ (Under (𝟙_ C))).hom = 𝟙 (𝟙_ C) := rfl

example : MonoidalCategory (Under (𝟙_ C)) := inferInstance

section Braided

variable [BraidedCategory C]

example : BraidedCategory (Under (𝟙_ C)) := inferInstance

example (X Y : Under (𝟙_ C)) : (β_ X Y).hom.right = (β_ X.right Y.right).hom := rfl

end Braided

section Symmetric

variable [SymmetricCategory C]

example : SymmetricCategory (Under (𝟙_ C)) := inferInstance

end Symmetric

end CategoryTheory
