/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Markov.Cartesian

/-!
# Tests for `Peluang.Markov.Cartesian`

Activating `MarkovCategory.ofCartesianMonoidalCategory` as a local instance gives a Markov
category whose copy-discard part is `CartesianCopyDiscard.ofCartesianMonoidalCategory`.
-/

public section

universe v u

namespace CategoryTheory

attribute [local instance] MarkovCategory.ofCartesianMonoidalCategory in
example {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C] :
    MarkovCategory C :=
  inferInstance

example {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C] :
    (MarkovCategory.ofCartesianMonoidalCategory (C := C)).toCopyDiscardCategory =
      CartesianCopyDiscard.ofCartesianMonoidalCategory :=
  rfl

end CategoryTheory
