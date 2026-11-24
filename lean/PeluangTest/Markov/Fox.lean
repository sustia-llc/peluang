/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Markov.Fox
import PeluangLint

/-!
# Tests for `Peluang.Markov.Fox`

The monoidal structure of `MarkovCategory.cartesianMonoidalCategoryOfDeterministic` against the
given one, its two projections against the marginal projections, the monoidal structure of
`MarkovCategory.cartesianMonoidalCategoryDeterministic` against the instance on the wide
subcategory, and instance search with `cartesianMonoidalCategoryDeterministic` as a local
instance.
-/

public section

universe v u

namespace CategoryTheory.MarkovCategory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

example (h : ∀ {X Y : C} (f : X ⟶ Y), Deterministic f) :
    (cartesianMonoidalCategoryOfDeterministic h).toSemiCartesianMonoidalCategory.toMonoidalCategory
      = ‹MonoidalCategory C› :=
  rfl

example (h : ∀ {X Y : C} (f : X ⟶ Y), Deterministic f) :
    (cartesianMonoidalCategoryOfDeterministic h).toSemiCartesianMonoidalCategory.toMonoidalCategory
      = ‹MonoidalCategory C› := by
  with_reducible_and_instances rfl

example (h : ∀ {X Y : C} (f : X ⟶ Y), Deterministic f) (X Y : C) :
    @SemiCartesianMonoidalCategory.fst C _
      (cartesianMonoidalCategoryOfDeterministic h).toSemiCartesianMonoidalCategory X Y =
        X ◁ ε[Y] ≫ (ρ_ X).hom :=
  rfl

example (h : ∀ {X Y : C} (f : X ⟶ Y), Deterministic f) (X Y : C) :
    @SemiCartesianMonoidalCategory.snd C _
      (cartesianMonoidalCategoryOfDeterministic h).toSemiCartesianMonoidalCategory X Y =
        ε[X] ▷ Y ≫ (λ_ Y).hom :=
  rfl

example :
    (cartesianMonoidalCategoryDeterministic
      (C := C)).toSemiCartesianMonoidalCategory.toMonoidalCategory =
        (inferInstance : MonoidalCategory (WideSubcategory (MorphismProperty.deterministic C))) :=
  rfl

section LocalInstance

attribute [local instance] cartesianMonoidalCategoryDeterministic

example : CartesianMonoidalCategory (WideSubcategory (MorphismProperty.deterministic C)) :=
  inferInstance

end LocalInstance

end CategoryTheory.MarkovCategory
