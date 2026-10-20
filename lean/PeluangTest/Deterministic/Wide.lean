/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Deterministic.Wide

/-!
# Tests for `Peluang.Deterministic.Wide`

Instance synthesis of the Markov category structure on the wide subcategory of deterministic
morphisms.
-/

public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

example [MarkovCategory C] :
    MarkovCategory (WideSubcategory (MorphismProperty.deterministic C)) :=
  inferInstance

end CategoryTheory
