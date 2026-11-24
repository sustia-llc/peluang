/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.AlmostSure.Deterministic
import PeluangLint

/-!
# Tests for `Peluang.AlmostSure.Deterministic`

`IsAlmostSurelyDeterministic p f` unfolds to its `AlmostSurelyEq` form,
`isAlmostSurelyDeterministic_of_deterministic` applied once at a `[Deterministic f]`
hypothesis, dot notation `hf.congr h` and `hf.comp_deterministic g` on
`IsAlmostSurelyDeterministic` hypotheses, and `hf.comp_deterministic (𝟙 Y)` with its
`Deterministic (𝟙 Y)` argument found by instance search.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

example {A X Y : C} (p : A ⟶ X) (f : X ⟶ Y) :
    IsAlmostSurelyDeterministic p f ↔ AlmostSurelyEq p (f ≫ Δ[Y]) (Δ[X] ≫ (f ⊗ₘ f)) :=
  Iff.rfl

example {A X Y : C} (p : A ⟶ X) (f : X ⟶ Y) [Deterministic f] :
    IsAlmostSurelyDeterministic p f :=
  isAlmostSurelyDeterministic_of_deterministic p f

example {A X Y : C} {p : A ⟶ X} {f g : X ⟶ Y} (h : AlmostSurelyEq p f g)
    (hf : IsAlmostSurelyDeterministic p f) : IsAlmostSurelyDeterministic p g :=
  hf.congr h

example {A X Y Z : C} {p : A ⟶ X} {f : X ⟶ Y} (hf : IsAlmostSurelyDeterministic p f)
    (g : Y ⟶ Z) [Deterministic g] : IsAlmostSurelyDeterministic p (f ≫ g) :=
  hf.comp_deterministic g

example {Y : C} : Deterministic (𝟙 Y) := inferInstance

example {A X Y : C} {p : A ⟶ X} {f : X ⟶ Y} (hf : IsAlmostSurelyDeterministic p f) :
    IsAlmostSurelyDeterministic p (f ≫ 𝟙 Y) :=
  hf.comp_deterministic (𝟙 Y)

end CategoryTheory
