/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Positive
import PeluangLint

/-!
# Tests for `Peluang.Positive`

The `RelativelyPositiveCategory C` and `PositiveCategory C` instances that search finds under
`[CausalCategory C]`, and the `PositiveCategory C` instance under
`[RelativelyPositiveCategory C]`; the `MarkovCategory` structure of each against the one of the
hypothesis; `Deterministic f` for an isomorphism `f`; dot notation `h.of_comp` on an
`AlmostSurelyEq` hypothesis and on an `IsAlmostSurelyDeterministic` hypothesis, and `hf.comp hg`;
and `copy_comp_natural_of_relativelyPositive` under `[CausalCategory C]` and under
`CausalCategory.ofHasConditionals`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section Causal

variable [CausalCategory C]

example : RelativelyPositiveCategory C :=
  inferInstance

example : PositiveCategory C :=
  inferInstance

example : (inferInstance : RelativelyPositiveCategory C).toMarkovCategory =
    CausalCategory.toMarkovCategory :=
  rfl

example : (inferInstance : RelativelyPositiveCategory C).toMarkovCategory =
    CausalCategory.toMarkovCategory := by
  with_reducible_and_instances rfl

example : (inferInstance : PositiveCategory C).toMarkovCategory =
    CausalCategory.toMarkovCategory :=
  rfl

example : (inferInstance : PositiveCategory C).toMarkovCategory =
    CausalCategory.toMarkovCategory := by
  with_reducible_and_instances rfl

example : (inferInstance : PositiveCategory C).toMarkovCategory =
    (inferInstance : RelativelyPositiveCategory C).toMarkovCategory :=
  rfl

example : (inferInstance : MarkovCategory C) = CausalCategory.toMarkovCategory :=
  rfl

example : (inferInstance : MarkovCategory C) = CausalCategory.toMarkovCategory := by
  with_reducible_and_instances rfl

example {X Y : C} (f : X ⟶ Y) [IsIso f] : Deterministic f :=
  inferInstance

example {A W X Y : C} {f : A ⟶ W} {g : W ⟶ X} {h₁ h₂ : X ⟶ Y}
    (h : AlmostSurelyEq (f ≫ g) h₁ h₂) : AlmostSurelyEq f (g ≫ h₁) (g ≫ h₂) :=
  h.of_comp

example {A X Y Z : C} {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsAlmostSurelyDeterministic p f) (hg : IsAlmostSurelyDeterministic (p ≫ f) g) :
    IsAlmostSurelyDeterministic p (f ≫ g) :=
  hf.comp hg

example {A X Y Z : C} {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : IsAlmostSurelyDeterministic p (f ≫ g)) : IsAlmostSurelyDeterministic (p ≫ f) g :=
  h.of_comp

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Deterministic (f ≫ g)] :
    f ≫ Δ[Y] ≫ (g ▷ Y) = Δ[X] ≫ ((f ≫ g) ⊗ₘ f) :=
  copy_comp_natural_of_relativelyPositive f g

end Causal

section RelativelyPositive

variable [RelativelyPositiveCategory C]

example : PositiveCategory C :=
  inferInstance

example : (inferInstance : PositiveCategory C).toMarkovCategory =
    RelativelyPositiveCategory.toMarkovCategory :=
  rfl

example : (inferInstance : PositiveCategory C).toMarkovCategory =
    RelativelyPositiveCategory.toMarkovCategory := by
  with_reducible_and_instances rfl

example : (inferInstance : MarkovCategory C) = RelativelyPositiveCategory.toMarkovCategory :=
  rfl

example {X Y : C} (f : X ⟶ Y) [IsIso f] : Deterministic f :=
  inferInstance

example {A X Y Z : C} {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : IsAlmostSurelyDeterministic p (f ≫ g)) : IsAlmostSurelyDeterministic (p ≫ f) g :=
  h.of_comp

end RelativelyPositive

section HasConditionals

variable [MarkovCategory C] [HasConditionals C]

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Deterministic (f ≫ g)] :
    f ≫ Δ[Y] ≫ (g ▷ Y) = Δ[X] ≫ ((f ≫ g) ⊗ₘ f) :=
  letI : CausalCategory C := CausalCategory.ofHasConditionals
  copy_comp_natural_of_relativelyPositive f g

end HasConditionals

end CategoryTheory
