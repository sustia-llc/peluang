/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Causal
import PeluangLint

/-!
# Tests for `Peluang.Causal`

Dot notation `h.of_comp` on an `AlmostSurelyEq` hypothesis and `hf.comp hg` on
`IsAlmostSurelyDeterministic` hypotheses, the `MarkovCategory` structure of
`CausalCategory.ofHasConditionals` against the one it is built from, the `MarkovCategory C`
instance that search finds under `[CausalCategory C]` against `CausalCategory.toMarkovCategory`,
and one theorem stated under `[MarkovCategory C]` and one under `[CopyDiscardCategory C]`
applied under `[CausalCategory C]`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section HasConditionals

variable [MarkovCategory C] [HasConditionals C]

example : (CausalCategory.ofHasConditionals (C := C)).toMarkovCategory = ‹MarkovCategory C› :=
  rfl

end HasConditionals

section Causal

variable [CausalCategory C]

example {A W X Y : C} {f : A ⟶ W} {g : W ⟶ X} {h₁ h₂ : X ⟶ Y}
    (h : AlmostSurelyEq (f ≫ g) h₁ h₂) : AlmostSurelyEq f (g ≫ h₁) (g ≫ h₂) :=
  h.of_comp

example {A X Y Z : C} {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsAlmostSurelyDeterministic p f) (hg : IsAlmostSurelyDeterministic (p ≫ f) g) :
    IsAlmostSurelyDeterministic p (f ≫ g) :=
  hf.comp hg

example : (inferInstance : MarkovCategory C) = CausalCategory.toMarkovCategory :=
  rfl

example : (inferInstance : MarkovCategory C) = CausalCategory.toMarkovCategory := by
  with_reducible_and_instances rfl

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Δ[X] ≫ ((f ≫ g) ⊗ₘ f)) ≫ ε[Z] ▷ Y ≫ (λ_ Y).hom = f :=
  MarkovCategory.marginalSnd_copy_comp_tensorHom (f ≫ g) f

example {A X Y Z : C} {p : A ⟶ X} {f g : X ⟶ Y} (h : AlmostSurelyEq p f g) (k : Y ⟶ Z) :
    AlmostSurelyEq p (f ≫ k) (g ≫ k) :=
  h.comp k

end Causal

end CategoryTheory
