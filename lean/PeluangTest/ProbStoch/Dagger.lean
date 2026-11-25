/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.ProbStoch.Dagger
import PeluangLint

/-!
# Tests for `Peluang.ProbStoch.Dagger`

Dot notation `h₁.almostSurelyEq_of_almostSurelyEq hf h₂` on `IsBayesianInverse` hypotheses under
`[CopyDiscardCategory C]`. Under `[CausalCategory C] [HasConditionals C]`: the equality by `rfl`
of the `MarkovCategory C` instance that search finds and `CausalCategory.toMarkovCategory`,
`ProbStoch.isBayesianInverse_bayesInv` applied to a morphism of `Under (𝟙_ C)`,
`ProbStoch.dagger_map` applied to an `IsBayesianInverse` hypothesis, dot notation `X.dagger_id`
on an object of `ProbStoch C`, and `ProbStoch.dagger_comp` and `ProbStoch.dagger_dagger` applied
to morphisms of `ProbStoch C`. Under `[MarkovCategory C] [HasConditionals C]` with the local
instance `CausalCategory.ofHasConditionals`: three equalities by `rfl`, of the Markov structure
of `CausalCategory.ofHasConditionals` and the `MarkovCategory C` instance, of `ProbStoch C` with
the causal structure given explicitly and `ProbStoch C`, and of the
`MonoidalCategory (ProbStoch C)` instance and `Quotient.monoidalCategory (probStochRel C)` over
`Under.monoidalCategory`, and `ProbStoch.dagger_dagger` applied to a morphism of `ProbStoch C`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section CopyDiscard

variable [CopyDiscardCategory C]

example {A X Y : C} {p : A ⟶ X} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : Y ⟶ X} (hf : AlmostSurelyEq p f₁ f₂)
    (h₁ : IsBayesianInverse p f₁ g₁) (h₂ : IsBayesianInverse p f₂ g₂) :
    AlmostSurelyEq (p ≫ f₁) g₁ g₂ :=
  h₁.almostSurelyEq_of_almostSurelyEq hf h₂

end CopyDiscard

section Causal

variable [CausalCategory C] [HasConditionals C]

example : (inferInstance : MarkovCategory C) = CausalCategory.toMarkovCategory := rfl

example {X Y : Under (𝟙_ C)} (f : X ⟶ Y) :
    IsBayesianInverse X.hom f.right (ProbStoch.bayesInv f).right :=
  ProbStoch.isBayesianInverse_bayesInv f

example {X Y : Under (𝟙_ C)} (f : X ⟶ Y) (g : Y ⟶ X)
    (h : IsBayesianInverse X.hom f.right g.right) :
    ProbStoch.dagger ((Quotient.functor (probStochRel C)).map f) =
      (Quotient.functor (probStochRel C)).map g :=
  ProbStoch.dagger_map f g h

example (X : ProbStoch C) : ProbStoch.dagger (𝟙 X) = 𝟙 X := X.dagger_id

example {X Y Z : ProbStoch C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ProbStoch.dagger (f ≫ g) = ProbStoch.dagger g ≫ ProbStoch.dagger f :=
  ProbStoch.dagger_comp f g

example {X Y : ProbStoch C} (f : X ⟶ Y) : ProbStoch.dagger (ProbStoch.dagger f) = f :=
  ProbStoch.dagger_dagger f

end Causal

section MarkovUser

variable [MarkovCategory C] [HasConditionals C]

attribute [local instance] CausalCategory.ofHasConditionals

example : (CausalCategory.ofHasConditionals (C := C)).toMarkovCategory = ‹MarkovCategory C› := rfl

example : @ProbStoch C _ ‹MonoidalCategory C› CausalCategory.ofHasConditionals = ProbStoch C :=
  rfl

example : (inferInstance : MonoidalCategory (ProbStoch C)) =
    @Quotient.monoidalCategory (Under (𝟙_ C)) _ (@Under.monoidalCategory C _ ‹MonoidalCategory C›)
      (probStochRel C) _ := rfl

example {X Y : ProbStoch C} (f : X ⟶ Y) :
    ProbStoch.dagger (ProbStoch.dagger f) = f := ProbStoch.dagger_dagger f

end MarkovUser

end CategoryTheory
