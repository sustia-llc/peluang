/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.ProbStoch.Basic
import PeluangLint

/-!
# Tests for `Peluang.ProbStoch.Basic`

Dot notation `hf.tensorHom hg` on `AlmostSurelyEq` hypotheses under `[CopyDiscardCategory C]`,
the `HomRel.IsStableUnderWhisker (probStochRel C)` instance that search finds under
`[CopyDiscardCategory C]`, the `Congruence (probStochRel C)`, `Category (ProbStoch C)`,
`MonoidalCategory (ProbStoch C)` and `SymmetricCategory (ProbStoch C)` instances that search
finds under `[CausalCategory C]`, `ProbStoch.functor_map_eq_iff` applied to an `AlmostSurelyEq`
hypothesis on morphisms of `Under (𝟙_ C)`, `ProbStoch.functor_map_tensorHom` applied to two
morphisms of `Under (𝟙_ C)`, and two equalities by `rfl`: the `MonoidalCategory (ProbStoch C)`
instance against `Quotient.monoidalCategory (probStochRel C)`, and the structure morphism of a
tensor product of two objects of `ProbStoch C`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section CopyDiscard

variable [CopyDiscardCategory C]

example {A B X Y W Z : C} {p : A ⟶ X} {q : B ⟶ W} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : W ⟶ Z}
    (hf : AlmostSurelyEq p f₁ f₂) (hg : AlmostSurelyEq q g₁ g₂) :
    AlmostSurelyEq (p ⊗ₘ q) (f₁ ⊗ₘ g₁) (f₂ ⊗ₘ g₂) :=
  hf.tensorHom hg

example : HomRel.IsStableUnderWhisker (probStochRel C) := inferInstance

end CopyDiscard

section Causal

variable [CausalCategory C]

example : Congruence (probStochRel C) := inferInstance

example : Category.{v} (ProbStoch C) := inferInstance

example {X Y : Under (𝟙_ C)} (f g : X ⟶ Y) (h : AlmostSurelyEq X.hom f.right g.right) :
    (Quotient.functor (probStochRel C)).map f = (Quotient.functor (probStochRel C)).map g :=
  (ProbStoch.functor_map_eq_iff f g).2 h

example : MonoidalCategory (ProbStoch C) := inferInstance

example : SymmetricCategory (ProbStoch C) := inferInstance

example {X Y X' Y' : Under (𝟙_ C)} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (Quotient.functor (probStochRel C)).map (f ⊗ₘ g) =
      (Quotient.functor (probStochRel C)).map f ⊗ₘ (Quotient.functor (probStochRel C)).map g :=
  ProbStoch.functor_map_tensorHom f g

example : (inferInstance : MonoidalCategory (ProbStoch C)) =
    Quotient.monoidalCategory (probStochRel C) := rfl

example (X Y : Under (𝟙_ C)) :
    ((Quotient.functor (probStochRel C)).obj X ⊗ (Quotient.functor (probStochRel C)).obj Y).as.hom =
      (λ_ (𝟙_ C)).inv ≫ (X.hom ⊗ₘ Y.hom) := rfl

end Causal

end CategoryTheory
