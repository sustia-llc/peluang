/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.ProbStoch.Coupling
import PeluangLint

/-!
# Tests for `Peluang.ProbStoch.Coupling`

Under `[CopyDiscardCategory C]`: `marginalSnd_comp_copy_whiskerLeft` applied to two morphisms,
and the forward direction of `almostSurelyEq_iff_copy_whiskerLeft` and of
`isConditional_rightUnitor_comp_iff` applied to a hypothesis. Under `[MarkovCategory C]`:
`MarkovCategory.marginalFst_comp_copy_whiskerLeft` applied to two morphisms. Under
`[CausalCategory C] [HasConditionals C]`: `ProbStoch.couplingHom_spec` applied to a morphism with
the two marginals, `ProbStoch.homEquivCoupling_map` applied to a morphism of `Under (𝟙_ C)`, the
same equation by `rfl`, `symm_apply_apply` and `apply_symm_apply` of
`ProbStoch.homEquivCoupling X Y`, and the two marginals of a value of
`ProbStoch.homEquivCoupling X Y` from its subtype property. Under
`[MarkovCategory C] [HasConditionals C]` with the local instance
`CausalCategory.ofHasConditionals`: `ProbStoch.homEquivCoupling X Y` as a term.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section CopyDiscard

variable [CopyDiscardCategory C]

example {A X Y : C} (p : A ⟶ X) (f : X ⟶ Y) : marginalSnd (p ≫ Δ[X] ≫ (X ◁ f)) = p ≫ f :=
  marginalSnd_comp_copy_whiskerLeft p f

example {A X Y : C} (p : A ⟶ X) (f g : X ⟶ Y) (h : AlmostSurelyEq p f g) :
    p ≫ Δ[X] ≫ (X ◁ f) = p ≫ Δ[X] ≫ (X ◁ g) :=
  (almostSurelyEq_iff_copy_whiskerLeft p f g).1 h

example {X Y : C} (γ : 𝟙_ C ⟶ X ⊗ Y) (g : X ⟶ Y) (h : IsConditional γ ((ρ_ X).hom ≫ g)) :
    γ = marginalFst γ ≫ Δ[X] ≫ (X ◁ g) :=
  (isConditional_rightUnitor_comp_iff γ g).1 h

end CopyDiscard

section Markov

variable [MarkovCategory C]

example {A X Y : C} (p : A ⟶ X) (f : X ⟶ Y) : marginalFst (p ≫ Δ[X] ≫ (X ◁ f)) = p :=
  MarkovCategory.marginalFst_comp_copy_whiskerLeft p f

end Markov

section Causal

variable [CausalCategory C] [HasConditionals C]

example (X Y : Under (𝟙_ C))
    (γ : {γ : 𝟙_ C ⟶ X.right ⊗ Y.right // marginalFst γ = X.hom ∧ marginalSnd γ = Y.hom}) :
    γ.1 = X.hom ≫ Δ[X.right] ≫ (X.right ◁ (ProbStoch.couplingHom X Y γ).right) :=
  ProbStoch.couplingHom_spec X Y γ

example {X Y : Under (𝟙_ C)} (f : X ⟶ Y) :
    (ProbStoch.homEquivCoupling X Y ((Quotient.functor (probStochRel C)).map f)).1 =
      X.hom ≫ Δ[X.right] ≫ (X.right ◁ f.right) :=
  ProbStoch.homEquivCoupling_map f

example {X Y : Under (𝟙_ C)} (f : X ⟶ Y) :
    (ProbStoch.homEquivCoupling X Y ((Quotient.functor (probStochRel C)).map f)).1 =
      X.hom ≫ Δ[X.right] ≫ (X.right ◁ f.right) :=
  rfl

example (X Y : Under (𝟙_ C))
    (g : (Quotient.functor (probStochRel C)).obj X ⟶ (Quotient.functor (probStochRel C)).obj Y) :
    (ProbStoch.homEquivCoupling X Y).symm (ProbStoch.homEquivCoupling X Y g) = g :=
  (ProbStoch.homEquivCoupling X Y).symm_apply_apply g

example (X Y : Under (𝟙_ C))
    (γ : {γ : 𝟙_ C ⟶ X.right ⊗ Y.right // marginalFst γ = X.hom ∧ marginalSnd γ = Y.hom}) :
    ProbStoch.homEquivCoupling X Y ((ProbStoch.homEquivCoupling X Y).symm γ) = γ :=
  (ProbStoch.homEquivCoupling X Y).apply_symm_apply γ

example (X Y : Under (𝟙_ C))
    (g : (Quotient.functor (probStochRel C)).obj X ⟶ (Quotient.functor (probStochRel C)).obj Y) :
    marginalFst (ProbStoch.homEquivCoupling X Y g).1 = X.hom :=
  (ProbStoch.homEquivCoupling X Y g).2.1

example (X Y : Under (𝟙_ C))
    (g : (Quotient.functor (probStochRel C)).obj X ⟶ (Quotient.functor (probStochRel C)).obj Y) :
    marginalSnd (ProbStoch.homEquivCoupling X Y g).1 = Y.hom :=
  (ProbStoch.homEquivCoupling X Y g).2.2

end Causal

section MarkovUser

variable [MarkovCategory C] [HasConditionals C]

attribute [local instance] CausalCategory.ofHasConditionals

noncomputable example (X Y : Under (𝟙_ C)) :=
  ProbStoch.homEquivCoupling X Y

end MarkovUser

end CategoryTheory
