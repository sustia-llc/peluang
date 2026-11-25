/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Quotient
public import Peluang.BayesianInverse
public import Peluang.ProbStoch.Basic

/-!
# The morphisms of the category of probability spaces as couplings

The bijection between the morphisms `X ⟶ Y` of `ProbStoch C` and the morphisms
`𝟙_ C ⟶ X.right ⊗ Y.right` of `C` with first marginal `X.hom` and second marginal `Y.hom`, for a
causal Markov category `C` with conditionals.

## Main definitions

* `ProbStoch.couplingHom` - a morphism `X ⟶ Y` of `Under (𝟙_ C)` for a morphism
  `γ : 𝟙_ C ⟶ X.right ⊗ Y.right` with marginals `X.hom` and `Y.hom`
  (Fritz 2020, Prop. 13.9 (b)).
* `ProbStoch.homEquivCoupling` - the bijection that sends the class of a morphism `f : X ⟶ Y` of
  `Under (𝟙_ C)` to `X.hom ≫ Δ[X.right] ≫ (X.right ◁ f.right)` (Fritz 2020, Prop. 13.9 (b)).

## Main results

* `CopyDiscardCategory.marginalSnd_comp_copy_whiskerLeft` - in a copy-discard category, the
  second marginal of `p ≫ Δ[X] ≫ (X ◁ f)` is `p ≫ f`.
* `CopyDiscardCategory.almostSurelyEq_iff_copy_whiskerLeft` - in a copy-discard category, `f` and
  `g` are `p`-almost surely equal iff `p ≫ Δ[X] ≫ (X ◁ f) = p ≫ Δ[X] ≫ (X ◁ g)`.
* `CopyDiscardCategory.isConditional_rightUnitor_comp_iff` - in a copy-discard category,
  `(ρ_ X).hom ≫ g` is a conditional of `γ : 𝟙_ C ⟶ X ⊗ Y` on `X` iff
  `γ = marginalFst γ ≫ Δ[X] ≫ (X ◁ g)`.
* `MarkovCategory.marginalFst_comp_copy_whiskerLeft` - in a Markov category, the first marginal
  of `p ≫ Δ[X] ≫ (X ◁ f)` is `p`.
* `ProbStoch.couplingHom_spec` - `γ = X.hom ≫ Δ[X.right] ≫ (X.right ◁ g.right)` for
  `g = ProbStoch.couplingHom X Y γ` (Fritz 2020, Prop. 13.9 (b)).
* `ProbStoch.homEquivCoupling_map` - the value of `ProbStoch.homEquivCoupling X Y` at the class
  of `f` is `X.hom ≫ Δ[X.right] ≫ (X.right ◁ f.right)` (Fritz 2020, Prop. 13.9 (b)).

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

namespace CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

-- WITNESS: none (step of ProbStoch.homEquivCoupling; witnessed through homEquivCoupling_map)
/-- In a copy-discard category, for `p : A ⟶ X` and `f : X ⟶ Y`, the second marginal of
`p ≫ Δ[X] ≫ (X ◁ f)` is `p ≫ f`. -/
theorem marginalSnd_comp_copy_whiskerLeft {A X Y : C} (p : A ⟶ X) (f : X ⟶ Y) :
    marginalSnd (p ≫ Δ[X] ≫ (X ◁ f)) = p ≫ f := by
  rw [marginalSnd_comp, marginalSnd_comp, marginalSnd_whiskerLeft, counit_comul_assoc,
    Iso.inv_hom_id_assoc]

-- WITNESS: none (step of ProbStoch.homEquivCoupling; witnessed through homEquivCoupling_map)
/-- In a copy-discard category, for `p : A ⟶ X` and `f g : X ⟶ Y`, `f` and `g` are `p`-almost
surely equal iff `p ≫ Δ[X] ≫ (X ◁ f) = p ≫ Δ[X] ≫ (X ◁ g)`. -/
theorem almostSurelyEq_iff_copy_whiskerLeft {A X Y : C} (p : A ⟶ X) (f g : X ⟶ Y) :
    AlmostSurelyEq p f g ↔ p ≫ Δ[X] ≫ (X ◁ f) = p ≫ Δ[X] ≫ (X ◁ g) := by
  unfold AlmostSurelyEq
  constructor
  · intro h
    rw [copy_comp_whiskerLeft_eq f, copy_comp_whiskerLeft_eq g, reassoc_of% h]
  · intro h
    rw [copy_comp_whiskerRight_eq f, copy_comp_whiskerRight_eq g, reassoc_of% h]

-- WITNESS: none (step of ProbStoch.homEquivCoupling; witnessed through homEquivCoupling_map)
/-- In a copy-discard category, for `γ : 𝟙_ C ⟶ X ⊗ Y` and `g : X ⟶ Y`, `(ρ_ X).hom ≫ g` is a
conditional of `γ` on `X` iff `γ = marginalFst γ ≫ Δ[X] ≫ (X ◁ g)`. -/
theorem isConditional_rightUnitor_comp_iff {X Y : C} (γ : 𝟙_ C ⟶ X ⊗ Y) (g : X ⟶ Y) :
    IsConditional γ ((ρ_ X).hom ≫ g) ↔ γ = marginalFst γ ≫ Δ[X] ≫ (X ◁ g) := by
  unfold IsConditional
  rw [copy_unit]
  have e : ∀ m : 𝟙_ C ⟶ X, (λ_ (𝟙_ C)).inv ≫ (m ▷ 𝟙_ C) ≫ (Δ[X] ▷ 𝟙_ C) ≫
      (α_ X X (𝟙_ C)).hom ≫ (X ◁ ((ρ_ X).hom ≫ g)) = m ≫ Δ[X] ≫ (X ◁ g) := by
    intro m
    monoidal
  rw [e]

end CopyDiscardCategory

section Markov

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

-- WITNESS: none (step of ProbStoch.homEquivCoupling; witnessed through homEquivCoupling_map)
/-- In a Markov category, for `p : A ⟶ X` and `f : X ⟶ Y`, the first marginal of
`p ≫ Δ[X] ≫ (X ◁ f)` is `p`. -/
theorem MarkovCategory.marginalFst_comp_copy_whiskerLeft {A X Y : C} (p : A ⟶ X) (f : X ⟶ Y) :
    marginalFst (p ≫ Δ[X] ≫ (X ◁ f)) = p := by
  rw [marginalFst_comp, marginalFst_comp, MarkovCategory.marginalFst_whiskerLeft,
    comul_counit_assoc, Iso.inv_hom_id, Category.comp_id]

end Markov

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CausalCategory C]
  [HasConditionals C]

/-- For a causal Markov category `C` with conditionals, objects `X Y` of `Under (𝟙_ C)` and a
morphism `γ : 𝟙_ C ⟶ X.right ⊗ Y.right` with first marginal `X.hom` and second marginal `Y.hom`,
a morphism `X ⟶ Y` of `Under (𝟙_ C)` whose underlying morphism is `(ρ_ X.right).inv` followed
by a conditional of `γ` on `X.right` (Fritz 2020, Prop. 13.9 (b)). -/
noncomputable def ProbStoch.couplingHom (X Y : Under (𝟙_ C))
    (γ : {γ : 𝟙_ C ⟶ X.right ⊗ Y.right // marginalFst γ = X.hom ∧ marginalSnd γ = Y.hom}) :
    X ⟶ Y :=
  Under.homMk ((ρ_ X.right).inv ≫ Classical.choose (HasConditionals.exists_isConditional γ.1)) (by
    have hk := Classical.choose_spec (HasConditionals.exists_isConditional γ.1)
    rw [← Iso.hom_inv_id_assoc (ρ_ X.right)
      (Classical.choose (HasConditionals.exists_isConditional γ.1)),
      isConditional_rightUnitor_comp_iff, γ.2.1] at hk
    rw [← marginalSnd_comp_copy_whiskerLeft, ← hk, γ.2.2])

-- WITNESS: none (a chosen morphism of states; witnessed through homEquivCoupling_map)
/-- For a causal Markov category `C` with conditionals, objects `X Y` of `Under (𝟙_ C)` and a
morphism `γ : 𝟙_ C ⟶ X.right ⊗ Y.right` with first marginal `X.hom` and second marginal `Y.hom`,
`γ = X.hom ≫ Δ[X.right] ≫ (X.right ◁ g.right)` for `g = ProbStoch.couplingHom X Y γ`
(Fritz 2020, Prop. 13.9 (b)). -/
theorem ProbStoch.couplingHom_spec (X Y : Under (𝟙_ C))
    (γ : {γ : 𝟙_ C ⟶ X.right ⊗ Y.right // marginalFst γ = X.hom ∧ marginalSnd γ = Y.hom}) :
    γ.1 = X.hom ≫ Δ[X.right] ≫ (X.right ◁ (ProbStoch.couplingHom X Y γ).right) := by
  have hk := Classical.choose_spec (HasConditionals.exists_isConditional γ.1)
  rw [← Iso.hom_inv_id_assoc (ρ_ X.right)
    (Classical.choose (HasConditionals.exists_isConditional γ.1)),
    isConditional_rightUnitor_comp_iff, γ.2.1] at hk
  exact hk

/-- For a causal Markov category `C` with conditionals and objects `X Y` of `Under (𝟙_ C)`, the
bijection between the morphisms from the image of `X` to the image of `Y` under
`Quotient.functor (probStochRel C)` and the morphisms `γ : 𝟙_ C ⟶ X.right ⊗ Y.right` with first
marginal `X.hom` and second marginal `Y.hom`. It sends the class of a morphism `f` of
`Under (𝟙_ C)` to `X.hom ≫ Δ[X.right] ≫ (X.right ◁ f.right)`, and its inverse sends `γ` to the
class of `ProbStoch.couplingHom X Y γ` (Fritz 2020, Prop. 13.9 (b)). -/
noncomputable def ProbStoch.homEquivCoupling (X Y : Under (𝟙_ C)) :
    ((Quotient.functor (probStochRel C)).obj X ⟶ (Quotient.functor (probStochRel C)).obj Y) ≃
      {γ : 𝟙_ C ⟶ X.right ⊗ Y.right // marginalFst γ = X.hom ∧ marginalSnd γ = Y.hom} where
  toFun f := Quot.liftOn f
    (fun f' => ⟨X.hom ≫ Δ[X.right] ≫ (X.right ◁ f'.right),
      MarkovCategory.marginalFst_comp_copy_whiskerLeft _ _,
      (marginalSnd_comp_copy_whiskerLeft _ _).trans (Under.w f')⟩) (by
    intro f₁ f₂ h
    have h' : probStochRel C f₁ f₂ := (HomRel.compClosure_iff_self _ f₁ f₂).1 h
    exact Subtype.ext ((almostSurelyEq_iff_copy_whiskerLeft _ _ _).1 h'))
  invFun γ := (Quotient.functor (probStochRel C)).map (ProbStoch.couplingHom X Y γ)
  left_inv f := by
    obtain ⟨f⟩ := f
    apply Quotient.sound
    exact (almostSurelyEq_iff_copy_whiskerLeft _ _ _).2 (ProbStoch.couplingHom_spec X Y _).symm
  right_inv γ := Subtype.ext (ProbStoch.couplingHom_spec X Y γ).symm

/-- For a causal Markov category `C` with conditionals and a morphism `f : X ⟶ Y` of
`Under (𝟙_ C)`, the value of `ProbStoch.homEquivCoupling X Y` at the image of `f` under
`Quotient.functor (probStochRel C)` is `X.hom ≫ Δ[X.right] ≫ (X.right ◁ f.right)`
(Fritz 2020, Prop. 13.9 (b)). -/
theorem ProbStoch.homEquivCoupling_map {X Y : Under (𝟙_ C)} (f : X ⟶ Y) :
    (ProbStoch.homEquivCoupling X Y ((Quotient.functor (probStochRel C)).map f)).1 =
      X.hom ≫ Δ[X.right] ≫ (X.right ◁ f.right) := rfl

end CategoryTheory
