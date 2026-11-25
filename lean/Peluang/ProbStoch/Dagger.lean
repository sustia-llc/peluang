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
# The dagger on the morphisms of the category of probability spaces

The map on the morphisms of `ProbStoch C` that sends the class of a morphism of states to the
class of its Bayesian inverses, for a causal Markov category `C` with conditionals.

## Main definitions

* `ProbStoch.bayesInv` - a Bayesian inverse `Y ⟶ X` of a morphism `f : X ⟶ Y` of `Under (𝟙_ C)`
  with respect to `X.hom` (Fritz 2020, Remark 13.10, equation (13.2)).
* `ProbStoch.dagger` - the map `(X ⟶ Y) → (Y ⟶ X)` on the morphisms of `ProbStoch C` that sends
  the class of `f` to the class of `ProbStoch.bayesInv f` (Fritz 2020, Remark 13.10).

## Main results

* `CopyDiscardCategory.IsBayesianInverse.almostSurelyEq_of_almostSurelyEq` - in a copy-discard
  category, Bayesian inverses with respect to `p` of two `p`-almost surely equal morphisms
  `f₁` and `f₂` are `p ≫ f₁`-almost surely equal (Fritz 2020, Remark 13.10).
* `ProbStoch.isBayesianInverse_bayesInv` - `(ProbStoch.bayesInv f).right` is a Bayesian inverse
  of `f.right` with respect to `X.hom` (Fritz 2020, Remark 13.10, equation (13.2)).
* `ProbStoch.dagger_map` - `ProbStoch.dagger` sends the class of `f` to the class of each
  morphism `g` of `Under (𝟙_ C)` with `g.right` a Bayesian inverse of `f.right` with respect to
  `X.hom` (Fritz 2020, Remark 13.10).
* `ProbStoch.dagger_id` - `ProbStoch.dagger (𝟙 X) = 𝟙 X` (Fritz 2020, Remark 13.10,
  footnote 28).
* `ProbStoch.dagger_comp` - `ProbStoch.dagger (f ≫ g) = ProbStoch.dagger g ≫ ProbStoch.dagger f`
  (Fritz 2020, Remark 13.10, footnote 28).
* `ProbStoch.dagger_dagger` - `ProbStoch.dagger (ProbStoch.dagger f) = f`
  (Fritz 2020, Remark 13.10, footnote 28).

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

namespace CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

/-- In a copy-discard category, for `p : A ⟶ X`, `p`-almost surely equal `f₁ f₂ : X ⟶ Y`, a
Bayesian inverse `g₁` of `f₁` with respect to `p` and a Bayesian inverse `g₂` of `f₂` with
respect to `p`, `g₁` and `g₂` are `p ≫ f₁`-almost surely equal (Fritz 2020, Remark 13.10). -/
theorem IsBayesianInverse.almostSurelyEq_of_almostSurelyEq {A X Y : C} {p : A ⟶ X}
    {f₁ f₂ : X ⟶ Y} {g₁ g₂ : Y ⟶ X} (hf : AlmostSurelyEq p f₁ f₂)
    (h₁ : IsBayesianInverse p f₁ g₁) (h₂ : IsBayesianInverse p f₂ g₂) :
    AlmostSurelyEq (p ≫ f₁) g₁ g₂ :=
  h₁.unique_as (IsBayesianInverse.congr ((almostSurelyEq_equivalence p).symm hf)
    ((almostSurelyEq_equivalence (p ≫ f₂)).refl g₂) h₂)

end CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CausalCategory C]
  [HasConditionals C]

/-- For a causal Markov category `C` with conditionals and a morphism `f : X ⟶ Y` of
`Under (𝟙_ C)`, a morphism `Y ⟶ X` of `Under (𝟙_ C)` whose underlying morphism is a Bayesian
inverse of `f.right` with respect to `X.hom` (Fritz 2020, Remark 13.10, equation (13.2)). -/
noncomputable def ProbStoch.bayesInv {X Y : Under (𝟙_ C)} (f : X ⟶ Y) : Y ⟶ X :=
  Under.homMk (Classical.choose (exists_isBayesianInverse X.hom f.right)) (by
    have e := (Classical.choose_spec (exists_isBayesianInverse X.hom f.right)).comp_eq
    rw [← Under.w f, Category.assoc]
    exact e)

/-- For a causal Markov category `C` with conditionals and a morphism `f : X ⟶ Y` of
`Under (𝟙_ C)`, `(ProbStoch.bayesInv f).right` is a Bayesian inverse of `f.right` with respect
to `X.hom` (Fritz 2020, Remark 13.10, equation (13.2)). -/
theorem ProbStoch.isBayesianInverse_bayesInv {X Y : Under (𝟙_ C)} (f : X ⟶ Y) :
    IsBayesianInverse X.hom f.right (ProbStoch.bayesInv f).right :=
  Classical.choose_spec (exists_isBayesianInverse X.hom f.right)

/-- For a causal Markov category `C` with conditionals and objects `X Y` of `ProbStoch C`, the
map `(X ⟶ Y) → (Y ⟶ X)` that sends the class of a morphism `f` of `Under (𝟙_ C)` to the class
of `ProbStoch.bayesInv f` (Fritz 2020, Remark 13.10). -/
noncomputable def ProbStoch.dagger {X Y : ProbStoch C} (f : X ⟶ Y) : Y ⟶ X :=
  Quot.liftOn f (fun f' => (Quotient.functor (probStochRel C)).map (ProbStoch.bayesInv f')) (by
    intro f₁ f₂ h
    have h' : probStochRel C f₁ f₂ := (HomRel.compClosure_iff_self _ f₁ f₂).1 h
    apply Quotient.sound
    have key := IsBayesianInverse.almostSurelyEq_of_almostSurelyEq h'
      (ProbStoch.isBayesianInverse_bayesInv f₁) (ProbStoch.isBayesianInverse_bayesInv f₂)
    rw [Under.w f₁] at key
    exact key)

/-- For a causal Markov category `C` with conditionals and morphisms `f : X ⟶ Y` and
`g : Y ⟶ X` of `Under (𝟙_ C)` with `g.right` a Bayesian inverse of `f.right` with respect to
`X.hom`, `ProbStoch.dagger` sends the image of `f` under `Quotient.functor (probStochRel C)` to
the image of `g` (Fritz 2020, Remark 13.10). -/
theorem ProbStoch.dagger_map {X Y : Under (𝟙_ C)} (f : X ⟶ Y) (g : Y ⟶ X)
    (h : IsBayesianInverse X.hom f.right g.right) :
    ProbStoch.dagger ((Quotient.functor (probStochRel C)).map f) =
      (Quotient.functor (probStochRel C)).map g := by
  change (Quotient.functor (probStochRel C)).map (ProbStoch.bayesInv f) = _
  apply Quotient.sound
  have key := (ProbStoch.isBayesianInverse_bayesInv f).unique_as h
  rw [Under.w f] at key
  exact key

/-- For a causal Markov category `C` with conditionals and an object `X` of `ProbStoch C`,
`ProbStoch.dagger (𝟙 X) = 𝟙 X` (Fritz 2020, Remark 13.10, footnote 28). -/
theorem ProbStoch.dagger_id (X : ProbStoch C) : ProbStoch.dagger (𝟙 X) = 𝟙 X :=
  ProbStoch.dagger_map (𝟙 X.as) (𝟙 X.as) (isBayesianInverse_id _)

/-- For a causal Markov category `C` with conditionals and morphisms `f : X ⟶ Y` and
`g : Y ⟶ Z` of `ProbStoch C`, `ProbStoch.dagger (f ≫ g) = ProbStoch.dagger g ≫ ProbStoch.dagger f`
(Fritz 2020, Remark 13.10, footnote 28). -/
theorem ProbStoch.dagger_comp {X Y Z : ProbStoch C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ProbStoch.dagger (f ≫ g) = ProbStoch.dagger g ≫ ProbStoch.dagger f := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  have hf := ProbStoch.isBayesianInverse_bayesInv f
  have hg := ProbStoch.isBayesianInverse_bayesInv g
  rw [← Under.w f] at hg
  exact ProbStoch.dagger_map (f ≫ g) (ProbStoch.bayesInv g ≫ ProbStoch.bayesInv f) (hf.comp hg)

/-- For a causal Markov category `C` with conditionals and a morphism `f : X ⟶ Y` of
`ProbStoch C`, `ProbStoch.dagger (ProbStoch.dagger f) = f`
(Fritz 2020, Remark 13.10, footnote 28). -/
theorem ProbStoch.dagger_dagger {X Y : ProbStoch C} (f : X ⟶ Y) :
    ProbStoch.dagger (ProbStoch.dagger f) = f := by
  obtain ⟨f⟩ := f
  have hs := (ProbStoch.isBayesianInverse_bayesInv f).symm
  rw [Under.w f] at hs
  exact ProbStoch.dagger_map (ProbStoch.bayesInv f) f hs

end CategoryTheory
