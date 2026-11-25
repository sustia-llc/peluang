/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Quotient
public import Peluang.Causal
public import Peluang.Monoidal.Quotient
public import Peluang.Monoidal.Under

/-!
# The category of probability spaces of a causal Markov category

The quotient of the category `Under (𝟙_ C)` of states of a causal Markov category `C` by almost
sure equality with respect to the state of the domain.

## Main definitions

* `probStochRel` - the relation on the morphisms of `Under (𝟙_ C)`, for a copy-discard category
  `C`: `f g : X ⟶ Y` are related when `f.right` and `g.right` are `X.hom`-almost surely equal
  (Fritz 2020, Def. 13.8).
* `ProbStoch` - the quotient of `Under (𝟙_ C)` by `probStochRel C`, for a causal Markov category
  `C` (Fritz 2020, Def. 13.8).

## Main results

* `CopyDiscardCategory.AlmostSurelyEq.tensorHom` - the tensor product of a `p`-almost surely
  equal pair and a `q`-almost surely equal pair is `(p ⊗ₘ q)`-almost surely equal
  (Fritz 2020, the sentence after Lemma 13.5).
* `probStochRel.congruence` - in a causal Markov category `C`, `probStochRel C` is a congruence
  (Fritz 2020, Prop. 13.9 (a)).
* `ProbStoch.functor_map_eq_iff` - two morphisms `f g : X ⟶ Y` of `Under (𝟙_ C)` have the same
  image in `ProbStoch C` if and only if `f.right` and `g.right` are `X.hom`-almost surely equal
  (Fritz 2020, Def. 13.8).
* `probStochRel.isStableUnderWhisker` - in a copy-discard category `C`, `probStochRel C` is
  stable under the whiskerings of `Under (𝟙_ C)` (Fritz 2020, Prop. 13.9 (a)).
* `ProbStoch.functor_map_tensorHom` - for a causal Markov category `C` and morphisms `f` and `g`
  of `Under (𝟙_ C)`, `Quotient.functor (probStochRel C)` sends `f ⊗ₘ g` to the tensor product of
  the images of `f` and `g` (Fritz 2020, Prop. 13.9 (a)).

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

/-- For `p : A ⟶ X`, `q : B ⟶ W`, `p`-almost surely equal `f₁ f₂ : X ⟶ Y` and `q`-almost surely
equal `g₁ g₂ : W ⟶ Z`, `f₁ ⊗ₘ g₁` and `f₂ ⊗ₘ g₂` are `(p ⊗ₘ q)`-almost surely equal
(Fritz 2020, the sentence after Lemma 13.5). -/
theorem AlmostSurelyEq.tensorHom {A B X Y W Z : C} {p : A ⟶ X} {q : B ⟶ W}
    {f₁ f₂ : X ⟶ Y} {g₁ g₂ : W ⟶ Z} (hf : AlmostSurelyEq p f₁ f₂)
    (hg : AlmostSurelyEq q g₁ g₂) :
    AlmostSurelyEq (p ⊗ₘ q) (f₁ ⊗ₘ g₁) (f₂ ⊗ₘ g₂) := by
  unfold AlmostSurelyEq at hf hg ⊢
  have e : ∀ (f : X ⟶ Y) (g : W ⟶ Z), tensorμ X X W W ≫ ((f ⊗ₘ g) ▷ (X ⊗ W)) =
      ((f ▷ X) ⊗ₘ (g ▷ W)) ≫ tensorμ Y X Z W := by
    intro f g
    have := tensorμ_natural f (𝟙 X) g (𝟙 W)
    rw [id_tensorHom_id, tensorHom_id, tensorHom_id, tensorHom_id] at this
    exact this.symm
  rw [copy_tensor]
  simp only [Category.assoc]
  rw [e, e]
  simp only [tensorHom_comp_tensorHom_assoc]
  rw [hf, hg]

end CopyDiscardCategory

/-- For a copy-discard category `C`, the relation on the morphisms of `Under (𝟙_ C)`:
`f g : X ⟶ Y` are related when `f.right` and `g.right` are `X.hom`-almost surely equal
(Fritz 2020, Def. 13.8). -/
def probStochRel (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    [CopyDiscardCategory C] : HomRel (Under (𝟙_ C)) :=
  fun X _ f g ↦ AlmostSurelyEq X.hom f.right g.right

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- For a causal Markov category `C`, `probStochRel C` is a congruence on `Under (𝟙_ C)`
(Fritz 2020, Prop. 13.9 (a)). -/
instance probStochRel.congruence [CausalCategory C] : Congruence (probStochRel C) where
  comp_left {X Y _} f g g' h := by
    have h' : AlmostSurelyEq (X.hom ≫ f.right) g.right g'.right := by
      rw [Under.w f]
      exact h
    exact h'.of_comp
  comp_right g h := AlmostSurelyEq.comp h g.right
  equivalence {X _} :=
    { refl := fun f => (almostSurelyEq_equivalence X.hom).refl f.right
      symm := fun h => (almostSurelyEq_equivalence X.hom).symm h
      trans := fun h₁ h₂ => (almostSurelyEq_equivalence X.hom).trans h₁ h₂ }

/-- For a causal Markov category `C`, the quotient of the category `Under (𝟙_ C)` of states of
`C` by `probStochRel C` (Fritz 2020, Def. 13.8). -/
abbrev ProbStoch (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    [CausalCategory C] : Type _ := Quotient (probStochRel C)

/-- For a causal Markov category `C` and morphisms `f g : X ⟶ Y` of `Under (𝟙_ C)`, the images
of `f` and `g` under `Quotient.functor (probStochRel C)` are equal if and only if `f.right` and
`g.right` are `X.hom`-almost surely equal (Fritz 2020, Def. 13.8). -/
theorem ProbStoch.functor_map_eq_iff [CausalCategory C] {X Y : Under (𝟙_ C)} (f g : X ⟶ Y) :
    (Quotient.functor (probStochRel C)).map f = (Quotient.functor (probStochRel C)).map g ↔
      AlmostSurelyEq X.hom f.right g.right :=
  Quotient.functor_map_eq_iff (probStochRel C) f g

/-- For a copy-discard category `C`, `probStochRel C` is stable under the whiskerings of
`Under (𝟙_ C)`: for morphisms `f g : Y ⟶ Z` of `Under (𝟙_ C)` with `f.right` and `g.right`
`Y.hom`-almost surely equal and an object `X`, `X ◁ f` and `X ◁ g` are related, and `f ▷ X` and
`g ▷ X` are related (Fritz 2020, Prop. 13.9 (a)). -/
instance probStochRel.isStableUnderWhisker [CopyDiscardCategory C] :
    HomRel.IsStableUnderWhisker (probStochRel C) where
  whiskerLeft X {_ _ _ _} h := by
    have key := (((almostSurelyEq_equivalence X.hom).refl (𝟙 X.right)).tensorHom h).precomp
      (λ_ (𝟙_ C)).inv
    simp only [id_tensorHom] at key
    exact key
  whiskerRight {X _ _ _} Z h := by
    have key := (AlmostSurelyEq.tensorHom h
      ((almostSurelyEq_equivalence Z.hom).refl (𝟙 Z.right))).precomp (λ_ (𝟙_ C)).inv
    simp only [tensorHom_id] at key
    exact key

/-- For a causal Markov category `C` and morphisms `f : X ⟶ Y` and `g : X' ⟶ Y'` of
`Under (𝟙_ C)`, `Quotient.functor (probStochRel C)` sends `f ⊗ₘ g` to the tensor product in
`ProbStoch C` of the images of `f` and `g` (Fritz 2020, Prop. 13.9 (a)). -/
theorem ProbStoch.functor_map_tensorHom [CausalCategory C] {X Y X' Y' : Under (𝟙_ C)}
    (f : X ⟶ Y) (g : X' ⟶ Y') :
    (Quotient.functor (probStochRel C)).map (f ⊗ₘ g) =
      (Quotient.functor (probStochRel C)).map f ⊗ₘ (Quotient.functor (probStochRel C)).map g :=
  Quotient.functor_map_tensorHom (probStochRel C) f g

end CategoryTheory
