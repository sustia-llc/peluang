/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Conditional

/-!
# Bayesian inverses

Bayesian inverses of morphisms with respect to a morphism into their domain, in a copy-discard
category.

## Main definitions

* `CopyDiscardCategory.IsBayesianInverse` - `g : Y ⟶ X` is a Bayesian inverse of `f : X ⟶ Y`
  with respect to `p : A ⟶ X` (Fritz 2020, Remark 13.10, equation (13.2); Cho–Jacobs 2019,
  equation (5)).

## Main results

* `CopyDiscardCategory.IsBayesianInverse.unique_as` - two Bayesian inverses of `f` with respect
  to `p` are `p ≫ f`-almost surely equal (Fritz 2020, Remark 13.10).
* `CopyDiscardCategory.isBayesianInverse_id` - `𝟙 X` is a Bayesian inverse of `𝟙 X` with
  respect to every `p : A ⟶ X` (Fritz 2020, Remark 13.10).
* `CopyDiscardCategory.IsBayesianInverse.comp` - a Bayesian inverse `f'` of `f` with respect to
  `p` and a Bayesian inverse `g'` of `g` with respect to `p ≫ f` compose to a Bayesian inverse
  `g' ≫ f'` of `f ≫ g` with respect to `p` (Fritz 2020, Remark 13.10).
* `CopyDiscardCategory.IsBayesianInverse.congr` - being a Bayesian inverse with respect to `p`
  is preserved by replacing `f` with a `p`-almost surely equal morphism and `g` with a
  `p ≫ f`-almost surely equal morphism (Fritz 2020, Remark 13.10).
* `CopyDiscardCategory.isBayesianInverse_iff_isConditional` - for `p : 𝟙_ C ⟶ X`, `g` is a
  Bayesian inverse of `f` with respect to `p` iff `(ρ_ Y).hom ≫ g` is a conditional of
  `p ≫ Δ[X] ≫ (f ▷ X)` on `Y` (Fritz 2020, Remark 13.10).
* `CopyDiscardCategory.exists_isBayesianInverse` - in a copy-discard category with
  conditionals, every `f : X ⟶ Y` has a Bayesian inverse with respect to every `p : 𝟙_ C ⟶ X`
  (Fritz 2020, Remark 13.10).
* `CopyDiscardCategory.IsBayesianInverse.tensor` - the tensor product of Bayesian inverses is
  a Bayesian inverse of the tensor product, with respect to the tensor product
  (Fritz 2020, Remark 13.10).
* `CopyDiscardCategory.IsBayesianInverse.comp_eq` - in a Markov category, a Bayesian inverse
  `g` of `f` with respect to `p` satisfies `p ≫ f ≫ g = p` (Fritz 2020, Remark 13.10).
* `CopyDiscardCategory.IsBayesianInverse.symm` - in a Markov category, `f` is a Bayesian
  inverse with respect to `p ≫ f` of each of its Bayesian inverses with respect to `p`
  (Fritz 2020, Remark 13.10).

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
* [Cho and Jacobs, *Disintegration and Bayesian inversion via string
  diagrams*][cho_jacobs_2019]
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace CopyDiscardCategory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

/-- For `p : A ⟶ X`, `f : X ⟶ Y` and `g : Y ⟶ X`, `g` is a Bayesian inverse of `f` with respect
to `p`: `p ≫ Δ[X] ≫ (X ◁ f) = (p ≫ f) ≫ Δ[Y] ≫ (g ▷ Y)` (Fritz 2020, Remark 13.10,
equation (13.2); Cho–Jacobs 2019, equation (5)). -/
def IsBayesianInverse {A X Y : C} (p : A ⟶ X) (f : X ⟶ Y) (g : Y ⟶ X) : Prop :=
  p ≫ Δ[X] ≫ (X ◁ f) = (p ≫ f) ≫ Δ[Y] ≫ (g ▷ Y)

-- WITNESS: none (step of isBayesianInverse_iff_isConditional; witnessed through it)
/-- For `f : X ⟶ Y`, copying `X` and applying `f` to the right copy equals copying `X`,
applying `f` to the left copy and swapping the two outputs. -/
theorem copy_comp_whiskerLeft_eq {X Y : C} (f : X ⟶ Y) :
    Δ[X] ≫ (X ◁ f) = Δ[X] ≫ (f ▷ X) ≫ (β_ Y X).hom := by
  rw [BraidedCategory.braiding_naturality_left, IsCommComonObj.comul_comm_assoc]

-- WITNESS: none (step of isBayesianInverse_iff_isConditional; witnessed through it)
/-- For `f : X ⟶ Y`, copying `X` and applying `f` to the left copy equals copying `X`,
applying `f` to the right copy and swapping the two outputs. -/
theorem copy_comp_whiskerRight_eq {X Y : C} (f : X ⟶ Y) :
    Δ[X] ≫ (f ▷ X) = Δ[X] ≫ (X ◁ f) ≫ (β_ X Y).hom := by
  rw [BraidedCategory.braiding_naturality_right, IsCommComonObj.comul_comm_assoc]

-- WITNESS: none (step of isBayesianInverse_iff_isConditional; witnessed through it)
/-- For `p : A ⟶ X` and `f : X ⟶ Y`, the first marginal of `p ≫ Δ[X] ≫ (f ▷ X) : A ⟶ Y ⊗ X`
is `p ≫ f`. -/
theorem marginalFst_comp_copy_whiskerRight {A X Y : C} (p : A ⟶ X) (f : X ⟶ Y) :
    marginalFst (p ≫ Δ[X] ≫ (f ▷ X)) = p ≫ f := by
  simp only [marginalFst, Category.assoc]
  rw [← whisker_exchange_assoc, comul_counit_assoc, rightUnitor_naturality,
    Iso.inv_hom_id_assoc]

/-- For `p : A ⟶ X` and `f : X ⟶ Y`, any two Bayesian inverses `g₁ g₂ : Y ⟶ X` of `f` with
respect to `p` are `p ≫ f`-almost surely equal (Fritz 2020, Remark 13.10). -/
theorem IsBayesianInverse.unique_as {A X Y : C} {p : A ⟶ X} {f : X ⟶ Y} {g₁ g₂ : Y ⟶ X}
    (h₁ : IsBayesianInverse p f g₁) (h₂ : IsBayesianInverse p f g₂) :
    AlmostSurelyEq (p ≫ f) g₁ g₂ := by
  unfold IsBayesianInverse at h₁ h₂
  unfold AlmostSurelyEq
  rw [← h₁, ← h₂]

/-- For every `p : A ⟶ X`, `𝟙 X` is a Bayesian inverse of `𝟙 X` with respect to `p`
(Fritz 2020, Remark 13.10). -/
theorem isBayesianInverse_id {A X : C} (p : A ⟶ X) : IsBayesianInverse p (𝟙 X) (𝟙 X) := by
  unfold IsBayesianInverse
  simp

/-- For `p : A ⟶ X`, `f : X ⟶ Y` and `g : Y ⟶ Z`, a Bayesian inverse `f'` of `f` with respect
to `p` and a Bayesian inverse `g'` of `g` with respect to `p ≫ f`, `g' ≫ f'` is a Bayesian
inverse of `f ≫ g` with respect to `p` (Fritz 2020, Remark 13.10). -/
theorem IsBayesianInverse.comp {A X Y Z : C} {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : Y ⟶ X} {g' : Z ⟶ Y} (hf : IsBayesianInverse p f f')
    (hg : IsBayesianInverse (p ≫ f) g g') : IsBayesianInverse p (f ≫ g) (g' ≫ f') := by
  unfold IsBayesianInverse at hf hg ⊢
  simp only [Category.assoc] at hf hg ⊢
  rw [whiskerLeft_comp, reassoc_of% hf, ← whisker_exchange, reassoc_of% hg, comp_whiskerRight]

/-- For `p : A ⟶ X`, `p`-almost surely equal `f₁ f₂ : X ⟶ Y`, `p ≫ f₁`-almost surely equal
`g₁ g₂ : Y ⟶ X` and `g₁` a Bayesian inverse of `f₁` with respect to `p`, `g₂` is a Bayesian
inverse of `f₂` with respect to `p` (Fritz 2020, Remark 13.10). -/
theorem IsBayesianInverse.congr {A X Y : C} {p : A ⟶ X} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : Y ⟶ X}
    (hf : AlmostSurelyEq p f₁ f₂) (hg : AlmostSurelyEq (p ≫ f₁) g₁ g₂)
    (h : IsBayesianInverse p f₁ g₁) : IsBayesianInverse p f₂ g₂ := by
  unfold IsBayesianInverse at h ⊢
  unfold AlmostSurelyEq at hf hg
  have e : p ≫ f₁ = p ≫ f₂ := by
    rw [← marginalFst_comp_copy_whiskerRight p f₁, ← marginalFst_comp_copy_whiskerRight p f₂, hf]
  have hf' : p ≫ Δ[X] ≫ (X ◁ f₁) = p ≫ Δ[X] ≫ (X ◁ f₂) := by
    rw [copy_comp_whiskerLeft_eq f₁, copy_comp_whiskerLeft_eq f₂, reassoc_of% hf]
  rw [← hf', ← e, ← hg]
  exact h

/-- For `p : 𝟙_ C ⟶ X`, `f : X ⟶ Y` and `g : Y ⟶ X`, `g` is a Bayesian inverse of `f` with
respect to `p` iff `(ρ_ Y).hom ≫ g : Y ⊗ 𝟙_ C ⟶ X` is a conditional of
`p ≫ Δ[X] ≫ (f ▷ X) : 𝟙_ C ⟶ Y ⊗ X` on `Y` (Fritz 2020, Remark 13.10). -/
theorem isBayesianInverse_iff_isConditional {X Y : C} (p : 𝟙_ C ⟶ X) (f : X ⟶ Y) (g : Y ⟶ X) :
    IsBayesianInverse p f g ↔ IsConditional (p ≫ Δ[X] ≫ (f ▷ X)) ((ρ_ Y).hom ≫ g) := by
  unfold IsBayesianInverse IsConditional
  rw [marginalFst_comp_copy_whiskerRight, copy_unit]
  have e : (λ_ (𝟙_ C)).inv ≫ ((p ≫ f) ▷ 𝟙_ C) ≫ (Δ[Y] ▷ 𝟙_ C) ≫ (α_ Y Y (𝟙_ C)).hom ≫
      (Y ◁ ((ρ_ Y).hom ≫ g)) = (p ≫ f) ≫ Δ[Y] ≫ (Y ◁ g) := by
    monoidal
  rw [e]
  constructor
  · intro h
    rw [copy_comp_whiskerRight_eq f, copy_comp_whiskerLeft_eq g]
    have := congrArg (· ≫ (β_ X Y).hom) h
    simpa only [Category.assoc] using this
  · intro h
    rw [copy_comp_whiskerLeft_eq f, copy_comp_whiskerRight_eq g]
    have := congrArg (· ≫ (β_ Y X).hom) h
    simpa only [Category.assoc] using this

-- WITNESS: none (witnessed through FinStoch.isBayesianInverse_bayesInv)
/-- In a copy-discard category with conditionals, every `f : X ⟶ Y` has a Bayesian inverse
with respect to every `p : 𝟙_ C ⟶ X` (Fritz 2020, Remark 13.10). -/
theorem exists_isBayesianInverse [HasConditionals C] {X Y : C} (p : 𝟙_ C ⟶ X) (f : X ⟶ Y) :
    ∃ g, IsBayesianInverse p f g := by
  obtain ⟨k, hk⟩ := HasConditionals.exists_isConditional (p ≫ Δ[X] ≫ (f ▷ X))
  refine ⟨(ρ_ Y).inv ≫ k, (isBayesianInverse_iff_isConditional p f _).2 ?_⟩
  rwa [Iso.hom_inv_id_assoc]

/-- For `p : A ⟶ X`, `q : B ⟶ W`, a Bayesian inverse `f'` of `f : X ⟶ Y` with respect to `p`
and a Bayesian inverse `k'` of `k : W ⟶ Z` with respect to `q`, `f' ⊗ₘ k'` is a Bayesian
inverse of `f ⊗ₘ k` with respect to `p ⊗ₘ q` (Fritz 2020, Remark 13.10). -/
theorem IsBayesianInverse.tensor {A B X Y W Z : C} {p : A ⟶ X} {q : B ⟶ W}
    {f : X ⟶ Y} {k : W ⟶ Z} {f' : Y ⟶ X} {k' : Z ⟶ W}
    (hf : IsBayesianInverse p f f') (hk : IsBayesianInverse q k k') :
    IsBayesianInverse (p ⊗ₘ q) (f ⊗ₘ k) (f' ⊗ₘ k') := by
  unfold IsBayesianInverse at hf hk ⊢
  have e1 : tensorμ X X W W ≫ ((X ⊗ W) ◁ (f ⊗ₘ k)) =
      ((X ◁ f) ⊗ₘ (W ◁ k)) ≫ tensorμ X Y W Z := by
    have := tensorμ_natural (𝟙 X) f (𝟙 W) k
    rw [id_tensorHom_id, id_tensorHom, id_tensorHom, id_tensorHom] at this
    exact this.symm
  have e2 : tensorμ Y Y Z Z ≫ ((f' ⊗ₘ k') ▷ (Y ⊗ Z)) =
      ((f' ▷ Y) ⊗ₘ (k' ▷ Z)) ≫ tensorμ X Y W Z := by
    have := tensorμ_natural f' (𝟙 Y) k' (𝟙 Z)
    rw [id_tensorHom_id, tensorHom_id, tensorHom_id, tensorHom_id] at this
    exact this.symm
  rw [copy_tensor, copy_tensor]
  simp only [Category.assoc] at hf hk ⊢
  rw [e1, e2]
  simp only [tensorHom_comp_tensorHom_assoc]
  rw [hf, hk]

end CopyDiscardCategory

namespace MarkovCategory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

/-- In a Markov category, for `p : A ⟶ X`, `f : X ⟶ Y` and a Bayesian inverse `g : Y ⟶ X` of
`f` with respect to `p`, `p ≫ f ≫ g = p` (Fritz 2020, Remark 13.10). -/
theorem _root_.CategoryTheory.CopyDiscardCategory.IsBayesianInverse.comp_eq {A X Y : C}
    {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ X}
    (h : IsBayesianInverse p f g) : p ≫ f ≫ g = p := by
  unfold IsBayesianInverse at h
  have e := congrArg marginalFst h
  rw [marginalFst_comp_copy_whiskerRight] at e
  rw [← Category.assoc, ← e, marginalFst_comp, marginalFst_comp,
    MarkovCategory.marginalFst_whiskerLeft, comul_counit_assoc, Iso.inv_hom_id, Category.comp_id]

/-- In a Markov category, for `p : A ⟶ X`, `f : X ⟶ Y` and a Bayesian inverse `g : Y ⟶ X` of
`f` with respect to `p`, `f` is a Bayesian inverse of `g` with respect to `p ≫ f`
(Fritz 2020, Remark 13.10). For `h : IsBayesianInverse p f g`, `h.symm` is this theorem, and
`Eq.symm h` is equation (13.2) read right to left. -/
theorem _root_.CategoryTheory.CopyDiscardCategory.IsBayesianInverse.symm {A X Y : C}
    {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ X}
    (h : IsBayesianInverse p f g) : IsBayesianInverse (p ≫ f) g f := by
  have e : (p ≫ f) ≫ g = p := by rw [Category.assoc, IsBayesianInverse.comp_eq h]
  unfold IsBayesianInverse at h ⊢
  rw [e, copy_comp_whiskerLeft_eq g, copy_comp_whiskerRight_eq f]
  have := congrArg (· ≫ (β_ X Y).hom) h
  simpa only [Category.assoc] using this.symm

end MarkovCategory

end CategoryTheory
