/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
public import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic
public import Peluang.AlmostSure
public import Peluang.Markov.Derived

/-!
# Conditionals

Conditionals of morphisms into a tensor product, in a copy-discard category.

## Main definitions

* `CopyDiscardCategory.IsConditional` - `g : X ⊗ A ⟶ Y` is a conditional of `f : A ⟶ X ⊗ Y`
  on `X` (Fritz 2020, Def. 11.5, equation (11.4)).
* `CopyDiscardCategory.HasConditionals` - every morphism into a tensor product has a
  conditional (Fritz 2020, Def. 11.5).

## Main results

* `CopyDiscardCategory.isConditional_unique_as` - two conditionals of `f : A ⟶ X ⊗ Y` on `X`
  are almost surely equal with respect to `Δ[A] ≫ (marginalFst f ▷ A)`;
  `CopyDiscardCategory.isConditional_unique_as_unit` is its case `A = 𝟙_ C` (Fritz 2020,
  Prop. 13.7).
* `CopyDiscardCategory.isConditional_unique_as_unit` - for `ψ : 𝟙_ C ⟶ X ⊗ Y`, two
  conditionals `g₁ g₂ : X ⟶ Y` of `ψ` on `X` (entering `IsConditional` through `(ρ_ X).hom`)
  are `marginalFst ψ`-almost surely equal (Fritz 2020, Prop. 13.7).
* `CopyDiscardCategory.IsConditional.nest` - a conditional of a conditional is a conditional
  on the tensor product (Fritz 2020, Lemma 11.11).
* `CopyDiscardCategory.IsConditional.deterministic_comp` - pre-composing `f` with a
  deterministic `g` pre-composes its conditional with `X ◁ g` (Café post T16; Fritz 2020,
  Def. 10.1 and Def. 11.5).
* `MarkovCategory.IsConditional.comp_whiskerLeft` - in a Markov category, post-composing
  `f ▷ B` with `X ◁ g` post-composes its conditional with `g` (Fritz 2020, Lemma 11.12).

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace CopyDiscardCategory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

/-- For `f : A ⟶ X ⊗ Y` and `g : X ⊗ A ⟶ Y`, `g` is a conditional of `f` on `X`: `f` equals
copying `A`, applying the first marginal of `f` to the left copy, copying that `X`, and
applying `g` to the right `X` and `A` (Fritz 2020, Def. 11.5, equation (11.4)). The inputs
of `g` are ordered `X ⊗ A`. -/
def IsConditional {A X Y : C} (f : A ⟶ X ⊗ Y) (g : X ⊗ A ⟶ Y) : Prop :=
  f = Δ[A] ≫ (marginalFst f ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ g)

/-- A copy-discard category `C` has conditionals: every morphism `f : A ⟶ X ⊗ Y` of `C` has
a conditional `g : X ⊗ A ⟶ Y` on `X` (Fritz 2020, Def. 11.5). -/
class HasConditionals (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    [CopyDiscardCategory C] : Prop where
  /-- Every morphism `f : A ⟶ X ⊗ Y` has a conditional `g : X ⊗ A ⟶ Y` on `X`. -/
  exists_isConditional : ∀ {A X Y : C} (f : A ⟶ X ⊗ Y), ∃ g, IsConditional f g

-- WITNESS: none (step of isConditional_unique_as; witnessed through it)
/-- For `m : A ⟶ X` and `g : X ⊗ A ⟶ Y`, copying `A`, applying `m` to the left copy, copying
`X ⊗ A` and applying `g` to the left copy equals copying `A`, applying the conditional form
`Δ[A] ≫ (m ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ g)` to the left copy, and rearranging
`(X ⊗ Y) ⊗ A` to `Y ⊗ (X ⊗ A)`. -/
theorem copy_whiskerRight_copy_eq {A X Y : C} (m : A ⟶ X) (g : X ⊗ A ⟶ Y) :
    Δ[A] ≫ (m ▷ A) ≫ @ComonObj.comul C _ _ (X ⊗ A) (CopyDiscardCategory.comonObj (X ⊗ A)) ≫
      (g ▷ (X ⊗ A)) =
    Δ[A] ≫ ((Δ[A] ≫ (m ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ g)) ▷ A) ≫
      ((β_ X Y).hom ▷ A) ≫ (α_ Y X A).hom := by
  conv_lhs => rw [copy_tensor, tensorHom_def, ← IsCommComonObj.comul_comm X]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← comp_whiskerRight_assoc (X ◁ g), BraidedCategory.braiding_naturality_right,
    comp_whiskerRight_assoc,
    associator_naturality_left, comul_assoc_flip_assoc, BraidedCategory.braiding_tensor_right_hom]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc, ← whisker_exchange_assoc]
  simp only [tensorμ]
  monoidal

/-- For `f : A ⟶ X ⊗ Y`, any two conditionals `g₁ g₂ : X ⊗ A ⟶ Y` of `f` on `X` are almost
surely equal with respect to `Δ[A] ≫ (marginalFst f ▷ A) : A ⟶ X ⊗ A`.
`isConditional_unique_as_unit` is its case `A = 𝟙_ C` (Fritz 2020, Prop. 13.7). -/
theorem isConditional_unique_as {A X Y : C} {f : A ⟶ X ⊗ Y} {g₁ g₂ : X ⊗ A ⟶ Y}
    (h₁ : IsConditional f g₁) (h₂ : IsConditional f g₂) :
    AlmostSurelyEq (Δ[A] ≫ (marginalFst f ▷ A)) g₁ g₂ := by
  unfold AlmostSurelyEq
  unfold IsConditional at h₁ h₂
  simp only [Category.assoc]
  rw [copy_whiskerRight_copy_eq, copy_whiskerRight_copy_eq, ← h₁, ← h₂]

/-- For `ψ : 𝟙_ C ⟶ X ⊗ Y`, any two conditionals `g₁ g₂ : X ⟶ Y` of `ψ` on `X` (entering
`IsConditional` through `(ρ_ X).hom`) are `marginalFst ψ`-almost surely equal (Fritz 2020,
Prop. 13.7). -/
theorem isConditional_unique_as_unit {X Y : C} {ψ : 𝟙_ C ⟶ X ⊗ Y} {g₁ g₂ : X ⟶ Y}
    (h₁ : IsConditional ψ ((ρ_ X).hom ≫ g₁)) (h₂ : IsConditional ψ ((ρ_ X).hom ≫ g₂)) :
    AlmostSurelyEq (marginalFst ψ) g₁ g₂ := by
  have h := isConditional_unique_as h₁ h₂
  unfold AlmostSurelyEq at h ⊢
  have key : ∀ g : X ⟶ Y,
      @ComonObj.comul C _ _ (𝟙_ C) (CopyDiscardCategory.comonObj (𝟙_ C)) ≫
      (marginalFst ψ ▷ 𝟙_ C) ≫
      @ComonObj.comul C _ _ (X ⊗ 𝟙_ C) (CopyDiscardCategory.comonObj (X ⊗ 𝟙_ C)) ≫
      (((ρ_ X).hom ≫ g) ▷ (X ⊗ 𝟙_ C)) ≫ (Y ◁ (ρ_ X).hom) =
      marginalFst ψ ≫ Δ[X] ≫ (g ▷ X) := by
    intro g
    rw [copy_tensor, copy_unit]
    simp only [tensorμ, braiding_tensorUnit_right]
    monoidal
  rw [← key g₁, ← key g₂, reassoc_of% h]

/-- For `f : A ⟶ X ⊗ (Y ⊗ Z)`, a conditional `k : X ⊗ A ⟶ Y ⊗ Z` of `f` on `X` and a
conditional `h : Y ⊗ (X ⊗ A) ⟶ Z` of `k` on `Y`, `h` with its first two inputs swapped is a
conditional of `f ≫ (α_ X Y Z).inv : A ⟶ (X ⊗ Y) ⊗ Z` on `X ⊗ Y` (Fritz 2020, Lemma 11.11). -/
theorem IsConditional.nest {A X Y Z : C} {f : A ⟶ X ⊗ (Y ⊗ Z)}
    {k : X ⊗ A ⟶ Y ⊗ Z} {h : Y ⊗ (X ⊗ A) ⟶ Z}
    (hk : IsConditional f k) (hh : IsConditional k h) :
    IsConditional (f ≫ (α_ X Y Z).inv) (((β_ X Y).hom ▷ A) ≫ (α_ Y X A).hom ≫ h) := by
  unfold IsConditional at hk hh ⊢
  have hM : marginalFst (f ≫ (α_ X Y Z).inv) =
      Δ[A] ≫ (marginalFst f ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ marginalFst k) := by
    have e : marginalFst (f ≫ (α_ X Y Z).inv) = f ≫ X ◁ (Y ◁ ε[Z] ≫ (ρ_ Y).hom) := by
      simp only [marginalFst, Category.assoc]
      congr 1
      monoidal
    rw [e]
    conv_lhs => rw [hk]
    simp only [Category.assoc, ← whiskerLeft_comp]
    rfl
  rw [hM]
  conv_lhs => rw [hk, hh]
  generalize marginalFst f = m
  generalize marginalFst k = n
  conv_rhs =>
    rw [copy_tensor]
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    rw [comul_assoc_flip_assoc A, tensorHom_def, comp_whiskerRight, Category.assoc,
      ← comp_whiskerRight_assoc (X ◁ n), whisker_exchange]
  conv_lhs =>
    rw [copy_tensor, show Δ[X] ⊗ₘ Δ[A] = (Δ[X] ≫ (β_ X X).hom) ⊗ₘ Δ[A] by
      rw [IsCommComonObj.comul_comm], tensorHom_def']
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc, ← whisker_exchange_assoc]
  symm
  calc _ = Δ[A] ⊗≫ (A ◁ Δ[A]) ⊗≫ (m ▷ (A ⊗ A)) ⊗≫ ((Δ[X] ≫ Δ[X] ▷ X) ▷ (A ⊗ A)) ⊗≫
        (X ◁ ((X ◁ (n ≫ Δ[Y]) ≫ (β_ X (Y ⊗ Y)).hom) ▷ A)) ⊗≫ (X ◁ Y ◁ h) ⊗≫
        𝟙 ((X ⊗ Y) ⊗ Z) := by
        rw [BraidedCategory.braiding_tensor_right_hom]
        simp only [tensorμ]
        monoidal
    _ = Δ[A] ⊗≫ (A ◁ Δ[A]) ⊗≫ (m ▷ (A ⊗ A)) ⊗≫
        ((Δ[X] ≫ X ◁ Δ[X] ≫ (α_ X X X).inv) ▷ (A ⊗ A)) ⊗≫
        (X ◁ (((β_ X (X ⊗ A)).hom ≫ (n ≫ Δ[Y]) ▷ X) ▷ A)) ⊗≫ (X ◁ Y ◁ h) ⊗≫
        𝟙 ((X ⊗ Y) ⊗ Z) := by
        rw [comul_assoc_flip, BraidedCategory.braiding_naturality_right]
    _ = _ := by
        rw [BraidedCategory.braiding_tensor_right_hom]
        simp only [tensorμ]
        monoidal

-- WITNESS: none (step of IsConditional.comp_whiskerLeft; witnessed through it)
/-- For objects `A` and `B`, copying `A ⊗ B` and discarding `B` from the left copy equals
copying `A` and reassociating `(A ⊗ A) ⊗ B` to `A ⊗ (A ⊗ B)`. -/
theorem copy_comp_fst_whiskerRight (A B : C) :
    @ComonObj.comul C _ _ (A ⊗ B) (CopyDiscardCategory.comonObj (A ⊗ B)) ≫
      ((A ◁ ε[B] ≫ (ρ_ A).hom) ▷ (A ⊗ B)) = (Δ[A] ▷ B) ≫ (α_ A A B).hom := by
  have e : (A ◁ ε[B] ≫ (ρ_ A).hom) ▷ (A ⊗ B) =
      ((𝟙 A ⊗ₘ ε[B]) ⊗ₘ (𝟙 A ⊗ₘ 𝟙 B)) ≫ ((ρ_ A).hom ▷ (A ⊗ B)) := by
    simp only [id_tensorHom, id_whiskerRight, tensorHom_id, comp_whiskerRight]
  rw [copy_tensor, e, Category.assoc, ← tensorμ_natural_assoc, tensorHom_comp_tensorHom_assoc,
    counit_comul_hom]
  simp only [id_tensorHom_id, Category.comp_id, Category.id_comp, tensorμ,
    braiding_tensorUnit_right]
  monoidal

/-- For `f : A' ⟶ X ⊗ Y`, a conditional `k : X ⊗ A' ⟶ Y` of `f` on `X` and a deterministic
`g : A ⟶ A'`, `(X ◁ g) ≫ k` is a conditional of `g ≫ f` on `X` (the third rewrite rule of the
n-Category Café post "Introduction to Categorical Probability", T16; Fritz 2020, Def. 10.1 and
Def. 11.5). -/
theorem IsConditional.deterministic_comp {A A' X Y : C} {f : A' ⟶ X ⊗ Y}
    {k : X ⊗ A' ⟶ Y} (h : IsConditional f k) (g : A ⟶ A') [Deterministic g] :
    IsConditional (g ≫ f) ((X ◁ g) ≫ k) := by
  unfold IsConditional at h ⊢
  rw [marginalFst_comp]
  conv_lhs => rw [h]
  simp only [Category.assoc, comp_whiskerRight, whiskerLeft_comp]
  rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc, ← whisker_exchange_assoc,
    ← tensorHom_def_assoc, IsComonHom.hom_comul_assoc]

end CopyDiscardCategory

namespace MarkovCategory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

/-- In a Markov category, for `f : A ⟶ X ⊗ W`, a conditional `k : X ⊗ A ⟶ W` of `f` on `X` and
`g : W ⊗ B ⟶ Y`, `(α_ X A B).inv ≫ (k ▷ B) ≫ g` is a conditional on `X` of
`(f ▷ B) ≫ (α_ X W B).hom ≫ (X ◁ g) : A ⊗ B ⟶ X ⊗ Y` (Fritz 2020, Lemma 11.12). -/
theorem IsConditional.comp_whiskerLeft {A B X W Y : C} {f : A ⟶ X ⊗ W}
    {k : X ⊗ A ⟶ W} (h : IsConditional f k) (g : W ⊗ B ⟶ Y) :
    IsConditional ((f ▷ B) ≫ (α_ X W B).hom ≫ (X ◁ g)) ((α_ X A B).inv ≫ (k ▷ B) ≫ g) := by
  unfold IsConditional at h ⊢
  have hM : marginalFst ((f ▷ B) ≫ (α_ X W B).hom ≫ (X ◁ g)) =
      (A ◁ ε[B] ≫ (ρ_ A).hom) ≫ marginalFst f := by
    simp only [marginalFst, Category.assoc, ← whiskerLeft_comp_assoc,
      MarkovCategory.discard_natural]
    rw [discard_tensor, tensorHom_def', ← rightUnitor_naturality_assoc, whisker_exchange_assoc]
    monoidal
  rw [hM, comp_whiskerRight (A ◁ ε[B] ≫ (ρ_ A).hom), Category.assoc,
    reassoc_of% copy_comp_fst_whiskerRight]
  conv_lhs => rw [h]
  monoidal

end MarkovCategory

end CategoryTheory
