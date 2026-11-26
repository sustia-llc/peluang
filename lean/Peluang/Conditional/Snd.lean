/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Conditional

/-!
# Conditionals on the second factor

Conditionals of morphisms into a tensor product on its second factor, in a copy-discard
category.

## Main definitions

* `CopyDiscardCategory.IsConditionalSnd` - `g : Y ⊗ A ⟶ X` is a conditional of
  `f : A ⟶ X ⊗ Y` on `Y` (Fritz 2020, Def. 11.5).

## Main results

* `CopyDiscardCategory.marginalFst_comp_braiding_hom` - the first marginal of
  `f ≫ (β_ X Y).hom` is the second marginal of `f` (Fritz 2020, Notation 2.8).
* `CopyDiscardCategory.marginalSnd_comp_braiding_hom` - the second marginal of
  `f ≫ (β_ X Y).hom` is the first marginal of `f` (Fritz 2020, Notation 2.8).
* `CopyDiscardCategory.isConditionalSnd_iff` - `IsConditionalSnd f g` as an equation for `f`
  with no braiding on the outputs (Fritz 2020, Def. 11.5).
* `CopyDiscardCategory.exists_isConditionalSnd` - in a copy-discard category with
  conditionals, every `f : A ⟶ X ⊗ Y` has a conditional on `Y` (Fritz 2020, Def. 11.5).

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

/-- For `f : A ⟶ X ⊗ Y` and `g : Y ⊗ A ⟶ X` in a copy-discard category `C`, `g` is a
conditional of `f` on `Y`: `g` is a conditional of `f ≫ (β_ X Y).hom : A ⟶ Y ⊗ X` on its
first factor `Y` (Fritz 2020, Def. 11.5). The inputs of `g` are ordered `Y ⊗ A`. -/
def IsConditionalSnd {A X Y : C} (f : A ⟶ X ⊗ Y) (g : Y ⊗ A ⟶ X) : Prop :=
  IsConditional (f ≫ (β_ X Y).hom) g

/-- For `f : A ⟶ X ⊗ Y` in a copy-discard category `C`, the first marginal of
`f ≫ (β_ X Y).hom : A ⟶ Y ⊗ X` equals the second marginal of `f` (Fritz 2020,
Notation 2.8). -/
theorem marginalFst_comp_braiding_hom {A X Y : C} (f : A ⟶ X ⊗ Y) :
    marginalFst (f ≫ (β_ X Y).hom) = marginalSnd f := by
  simp only [marginalFst, marginalSnd, Category.assoc]
  rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_tensorUnit_left]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- For `f : A ⟶ X ⊗ Y` in a copy-discard category `C`, the second marginal of
`f ≫ (β_ X Y).hom : A ⟶ Y ⊗ X` equals the first marginal of `f` (Fritz 2020,
Notation 2.8). -/
theorem marginalSnd_comp_braiding_hom {A X Y : C} (f : A ⟶ X ⊗ Y) :
    marginalSnd (f ≫ (β_ X Y).hom) = marginalFst f := by
  simp only [marginalFst, marginalSnd, Category.assoc]
  rw [← BraidedCategory.braiding_naturality_right_assoc, braiding_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

-- WITNESS: none (step of isConditionalSnd_iff; witnessed through it)
/-- For `m : A ⟶ Y` and `g : Y ⊗ A ⟶ X` in a copy-discard category `C`, the conditional form
`Δ[A] ≫ (m ▷ A) ≫ (Δ[Y] ▷ A) ≫ (α_ Y Y A).hom ≫ (Y ◁ g) : A ⟶ Y ⊗ X` followed by the
braiding `(β_ Y X).hom` equals copying `A`, applying `m` to the right copy, copying that `Y`,
and applying `g` to the left `Y` and `A`. -/
theorem conditional_form_comp_braiding_hom {A X Y : C} (m : A ⟶ Y) (g : Y ⊗ A ⟶ X) :
    (Δ[A] ≫ (m ▷ A) ≫ (Δ[Y] ▷ A) ≫ (α_ Y Y A).hom ≫ (Y ◁ g)) ≫ (β_ Y X).hom =
      Δ[A] ≫ (A ◁ (m ≫ Δ[Y])) ≫ (α_ A Y Y).inv ≫ ((β_ A Y).hom ▷ Y) ≫ (g ▷ Y) := by
  have s1 : Δ[A] ≫ A ◁ (m ≫ Δ[Y]) = Δ[A] ≫ (m ≫ Δ[Y]) ▷ A ≫ (β_ (Y ⊗ Y) A).hom := by
    rw [BraidedCategory.braiding_naturality_left, IsCommComonObj.comul_comm_assoc]
  rw [reassoc_of% s1]
  simp only [Category.assoc]
  rw [BraidedCategory.braiding_naturality_right, BraidedCategory.braiding_tensor_right_hom,
    BraidedCategory.braiding_tensor_left_hom]
  calc
    _ = Δ[A] ≫ (m ▷ A) ≫ ((Δ[Y] ≫ (β_ Y Y).hom) ▷ A) ⊗≫ Y ◁ (β_ Y A).hom ⊗≫ g ▷ Y := by
      monoidal
    _ = Δ[A] ≫ (m ≫ Δ[Y]) ▷ A ⊗≫ Y ◁ (β_ Y A).hom ⊗≫
          ((β_ Y A).hom ≫ (β_ A Y).hom) ▷ Y ⊗≫ g ▷ Y := by
      rw [IsCommComonObj.comul_comm, SymmetricCategory.symmetry]
      monoidal
    _ = _ := by
      monoidal

/-- For `f : A ⟶ X ⊗ Y` and `g : Y ⊗ A ⟶ X` in a copy-discard category `C`, `g` is a
conditional of `f` on `Y` if and only if `f` equals copying `A`, applying the second marginal
of `f` to the right copy, copying that `Y`, and applying `g` to the left `Y` and `A`
(Fritz 2020, Def. 11.5). -/
theorem isConditionalSnd_iff {A X Y : C} (f : A ⟶ X ⊗ Y) (g : Y ⊗ A ⟶ X) :
    IsConditionalSnd f g ↔
      f = Δ[A] ≫ (A ◁ (marginalSnd f ≫ Δ[Y])) ≫ (α_ A Y Y).inv ≫
        ((β_ A Y).hom ▷ Y) ≫ (g ▷ Y) := by
  unfold IsConditionalSnd IsConditional
  rw [marginalFst_comp_braiding_hom, ← conditional_form_comp_braiding_hom]
  generalize marginalSnd f = m
  constructor
  · intro h
    rw [← h]
    simp only [Category.assoc, SymmetricCategory.symmetry, Category.comp_id]
  · intro h
    rw [h]
    simp only [Category.assoc, SymmetricCategory.symmetry, Category.comp_id]

/-- In a copy-discard category `C` with conditionals, every morphism `f : A ⟶ X ⊗ Y` has a
conditional `g : Y ⊗ A ⟶ X` on `Y` (Fritz 2020, Def. 11.5). -/
theorem exists_isConditionalSnd [HasConditionals C] {A X Y : C} (f : A ⟶ X ⊗ Y) :
    ∃ g, IsConditionalSnd f g :=
  HasConditionals.exists_isConditional (f ≫ (β_ X Y).hom)

end CopyDiscardCategory

end CategoryTheory
