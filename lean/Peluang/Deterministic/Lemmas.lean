/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic

/-!
# Closure properties of deterministic morphisms

In a copy-discard category, copy and discard are deterministic (Fritz 2020,
Def. 10.1 and Remark 10.2), and deterministic morphisms are closed under
whiskering and tensor products and contain the associators, unitors and
braidings (Fritz 2020, Lemma 10.12). The `.inv` halves follow from the
instance for inverses of comonoid morphisms in `Mathlib.CategoryTheory.Monoidal.Comon_`.

## Implementation notes

`Deterministic f` for `f` between tensor products refers to the comonoid structures
`CopyDiscardCategory.comonObj`, while instance synthesis for `ComonObj (X ⊗ Y)` finds
`Comon.instComonObjTensorObj`. The instances below are therefore built with
`IsComonHom.mk` at explicitly supplied `CopyDiscardCategory.comonObj` instances, and
the proofs unfold the tensor structures with `CopyDiscardCategory.copy_tensor` and
`CopyDiscardCategory.discard_tensor`.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

namespace Deterministic

variable [CopyDiscardCategory C]

/-- Copying is deterministic (Fritz 2020, Remark 10.2). -/
instance instCopy (X : C) : Deterministic Δ[X] := by
  refine @IsComonHom.mk _ _ _ _ _ (comonObj _) (comonObj _) _ ?_ ?_
  · rw [discard_tensor]
    simp [unitors_equal]
  · rw [copy_tensor]
    have key : Δ[X] ≫ (Δ[X] ⊗ₘ Δ[X]) =
        Δ[X] ≫ X ◁ Δ[X] ≫ X ◁ (X ◁ Δ[X]) ≫ (α_ X X (X ⊗ X)).inv := by
      rw [tensorHom_def, comul_assoc_flip_assoc, associator_inv_naturality_right]
    have inner : Δ[X] ≫ X ◁ Δ[X] ≫ (α_ X X X).inv ≫ (β_ X X).hom ▷ X ≫ (α_ X X X).hom =
        Δ[X] ≫ X ◁ Δ[X] := by
      rw [← comul_assoc_flip_assoc, ← comp_whiskerRight_assoc, IsCommComonObj.comul_comm,
        ← comul_assoc]
    have h := congrArg (fun t => Δ[X] ≫ X ◁ t ≫ (α_ X X (X ⊗ X)).inv) inner
    rw [← Category.assoc, key, tensorμ]
    simpa only [whiskerLeft_comp, Category.assoc, Iso.inv_hom_id_assoc] using h

/-- Discarding is deterministic (Fritz 2020, Remark 10.2). -/
instance instDiscard (X : C) : Deterministic ε[X] := by
  refine @IsComonHom.mk _ _ _ _ _ (comonObj _) (comonObj _) _ ?_ ?_
  · rw [discard_unit]
    simp
  · rw [copy_unit, tensorHom_def, counit_comul_assoc, leftUnitor_inv_naturality]

/-- The tensor product of deterministic morphisms is deterministic
(Fritz 2020, Lemma 10.12). -/
instance instTensorHom {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') [Deterministic f]
    [Deterministic g] : Deterministic (f ⊗ₘ g) := by
  refine @IsComonHom.mk _ _ _ _ _ (comonObj _) (comonObj _) _ ?_ ?_
  · rw [discard_tensor, discard_tensor, tensorHom_comp_tensorHom_assoc, IsComonHom.hom_counit,
      IsComonHom.hom_counit]
  · rw [copy_tensor, copy_tensor, tensorHom_comp_tensorHom_assoc, IsComonHom.hom_comul,
      IsComonHom.hom_comul, ← tensorHom_comp_tensorHom_assoc, tensorμ_natural, Category.assoc]

/-- Right whiskering preserves determinism (Fritz 2020, Lemma 10.12). -/
instance instWhiskerRight {X Y : C} (f : X ⟶ Y) [Deterministic f] (Z : C) :
    Deterministic (f ▷ Z) := by
  have := instTensorHom f (𝟙 Z)
  rwa [tensorHom_id] at this

/-- Left whiskering preserves determinism (Fritz 2020, Lemma 10.12). -/
instance instWhiskerLeft (Z : C) {X Y : C} (f : X ⟶ Y) [Deterministic f] :
    Deterministic (Z ◁ f) := by
  have := instTensorHom (𝟙 Z) f
  rwa [id_tensorHom] at this

/-- The associator is deterministic (Fritz 2020, Lemma 10.12). -/
instance instAssociator (X Y Z : C) : Deterministic (α_ X Y Z).hom := by
  refine @IsComonHom.mk _ _ _ _ _ (comonObj _) (comonObj _) _ ?_ ?_
  · rw [discard_tensor, discard_tensor, discard_tensor, discard_tensor]
    simp [tensorHom_def]
  · rw [copy_tensor, copy_tensor, copy_tensor, copy_tensor,
      show Δ[X] ⊗ₘ ((Δ[Y] ⊗ₘ Δ[Z]) ≫ tensorμ Y Y Z Z) =
          (Δ[X] ⊗ₘ (Δ[Y] ⊗ₘ Δ[Z])) ≫ (X ⊗ X) ◁ tensorμ Y Y Z Z by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id],
      show ((Δ[X] ⊗ₘ Δ[Y]) ≫ tensorμ X X Y Y) ⊗ₘ Δ[Z] =
          ((Δ[X] ⊗ₘ Δ[Y]) ⊗ₘ Δ[Z]) ≫ tensorμ X X Y Y ▷ (Z ⊗ Z) by
        rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]]
    simp only [Category.assoc]
    rw [← associator_naturality_assoc, tensor_associativity]

/-- The left unitor is deterministic (Fritz 2020, Lemma 10.12). -/
instance instLeftUnitor (X : C) : Deterministic (λ_ X).hom := by
  refine @IsComonHom.mk _ _ _ _ _ (comonObj _) (comonObj _) _ ?_ ?_
  · rw [discard_tensor, discard_unit]
    simp [tensorHom_def]
  · rw [copy_tensor, copy_unit, tensorHom_def', Category.assoc, Category.assoc,
      ← tensor_left_unitality, leftUnitor_naturality]

/-- The right unitor is deterministic (Fritz 2020, Lemma 10.12). -/
instance instRightUnitor (X : C) : Deterministic (ρ_ X).hom := by
  refine @IsComonHom.mk _ _ _ _ _ (comonObj _) (comonObj _) _ ?_ ?_
  · rw [discard_tensor, discard_unit]
    simp [tensorHom_def, unitors_equal]
  · rw [copy_tensor, copy_unit, tensorHom_def, Category.assoc, Category.assoc,
      ← tensor_right_unitality, rightUnitor_naturality]

/-- The braiding is deterministic (Fritz 2020, Lemma 10.12). -/
instance instBraiding (X Y : C) : Deterministic (β_ X Y).hom := by
  refine @IsComonHom.mk _ _ _ _ _ (comonObj _) (comonObj _) _ ?_ ?_
  · rw [discard_tensor, discard_tensor, ← BraidedCategory.braiding_naturality_assoc,
      braiding_leftUnitor, unitors_equal]
  · have hs : Y ◁ (β_ X Y).hom ▷ X ≫ Y ◁ (β_ Y X).hom ▷ X = 𝟙 _ := by
      rw [← whiskerLeft_comp, ← comp_whiskerRight, SymmetricCategory.symmetry]
      simp
    have coh : (β_ (X ⊗ X) (Y ⊗ Y)).hom ≫ tensorμ Y Y X X =
        tensorμ X X Y Y ≫ ((β_ X Y).hom ⊗ₘ (β_ X Y).hom) := by
      simp only [tensorμ, BraidedCategory.braiding_tensor_left_hom,
        BraidedCategory.braiding_tensor_right_hom, tensorHom_def, Category.assoc,
        whiskerLeft_comp, comp_whiskerRight, whisker_assoc]
      simp only [Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc, reassoc_of% hs]
      monoidal
    rw [copy_tensor, copy_tensor, ← BraidedCategory.braiding_naturality_assoc, coh,
      Category.assoc]

end Deterministic

end CategoryTheory
