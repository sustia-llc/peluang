/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic
public import Peluang.Markov.Derived

/-!
# Closure properties of deterministic morphisms

In a copy-discard category, copy and discard are deterministic (Fritz 2020,
Def. 10.1 and Remark 10.2), and deterministic morphisms are closed under
whiskering and tensor products and contain the associators, unitors and
braidings (Fritz 2020, Lemma 10.12).

## Main results

* `Deterministic.instCopy`, `Deterministic.instDiscard` - copy and discard are deterministic.
* `Deterministic.instTensorHom`, `Deterministic.instWhiskerRight`,
  `Deterministic.instWhiskerLeft` - closure under tensor products and whiskering.
* `Deterministic.instAssociator`, `Deterministic.instLeftUnitor`,
  `Deterministic.instRightUnitor`, `Deterministic.instBraiding` - the structure
  isomorphisms are deterministic.
* `Deterministic.instIsComonHomCopy`, `Deterministic.instIsComonHomWhiskerRight`,
  `Deterministic.instIsComonHomWhiskerLeft`, `Deterministic.instIsComonHomAssociator`,
  `Deterministic.instIsComonHomLeftUnitor`, `Deterministic.instIsComonHomRightUnitor`,
  `Deterministic.instIsComonHomBraiding` - the same statements as `IsComonHom` instances
  at the tensor product comonoid structure `Comon.instComonObjTensorObj` on every tensor
  product object.
* `Deterministic.instIsComonHomOfTensorObjSource`,
  `Deterministic.instIsComonHomOfTensorObjTarget` - a comonoid morphism out of or into
  `X ⊗ Y` at `CopyDiscardCategory.comonObj (X ⊗ Y)` is a comonoid morphism at
  `Comon.instComonObjTensorObj X Y`.
* `Comon.instIsComonHomTensorHom` - in a braided monoidal category, the tensor product of
  comonoid morphisms is a comonoid morphism for the tensor product comonoid structures, at any
  comonoid structures on the four objects.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- In a braided monoidal category, the tensor product of comonoid morphisms is a comonoid
morphism for the tensor product comonoid structures, at any comonoid structures on the four
objects. -/
instance Comon.instIsComonHomTensorHom [BraidedCategory C] {X Y X' Y' : C} [ComonObj X]
    [ComonObj Y] [ComonObj X'] [ComonObj Y'] (f : X ⟶ Y) (g : X' ⟶ Y') [IsComonHom f]
    [IsComonHom g] : IsComonHom (f ⊗ₘ g) :=
  inferInstanceAs (IsComonHom (MonoidalCategoryStruct.tensorHom (C := Comon C)
    (X₁ := Comon.mk X) (Y₁ := Comon.mk Y) (X₂ := Comon.mk X') (Y₂ := Comon.mk Y')
    (Comon.Hom.mk f) (Comon.Hom.mk g)).hom)

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
  unfold Deterministic
  rw [comonObj_tensor, comonObj_tensor]
  exact Comon.instIsComonHomTensorHom f g

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
  have h : IsComonHom (𝟙 (X ⊗ Y) ▷ Z ≫ (α_ X Y Z).hom ≫ X ◁ 𝟙 (Y ⊗ Z)) :=
    inferInstanceAs (IsComonHom (α_ (Comon.mk X) (Comon.mk Y) (Comon.mk Z)).hom.hom)
  unfold Deterministic
  rw [comonObj_tensor, comonObj_tensor, comonObj_tensor, comonObj_tensor]
  simpa using h

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

/-! The instances below restate the ones above at the comonoid structure that
instance synthesis finds on tensor products, `Comon.instComonObjTensorObj`. -/

/-- Copying `X` is a comonoid morphism into `X ⊗ X` with the tensor product comonoid
structure. -/
instance instIsComonHomCopy (X : C) : IsComonHom Δ[X] := by
  rw [← comonObj_tensor]
  exact instCopy X

/-- Right whiskering a comonoid morphism gives a comonoid morphism for the tensor product
comonoid structures. -/
instance instIsComonHomWhiskerRight {X Y : C} (f : X ⟶ Y) [IsComonHom f] (Z : C) :
    IsComonHom (f ▷ Z) := by
  rw [← comonObj_tensor, ← comonObj_tensor]
  exact instWhiskerRight f Z

/-- Left whiskering a comonoid morphism gives a comonoid morphism for the tensor product
comonoid structures. -/
instance instIsComonHomWhiskerLeft (Z : C) {X Y : C} (f : X ⟶ Y) [IsComonHom f] :
    IsComonHom (Z ◁ f) := by
  rw [← comonObj_tensor, ← comonObj_tensor]
  exact instWhiskerLeft Z f

/-- The associator is a comonoid morphism for the tensor product comonoid structures. -/
instance instIsComonHomAssociator (X Y Z : C) : IsComonHom (α_ X Y Z).hom := by
  rw [← comonObj_tensor X Y, ← comonObj_tensor, ← comonObj_tensor Y Z, ← comonObj_tensor]
  exact instAssociator X Y Z

/-- The left unitor is a comonoid morphism for the tensor product comonoid structure on
`𝟙_ C ⊗ X`. -/
instance instIsComonHomLeftUnitor (X : C) : IsComonHom (λ_ X).hom := by
  rw [← comonObj_tensor]
  exact instLeftUnitor X

/-- The right unitor is a comonoid morphism for the tensor product comonoid structure on
`X ⊗ 𝟙_ C`. -/
instance instIsComonHomRightUnitor (X : C) : IsComonHom (ρ_ X).hom := by
  rw [← comonObj_tensor]
  exact instRightUnitor X

/-- The braiding is a comonoid morphism for the tensor product comonoid structures. -/
instance instIsComonHomBraiding (X Y : C) : IsComonHom (β_ X Y).hom := by
  rw [← comonObj_tensor, ← comonObj_tensor]
  exact instBraiding X Y

/-- A deterministic morphism out of `X ⊗ Y` is a comonoid morphism for the tensor product
comonoid structure on `X ⊗ Y`, at any comonoid structure on its codomain for which it is a
comonoid morphism out of `CopyDiscardCategory.comonObj (X ⊗ Y)`. -/
instance (priority := low) instIsComonHomOfTensorObjSource {X Y Z : C} [N : ComonObj Z]
    (f : X ⊗ Y ⟶ Z) [@IsComonHom C _ _ _ _ (comonObj (X ⊗ Y)) N f] : IsComonHom f := by
  rwa [← comonObj_tensor]

/-- A morphism into `X ⊗ Y` that is a comonoid morphism into
`CopyDiscardCategory.comonObj (X ⊗ Y)` is a comonoid morphism for the tensor product comonoid
structure on `X ⊗ Y`, at any comonoid structure on its domain. -/
instance (priority := low) instIsComonHomOfTensorObjTarget {X Y Z : C} [M : ComonObj Z]
    (f : Z ⟶ X ⊗ Y) [@IsComonHom C _ _ _ _ M (comonObj (X ⊗ Y)) f] : IsComonHom f := by
  rwa [← comonObj_tensor]

end Deterministic

end CategoryTheory
