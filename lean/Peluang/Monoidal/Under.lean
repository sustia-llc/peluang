/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# The monoidal structure on the category of states of a monoidal category

For a monoidal category `C`, the category `Under (𝟙_ C)` of states of `C` is monoidal. It is
braided when `C` is braided, and symmetric when `C` is symmetric.

## Main definitions

* `Under.monoidalCategoryStruct` - for a monoidal category `C`, the tensor product, unit,
  whiskerings, associator and unitors of `Under (𝟙_ C)`: the tensor product of `X` and `Y` is
  `(λ_ (𝟙_ C)).inv ≫ (X.hom ⊗ₘ Y.hom)`, and the unit is `𝟙 (𝟙_ C)` (Fritz 2020, the proof of
  Prop. 13.9 (a)).
* `Under.monoidalCategory` - for a monoidal category `C`, `Under (𝟙_ C)` is a monoidal category.
* `Under.braidedCategory` - for a braided monoidal category `C`, `Under (𝟙_ C)` is braided.
* `Under.symmetricCategory` - for a symmetric monoidal category `C`, `Under (𝟙_ C)` is
  symmetric.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- For a monoidal category `C`, the monoidal data of `Under (𝟙_ C)`: the tensor product of `X`
and `Y` is `(λ_ (𝟙_ C)).inv ≫ (X.hom ⊗ₘ Y.hom)`, the unit is `𝟙 (𝟙_ C)`, and the whiskerings,
the tensor product of morphisms, the associator and the unitors are those of `C` on `.right`
(Fritz 2020, the proof of Prop. 13.9 (a)). -/
instance Under.monoidalCategoryStruct : MonoidalCategoryStruct (Under (𝟙_ C)) where
  tensorObj X Y := Under.mk ((λ_ (𝟙_ C)).inv ≫ (X.hom ⊗ₘ Y.hom))
  whiskerLeft X _ _ f := Under.homMk (X.right ◁ f.right) (by
    dsimp
    rw [Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Under.w])
  whiskerRight f Y := Under.homMk (f.right ▷ Y.right) (by
    dsimp
    rw [Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Under.w])
  tensorHom f g := Under.homMk (f.right ⊗ₘ g.right) (by
    dsimp
    rw [Category.assoc, tensorHom_comp_tensorHom, Under.w, Under.w])
  tensorUnit := Under.mk (𝟙 (𝟙_ C))
  associator X Y Z := Under.isoMk (α_ X.right Y.right Z.right) (by
    dsimp
    monoidal)
  leftUnitor X := Under.isoMk (λ_ X.right) (by
    dsimp
    simp)
  rightUnitor X := Under.isoMk (ρ_ X.right) (by
    dsimp
    simp only [tensorHom_id, Category.assoc, rightUnitor_naturality]
    rw [← unitors_equal, Iso.inv_hom_id_assoc])

/-- For a monoidal category `C`, the category `Under (𝟙_ C)` of states of `C` is monoidal
(Fritz 2020, the proof of Prop. 13.9 (a)). -/
instance Under.monoidalCategory : MonoidalCategory (Under (𝟙_ C)) where
  tensorHom_def f g := by
    ext
    exact MonoidalCategory.tensorHom_def f.right g.right
  id_tensorHom_id X Y := by
    ext
    exact MonoidalCategory.id_tensorHom_id X.right Y.right
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    ext
    exact MonoidalCategory.tensorHom_comp_tensorHom f₁.right f₂.right g₁.right g₂.right
  whiskerLeft_id X Y := by
    ext
    exact MonoidalCategory.whiskerLeft_id X.right Y.right
  id_whiskerRight X Y := by
    ext
    exact MonoidalCategory.id_whiskerRight X.right Y.right
  associator_naturality f₁ f₂ f₃ := by
    ext
    exact MonoidalCategory.associator_naturality f₁.right f₂.right f₃.right
  leftUnitor_naturality f := by
    ext
    exact MonoidalCategory.leftUnitor_naturality f.right
  rightUnitor_naturality f := by
    ext
    exact MonoidalCategory.rightUnitor_naturality f.right
  pentagon W X Y Z := by
    ext
    exact MonoidalCategory.pentagon W.right X.right Y.right Z.right
  triangle X Y := by
    ext
    exact MonoidalCategory.triangle X.right Y.right

/-- For a braided monoidal category `C`, the category `Under (𝟙_ C)` of states of `C` is
braided: the braiding of `X` and `Y` is `β_ X.right Y.right` on `.right`
(Fritz 2020, Prop. 13.9 (a)). -/
instance Under.braidedCategory [BraidedCategory C] : BraidedCategory (Under (𝟙_ C)) where
  braiding X Y := Under.isoMk (β_ X.right Y.right) (by
    change ((λ_ (𝟙_ C)).inv ≫ (X.hom ⊗ₘ Y.hom)) ≫ (β_ X.right Y.right).hom =
      (λ_ (𝟙_ C)).inv ≫ (Y.hom ⊗ₘ X.hom)
    rw [Category.assoc, BraidedCategory.braiding_naturality, braiding_tensorUnit_left,
      Category.assoc, Iso.inv_hom_id_assoc, unitors_inv_equal])
  braiding_naturality_right X _ _ f := by
    ext
    exact BraidedCategory.braiding_naturality_right X.right f.right
  braiding_naturality_left f Z := by
    ext
    exact BraidedCategory.braiding_naturality_left f.right Z.right
  hexagon_forward X Y Z := by
    ext
    exact BraidedCategory.hexagon_forward X.right Y.right Z.right
  hexagon_reverse X Y Z := by
    ext
    exact BraidedCategory.hexagon_reverse X.right Y.right Z.right

/-- For a symmetric monoidal category `C`, the category `Under (𝟙_ C)` of states of `C` is
symmetric (Fritz 2020, Prop. 13.9 (a)). -/
instance Under.symmetricCategory [SymmetricCategory C] :
    SymmetricCategory (Under (𝟙_ C)) where
  symmetry X Y := by
    ext
    exact SymmetricCategory.symmetry X.right Y.right

end CategoryTheory
