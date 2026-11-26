/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Isomorphisms that reorder the factors of a tensor product

For a monoidal category `C`, and for a braided monoidal category `C`, named isomorphisms
between tensor products of the same objects in two orders or two bracketings, each built
from associators, braidings and whiskerings.

## Main definitions

* `MonoidalCategory.tensorCompAssoc` - for a monoidal category `C`,
  `A ⊗ ((X₁ ⊗ (W ⊗ Y₁)) ⊗ A') ≅ (A ⊗ X₁) ⊗ (W ⊗ (Y₁ ⊗ A'))` (Fritz 2020, Prop. 12.18 (c)).
* `MonoidalCategory.tensorLeftComm` - for a braided monoidal category `C`,
  `X ⊗ (Y ⊗ Z) ≅ Y ⊗ (X ⊗ Z)`.
* `MonoidalCategory.tensorμIso` - for a braided monoidal category `C`,
  `(X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂) ≅ (X₁ ⊗ Y₁) ⊗ (X₂ ⊗ Y₂)`, with `hom := tensorμ` and `inv := tensorδ`.
* `MonoidalCategory.tensorRev₃` - for a braided monoidal category `C`,
  `X ⊗ (W ⊗ Y) ≅ Y ⊗ (W ⊗ X)` (Fritz 2020, Lemma 12.5 (a) and Prop. 12.17 (a)).
* `MonoidalCategory.tensorWeakUnionIso` - for a braided monoidal category `C`,
  `(X₁ ⊗ X₂) ⊗ (W ⊗ Y) ≅ X₁ ⊗ ((W ⊗ X₂) ⊗ Y)` (Fritz 2020, Lemma 12.5 (d) and
  Prop. 12.17 (d)).
* `MonoidalCategory.tensorTripleInterchange` - for a braided monoidal category `C`,
  `(X₁ ⊗ (W₁ ⊗ Y₁)) ⊗ (X₂ ⊗ (W₂ ⊗ Y₂)) ≅ (X₁ ⊗ X₂) ⊗ ((W₁ ⊗ W₂) ⊗ (Y₁ ⊗ Y₂))`
  (Fritz 2020, Prop. 12.18 (a)).
* `MonoidalCategory.tensorCondReorder` - for a braided monoidal category `C`,
  `X ⊗ ((V ⊗ W) ⊗ Y) ≅ V ⊗ (X ⊗ (W ⊗ Y))` (Fritz 2020, Prop. 12.18 (d)).
* `MonoidalCategory.tensorCompReorder` - for a braided monoidal category `C`,
  `X₁ ⊗ ((V ⊗ (X₂ ⊗ (W ⊗ Y₂))) ⊗ Y₁) ≅ (X₁ ⊗ X₂) ⊗ ((V ⊗ W) ⊗ (Y₂ ⊗ Y₁))`
  (Fritz 2020, Prop. 12.18 (b)).

## Main statements

* `MonoidalCategory.tensorRev₃_eq_tensorLeftComm` - for a braided monoidal category `C`,
  `tensorRev₃ X W Y` is `tensorLeftComm X W Y`, then the braiding of `X` and `Y` whiskered
  by `W`, then `tensorLeftComm W Y X` (the reordering of Fritz 2020, Lemma 12.5 (a) and
  Prop. 12.17 (a)).
* `MonoidalCategory.tensorRev₃_hom_naturality` - for a braided monoidal category `C`,
  `(tensorRev₃ X W Y).hom` is natural in `X`, `W` and `Y` (the reordering of Fritz 2020,
  Lemma 12.5 (a) and Prop. 12.17 (a)).

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- For objects `A`, `X₁`, `W`, `Y₁`, `A'` of a monoidal category `C`, the isomorphism
`A ⊗ ((X₁ ⊗ (W ⊗ Y₁)) ⊗ A') ≅ (A ⊗ X₁) ⊗ (W ⊗ (Y₁ ⊗ A'))` built from associators
(Fritz 2020, Prop. 12.18 (c)). -/
def tensorCompAssoc (A X₁ W Y₁ A' : C) :
    A ⊗ ((X₁ ⊗ (W ⊗ Y₁)) ⊗ A') ≅ (A ⊗ X₁) ⊗ (W ⊗ (Y₁ ⊗ A')) :=
  whiskerLeftIso A (α_ X₁ (W ⊗ Y₁) A' ≪≫ whiskerLeftIso X₁ (α_ W Y₁ A')) ≪≫
    (α_ A X₁ (W ⊗ (Y₁ ⊗ A'))).symm

-- WITNESS: none (restates the definition of tensorCompAssoc)
/-- For objects `A`, `X₁`, `W`, `Y₁`, `A'` of a monoidal category `C`, the morphism
`(tensorCompAssoc A X₁ W Y₁ A').hom` as a composite of two whiskered associators and the
inverse of an associator. -/
theorem tensorCompAssoc_hom (A X₁ W Y₁ A' : C) :
    (tensorCompAssoc A X₁ W Y₁ A').hom =
      A ◁ (α_ X₁ (W ⊗ Y₁) A').hom ≫ A ◁ X₁ ◁ (α_ W Y₁ A').hom ≫
        (α_ A X₁ (W ⊗ (Y₁ ⊗ A'))).inv := by
  simp only [tensorCompAssoc, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerLeft_comp,
    Category.assoc]

variable [BraidedCategory C]

/-- For objects `X`, `Y`, `Z` of a braided monoidal category `C`, the isomorphism
`X ⊗ (Y ⊗ Z) ≅ Y ⊗ (X ⊗ Z)` that braids the first two factors. -/
def tensorLeftComm (X Y Z : C) : X ⊗ (Y ⊗ Z) ≅ Y ⊗ (X ⊗ Z) :=
  (α_ X Y Z).symm ≪≫ whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z

-- WITNESS: none (restates the definition of tensorLeftComm)
/-- For objects `X`, `Y`, `Z` of a braided monoidal category `C`, the morphism
`(tensorLeftComm X Y Z).hom` as a composite of associators and a whiskered braiding. -/
theorem tensorLeftComm_hom (X Y Z : C) :
    (tensorLeftComm X Y Z).hom = (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom :=
  rfl

/-- For objects `X₁`, `X₂`, `Y₁`, `Y₂` of a braided monoidal category `C`, the isomorphism
`(X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂) ≅ (X₁ ⊗ Y₁) ⊗ (X₂ ⊗ Y₂)` with `hom := tensorμ` and
`inv := tensorδ`. -/
def tensorμIso (X₁ X₂ Y₁ Y₂ : C) : (X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂) ≅ (X₁ ⊗ Y₁) ⊗ (X₂ ⊗ Y₂) where
  hom := tensorμ X₁ X₂ Y₁ Y₂
  inv := tensorδ X₁ X₂ Y₁ Y₂
  hom_inv_id := tensorμ_tensorδ X₁ X₂ Y₁ Y₂
  inv_hom_id := tensorδ_tensorμ X₁ X₂ Y₁ Y₂

-- WITNESS: none (restates the definition of tensorμIso)
/-- For objects `X₁`, `X₂`, `Y₁`, `Y₂` of a braided monoidal category `C`, the morphism
`(tensorμIso X₁ X₂ Y₁ Y₂).hom` as a composite of associators and a whiskered braiding. -/
theorem tensorμIso_hom (X₁ X₂ Y₁ Y₂ : C) :
    (tensorμIso X₁ X₂ Y₁ Y₂).hom =
      (α_ X₁ X₂ (Y₁ ⊗ Y₂)).hom ≫ X₁ ◁ (α_ X₂ Y₁ Y₂).inv ≫ X₁ ◁ (β_ X₂ Y₁).hom ▷ Y₂ ≫
        X₁ ◁ (α_ Y₁ X₂ Y₂).hom ≫ (α_ X₁ Y₁ (X₂ ⊗ Y₂)).inv :=
  rfl

/-- For objects `X`, `W`, `Y` of a braided monoidal category `C`, the isomorphism
`X ⊗ (W ⊗ Y) ≅ Y ⊗ (W ⊗ X)` that exchanges the outer factors (Fritz 2020, Lemma 12.5 (a)
and Prop. 12.17 (a)). -/
def tensorRev₃ (X W Y : C) : X ⊗ (W ⊗ Y) ≅ Y ⊗ (W ⊗ X) :=
  β_ X (W ⊗ Y) ≪≫ whiskerRightIso (β_ W Y) X ≪≫ α_ Y W X

-- WITNESS: none (restates the definition of tensorRev₃)
/-- For objects `X`, `W`, `Y` of a braided monoidal category `C`, the morphism
`(tensorRev₃ X W Y).hom` as a composite of two braidings and an associator. -/
theorem tensorRev₃_hom (X W Y : C) :
    (tensorRev₃ X W Y).hom = (β_ X (W ⊗ Y)).hom ≫ (β_ W Y).hom ▷ X ≫ (α_ Y W X).hom :=
  rfl

/-- For objects `X₁`, `X₂`, `W`, `Y` of a braided monoidal category `C`, the isomorphism
`(X₁ ⊗ X₂) ⊗ (W ⊗ Y) ≅ X₁ ⊗ ((W ⊗ X₂) ⊗ Y)` that moves `X₂` to the right of `W`
(Fritz 2020, Lemma 12.5 (d) and Prop. 12.17 (d)). -/
def tensorWeakUnionIso (X₁ X₂ W Y : C) : (X₁ ⊗ X₂) ⊗ (W ⊗ Y) ≅ X₁ ⊗ ((W ⊗ X₂) ⊗ Y) :=
  α_ X₁ X₂ (W ⊗ Y) ≪≫ whiskerLeftIso X₁ ((α_ X₂ W Y).symm ≪≫ whiskerRightIso (β_ X₂ W) Y)

-- WITNESS: none (restates the definition of tensorWeakUnionIso)
/-- For objects `X₁`, `X₂`, `W`, `Y` of a braided monoidal category `C`, the morphism
`(tensorWeakUnionIso X₁ X₂ W Y).hom` as a composite of associators and a whiskered
braiding. -/
theorem tensorWeakUnionIso_hom (X₁ X₂ W Y : C) :
    (tensorWeakUnionIso X₁ X₂ W Y).hom =
      (α_ X₁ X₂ (W ⊗ Y)).hom ≫ X₁ ◁ (α_ X₂ W Y).inv ≫ X₁ ◁ (β_ X₂ W).hom ▷ Y := by
  simp only [tensorWeakUnionIso, Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    Iso.symm_hom, whiskerLeft_comp]

/-- For objects `X₁`, `W₁`, `Y₁`, `X₂`, `W₂`, `Y₂` of a braided monoidal category `C`, the
isomorphism `(X₁ ⊗ (W₁ ⊗ Y₁)) ⊗ (X₂ ⊗ (W₂ ⊗ Y₂)) ≅ (X₁ ⊗ X₂) ⊗ ((W₁ ⊗ W₂) ⊗ (Y₁ ⊗ Y₂))`
built from two `tensorμIso` (Fritz 2020, Prop. 12.18 (a)). -/
def tensorTripleInterchange (X₁ W₁ Y₁ X₂ W₂ Y₂ : C) :
    (X₁ ⊗ (W₁ ⊗ Y₁)) ⊗ (X₂ ⊗ (W₂ ⊗ Y₂)) ≅ (X₁ ⊗ X₂) ⊗ ((W₁ ⊗ W₂) ⊗ (Y₁ ⊗ Y₂)) :=
  tensorμIso X₁ (W₁ ⊗ Y₁) X₂ (W₂ ⊗ Y₂) ≪≫ whiskerLeftIso (X₁ ⊗ X₂) (tensorμIso W₁ Y₁ W₂ Y₂)

-- WITNESS: none (restates the definition of tensorTripleInterchange)
/-- For objects `X₁`, `W₁`, `Y₁`, `X₂`, `W₂`, `Y₂` of a braided monoidal category `C`, the
morphism `(tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom` as a composite of associators and
whiskered braidings. -/
theorem tensorTripleInterchange_hom (X₁ W₁ Y₁ X₂ W₂ Y₂ : C) :
    (tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom =
      ((α_ X₁ (W₁ ⊗ Y₁) (X₂ ⊗ (W₂ ⊗ Y₂))).hom ≫ X₁ ◁ (α_ (W₁ ⊗ Y₁) X₂ (W₂ ⊗ Y₂)).inv ≫
        X₁ ◁ (β_ (W₁ ⊗ Y₁) X₂).hom ▷ (W₂ ⊗ Y₂) ≫ X₁ ◁ (α_ X₂ (W₁ ⊗ Y₁) (W₂ ⊗ Y₂)).hom ≫
        (α_ X₁ X₂ ((W₁ ⊗ Y₁) ⊗ (W₂ ⊗ Y₂))).inv) ≫
      (X₁ ⊗ X₂) ◁ ((α_ W₁ Y₁ (W₂ ⊗ Y₂)).hom ≫ W₁ ◁ (α_ Y₁ W₂ Y₂).inv ≫
        W₁ ◁ (β_ Y₁ W₂).hom ▷ Y₂ ≫ W₁ ◁ (α_ W₂ Y₁ Y₂).hom ≫ (α_ W₁ W₂ (Y₁ ⊗ Y₂)).inv) :=
  rfl

/-- For objects `X`, `V`, `W`, `Y` of a braided monoidal category `C`, the isomorphism
`X ⊗ ((V ⊗ W) ⊗ Y) ≅ V ⊗ (X ⊗ (W ⊗ Y))` that moves `V` to the first place
(Fritz 2020, Prop. 12.18 (d)). -/
def tensorCondReorder (X V W Y : C) : X ⊗ ((V ⊗ W) ⊗ Y) ≅ V ⊗ (X ⊗ (W ⊗ Y)) :=
  whiskerLeftIso X (α_ V W Y) ≪≫ tensorLeftComm X V (W ⊗ Y)

-- WITNESS: none (restates the definition of tensorCondReorder)
/-- For objects `X`, `V`, `W`, `Y` of a braided monoidal category `C`, the morphism
`(tensorCondReorder X V W Y).hom` as a composite of associators and a whiskered braiding. -/
theorem tensorCondReorder_hom (X V W Y : C) :
    (tensorCondReorder X V W Y).hom =
      X ◁ (α_ V W Y).hom ≫ (α_ X V (W ⊗ Y)).inv ≫ (β_ X V).hom ▷ (W ⊗ Y) ≫
        (α_ V X (W ⊗ Y)).hom :=
  rfl

/-- For objects `X₁`, `V`, `X₂`, `W`, `Y₂`, `Y₁` of a braided monoidal category `C`, the
isomorphism `X₁ ⊗ ((V ⊗ (X₂ ⊗ (W ⊗ Y₂))) ⊗ Y₁) ≅ (X₁ ⊗ X₂) ⊗ ((V ⊗ W) ⊗ (Y₂ ⊗ Y₁))` that
moves `X₂` to the left of `V` (Fritz 2020, Prop. 12.18 (b)). -/
def tensorCompReorder (X₁ V X₂ W Y₂ Y₁ : C) :
    X₁ ⊗ ((V ⊗ (X₂ ⊗ (W ⊗ Y₂))) ⊗ Y₁) ≅ (X₁ ⊗ X₂) ⊗ ((V ⊗ W) ⊗ (Y₂ ⊗ Y₁)) :=
  whiskerLeftIso X₁ (whiskerRightIso (tensorLeftComm V X₂ (W ⊗ Y₂)) Y₁ ≪≫
      α_ X₂ (V ⊗ (W ⊗ Y₂)) Y₁) ≪≫
    (α_ X₁ X₂ ((V ⊗ (W ⊗ Y₂)) ⊗ Y₁)).symm ≪≫
    whiskerLeftIso (X₁ ⊗ X₂) (whiskerRightIso (α_ V W Y₂).symm Y₁ ≪≫ α_ (V ⊗ W) Y₂ Y₁)

-- WITNESS: none (restates the definition of tensorCompReorder)
/-- For objects `X₁`, `V`, `X₂`, `W`, `Y₂`, `Y₁` of a braided monoidal category `C`, the
morphism `(tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom` as a composite of whiskered associators,
a whiskered braiding and the inverse of an associator. -/
theorem tensorCompReorder_hom (X₁ V X₂ W Y₂ Y₁ : C) :
    (tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom =
      X₁ ◁ ((α_ V X₂ (W ⊗ Y₂)).inv ≫ (β_ V X₂).hom ▷ (W ⊗ Y₂) ≫
        (α_ X₂ V (W ⊗ Y₂)).hom) ▷ Y₁ ≫
      X₁ ◁ (α_ X₂ (V ⊗ (W ⊗ Y₂)) Y₁).hom ≫ (α_ X₁ X₂ ((V ⊗ (W ⊗ Y₂)) ⊗ Y₁)).inv ≫
      (X₁ ⊗ X₂) ◁ (α_ V W Y₂).inv ▷ Y₁ ≫ (X₁ ⊗ X₂) ◁ (α_ (V ⊗ W) Y₂ Y₁).hom := by
  simp only [tensorCompReorder, tensorLeftComm, Iso.trans_hom, whiskerLeftIso_hom,
    whiskerRightIso_hom, Iso.symm_hom, whiskerLeft_comp, comp_whiskerRight, Category.assoc]

/-- For objects `X`, `W`, `Y` of a braided monoidal category `C`, the isomorphism
`tensorRev₃ X W Y` equals `tensorLeftComm X W Y`, then the braiding of `X` and `Y` whiskered
on the left by `W`, then `tensorLeftComm W Y X` (the reordering of Fritz 2020, Lemma 12.5 (a)
and Prop. 12.17 (a)). -/
theorem tensorRev₃_eq_tensorLeftComm (X W Y : C) :
    tensorRev₃ X W Y =
      tensorLeftComm X W Y ≪≫ whiskerLeftIso W (β_ X Y) ≪≫ tensorLeftComm W Y X := by
  ext
  simp only [tensorRev₃, tensorLeftComm, Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    Iso.symm_hom, BraidedCategory.braiding_tensor_right_hom, Category.assoc]

/-- For morphisms `f : X ⟶ X'`, `g : W ⟶ W'`, `h : Y ⟶ Y'` of a braided monoidal category
`C`, the morphism `(tensorRev₃ X W Y).hom` is natural: `f ⊗ₘ (g ⊗ₘ h)` followed by
`(tensorRev₃ X' W' Y').hom` equals `(tensorRev₃ X W Y).hom` followed by `h ⊗ₘ (g ⊗ₘ f)`
(the reordering of Fritz 2020, Lemma 12.5 (a) and Prop. 12.17 (a)). -/
theorem tensorRev₃_hom_naturality {X W Y X' W' Y' : C} (f : X ⟶ X') (g : W ⟶ W')
    (h : Y ⟶ Y') :
    (f ⊗ₘ (g ⊗ₘ h)) ≫ (tensorRev₃ X' W' Y').hom =
      (tensorRev₃ X W Y).hom ≫ (h ⊗ₘ (g ⊗ₘ f)) := by
  rw [tensorRev₃_hom, tensorRev₃_hom, BraidedCategory.braiding_naturality_assoc]
  simp only [Category.assoc, ← associator_naturality, ← tensorHom_id,
    tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp,
    BraidedCategory.braiding_naturality]

end MonoidalCategory

end CategoryTheory
