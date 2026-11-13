/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic

/-!
# Almost-sure equality

Almost-sure equality of morphisms with respect to a morphism into their common domain, in a
copy-discard category.

## Main definitions

* `CopyDiscardCategory.AlmostSurelyEq` - `f g : X ⟶ Y` are `p`-almost surely equal for
  `p : A ⟶ X` (Fritz 2020, Def. 13.1).

## Main results

* `CopyDiscardCategory.almostSurelyEq_equivalence` - for every `p : A ⟶ X`, `p`-almost sure
  equality is an equivalence relation on `X ⟶ Y`.
* `CopyDiscardCategory.AlmostSurelyEq.comp` - `p`-almost sure equality is preserved by
  postcomposition (Fritz 2020, Lemma 13.4).
* `CopyDiscardCategory.AlmostSurelyEq.copy_tensorHom` - `p`-almost surely equal pairs
  `f₁, f₂ : X ⟶ Y` and `g₁, g₂ : X ⟶ Z` give equal composites
  `p ≫ Δ[X] ≫ (Δ[X] ▷ X) ≫ ((fᵢ ▷ X) ⊗ₘ gᵢ)` (Fritz 2020, Lemma 13.5).

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

/-- For `p : A ⟶ X` and `f g : X ⟶ Y`, `f` and `g` are `p`-almost surely equal:
`p ≫ Δ[X] ≫ (f ▷ X) = p ≫ Δ[X] ≫ (g ▷ X)` (Fritz 2020, Def. 13.1). -/
def AlmostSurelyEq {A X Y : C} (p : A ⟶ X) (f g : X ⟶ Y) : Prop :=
  p ≫ Δ[X] ≫ (f ▷ X) = p ≫ Δ[X] ≫ (g ▷ X)

/-- For every `p : A ⟶ X`, `p`-almost sure equality is an equivalence relation on
`X ⟶ Y`. -/
theorem almostSurelyEq_equivalence {A X Y : C} (p : A ⟶ X) :
    _root_.Equivalence (AlmostSurelyEq (Y := Y) p) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- For `p : A ⟶ X`, `p`-almost surely equal `f g : X ⟶ Y` and every `k : Y ⟶ Z`, `f ≫ k`
and `g ≫ k` are `p`-almost surely equal (Fritz 2020, Lemma 13.4). -/
theorem AlmostSurelyEq.comp {A X Y Z : C} {p : A ⟶ X} {f g : X ⟶ Y}
    (h : AlmostSurelyEq p f g) (k : Y ⟶ Z) : AlmostSurelyEq p (f ≫ k) (g ≫ k) := by
  unfold AlmostSurelyEq at h ⊢
  simp only [comp_whiskerRight]
  rw [reassoc_of% h]

/-- For `p : A ⟶ X`, `p`-almost surely equal `f₁ f₂ : X ⟶ Y` and `p`-almost surely equal
`g₁ g₂ : X ⟶ Z`, copying `X` into three outputs and applying `fᵢ`, the identity and `gᵢ`
to them gives the same morphism `A ⟶ (Y ⊗ X) ⊗ Z` for `i = 1, 2`
(Fritz 2020, Lemma 13.5). -/
theorem AlmostSurelyEq.copy_tensorHom {A X Y Z : C} {p : A ⟶ X} {f₁ f₂ : X ⟶ Y}
    {g₁ g₂ : X ⟶ Z} (hf : AlmostSurelyEq p f₁ f₂) (hg : AlmostSurelyEq p g₁ g₂) :
    p ≫ Δ[X] ≫ (Δ[X] ▷ X) ≫ ((f₁ ▷ X) ⊗ₘ g₁) = p ≫ Δ[X] ≫ (Δ[X] ▷ X) ≫ ((f₂ ▷ X) ⊗ₘ g₂) := by
  have key1 : ∀ (f : X ⟶ Y) (g : X ⟶ Z), Δ[X] ≫ (Δ[X] ▷ X) ≫ ((f ▷ X) ⊗ₘ g) =
      Δ[X] ≫ (f ▷ X) ≫ (Y ◁ (Δ[X] ≫ (X ◁ g))) ≫ (α_ Y X Z).inv := by
    intro f g
    rw [comul_assoc_flip_assoc, whiskerLeft_comp, Category.assoc, ← whisker_exchange_assoc]
    congr 2
    simp [tensorHom_def]
  have key2 : ∀ (f : X ⟶ Y) (g : X ⟶ Z), Δ[X] ≫ (Δ[X] ▷ X) ≫ ((f ▷ X) ⊗ₘ g) =
      Δ[X] ≫ (g ▷ X) ≫ (Z ◁ (Δ[X] ≫ (f ▷ X))) ≫ (β_ Z (Y ⊗ X)).hom := by
    intro f g
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, ← tensorHom_def_assoc,
      BraidedCategory.braiding_naturality, IsCommComonObj.comul_comm_assoc]
  rw [key1 f₁ g₁, reassoc_of% hf, ← key1 f₂ g₁, key2 f₂ g₁, reassoc_of% hg, ← key2 f₂ g₂]

end CopyDiscardCategory

end CategoryTheory
