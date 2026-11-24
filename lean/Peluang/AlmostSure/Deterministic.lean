/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic
public import Peluang.AlmostSure

/-!
# Almost surely deterministic morphisms

Morphisms that are deterministic almost surely with respect to a morphism into their domain,
in a copy-discard category.

## Main definitions

* `CopyDiscardCategory.IsAlmostSurelyDeterministic` - `f : X ⟶ Y` is `p`-almost surely
  deterministic for `p : A ⟶ X` (Fritz 2020, Def. 13.11).

## Main results

* `CopyDiscardCategory.isAlmostSurelyDeterministic_of_deterministic` - a deterministic
  `f : X ⟶ Y` is `p`-almost surely deterministic for every `p : A ⟶ X` (Fritz 2020, Def. 13.11
  and Def. 10.1).
* `CopyDiscardCategory.IsAlmostSurelyDeterministic.congr` - a morphism `p`-almost surely equal
  to a `p`-almost surely deterministic morphism is `p`-almost surely deterministic
  (Fritz 2020, Lemma 13.12).
* `CopyDiscardCategory.IsAlmostSurelyDeterministic.comp_deterministic` - a `p`-almost surely
  deterministic morphism followed by a deterministic morphism is `p`-almost surely
  deterministic.

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

/-- For `p : A ⟶ X` and `f : X ⟶ Y`, `f` is `p`-almost surely deterministic: `f ≫ Δ[Y]` and
`Δ[X] ≫ (f ⊗ₘ f)` are `p`-almost surely equal (Fritz 2020, Def. 13.11). -/
def IsAlmostSurelyDeterministic {A X Y : C} (p : A ⟶ X) (f : X ⟶ Y) : Prop :=
  AlmostSurelyEq p (f ≫ Δ[Y]) (Δ[X] ≫ (f ⊗ₘ f))

-- WITNESS: none (step of IsAlmostSurelyDeterministic.congr; witnessed through it)
/-- For `f : X ⟶ Y` and `g : X ⟶ Z`, copying `X` into three outputs, applying `f` to the first
and `g` to the third, and rearranging `(Y ⊗ X) ⊗ Z` to `(Y ⊗ Z) ⊗ X` equals copying `X` and
applying `Δ[X] ≫ (f ⊗ₘ g)` to the left copy. -/
theorem copy_comp_copy_tensorHom_whiskerRight {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    Δ[X] ≫ (Δ[X] ▷ X) ≫ ((f ▷ X) ⊗ₘ g) ≫ (α_ Y X Z).hom ≫ (Y ◁ (β_ X Z).hom) ≫
      (α_ Y Z X).inv = Δ[X] ≫ ((Δ[X] ≫ (f ⊗ₘ g)) ▷ X) := by
  calc
    _ = Δ[X] ≫ (Δ[X] ▷ X) ≫ (α_ X X X).hom ≫ (f ▷ (X ⊗ X)) ≫
        (Y ◁ (X ◁ g ≫ (β_ X Z).hom)) ≫ (α_ Y Z X).inv := by
      rw [tensorHom_def]
      monoidal
    _ = Δ[X] ≫ (Δ[X] ▷ X) ≫ (α_ X X X).hom ≫ (X ◁ (β_ X X).hom) ≫ (f ▷ (X ⊗ X)) ≫
        (Y ◁ (g ▷ X)) ≫ (α_ Y Z X).inv := by
      conv_lhs =>
        rw [BraidedCategory.braiding_naturality_right, whiskerLeft_comp, Category.assoc,
          ← whisker_exchange_assoc]
    _ = Δ[X] ≫ (Δ[X] ▷ X) ≫ (α_ X X X).hom ≫ (f ▷ (X ⊗ X)) ≫ (Y ◁ (g ▷ X)) ≫
        (α_ Y Z X).inv := by
      rw [← comul_assoc_assoc, ← whiskerLeft_comp_assoc, IsCommComonObj.comul_comm,
        comul_assoc_assoc]
    _ = _ := by
      rw [tensorHom_def]
      monoidal

/-- A deterministic `f : X ⟶ Y` is `p`-almost surely deterministic for every `p : A ⟶ X`
(Fritz 2020, Def. 13.11 and Def. 10.1). -/
theorem isAlmostSurelyDeterministic_of_deterministic {A X Y : C} (p : A ⟶ X) (f : X ⟶ Y)
    [Deterministic f] : IsAlmostSurelyDeterministic p f := by
  unfold IsAlmostSurelyDeterministic AlmostSurelyEq
  rw [Deterministic.copy_natural f]

/-- For `p : A ⟶ X`, `p`-almost surely equal `f g : X ⟶ Y` and `f` `p`-almost surely
deterministic, `g` is `p`-almost surely deterministic (Fritz 2020, Lemma 13.12). -/
theorem IsAlmostSurelyDeterministic.congr {A X Y : C} {p : A ⟶ X} {f g : X ⟶ Y}
    (h : AlmostSurelyEq p f g) (hf : IsAlmostSurelyDeterministic p f) :
    IsAlmostSurelyDeterministic p g := by
  have h1 := h.comp Δ[Y]
  have h2 := AlmostSurelyEq.copy_tensorHom h h
  unfold IsAlmostSurelyDeterministic at hf ⊢
  unfold AlmostSurelyEq at hf h1 ⊢
  have h3 : ∀ k : X ⟶ Y, p ≫ Δ[X] ≫ ((Δ[X] ≫ (k ⊗ₘ k)) ▷ X) =
      (p ≫ Δ[X] ≫ (Δ[X] ▷ X) ≫ ((k ▷ X) ⊗ₘ k)) ≫ (α_ Y X Y).hom ≫ (Y ◁ (β_ X Y).hom) ≫
        (α_ Y Y X).inv := by
    intro k
    rw [← copy_comp_copy_tensorHom_whiskerRight]
    simp only [Category.assoc]
  rw [← h1, hf, h3 f, h3 g, h2]

/-- For `p : A ⟶ X`, a `p`-almost surely deterministic `f : X ⟶ Y` and a deterministic
`g : Y ⟶ Z`, `f ≫ g` is `p`-almost surely deterministic. -/
theorem IsAlmostSurelyDeterministic.comp_deterministic {A X Y Z : C} {p : A ⟶ X}
    {f : X ⟶ Y} (hf : IsAlmostSurelyDeterministic p f) (g : Y ⟶ Z) [Deterministic g] :
    IsAlmostSurelyDeterministic p (f ≫ g) := by
  have h := AlmostSurelyEq.comp hf (g ⊗ₘ g)
  unfold AlmostSurelyEq at h
  unfold IsAlmostSurelyDeterministic AlmostSurelyEq
  simpa only [Category.assoc, tensorHom_comp_tensorHom, Deterministic.copy_natural g] using h

end CopyDiscardCategory

end CategoryTheory
