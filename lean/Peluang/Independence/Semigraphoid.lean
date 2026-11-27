/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Conditional.Snd
public import Peluang.Independence
public import Peluang.Monoidal.Reorder

/-!
# The semigraphoid properties

The semigraphoid properties of independence given an input, and of conditional independence
for a state. The semigraphoid properties of conditional independence given an input
(Fritz 2020, Prop. 12.17).

## Main results

* `CopyDiscardCategory.DisplaysIndep.symm` - if `f : A ⟶ X ⊗ Y` displays independence, then
  `f ≫ (β_ X Y).hom` displays independence (Fritz 2020, Lemma 12.13 (a)).
* `CopyDiscardCategory.DisplaysIndep.decomposition` - if `f : A ⟶ (X₁ ⊗ X₂) ⊗ Y` displays
  independence, then its marginal on `X₁ ⊗ Y` displays independence (Fritz 2020,
  Lemma 12.13 (b)).
* `CopyDiscardCategory.DisplaysCondIndepState.symm` - if a state `ψ : 𝟙_ C ⟶ X ⊗ (W ⊗ Y)`
  displays conditional independence, then `ψ ≫ (tensorRev₃ X W Y).hom` displays conditional
  independence (Fritz 2020, Lemma 12.5 (a)).
* `CopyDiscardCategory.DisplaysCondIndepState.decomposition` - if a state
  `ψ : 𝟙_ C ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)` displays conditional independence, then its marginal on
  `X₁ ⊗ (W ⊗ Y)` displays conditional independence (Fritz 2020, Lemma 12.5 (b)).
* `CopyDiscardCategory.DisplaysCondIndepState.contraction` - in a Markov category, if a state
  `ψ : 𝟙_ C ⟶ X ⊗ ((W ⊗ Z) ⊗ Y)` and its marginal on `X ⊗ (W ⊗ Z)` display conditional
  independence, then `ψ ≫ X ◁ (α_ W Z Y).hom` displays conditional independence (Fritz 2020,
  Lemma 12.5 (c)).
* `CopyDiscardCategory.DisplaysCondIndepState.weak_union` - in a copy-discard category with
  conditionals, if a state `ψ : 𝟙_ C ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)` displays conditional
  independence, then `ψ ≫ (tensorWeakUnionIso X₁ X₂ W Y).hom` displays conditional
  independence (Fritz 2020, Lemma 12.5 (d)).
* `CopyDiscardCategory.DisplaysCondIndep.symm` - if `f : A ⟶ X ⊗ (W ⊗ Y)` displays conditional
  independence, then `f ≫ (tensorRev₃ X W Y).hom` displays conditional independence
  (Fritz 2020, Prop. 12.17 (a)).
* `CopyDiscardCategory.DisplaysCondIndep.decomposition` - if `f : A ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)`
  displays conditional independence, then its marginal on `X₁ ⊗ (W ⊗ Y)` displays conditional
  independence (Fritz 2020, Prop. 12.17 (b)).
* `CopyDiscardCategory.DisplaysCondIndep.contraction` - in a Markov category, if
  `f : A ⟶ X ⊗ ((W ⊗ Z) ⊗ Y)` and its marginal on `X ⊗ (W ⊗ Z)` display conditional
  independence, then `f ≫ X ◁ (α_ W Z Y).hom` displays conditional independence (Fritz 2020,
  Prop. 12.17 (c)).
* `CopyDiscardCategory.DisplaysCondIndep.weak_union` - in a copy-discard category with
  conditionals, if `f : A ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)` displays conditional independence, then
  `f ≫ (tensorWeakUnionIso X₁ X₂ W Y).hom` displays conditional independence (Fritz 2020,
  Prop. 12.17 (d)).

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
-/

public section

universe v u

namespace CategoryTheory

namespace CopyDiscardCategory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

/-- For `f : A ⟶ X ⊗ Y` in a copy-discard category `C`, if `f` displays the independence of
`X` and `Y` given `A`, then `f ≫ (β_ X Y).hom : A ⟶ Y ⊗ X` displays the independence of `Y`
and `X` given `A` (Fritz 2020, Lemma 12.13 (a)). -/
theorem DisplaysIndep.symm {A X Y : C} {f : A ⟶ X ⊗ Y} (hf : DisplaysIndep f) :
    DisplaysIndep (f ≫ (β_ X Y).hom) := by
  unfold DisplaysIndep at hf ⊢
  rw [marginalFst_comp_braiding_hom, marginalSnd_comp_braiding_hom]
  conv_lhs => rw [hf]
  rw [Category.assoc, BraidedCategory.braiding_naturality, IsCommComonObj.comul_comm_assoc]

-- WITNESS: none (step of DisplaysIndep.decomposition; witnessed through it)
/-- For objects `X₁`, `X₂` of a copy-discard category `C`, discarding `X₂` from `X₁ ⊗ X₂` and
then discarding `X₁` equals the discard of `X₁ ⊗ X₂`. -/
theorem fst_comp_discard (X₁ X₂ : C) :
    (X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ≫ ε[X₁] =
      @ComonObj.counit C _ _ (X₁ ⊗ X₂) (CopyDiscardCategory.comonObj (X₁ ⊗ X₂)) := by
  rw [discard_tensor, tensorHom_def']
  simp only [Category.assoc]
  rw [← rightUnitor_naturality, unitors_equal]

/-- For `f : A ⟶ (X₁ ⊗ X₂) ⊗ Y` in a copy-discard category `C`, if `f` displays the
independence of `X₁ ⊗ X₂` and `Y` given `A`, then `f ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ Y)`,
which drops the second factor `X₂` of the first place, displays the independence of `X₁` and
`Y` given `A` (Fritz 2020, Lemma 12.13 (b)). -/
theorem DisplaysIndep.decomposition {A X₁ X₂ Y : C} {f : A ⟶ (X₁ ⊗ X₂) ⊗ Y}
    (hf : DisplaysIndep f) :
    DisplaysIndep (f ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ Y)) := by
  unfold DisplaysIndep at hf ⊢
  have e1 : marginalFst (f ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ Y)) =
      marginalFst f ≫ (X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) := by
    simp only [marginalFst, Category.assoc]
    rw [← whisker_exchange_assoc, rightUnitor_naturality]
  have e2 : marginalSnd (f ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ Y)) = marginalSnd f := by
    simp only [marginalSnd, Category.assoc]
    rw [← comp_whiskerRight_assoc, fst_comp_discard]
  rw [e1, e2]
  conv_lhs => rw [hf]
  rw [Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]

-- WITNESS: none (step of DisplaysCondIndepState.symm; witnessed through it)
/-- For an object `X` of a copy-discard category `C`, the composite
`Δ[X] ≫ X ◁ Δ[X] : X ⟶ X ⊗ (X ⊗ X)`, which copies `X` and then copies the right copy, followed
by `(tensorRev₃ X X X).hom` equals `Δ[X] ≫ X ◁ Δ[X]`. -/
theorem copy_comp_whiskerLeft_copy_comp_tensorRev₃_hom (X : C) :
    Δ[X] ≫ X ◁ Δ[X] ≫ (tensorRev₃ X X X).hom = Δ[X] ≫ X ◁ Δ[X] := by
  rw [tensorRev₃_hom, BraidedCategory.braiding_naturality_right_assoc,
    IsCommComonObj.comul_comm_assoc, ← comp_whiskerRight_assoc, IsCommComonObj.comul_comm,
    ← comul_assoc]

/-- For a state `ψ : 𝟙_ C ⟶ X ⊗ (W ⊗ Y)` in a copy-discard category `C`, if `ψ` displays the
conditional independence of `X` and `Y` given `W`, then
`ψ ≫ (tensorRev₃ X W Y).hom : 𝟙_ C ⟶ Y ⊗ (W ⊗ X)` displays the conditional independence of `Y`
and `X` given `W` (Fritz 2020, Lemma 12.5 (a)). -/
theorem DisplaysCondIndepState.symm {X W Y : C} {ψ : 𝟙_ C ⟶ X ⊗ (W ⊗ Y)}
    (hψ : DisplaysCondIndepState ψ) :
    DisplaysCondIndepState (ψ ≫ (tensorRev₃ X W Y).hom) := by
  obtain ⟨φ, f, g, rfl⟩ := hψ
  refine ⟨φ, g, f, ?_⟩
  have e := tensorRev₃_hom_naturality f (𝟙 W) g
  simp only [id_tensorHom] at e
  simp only [Category.assoc]
  rw [e, reassoc_of% copy_comp_whiskerLeft_copy_comp_tensorRev₃_hom W]

/-- For a state `ψ : 𝟙_ C ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)` in a copy-discard category `C`, if `ψ`
displays the conditional independence of `X₁ ⊗ X₂` and `Y` given `W`, then
`ψ ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ (W ⊗ Y))`, which drops the second factor `X₂` of the first
place, displays the conditional independence of `X₁` and `Y` given `W` (Fritz 2020,
Lemma 12.5 (b)). -/
theorem DisplaysCondIndepState.decomposition {X₁ X₂ W Y : C}
    {ψ : 𝟙_ C ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)} (hψ : DisplaysCondIndepState ψ) :
    DisplaysCondIndepState (ψ ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ (W ⊗ Y))) := by
  obtain ⟨φ, f, g, rfl⟩ := hψ
  refine ⟨φ, f ≫ X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom, g, ?_⟩
  simp only [Category.assoc]
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]

-- WITNESS: none (step of DisplaysCondIndepState.contraction; witnessed through it)
/-- For `k : W ⟶ Z` and `g : W ⊗ Z ⟶ Y` in a copy-discard category `C`, copying `W`, applying
`k` to the right copy, copying `W ⊗ Z`, applying `g` to the right copy and reassociating
equals copying `W` and applying
`Δ[W] ≫ W ◁ (k ≫ Δ[Z]) ≫ (α_ W Z Z).inv ≫ (β_ W Z).hom ▷ Z ≫ (α_ Z W Z).hom ≫ Z ◁ g` to the
right copy. -/
theorem copy_comp_whiskerLeft_comp_copy_tensor {W Z Y : C} (k : W ⟶ Z) (g : W ⊗ Z ⟶ Y) :
    Δ[W] ≫ W ◁ k ≫ @ComonObj.comul C _ _ (W ⊗ Z) (CopyDiscardCategory.comonObj (W ⊗ Z)) ≫
        (W ⊗ Z) ◁ g ≫ (α_ W Z Y).hom =
      Δ[W] ≫ W ◁ (Δ[W] ≫ W ◁ (k ≫ Δ[Z]) ≫ (α_ W Z Z).inv ≫ (β_ W Z).hom ▷ Z ≫
        (α_ Z W Z).hom ≫ Z ◁ g) := by
  rw [copy_tensor, tensorHom_def]
  simp only [tensorμ, Category.assoc]
  rw [whisker_exchange_assoc]
  calc
    _ = (Δ[W] ≫ Δ[W] ▷ W ≫ (α_ W W W).hom) ≫ W ◁ (W ◁ (k ≫ Δ[Z]) ≫ (α_ W Z Z).inv ≫
          (β_ W Z).hom ▷ Z ≫ (α_ Z W Z).hom ≫ Z ◁ g) := by
      monoidal
    _ = _ := by
      rw [← comul_assoc]
      monoidal

-- WITNESS: none (step of DisplaysCondIndepState.weak_union; witnessed through it)
/-- For objects `A`, `B` of a copy-discard category `C`, copying `A ⊗ B` and discarding `B`
from the right copy equals copying `A` and moving the right copy of `A` past `B`. -/
theorem copy_tensor_comp_whiskerLeft_fst (A B : C) :
    @ComonObj.comul C _ _ (A ⊗ B) (CopyDiscardCategory.comonObj (A ⊗ B)) ≫
        (A ⊗ B) ◁ (A ◁ ε[B] ≫ (ρ_ A).hom) =
      Δ[A] ▷ B ≫ (α_ A A B).hom ≫ A ◁ (β_ A B).hom ≫ (α_ A B A).inv := by
  have e : (A ⊗ B) ◁ (A ◁ ε[B] ≫ (ρ_ A).hom) =
      ((𝟙 A ⊗ₘ 𝟙 B) ⊗ₘ (𝟙 A ⊗ₘ ε[B])) ≫ ((A ⊗ B) ◁ (ρ_ A).hom) := by
    simp only [id_tensorHom, whiskerLeft_id, whiskerLeft_comp]
  rw [copy_tensor, e, Category.assoc, ← tensorμ_natural_assoc, tensorHom_comp_tensorHom_assoc,
    comul_counit_hom]
  simp only [id_tensorHom_id, Category.comp_id, Category.id_comp, tensorμ]
  monoidal

-- WITNESS: none (step of DisplaysCondIndepState.weak_union; witnessed through it)
/-- For objects `A`, `B` of a copy-discard category `C`, braiding `B ⊗ A` to `A ⊗ B`, copying
`A` and moving the right copy of `A` past `B` equals copying `A` in `B ⊗ A` and braiding `B`
past the left copy of `A`. -/
theorem braiding_comp_copy_whiskerRight (A B : C) :
    (β_ B A).hom ≫ Δ[A] ▷ B ≫ (α_ A A B).hom ≫ A ◁ (β_ A B).hom ≫ (α_ A B A).inv =
      B ◁ Δ[A] ≫ (α_ B A A).inv ≫ (β_ B A).hom ▷ A := by
  rw [← BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry, whiskerLeft_id, Category.id_comp,
    Iso.hom_inv_id, Category.comp_id]

-- WITNESS: none (step of DisplaysCondIndepState.weak_union; witnessed through it)
/-- For objects `A`, `B` of a copy-discard category `C`, braiding `B ⊗ A` to `A ⊗ B`, copying
`A ⊗ B` and discarding `B` from the right copy equals copying `A` in `B ⊗ A` and braiding `B`
past the left copy of `A`. -/
theorem braiding_comp_copy_tensor_comp_whiskerLeft_fst (A B : C) :
    (β_ B A).hom ≫ @ComonObj.comul C _ _ (A ⊗ B) (CopyDiscardCategory.comonObj (A ⊗ B)) ≫
        (A ⊗ B) ◁ (A ◁ ε[B] ≫ (ρ_ A).hom) =
      B ◁ Δ[A] ≫ (α_ B A A).inv ≫ (β_ B A).hom ▷ A := by
  rw [copy_tensor_comp_whiskerLeft_fst, braiding_comp_copy_whiskerRight]

-- WITNESS: none (step of DisplaysCondIndepState.weak_union; witnessed through it)
/-- For `s : W ⟶ B` in a copy-discard category `C`, copying `W`, applying `s` to the right
copy and copying `W ⊗ B` equals copying `W`, applying
`Δ[W] ≫ W ◁ (s ≫ Δ[B]) ≫ (α_ W B B).inv` to the left copy, and braiding the right copy of `W`
past the right copy of `B`. -/
theorem copy_comp_whiskerLeft_comp_copy_tensor_eq {W B : C} (s : W ⟶ B) :
    Δ[W] ≫ W ◁ s ≫ @ComonObj.comul C _ _ (W ⊗ B) (CopyDiscardCategory.comonObj (W ⊗ B)) =
      Δ[W] ≫ (Δ[W] ≫ W ◁ (s ≫ Δ[B]) ≫ (α_ W B B).inv) ▷ W ≫ (α_ (W ⊗ B) B W).hom ≫
        (W ⊗ B) ◁ (β_ B W).hom := by
  have inner : (β_ W W).hom ≫ W ◁ (s ≫ Δ[B]) ≫ (α_ W B B).inv ≫ (β_ W B).hom ▷ B ≫
      (α_ B W B).hom = (s ≫ Δ[B]) ▷ W ≫ (α_ B B W).hom ≫ B ◁ (β_ B W).hom := by
    rw [← BraidedCategory.braiding_naturality_left_assoc,
      BraidedCategory.braiding_tensor_left_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry, id_whiskerRight,
      Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  rw [copy_tensor, tensorHom_def]
  simp only [tensorμ, Category.assoc]
  rw [whisker_exchange_assoc]
  calc
    _ = (Δ[W] ≫ Δ[W] ▷ W ≫ (α_ W W W).hom) ≫ W ◁ (W ◁ (s ≫ Δ[B]) ≫ (α_ W B B).inv ≫
          (β_ W B).hom ▷ B ≫ (α_ B W B).hom) ≫ (α_ W B (W ⊗ B)).inv := by
      monoidal
    _ = Δ[W] ≫ W ◁ (Δ[W] ≫ (β_ W W).hom ≫ W ◁ (s ≫ Δ[B]) ≫ (α_ W B B).inv ≫
          (β_ W B).hom ▷ B ≫ (α_ B W B).hom) ≫ (α_ W B (W ⊗ B)).inv := by
      rw [← comul_assoc, IsCommComonObj.comul_comm_assoc]
      simp only [whiskerLeft_comp, Category.assoc]
    _ = (Δ[W] ≫ W ◁ Δ[W]) ≫ W ◁ ((s ≫ Δ[B]) ▷ W ≫ (α_ B B W).hom ≫ B ◁ (β_ B W).hom) ≫
          (α_ W B (W ⊗ B)).inv := by
      rw [inner]
      simp only [whiskerLeft_comp, Category.assoc]
    _ = (Δ[W] ≫ Δ[W] ▷ W ≫ (α_ W W W).hom) ≫
          W ◁ ((s ≫ Δ[B]) ▷ W ≫ (α_ B B W).hom ≫ B ◁ (β_ B W).hom) ≫
          (α_ W B (W ⊗ B)).inv := by
      rw [comul_assoc]
    _ = _ := by
      monoidal

/-- For a state `ψ : 𝟙_ C ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)` in a copy-discard category `C` with
conditionals, if `ψ` displays the conditional independence of `X₁ ⊗ X₂` and `Y` given `W`,
then `ψ ≫ (tensorWeakUnionIso X₁ X₂ W Y).hom : 𝟙_ C ⟶ X₁ ⊗ ((W ⊗ X₂) ⊗ Y)` displays the
conditional independence of `X₁` and `Y` given `W ⊗ X₂` (Fritz 2020, Lemma 12.5 (d)). -/
theorem DisplaysCondIndepState.weak_union [HasConditionals C] {X₁ X₂ W Y : C}
    {ψ : 𝟙_ C ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)} (hψ : DisplaysCondIndepState ψ) :
    DisplaysCondIndepState (ψ ≫ (tensorWeakUnionIso X₁ X₂ W Y).hom) := by
  obtain ⟨φ, f, g, rfl⟩ := hψ
  obtain ⟨c, hc⟩ := exists_isConditionalSnd f
  rw [isConditionalSnd_iff] at hc
  refine ⟨φ ≫ Δ[W] ≫ W ◁ marginalSnd f, (β_ W X₂).hom ≫ c,
    (W ◁ ε[X₂] ≫ (ρ_ W).hom) ≫ g, ?_⟩
  generalize marginalSnd f = s at hc ⊢
  subst hc
  rw [tensorWeakUnionIso_hom]
  symm
  calc
    _ = φ ≫ (Δ[W] ≫ W ◁ s ≫
            @ComonObj.comul C _ _ (W ⊗ X₂) (CopyDiscardCategory.comonObj (W ⊗ X₂))) ≫
          (W ⊗ X₂) ◁ (@ComonObj.comul C _ _ (W ⊗ X₂) (CopyDiscardCategory.comonObj (W ⊗ X₂)) ≫
            (W ⊗ X₂) ◁ (W ◁ ε[X₂] ≫ (ρ_ W).hom)) ≫
          (((β_ W X₂).hom ≫ c) ⊗ₘ (W ⊗ X₂) ◁ g) := by
      simp only [tensorHom_def', whiskerLeft_comp, Category.assoc]
    _ = φ ≫ Δ[W] ≫ (Δ[W] ≫ W ◁ (s ≫ Δ[X₂]) ≫ (α_ W X₂ X₂).inv) ▷ W ≫
          (α_ (W ⊗ X₂) X₂ W).hom ≫
          (W ⊗ X₂) ◁ ((β_ X₂ W).hom ≫
            @ComonObj.comul C _ _ (W ⊗ X₂) (CopyDiscardCategory.comonObj (W ⊗ X₂)) ≫
            (W ⊗ X₂) ◁ (W ◁ ε[X₂] ≫ (ρ_ W).hom)) ≫
          (((β_ W X₂).hom ≫ c) ⊗ₘ (W ⊗ X₂) ◁ g) := by
      rw [copy_comp_whiskerLeft_comp_copy_tensor_eq]
      simp only [whiskerLeft_comp, Category.assoc]
    _ = φ ≫ Δ[W] ≫ (Δ[W] ≫ W ◁ (s ≫ Δ[X₂]) ≫ (α_ W X₂ X₂).inv) ▷ W ≫
          (α_ (W ⊗ X₂) X₂ W).hom ≫ ((β_ W X₂).hom ≫ c) ▷ (X₂ ⊗ W) ≫
          X₁ ◁ (X₂ ◁ Δ[W] ≫ (α_ X₂ W W).inv ≫ (β_ X₂ W).hom ▷ W ≫ (W ⊗ X₂) ◁ g) := by
      rw [braiding_comp_copy_tensor_comp_whiskerLeft_fst, tensorHom_def',
        ← whiskerLeft_comp_assoc, whisker_exchange]
      simp only [Category.assoc]
    _ = φ ≫ Δ[W] ≫ (Δ[W] ≫ W ◁ (s ≫ Δ[X₂]) ≫ (α_ W X₂ X₂).inv) ▷ W ≫
          (α_ (W ⊗ X₂) X₂ W).hom ≫ ((β_ W X₂).hom ≫ c) ▷ (X₂ ⊗ W) ≫
          X₁ ◁ (X₂ ◁ Δ[W] ≫ X₂ ◁ W ◁ g ≫ (α_ X₂ W Y).inv ≫ (β_ X₂ W).hom ▷ Y) := by
      rw [← whisker_exchange (β_ X₂ W).hom g, ← associator_inv_naturality_right_assoc]
    _ = _ := by
      rw [tensorHom_def]
      simp only [Category.assoc]
      rw [whisker_exchange_assoc]
      monoidal

-- WITNESS: none (step of DisplaysCondIndep.symm; witnessed through it)
/-- For objects `A`, `W` of a copy-discard category `C`, copying `A ⊗ W` and discarding `A`
from the left copy equals copying `W` in `A ⊗ W`, braiding `A` past the left copy of `W` and
reassociating. -/
theorem copy_tensor_comp_snd_whiskerRight (A W : C) :
    @ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        ((ε[A] ▷ W ≫ (λ_ W).hom) ▷ (A ⊗ W)) =
      A ◁ Δ[W] ≫ (α_ A W W).inv ≫ (β_ A W).hom ▷ W ≫ (α_ W A W).hom := by
  have e : (ε[A] ▷ W ≫ (λ_ W).hom) ▷ (A ⊗ W) =
      ((ε[A] ⊗ₘ 𝟙 W) ⊗ₘ (𝟙 A ⊗ₘ 𝟙 W)) ≫ ((λ_ W).hom ▷ (A ⊗ W)) := by
    simp only [tensorHom_id, id_whiskerRight, comp_whiskerRight]
  rw [copy_tensor, e, Category.assoc, ← tensorμ_natural_assoc, tensorHom_comp_tensorHom_assoc,
    counit_comul_hom]
  simp only [id_tensorHom_id, Category.comp_id, Category.id_comp, tensorμ]
  monoidal

-- WITNESS: none (step of DisplaysCondIndep.symm; witnessed through it)
/-- For objects `A`, `W` of a copy-discard category `C`, copying `A ⊗ W`, discarding `A` from
the left copy and braiding the right copy to `W ⊗ A` equals braiding `A ⊗ W` to `W ⊗ A`,
copying `W` and reassociating. -/
theorem copy_tensor_comp_snd_tensorHom_braiding (A W : C) :
    @ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        ((ε[A] ▷ W ≫ (λ_ W).hom) ⊗ₘ (β_ A W).hom) =
      (β_ A W).hom ≫ Δ[W] ▷ A ≫ (α_ W W A).hom := by
  rw [tensorHom_def, reassoc_of% copy_tensor_comp_snd_whiskerRight,
    ← BraidedCategory.braiding_naturality_right_assoc, BraidedCategory.braiding_tensor_right_hom]
  monoidal

-- WITNESS: none (step of DisplaysCondIndep.symm; witnessed through it)
/-- For objects `A`, `W` of a copy-discard category `C`, copying `A ⊗ W` and braiding the right
copy to `W ⊗ A` equals copying `A` and `W`, braiding the right copy of `A` past the two copies
of `W` and reassociating. -/
theorem copy_tensor_comp_whiskerLeft_braiding (A W : C) :
    @ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        (A ⊗ W) ◁ (β_ A W).hom =
      (Δ[A] ⊗ₘ Δ[W]) ≫ (α_ A A (W ⊗ W)).hom ≫ A ◁ (β_ A (W ⊗ W)).hom ≫
        A ◁ (α_ W W A).hom ≫ (α_ A W (W ⊗ A)).inv := by
  rw [copy_tensor, BraidedCategory.braiding_tensor_right_hom]
  simp only [tensorμ]
  monoidal

-- WITNESS: none (step of DisplaysCondIndep.symm; witnessed through it)
/-- For `g : A ⟶ W`, `h : A ⊗ W ⟶ X` and `k : W ⊗ A ⟶ Y` in a copy-discard category `C`,
`condIndepForm g h k` equals copying `A`, applying `g` to the right copy, copying `A ⊗ W`,
copying its right copy, and applying `h` to the first copy of `A ⊗ W`, discarding `A` from the
second copy, and braiding the third copy to `W ⊗ A` and applying `k` to it (Fritz 2020,
Def. 12.16). -/
theorem condIndepForm_eq_copy_tensor {A X W Y : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X)
    (k : W ⊗ A ⟶ Y) :
    condIndepForm g h k =
      Δ[A] ≫ A ◁ g ≫ @ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        (A ⊗ W) ◁ @ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        (h ⊗ₘ ((ε[A] ▷ W ≫ (λ_ W).hom) ⊗ₘ ((β_ A W).hom ≫ k))) := by
  have e1 : (A ⊗ W) ◁ @ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        (h ⊗ₘ ((ε[A] ▷ W ≫ (λ_ W).hom) ⊗ₘ ((β_ A W).hom ≫ k))) =
      (A ⊗ W) ◁ (@ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
          ((ε[A] ▷ W ≫ (λ_ W).hom) ⊗ₘ (β_ A W).hom)) ≫
        (A ⊗ W) ◁ W ◁ k ≫ h ▷ (W ⊗ Y) := by
    rw [tensorHom_def' h]
    monoidal
  have s : Δ[A] ≫ Δ[A] ▷ A ≫ (A ⊗ A) ◁ g ≫ (A ⊗ A) ◁ Δ[W] ≫ (α_ A A (W ⊗ W)).hom ≫
        A ◁ (β_ A (W ⊗ W)).hom =
      Δ[A] ≫ A ◁ (Δ[A] ≫ (g ≫ Δ[W]) ▷ A) := by
    calc
      _ = (Δ[A] ≫ Δ[A] ▷ A ≫ (α_ A A A).hom) ≫
            A ◁ (A ◁ (g ≫ Δ[W]) ≫ (β_ A (W ⊗ W)).hom) := by
        monoidal
      _ = Δ[A] ≫ A ◁ ((Δ[A] ≫ (β_ A A).hom) ≫ (g ≫ Δ[W]) ▷ A) := by
        rw [← comul_assoc, BraidedCategory.braiding_naturality_right]
        simp only [whiskerLeft_comp, Category.assoc]
      _ = _ := by
        rw [IsCommComonObj.comul_comm]
  rw [e1, copy_tensor_comp_snd_tensorHom_braiding]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% copy_tensor_comp_whiskerLeft_braiding, tensorHom_def]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, reassoc_of% s]
  unfold condIndepForm
  rw [tensorHom_def']
  monoidal

-- WITNESS: none (step of DisplaysCondIndep.symm; witnessed through it)
/-- For `g : A ⟶ W`, `h : A ⊗ W ⟶ X` and `k : W ⊗ A ⟶ Y` in a copy-discard category `C`,
`condIndepForm g h k ≫ (tensorRev₃ X W Y).hom : A ⟶ Y ⊗ (W ⊗ X)` equals
`condIndepForm g ((β_ A W).hom ≫ k) ((β_ W A).hom ≫ h)` (Fritz 2020, Def. 12.16). -/
theorem condIndepForm_comp_tensorRev₃ {A X W Y : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X)
    (k : W ⊗ A ⟶ Y) :
    condIndepForm g h k ≫ (tensorRev₃ X W Y).hom =
      condIndepForm g ((β_ A W).hom ≫ k) ((β_ W A).hom ≫ h) := by
  rw [condIndepForm_eq_copy_tensor, condIndepForm_eq_copy_tensor]
  simp only [Category.assoc]
  rw [tensorRev₃_hom_naturality,
    reassoc_of% copy_comp_whiskerLeft_copy_comp_tensorRev₃_hom (A ⊗ W),
    SymmetricCategory.symmetry_assoc]

/-- For `f : A ⟶ X ⊗ (W ⊗ Y)` in a copy-discard category `C`, if `f` displays the conditional
independence of `X` and `Y` given `W` and `A`, then
`f ≫ (tensorRev₃ X W Y).hom : A ⟶ Y ⊗ (W ⊗ X)` displays the conditional independence of `Y`
and `X` given `W` and `A` (Fritz 2020, Prop. 12.17 (a)). -/
theorem DisplaysCondIndep.symm {A X W Y : C} {f : A ⟶ X ⊗ (W ⊗ Y)}
    (hf : DisplaysCondIndep f) :
    DisplaysCondIndep (f ≫ (tensorRev₃ X W Y).hom) := by
  obtain ⟨g, h, k, rfl⟩ := hf
  exact ⟨g, (β_ A W).hom ≫ k, (β_ W A).hom ≫ h, condIndepForm_comp_tensorRev₃ g h k⟩

-- WITNESS: none (step of DisplaysCondIndep.decomposition; witnessed through it)
/-- For `g : A ⟶ W`, `h : A ⊗ W ⟶ X`, `k : W ⊗ A ⟶ Y`, `u : X ⟶ X'` and `v : Y ⟶ Y'` in a
copy-discard category `C`, `condIndepForm g h k ≫ (u ⊗ₘ W ◁ v) : A ⟶ X' ⊗ (W ⊗ Y')` equals
`condIndepForm g (h ≫ u) (k ≫ v)` (Fritz 2020, Def. 12.16). -/
theorem condIndepForm_comp_tensorHom_whiskerLeft {A X X' W Y Y' : C} (g : A ⟶ W)
    (h : A ⊗ W ⟶ X) (k : W ⊗ A ⟶ Y) (u : X ⟶ X') (v : Y ⟶ Y') :
    condIndepForm g h k ≫ (u ⊗ₘ W ◁ v) = condIndepForm g (h ≫ u) (k ≫ v) := by
  unfold condIndepForm
  simp only [Category.assoc, tensorHom_comp_tensorHom, whiskerLeft_comp]

/-- For `f : A ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)` in a copy-discard category `C`, if `f` displays the
conditional independence of `X₁ ⊗ X₂` and `Y` given `W` and `A`, then
`f ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ (W ⊗ Y)) : A ⟶ X₁ ⊗ (W ⊗ Y)`, which drops the second factor
`X₂` of the first place, displays the conditional independence of `X₁` and `Y` given `W` and
`A` (Fritz 2020, Prop. 12.17 (b)). -/
theorem DisplaysCondIndep.decomposition {A X₁ X₂ W Y : C}
    {f : A ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)} (hf : DisplaysCondIndep f) :
    DisplaysCondIndep (f ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ (W ⊗ Y))) := by
  obtain ⟨g, h, k, rfl⟩ := hf
  refine ⟨g, h ≫ X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom, k, ?_⟩
  have e := condIndepForm_comp_tensorHom_whiskerLeft g h k (X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) (𝟙 Y)
  rw [whiskerLeft_id, tensorHom_id, Category.comp_id] at e
  exact e

-- WITNESS: none (step of DisplaysCondIndep.contraction, DisplaysCondIndep.weak_union)
/-- For `g : A ⟶ W`, `h : A ⊗ W ⟶ X` and `k : W ⊗ A ⟶ Y` in a copy-discard category `C`,
`condIndepForm g h k` equals copying `A`, applying
`Δ[A] ≫ A ◁ (g ≫ Δ[W]) ≫ (α_ A W W).inv ≫ h ▷ W : A ⟶ X ⊗ W` to the left copy, copying `W`,
and applying `k` to the right copy of `W` and the right copy of `A` (Fritz 2020,
Def. 12.16). -/
theorem condIndepForm_eq_copy_comp_whiskerRight {A X W Y : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X)
    (k : W ⊗ A ⟶ Y) :
    condIndepForm g h k =
      Δ[A] ≫ (Δ[A] ≫ A ◁ (g ≫ Δ[W]) ≫ (α_ A W W).inv ≫ h ▷ W) ▷ A ≫ (α_ X W A).hom ≫
        X ◁ (Δ[W] ▷ A ≫ (α_ W W A).hom ≫ W ◁ k) := by
  unfold condIndepForm
  rw [tensorHom_def']
  calc
    _ = (Δ[A] ≫ A ◁ Δ[A]) ≫ A ◁ ((g ≫ Δ[W]) ▷ A) ≫ (α_ A (W ⊗ W) A).inv ≫
          (α_ A W W).inv ▷ A ≫ (α_ (A ⊗ W) W A).hom ≫
          (A ⊗ W) ◁ (Δ[W] ▷ A ≫ (α_ W W A).hom ≫ W ◁ k) ≫ h ▷ (W ⊗ Y) := by
      monoidal
    _ = (Δ[A] ≫ Δ[A] ▷ A ≫ (α_ A A A).hom) ≫ A ◁ ((g ≫ Δ[W]) ▷ A) ≫
          (α_ A (W ⊗ W) A).inv ≫ (α_ A W W).inv ▷ A ≫ (α_ (A ⊗ W) W A).hom ≫
          h ▷ (W ⊗ A) ≫ X ◁ (Δ[W] ▷ A ≫ (α_ W W A).hom ≫ W ◁ k) := by
      rw [comul_assoc, whisker_exchange]
    _ = _ := by
      monoidal

-- WITNESS: none (step of DisplaysCondIndep.contraction; witnessed through it)
/-- For `m : A ⟶ B` in a copy-discard category `C`, copying `A`, copying the left copy and
applying `m` to its left copy equals copying `A`, applying `m` to the left copy, copying the
right copy and reassociating. -/
theorem copy_comp_copy_comp_whiskerRight_whiskerRight {A B : C} (m : A ⟶ B) :
    Δ[A] ≫ (Δ[A] ≫ m ▷ A) ▷ A = Δ[A] ≫ m ▷ A ≫ B ◁ Δ[A] ≫ (α_ B A A).inv := by
  rw [comp_whiskerRight, comul_assoc_flip_assoc, ← associator_inv_naturality_left,
    whisker_exchange_assoc]

-- WITNESS: none (step of DisplaysCondIndep.contraction; witnessed through it)
/-- For `k' : W ⊗ A ⟶ Z` and `k : (W ⊗ Z) ⊗ A ⟶ Y` in a copy-discard category `C`, copying `A`
in `W ⊗ A`, copying `W`, applying `k'` to the right copy of `W` and the left copy of `A`,
copying `W ⊗ Z`, applying `k` to the right copy of `W ⊗ Z` and the right copy of `A`, and
reassociating equals copying `W` in `W ⊗ A` and applying to the right copy of `W` and `A` the
composite `W ⊗ A ⟶ Z ⊗ Y` that copies `W` and `A`, applies `k'` to the right copy of `W` and
the left copy of `A`, copies `Z`, and applies `k` to the left copy of `W`, the right copy of
`Z` and the right copy of `A`. -/
theorem whiskerLeft_copy_comp_whiskerRight_comp_copy_tensor {A W Z Y : C} (k' : W ⊗ A ⟶ Z)
    (k : (W ⊗ Z) ⊗ A ⟶ Y) :
    W ◁ Δ[A] ≫ (α_ W A A).inv ≫ (Δ[W] ▷ A ≫ (α_ W W A).hom ≫ W ◁ k') ▷ A ≫
        @ComonObj.comul C _ _ (W ⊗ Z) (CopyDiscardCategory.comonObj (W ⊗ Z)) ▷ A ≫
        (α_ (W ⊗ Z) (W ⊗ Z) A).hom ≫ (W ⊗ Z) ◁ k ≫ (α_ W Z Y).hom =
      Δ[W] ▷ A ≫ (α_ W W A).hom ≫ W ◁ (Δ[W] ▷ A ≫ (α_ W W A).hom ≫
        W ◁ (W ◁ Δ[A] ≫ (α_ W A A).inv ≫ k' ▷ A) ≫ (α_ W Z A).inv ≫
        (W ◁ Δ[Z] ≫ (α_ W Z Z).inv ≫ (β_ W Z).hom ▷ Z ≫ (α_ Z W Z).hom) ▷ A ≫
        (α_ Z (W ⊗ Z) A).hom ≫ Z ◁ k) := by
  rw [copy_tensor, tensorHom_def]
  simp only [tensorμ]
  calc
    _ = W ◁ Δ[A] ⊗≫ (Δ[W] ▷ A) ▷ A ⊗≫ (Δ[W] ⊗ₘ k') ▷ A ⊗≫ ((W ⊗ W) ◁ Δ[Z]) ▷ A ⊗≫
          (W ◁ (β_ W Z).hom ▷ Z) ▷ A ⊗≫ (W ⊗ Z) ◁ k ⊗≫ 𝟙 (W ⊗ (Z ⊗ Y)) := by
      rw [tensorHom_def' Δ[W] k']
      monoidal
    _ = ((Δ[W] ≫ Δ[W] ▷ W) ⊗ₘ Δ[A]) ⊗≫ ((W ⊗ W) ◁ k') ▷ A ⊗≫ ((W ⊗ W) ◁ Δ[Z]) ▷ A ⊗≫
          (W ◁ (β_ W Z).hom ▷ Z) ▷ A ⊗≫ (W ⊗ Z) ◁ k ⊗≫ 𝟙 (W ⊗ (Z ⊗ Y)) := by
      rw [tensorHom_def Δ[W] k', tensorHom_def' (Δ[W] ≫ Δ[W] ▷ W) Δ[A]]
      monoidal
    _ = ((Δ[W] ≫ W ◁ Δ[W] ≫ (α_ W W W).inv) ⊗ₘ Δ[A]) ⊗≫ ((W ⊗ W) ◁ k') ▷ A ⊗≫
          ((W ⊗ W) ◁ Δ[Z]) ▷ A ⊗≫ (W ◁ (β_ W Z).hom ▷ Z) ▷ A ⊗≫ (W ⊗ Z) ◁ k ⊗≫
          𝟙 (W ⊗ (Z ⊗ Y)) := by
      rw [comul_assoc_flip]
    _ = _ := by
      rw [tensorHom_def]
      monoidal

-- WITNESS: none (step of DisplaysCondIndep.weak_union; witnessed through it)
/-- For `k : W ⊗ A ⟶ Y` and an object `X` in a copy-discard category `C`, braiding `X ⊗ W` to
`W ⊗ X` in `(X ⊗ W) ⊗ A`, copying `W ⊗ X`, discarding `X` from the right copy and applying `k`
to that copy and `A` equals copying `W` in `X ⊗ W`, braiding `X` past the left copy of `W`, and
applying `k` to the right copy of `W` and `A`. -/
theorem braiding_whiskerRight_comp_copy_tensor_whiskerRight {A W X Y : C} (k : W ⊗ A ⟶ Y) :
    (β_ X W).hom ▷ A ≫
        @ComonObj.comul C _ _ (W ⊗ X) (CopyDiscardCategory.comonObj (W ⊗ X)) ▷ A ≫
        (α_ (W ⊗ X) (W ⊗ X) A).hom ≫ (W ⊗ X) ◁ ((W ◁ ε[X] ≫ (ρ_ W).hom) ▷ A ≫ k) =
      (X ◁ Δ[W] ≫ (α_ X W W).inv ≫ (β_ X W).hom ▷ W) ▷ A ≫ (α_ (W ⊗ X) W A).hom ≫
        (W ⊗ X) ◁ k := by
  calc
    _ = ((β_ X W).hom ≫ @ComonObj.comul C _ _ (W ⊗ X) (CopyDiscardCategory.comonObj (W ⊗ X)) ≫
            (W ⊗ X) ◁ (W ◁ ε[X] ≫ (ρ_ W).hom)) ▷ A ≫
          (α_ (W ⊗ X) W A).hom ≫ (W ⊗ X) ◁ k := by
      monoidal
    _ = _ := by
      rw [braiding_comp_copy_tensor_comp_whiskerLeft_fst]

/-- For `f : A ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)` in a copy-discard category `C` with conditionals, if `f`
displays the conditional independence of `X₁ ⊗ X₂` and `Y` given `W` and `A`, then
`f ≫ (tensorWeakUnionIso X₁ X₂ W Y).hom : A ⟶ X₁ ⊗ ((W ⊗ X₂) ⊗ Y)` displays the conditional
independence of `X₁` and `Y` given `W ⊗ X₂` and `A` (Fritz 2020, Prop. 12.17 (d)). -/
theorem DisplaysCondIndep.weak_union [HasConditionals C] {A X₁ X₂ W Y : C}
    {f : A ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)} (hf : DisplaysCondIndep f) :
    DisplaysCondIndep (f ≫ (tensorWeakUnionIso X₁ X₂ W Y).hom) := by
  obtain ⟨g, h, k, rfl⟩ := hf
  obtain ⟨m, hm⟩ : ∃ m, m = Δ[A] ≫ A ◁ (g ≫ Δ[W]) ≫ (α_ A W W).inv ≫ h ▷ W := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := exists_isConditionalSnd (m ≫ (α_ X₁ X₂ W).hom ≫ X₁ ◁ (β_ X₂ W).hom)
  rw [isConditionalSnd_iff] at hc
  refine ⟨marginalSnd (m ≫ (α_ X₁ X₂ W).hom ≫ X₁ ◁ (β_ X₂ W).hom), (β_ A (W ⊗ X₂)).hom ≫ c,
    (W ◁ ε[X₂] ≫ (ρ_ W).hom) ▷ A ≫ k, ?_⟩
  generalize marginalSnd (m ≫ (α_ X₁ X₂ W).hom ≫ X₁ ◁ (β_ X₂ W).hom) = s at hc ⊢
  rw [condIndepForm_eq_copy_comp_whiskerRight g h k, condIndepForm_eq_copy_comp_whiskerRight,
    comp_whiskerRight (β_ A (W ⊗ X₂)).hom c (W ⊗ X₂), ← hc, ← hm, tensorWeakUnionIso_hom]
  calc
    _ = Δ[A] ≫ m ▷ A ⊗≫ X₁ ◁ (X₂ ◁ Δ[W]) ▷ A ⊗≫ X₁ ◁ ((β_ X₂ W).hom ⊗ₘ k) := by
      rw [tensorHom_def' (β_ X₂ W).hom k]
      monoidal
    _ = Δ[A] ≫ m ▷ A ⊗≫ X₁ ◁ ((X₂ ◁ Δ[W] ≫ (α_ X₂ W W).inv ≫ (β_ X₂ W).hom ▷ W) ▷ A ≫
          (α_ (W ⊗ X₂) W A).hom ≫ (W ⊗ X₂) ◁ k) := by
      rw [tensorHom_def (β_ X₂ W).hom k]
      monoidal
    _ = Δ[A] ≫ m ▷ A ⊗≫ X₁ ◁ ((β_ X₂ W).hom ▷ A ≫
          @ComonObj.comul C _ _ (W ⊗ X₂) (CopyDiscardCategory.comonObj (W ⊗ X₂)) ▷ A ≫
          (α_ (W ⊗ X₂) (W ⊗ X₂) A).hom ≫
          (W ⊗ X₂) ◁ ((W ◁ ε[X₂] ≫ (ρ_ W).hom) ▷ A ≫ k)) := by
      rw [braiding_whiskerRight_comp_copy_tensor_whiskerRight]
    _ = _ := by
      monoidal

end CopyDiscardCategory

namespace MarkovCategory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

-- WITNESS: none (step of DisplaysCondIndepState.contraction; witnessed through it)
/-- For `f : V ⟶ X` and `g : V ⟶ Y` in a Markov category `C`, copying the right `V` of
`V ⊗ V`, applying `f` to the left `V` and `g` to the right copy, and discarding `Y` equals
`f ▷ V`. -/
theorem whiskerLeft_copy_comp_tensorHom_comp_fst {V X Y : C} (f : V ⟶ X) (g : V ⟶ Y) :
    V ◁ Δ[V] ≫ (f ⊗ₘ V ◁ g) ≫ X ◁ (V ◁ ε[Y] ≫ (ρ_ V).hom) = f ▷ V := by
  have inner : Δ[V] ≫ V ◁ g ≫ V ◁ ε[Y] ≫ (ρ_ V).hom = 𝟙 V := by
    rw [← whiskerLeft_comp_assoc, MarkovCategory.discard_natural, comul_counit_assoc,
      Iso.inv_hom_id]
  calc
    _ = V ◁ (Δ[V] ≫ V ◁ g ≫ V ◁ ε[Y] ≫ (ρ_ V).hom) ≫ f ▷ V := by
      rw [tensorHom_def', Category.assoc, ← whisker_exchange]
      simp only [whiskerLeft_comp, Category.assoc]
    _ = _ := by
      rw [inner, whiskerLeft_id, Category.id_comp]

-- WITNESS: none (step of DisplaysCondIndep.contraction; witnessed through it)
/-- For `g : A ⟶ W`, `h : A ⊗ W ⟶ X` and `k : W ⊗ A ⟶ Y` in a Markov category `C`, the
marginal `condIndepForm g h k ≫ X ◁ (W ◁ ε[Y] ≫ (ρ_ W).hom) : A ⟶ X ⊗ W` equals
`Δ[A] ≫ A ◁ (g ≫ Δ[W]) ≫ (α_ A W W).inv ≫ h ▷ W` (Fritz 2020, Def. 12.16). -/
theorem condIndepForm_comp_whiskerLeft_fst {A X W Y : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X)
    (k : W ⊗ A ⟶ Y) :
    condIndepForm g h k ≫ X ◁ (W ◁ ε[Y] ≫ (ρ_ W).hom) =
      Δ[A] ≫ A ◁ (g ≫ Δ[W]) ≫ (α_ A W W).inv ≫ h ▷ W := by
  have inner : (Δ[W] ▷ A ≫ (α_ W W A).hom ≫ W ◁ k) ≫ W ◁ ε[Y] ≫ (ρ_ W).hom =
      W ◁ ε[A] ≫ (ρ_ W).hom := by
    rw [Category.assoc, Category.assoc, ← whiskerLeft_comp_assoc, MarkovCategory.discard_natural,
      discard_tensor, tensorHom_def]
    calc
      _ = (Δ[W] ≫ W ◁ ε[W]) ▷ A ≫ (ρ_ W).hom ▷ A ≫ W ◁ ε[A] ≫ (ρ_ W).hom := by
        monoidal
      _ = _ := by
        rw [comul_counit]
        monoidal
  rw [condIndepForm_eq_copy_comp_whiskerRight]
  generalize Δ[A] ≫ A ◁ (g ≫ Δ[W]) ≫ (α_ A W W).inv ≫ h ▷ W = m
  simp only [Category.assoc]
  rw [← whiskerLeft_comp, inner]
  calc
    _ = Δ[A] ≫ m ▷ A ≫ (X ⊗ W) ◁ ε[A] ≫ (ρ_ (X ⊗ W)).hom := by
      monoidal
    _ = _ := by
      rw [← whisker_exchange_assoc, rightUnitor_naturality, comul_counit_assoc,
        Iso.inv_hom_id_assoc]

end MarkovCategory

namespace CopyDiscardCategory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

/-- For a state `ψ : 𝟙_ C ⟶ X ⊗ ((W ⊗ Z) ⊗ Y)` in a Markov category `C`, if `ψ` displays the
conditional independence of `X` and `Y` given `W ⊗ Z`, and its marginal
`ψ ≫ X ◁ ((W ⊗ Z) ◁ ε[Y] ≫ (ρ_ (W ⊗ Z)).hom) : 𝟙_ C ⟶ X ⊗ (W ⊗ Z)` displays the conditional
independence of `X` and `Z` given `W`, then `ψ ≫ X ◁ (α_ W Z Y).hom : 𝟙_ C ⟶ X ⊗ (W ⊗ (Z ⊗ Y))`
displays the conditional independence of `X` and `Z ⊗ Y` given `W` (Fritz 2020,
Lemma 12.5 (c)). -/
theorem DisplaysCondIndepState.contraction {X W Z Y : C}
    {ψ : 𝟙_ C ⟶ X ⊗ ((W ⊗ Z) ⊗ Y)} (hψ : DisplaysCondIndepState ψ)
    (hm : DisplaysCondIndepState (ψ ≫ X ◁ ((W ⊗ Z) ◁ ε[Y] ≫ (ρ_ (W ⊗ Z)).hom))) :
    DisplaysCondIndepState (ψ ≫ X ◁ (α_ W Z Y).hom) := by
  obtain ⟨φ, f, g, rfl⟩ := hψ
  obtain ⟨η, h, k, hm⟩ := hm
  simp only [Category.assoc] at hm
  rw [MarkovCategory.whiskerLeft_copy_comp_tensorHom_comp_fst] at hm
  refine ⟨η, h, Δ[W] ≫ W ◁ (k ≫ Δ[Z]) ≫ (α_ W Z Z).inv ≫ (β_ W Z).hom ▷ Z ≫
    (α_ Z W Z).hom ≫ Z ◁ g, ?_⟩
  calc
    _ = (φ ≫ @ComonObj.comul C _ _ (W ⊗ Z) (CopyDiscardCategory.comonObj (W ⊗ Z)) ≫
            f ▷ (W ⊗ Z)) ≫
          X ◁ (@ComonObj.comul C _ _ (W ⊗ Z) (CopyDiscardCategory.comonObj (W ⊗ Z)) ≫
            (W ⊗ Z) ◁ g ≫ (α_ W Z Y).hom) := by
      rw [tensorHom_def]
      simp only [Category.assoc, whiskerLeft_comp]
      rw [whisker_exchange_assoc]
    _ = η ≫ Δ[W] ≫ W ◁ (Δ[W] ≫ W ◁ k ≫
            @ComonObj.comul C _ _ (W ⊗ Z) (CopyDiscardCategory.comonObj (W ⊗ Z)) ≫
            (W ⊗ Z) ◁ g ≫ (α_ W Z Y).hom) ≫
          h ▷ (W ⊗ (Z ⊗ Y)) := by
      rw [hm, tensorHom_def']
      simp only [Category.assoc]
      rw [← whisker_exchange]
      simp only [Category.assoc, whiskerLeft_comp]
    _ = _ := by
      rw [copy_comp_whiskerLeft_comp_copy_tensor, tensorHom_def']
      simp only [Category.assoc, whiskerLeft_comp]

/-- For `f : A ⟶ X ⊗ ((W ⊗ Z) ⊗ Y)` in a Markov category `C`, if `f` displays the conditional
independence of `X` and `Y` given `W ⊗ Z` and `A`, and its marginal
`f ≫ X ◁ ((W ⊗ Z) ◁ ε[Y] ≫ (ρ_ (W ⊗ Z)).hom) : A ⟶ X ⊗ (W ⊗ Z)` displays the conditional
independence of `X` and `Z` given `W` and `A`, then
`f ≫ X ◁ (α_ W Z Y).hom : A ⟶ X ⊗ (W ⊗ (Z ⊗ Y))` displays the conditional independence of `X`
and `Z ⊗ Y` given `W` and `A` (Fritz 2020, Prop. 12.17 (c)). -/
theorem DisplaysCondIndep.contraction {A X W Z Y : C}
    {f : A ⟶ X ⊗ ((W ⊗ Z) ⊗ Y)} (hf : DisplaysCondIndep f)
    (hm : DisplaysCondIndep (f ≫ X ◁ ((W ⊗ Z) ◁ ε[Y] ≫ (ρ_ (W ⊗ Z)).hom))) :
    DisplaysCondIndep (f ≫ X ◁ (α_ W Z Y).hom) := by
  obtain ⟨g, h, k, rfl⟩ := hf
  obtain ⟨g', h', k', hm⟩ := hm
  rw [MarkovCategory.condIndepForm_comp_whiskerLeft_fst] at hm
  refine ⟨g', h', Δ[W] ▷ A ≫ (α_ W W A).hom ≫
    W ◁ (W ◁ Δ[A] ≫ (α_ W A A).inv ≫ k' ▷ A) ≫ (α_ W Z A).inv ≫
    (W ◁ Δ[Z] ≫ (α_ W Z Z).inv ≫ (β_ W Z).hom ▷ Z ≫ (α_ Z W Z).hom) ▷ A ≫
    (α_ Z (W ⊗ Z) A).hom ≫ Z ◁ k, ?_⟩
  rw [condIndepForm_eq_copy_comp_whiskerRight g h k, hm,
    condIndepForm_eq_copy_comp_whiskerRight g' h' k', condIndepForm_eq_copy_comp_whiskerRight,
    ← whiskerLeft_copy_comp_whiskerRight_comp_copy_tensor k' k]
  generalize Δ[A] ≫ A ◁ (g' ≫ Δ[W]) ≫ (α_ A W W).inv ≫ h' ▷ W = m
  calc
    _ = (Δ[A] ≫ (Δ[A] ≫ m ▷ A) ▷ A) ≫ (α_ (X ⊗ W) A A).hom ≫ (α_ X W (A ⊗ A)).hom ≫
          X ◁ ((α_ W A A).inv ≫ (Δ[W] ▷ A ≫ (α_ W W A).hom ≫ W ◁ k') ▷ A ≫
            @ComonObj.comul C _ _ (W ⊗ Z) (CopyDiscardCategory.comonObj (W ⊗ Z)) ▷ A ≫
            (α_ (W ⊗ Z) (W ⊗ Z) A).hom ≫ (W ⊗ Z) ◁ k ≫ (α_ W Z Y).hom) := by
      monoidal
    _ = _ := by
      rw [copy_comp_copy_comp_whiskerRight_whiskerRight]
      monoidal

end CopyDiscardCategory

end CategoryTheory
