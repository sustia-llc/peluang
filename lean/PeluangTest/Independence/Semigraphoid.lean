/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Independence.Semigraphoid
import PeluangLint

/-!
# Tests for `Peluang.Independence.Semigraphoid`

Each of `DisplaysIndep.symm`, `fst_comp_discard`, `DisplaysIndep.decomposition`,
`copy_comp_whiskerLeft_copy_comp_tensorRev₃_hom`, `DisplaysCondIndepState.symm`,
`DisplaysCondIndepState.decomposition`, `copy_comp_whiskerLeft_comp_copy_tensor`,
`copy_tensor_comp_whiskerLeft_fst`, `braiding_comp_copy_whiskerRight`,
`braiding_comp_copy_tensor_comp_whiskerLeft_fst`, `copy_comp_whiskerLeft_comp_copy_tensor_eq`,
`DisplaysCondIndepState.weak_union`, `copy_tensor_comp_snd_whiskerRight`,
`copy_tensor_comp_snd_tensorHom_braiding`, `copy_tensor_comp_whiskerLeft_braiding`,
`condIndepForm_eq_copy_tensor`, `condIndepForm_comp_tensorRev₃`, `DisplaysCondIndep.symm`,
`condIndepForm_comp_tensorHom_whiskerLeft`, `DisplaysCondIndep.decomposition`,
`condIndepForm_eq_copy_comp_whiskerRight`, `copy_comp_copy_comp_whiskerRight_whiskerRight`,
`whiskerLeft_copy_comp_whiskerRight_comp_copy_tensor`,
`braiding_whiskerRight_comp_copy_tensor_whiskerRight`, `DisplaysCondIndep.weak_union`,
`MarkovCategory.whiskerLeft_copy_comp_tensorHom_comp_fst`,
`CopyDiscardCategory.DisplaysCondIndepState.contraction`,
`MarkovCategory.condIndepForm_comp_whiskerLeft_fst` and
`CopyDiscardCategory.DisplaysCondIndep.contraction` applied at variables.
`DisplaysIndep.symm`, `DisplaysIndep.decomposition`, `DisplaysCondIndepState.symm`,
`DisplaysCondIndepState.decomposition`, `DisplaysCondIndepState.weak_union`,
`DisplaysCondIndepState.contraction`, `DisplaysCondIndep.symm`,
`DisplaysCondIndep.decomposition`, `DisplaysCondIndep.weak_union` and
`DisplaysCondIndep.contraction` through dot notation on the hypothesis.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section CopyDiscard

variable [CopyDiscardCategory C]

example {A X Y : C} {f : A ⟶ X ⊗ Y} (hf : DisplaysIndep f) :
    DisplaysIndep (f ≫ (β_ X Y).hom) :=
  DisplaysIndep.symm hf

example {A X Y : C} {f : A ⟶ X ⊗ Y} (hf : DisplaysIndep f) :
    DisplaysIndep (f ≫ (β_ X Y).hom) :=
  hf.symm

example (X₁ X₂ : C) :
    (X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ≫ ε[X₁] =
      @ComonObj.counit C _ _ (X₁ ⊗ X₂) (CopyDiscardCategory.comonObj (X₁ ⊗ X₂)) :=
  fst_comp_discard X₁ X₂

example {A X₁ X₂ Y : C} {f : A ⟶ (X₁ ⊗ X₂) ⊗ Y} (hf : DisplaysIndep f) :
    DisplaysIndep (f ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ Y)) :=
  DisplaysIndep.decomposition hf

example {A X₁ X₂ Y : C} {f : A ⟶ (X₁ ⊗ X₂) ⊗ Y} (hf : DisplaysIndep f) :
    DisplaysIndep (f ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ Y)) :=
  hf.decomposition

example (X : C) : Δ[X] ≫ X ◁ Δ[X] ≫ (tensorRev₃ X X X).hom = Δ[X] ≫ X ◁ Δ[X] :=
  copy_comp_whiskerLeft_copy_comp_tensorRev₃_hom X

example {X W Y : C} {ψ : 𝟙_ C ⟶ X ⊗ (W ⊗ Y)} (hψ : DisplaysCondIndepState ψ) :
    DisplaysCondIndepState (ψ ≫ (tensorRev₃ X W Y).hom) :=
  DisplaysCondIndepState.symm hψ

example {X W Y : C} {ψ : 𝟙_ C ⟶ X ⊗ (W ⊗ Y)} (hψ : DisplaysCondIndepState ψ) :
    DisplaysCondIndepState (ψ ≫ (tensorRev₃ X W Y).hom) :=
  hψ.symm

example {X₁ X₂ W Y : C} {ψ : 𝟙_ C ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)} (hψ : DisplaysCondIndepState ψ) :
    DisplaysCondIndepState (ψ ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ (W ⊗ Y))) :=
  DisplaysCondIndepState.decomposition hψ

example {X₁ X₂ W Y : C} {ψ : 𝟙_ C ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)} (hψ : DisplaysCondIndepState ψ) :
    DisplaysCondIndepState (ψ ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ (W ⊗ Y))) :=
  hψ.decomposition

example {W Z Y : C} (k : W ⟶ Z) (g : W ⊗ Z ⟶ Y) :
    Δ[W] ≫ W ◁ k ≫ @ComonObj.comul C _ _ (W ⊗ Z) (CopyDiscardCategory.comonObj (W ⊗ Z)) ≫
        (W ⊗ Z) ◁ g ≫ (α_ W Z Y).hom =
      Δ[W] ≫ W ◁ (Δ[W] ≫ W ◁ (k ≫ Δ[Z]) ≫ (α_ W Z Z).inv ≫ (β_ W Z).hom ▷ Z ≫
        (α_ Z W Z).hom ≫ Z ◁ g) :=
  copy_comp_whiskerLeft_comp_copy_tensor k g

example (A B : C) :
    @ComonObj.comul C _ _ (A ⊗ B) (CopyDiscardCategory.comonObj (A ⊗ B)) ≫
        (A ⊗ B) ◁ (A ◁ ε[B] ≫ (ρ_ A).hom) =
      Δ[A] ▷ B ≫ (α_ A A B).hom ≫ A ◁ (β_ A B).hom ≫ (α_ A B A).inv :=
  copy_tensor_comp_whiskerLeft_fst A B

example (A B : C) :
    (β_ B A).hom ≫ Δ[A] ▷ B ≫ (α_ A A B).hom ≫ A ◁ (β_ A B).hom ≫ (α_ A B A).inv =
      B ◁ Δ[A] ≫ (α_ B A A).inv ≫ (β_ B A).hom ▷ A :=
  braiding_comp_copy_whiskerRight A B

example (A B : C) :
    (β_ B A).hom ≫ @ComonObj.comul C _ _ (A ⊗ B) (CopyDiscardCategory.comonObj (A ⊗ B)) ≫
        (A ⊗ B) ◁ (A ◁ ε[B] ≫ (ρ_ A).hom) =
      B ◁ Δ[A] ≫ (α_ B A A).inv ≫ (β_ B A).hom ▷ A :=
  braiding_comp_copy_tensor_comp_whiskerLeft_fst A B

example {W B : C} (s : W ⟶ B) :
    Δ[W] ≫ W ◁ s ≫ @ComonObj.comul C _ _ (W ⊗ B) (CopyDiscardCategory.comonObj (W ⊗ B)) =
      Δ[W] ≫ (Δ[W] ≫ W ◁ (s ≫ Δ[B]) ≫ (α_ W B B).inv) ▷ W ≫ (α_ (W ⊗ B) B W).hom ≫
        (W ⊗ B) ◁ (β_ B W).hom :=
  copy_comp_whiskerLeft_comp_copy_tensor_eq s

example [HasConditionals C] {X₁ X₂ W Y : C} {ψ : 𝟙_ C ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)}
    (hψ : DisplaysCondIndepState ψ) :
    DisplaysCondIndepState (ψ ≫ (tensorWeakUnionIso X₁ X₂ W Y).hom) :=
  DisplaysCondIndepState.weak_union hψ

example [HasConditionals C] {X₁ X₂ W Y : C} {ψ : 𝟙_ C ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)}
    (hψ : DisplaysCondIndepState ψ) :
    DisplaysCondIndepState (ψ ≫ (tensorWeakUnionIso X₁ X₂ W Y).hom) :=
  hψ.weak_union

example (A W : C) :
    @ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        ((ε[A] ▷ W ≫ (λ_ W).hom) ▷ (A ⊗ W)) =
      A ◁ Δ[W] ≫ (α_ A W W).inv ≫ (β_ A W).hom ▷ W ≫ (α_ W A W).hom :=
  copy_tensor_comp_snd_whiskerRight A W

example (A W : C) :
    @ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        ((ε[A] ▷ W ≫ (λ_ W).hom) ⊗ₘ (β_ A W).hom) =
      (β_ A W).hom ≫ Δ[W] ▷ A ≫ (α_ W W A).hom :=
  copy_tensor_comp_snd_tensorHom_braiding A W

example (A W : C) :
    @ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        (A ⊗ W) ◁ (β_ A W).hom =
      (Δ[A] ⊗ₘ Δ[W]) ≫ (α_ A A (W ⊗ W)).hom ≫ A ◁ (β_ A (W ⊗ W)).hom ≫
        A ◁ (α_ W W A).hom ≫ (α_ A W (W ⊗ A)).inv :=
  copy_tensor_comp_whiskerLeft_braiding A W

example {A X W Y : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X) (k : W ⊗ A ⟶ Y) :
    condIndepForm g h k =
      Δ[A] ≫ A ◁ g ≫ @ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        (A ⊗ W) ◁ @ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        (h ⊗ₘ ((ε[A] ▷ W ≫ (λ_ W).hom) ⊗ₘ ((β_ A W).hom ≫ k))) :=
  condIndepForm_eq_copy_tensor g h k

example {A X W Y : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X) (k : W ⊗ A ⟶ Y) :
    condIndepForm g h k ≫ (tensorRev₃ X W Y).hom =
      condIndepForm g ((β_ A W).hom ≫ k) ((β_ W A).hom ≫ h) :=
  condIndepForm_comp_tensorRev₃ g h k

example {A X W Y : C} {f : A ⟶ X ⊗ (W ⊗ Y)} (hf : DisplaysCondIndep f) :
    DisplaysCondIndep (f ≫ (tensorRev₃ X W Y).hom) :=
  DisplaysCondIndep.symm hf

example {A X W Y : C} {f : A ⟶ X ⊗ (W ⊗ Y)} (hf : DisplaysCondIndep f) :
    DisplaysCondIndep (f ≫ (tensorRev₃ X W Y).hom) :=
  hf.symm

example {A X X' W Y Y' : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X) (k : W ⊗ A ⟶ Y) (u : X ⟶ X')
    (v : Y ⟶ Y') :
    condIndepForm g h k ≫ (u ⊗ₘ W ◁ v) = condIndepForm g (h ≫ u) (k ≫ v) :=
  condIndepForm_comp_tensorHom_whiskerLeft g h k u v

example {A X₁ X₂ W Y : C} {f : A ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)} (hf : DisplaysCondIndep f) :
    DisplaysCondIndep (f ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ (W ⊗ Y))) :=
  DisplaysCondIndep.decomposition hf

example {A X₁ X₂ W Y : C} {f : A ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)} (hf : DisplaysCondIndep f) :
    DisplaysCondIndep (f ≫ ((X₁ ◁ ε[X₂] ≫ (ρ_ X₁).hom) ▷ (W ⊗ Y))) :=
  hf.decomposition

example {A X W Y : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X) (k : W ⊗ A ⟶ Y) :
    condIndepForm g h k =
      Δ[A] ≫ (Δ[A] ≫ A ◁ (g ≫ Δ[W]) ≫ (α_ A W W).inv ≫ h ▷ W) ▷ A ≫ (α_ X W A).hom ≫
        X ◁ (Δ[W] ▷ A ≫ (α_ W W A).hom ≫ W ◁ k) :=
  condIndepForm_eq_copy_comp_whiskerRight g h k

example {A B : C} (m : A ⟶ B) :
    Δ[A] ≫ (Δ[A] ≫ m ▷ A) ▷ A = Δ[A] ≫ m ▷ A ≫ B ◁ Δ[A] ≫ (α_ B A A).inv :=
  copy_comp_copy_comp_whiskerRight_whiskerRight m

example {A W Z Y : C} (k' : W ⊗ A ⟶ Z) (k : (W ⊗ Z) ⊗ A ⟶ Y) :
    W ◁ Δ[A] ≫ (α_ W A A).inv ≫ (Δ[W] ▷ A ≫ (α_ W W A).hom ≫ W ◁ k') ▷ A ≫
        @ComonObj.comul C _ _ (W ⊗ Z) (CopyDiscardCategory.comonObj (W ⊗ Z)) ▷ A ≫
        (α_ (W ⊗ Z) (W ⊗ Z) A).hom ≫ (W ⊗ Z) ◁ k ≫ (α_ W Z Y).hom =
      Δ[W] ▷ A ≫ (α_ W W A).hom ≫ W ◁ (Δ[W] ▷ A ≫ (α_ W W A).hom ≫
        W ◁ (W ◁ Δ[A] ≫ (α_ W A A).inv ≫ k' ▷ A) ≫ (α_ W Z A).inv ≫
        (W ◁ Δ[Z] ≫ (α_ W Z Z).inv ≫ (β_ W Z).hom ▷ Z ≫ (α_ Z W Z).hom) ▷ A ≫
        (α_ Z (W ⊗ Z) A).hom ≫ Z ◁ k) :=
  whiskerLeft_copy_comp_whiskerRight_comp_copy_tensor k' k

example {A W X Y : C} (k : W ⊗ A ⟶ Y) :
    (β_ X W).hom ▷ A ≫
        @ComonObj.comul C _ _ (W ⊗ X) (CopyDiscardCategory.comonObj (W ⊗ X)) ▷ A ≫
        (α_ (W ⊗ X) (W ⊗ X) A).hom ≫ (W ⊗ X) ◁ ((W ◁ ε[X] ≫ (ρ_ W).hom) ▷ A ≫ k) =
      (X ◁ Δ[W] ≫ (α_ X W W).inv ≫ (β_ X W).hom ▷ W) ▷ A ≫ (α_ (W ⊗ X) W A).hom ≫
        (W ⊗ X) ◁ k :=
  braiding_whiskerRight_comp_copy_tensor_whiskerRight k

example [HasConditionals C] {A X₁ X₂ W Y : C} {f : A ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)}
    (hf : DisplaysCondIndep f) :
    DisplaysCondIndep (f ≫ (tensorWeakUnionIso X₁ X₂ W Y).hom) :=
  DisplaysCondIndep.weak_union hf

example [HasConditionals C] {A X₁ X₂ W Y : C} {f : A ⟶ (X₁ ⊗ X₂) ⊗ (W ⊗ Y)}
    (hf : DisplaysCondIndep f) :
    DisplaysCondIndep (f ≫ (tensorWeakUnionIso X₁ X₂ W Y).hom) :=
  hf.weak_union

end CopyDiscard

section Markov

variable [MarkovCategory C]

example {V X Y : C} (f : V ⟶ X) (g : V ⟶ Y) :
    V ◁ Δ[V] ≫ (f ⊗ₘ V ◁ g) ≫ X ◁ (V ◁ ε[Y] ≫ (ρ_ V).hom) = f ▷ V :=
  MarkovCategory.whiskerLeft_copy_comp_tensorHom_comp_fst f g

example {X W Z Y : C} {ψ : 𝟙_ C ⟶ X ⊗ ((W ⊗ Z) ⊗ Y)} (hψ : DisplaysCondIndepState ψ)
    (hm : DisplaysCondIndepState (ψ ≫ X ◁ ((W ⊗ Z) ◁ ε[Y] ≫ (ρ_ (W ⊗ Z)).hom))) :
    DisplaysCondIndepState (ψ ≫ X ◁ (α_ W Z Y).hom) :=
  CategoryTheory.CopyDiscardCategory.DisplaysCondIndepState.contraction hψ hm

example {X W Z Y : C} {ψ : 𝟙_ C ⟶ X ⊗ ((W ⊗ Z) ⊗ Y)} (hψ : DisplaysCondIndepState ψ)
    (hm : DisplaysCondIndepState (ψ ≫ X ◁ ((W ⊗ Z) ◁ ε[Y] ≫ (ρ_ (W ⊗ Z)).hom))) :
    DisplaysCondIndepState (ψ ≫ X ◁ (α_ W Z Y).hom) :=
  hψ.contraction hm

example {A X W Y : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X) (k : W ⊗ A ⟶ Y) :
    condIndepForm g h k ≫ X ◁ (W ◁ ε[Y] ≫ (ρ_ W).hom) =
      Δ[A] ≫ A ◁ (g ≫ Δ[W]) ≫ (α_ A W W).inv ≫ h ▷ W :=
  MarkovCategory.condIndepForm_comp_whiskerLeft_fst g h k

example {A X W Z Y : C} {f : A ⟶ X ⊗ ((W ⊗ Z) ⊗ Y)} (hf : DisplaysCondIndep f)
    (hm : DisplaysCondIndep (f ≫ X ◁ ((W ⊗ Z) ◁ ε[Y] ≫ (ρ_ (W ⊗ Z)).hom))) :
    DisplaysCondIndep (f ≫ X ◁ (α_ W Z Y).hom) :=
  CategoryTheory.CopyDiscardCategory.DisplaysCondIndep.contraction hf hm

example {A X W Z Y : C} {f : A ⟶ X ⊗ ((W ⊗ Z) ⊗ Y)} (hf : DisplaysCondIndep f)
    (hm : DisplaysCondIndep (f ≫ X ◁ ((W ⊗ Z) ◁ ε[Y] ≫ (ρ_ (W ⊗ Z)).hom))) :
    DisplaysCondIndep (f ≫ X ◁ (α_ W Z Y).hom) :=
  hf.contraction hm

end Markov

end CategoryTheory
