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
`DisplaysCondIndepState.weak_union`, `MarkovCategory.whiskerLeft_copy_comp_tensorHom_comp_fst`
and `MarkovCategory.DisplaysCondIndepState.contraction` applied at variables.
`DisplaysIndep.symm`, `DisplaysIndep.decomposition`, `DisplaysCondIndepState.symm`,
`DisplaysCondIndepState.decomposition` and `DisplaysCondIndepState.weak_union` through dot
notation on the hypothesis. Dot notation on the hypothesis does not resolve
`MarkovCategory.DisplaysCondIndepState.contraction`.
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

end CopyDiscard

section Markov

variable [MarkovCategory C]

example {V X Y : C} (f : V ⟶ X) (g : V ⟶ Y) :
    V ◁ Δ[V] ≫ (f ⊗ₘ V ◁ g) ≫ X ◁ (V ◁ ε[Y] ≫ (ρ_ V).hom) = f ▷ V :=
  MarkovCategory.whiskerLeft_copy_comp_tensorHom_comp_fst f g

example {X W Z Y : C} {ψ : 𝟙_ C ⟶ X ⊗ ((W ⊗ Z) ⊗ Y)} (hψ : DisplaysCondIndepState ψ)
    (hm : DisplaysCondIndepState (ψ ≫ X ◁ ((W ⊗ Z) ◁ ε[Y] ≫ (ρ_ (W ⊗ Z)).hom))) :
    DisplaysCondIndepState (ψ ≫ X ◁ (α_ W Z Y).hom) :=
  MarkovCategory.DisplaysCondIndepState.contraction hψ hm

example {X W Z Y : C} {ψ : 𝟙_ C ⟶ X ⊗ ((W ⊗ Z) ⊗ Y)} (hψ : DisplaysCondIndepState ψ)
    (hm : DisplaysCondIndepState (ψ ≫ X ◁ ((W ⊗ Z) ◁ ε[Y] ≫ (ρ_ (W ⊗ Z)).hom))) :
    DisplaysCondIndepState (ψ ≫ X ◁ (α_ W Z Y).hom) := by
  fail_if_success exact hψ.contraction hm
  exact MarkovCategory.DisplaysCondIndepState.contraction hψ hm

end Markov

end CategoryTheory
