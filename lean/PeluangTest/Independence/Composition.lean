/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Independence.Composition
import PeluangLint

/-!
# Tests for `Peluang.Independence.Composition`

Each of `copy_comp_whiskerLeft_copy_five`, `copy_comp_condIndepForm_comp_tensorHom`,
`DisplaysCondIndep.comp_tensorHom`, `deterministic_comp`, `deterministic_tensorμ`,
`comp_copy_comp_whiskerLeft_copy`, `copy_tensor_comp_whiskerLeft_copy_tensor`,
`copy_tensor_comp_whiskerLeft_tensorHom`, `tensorμ_comp_snd`,
`condIndepForm_tensorHom_comp_tensorTripleInterchange`, `DisplaysCondIndep.tensor`,
`condIndepForm_eq_copyPair`, `copyPair_id_condIndepForm_comp_tensorLeftComm`,
`condIndepForm_comp_copy_condIndepForm`, `DisplaysCondIndep.comp`, `isConditional_iff_copyPair`,
`braiding_comp_snd`, `copyPair_id_right_comp_copyPair`, `copyPair_id_copyPair_comp`,
`condIndepForm_comp_tensorCondReorder_eq_copyPair`, `condIndepForm_comp_tensorCondReorder`,
`copyPair_discard_comp_rightUnitor`, `copyPair_id_comp_snd`,
`MarkovCategory.marginalFst_condIndepForm_comp_tensorCondReorder`,
`CopyDiscardCategory.IsConditional.condIndepForm` and
`CopyDiscardCategory.DisplaysCondIndep.exists_isConditional` applied at variables.
`DisplaysCondIndep.tensor`, `DisplaysCondIndep.comp`, `DisplaysCondIndep.comp_tensorHom`,
`IsConditional.condIndepForm` and `DisplaysCondIndep.exists_isConditional` through dot notation
on the hypothesis.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section CopyDiscard

variable [CopyDiscardCategory C]

example (A : C) :
    Δ[A] ≫ A ◁ Δ[A] ≫ A ◁ (Δ[A] ▷ A) ≫ A ◁ ((A ◁ Δ[A]) ▷ A) =
      Δ[A] ≫ A ◁ Δ[A] ≫ Δ[A] ▷ (A ⊗ A) ≫ (A ⊗ A) ◁ (A ◁ Δ[A]) ≫
        (α_ A A (A ⊗ (A ⊗ A))).hom ≫ A ◁ (A ◁ (α_ A A A).inv) ≫
        A ◁ (α_ A (A ⊗ A) A).inv :=
  copy_comp_whiskerLeft_copy_five A

example {A X₁ W Y₁ X₂ Y₂ : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X₁) (k : W ⊗ A ⟶ Y₁) (u : A ⊗ X₁ ⟶ X₂)
    (v : Y₁ ⊗ A ⟶ Y₂) :
    Δ[A] ≫ A ◁ Δ[A] ≫ A ◁ (condIndepForm g h k ▷ A) ≫ (tensorCompAssoc A X₁ W Y₁ A).hom ≫
        (u ⊗ₘ W ◁ v) =
      condIndepForm g (Δ[A] ▷ W ≫ (α_ A A W).hom ≫ A ◁ h ≫ u)
        (W ◁ Δ[A] ≫ (α_ W A A).inv ≫ k ▷ A ≫ v) :=
  copy_comp_condIndepForm_comp_tensorHom g h k u v

example {A X₁ W Y₁ X₂ Y₂ : C} {f : A ⟶ X₁ ⊗ (W ⊗ Y₁)} (hf : DisplaysCondIndep f)
    (u : A ⊗ X₁ ⟶ X₂) (v : Y₁ ⊗ A ⟶ Y₂) :
    DisplaysCondIndep
      (Δ[A] ≫ A ◁ Δ[A] ≫ A ◁ (f ▷ A) ≫ (tensorCompAssoc A X₁ W Y₁ A).hom ≫ (u ⊗ₘ W ◁ v)) :=
  DisplaysCondIndep.comp_tensorHom hf u v

example {A X₁ W Y₁ X₂ Y₂ : C} {f : A ⟶ X₁ ⊗ (W ⊗ Y₁)} (hf : DisplaysCondIndep f)
    (u : A ⊗ X₁ ⟶ X₂) (v : Y₁ ⊗ A ⟶ Y₂) :
    DisplaysCondIndep
      (Δ[A] ≫ A ◁ Δ[A] ≫ A ◁ (f ▷ A) ≫ (tensorCompAssoc A X₁ W Y₁ A).hom ≫ (u ⊗ₘ W ◁ v)) :=
  hf.comp_tensorHom u v

example {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Deterministic f) (hg : Deterministic g) :
    Deterministic (f ≫ g) :=
  deterministic_comp hf hg

example (X₁ X₂ Y₁ Y₂ : C) : Deterministic (tensorμ X₁ X₂ Y₁ Y₂) :=
  deterministic_tensorμ X₁ X₂ Y₁ Y₂

example {P Q : C} (s : P ⟶ Q) [Deterministic s] :
    s ≫ Δ[Q] ≫ Q ◁ Δ[Q] = Δ[P] ≫ P ◁ Δ[P] ≫ (s ⊗ₘ (s ⊗ₘ s)) :=
  comp_copy_comp_whiskerLeft_copy s

example (B₁ B₂ : C) :
    @ComonObj.comul C _ _ (B₁ ⊗ B₂) (CopyDiscardCategory.comonObj (B₁ ⊗ B₂)) ≫
        (B₁ ⊗ B₂) ◁ @ComonObj.comul C _ _ (B₁ ⊗ B₂) (CopyDiscardCategory.comonObj (B₁ ⊗ B₂)) =
      ((Δ[B₁] ≫ B₁ ◁ Δ[B₁]) ⊗ₘ (Δ[B₂] ≫ B₂ ◁ Δ[B₂])) ≫
        (tensorTripleInterchange B₁ B₁ B₁ B₂ B₂ B₂).hom :=
  copy_tensor_comp_whiskerLeft_copy_tensor B₁ B₂

example {A₁ A₂ W₁ W₂ : C} (g₁ : A₁ ⟶ W₁) (g₂ : A₂ ⟶ W₂) :
    @ComonObj.comul C _ _ (A₁ ⊗ A₂) (CopyDiscardCategory.comonObj (A₁ ⊗ A₂)) ≫
        (A₁ ⊗ A₂) ◁ (g₁ ⊗ₘ g₂) =
      ((Δ[A₁] ≫ A₁ ◁ g₁) ⊗ₘ (Δ[A₂] ≫ A₂ ◁ g₂)) ≫ tensorμ A₁ W₁ A₂ W₂ :=
  copy_tensor_comp_whiskerLeft_tensorHom g₁ g₂

example (A₁ W₁ A₂ W₂ : C) :
    tensorμ A₁ W₁ A₂ W₂ ≫
        @ComonObj.counit C _ _ (A₁ ⊗ A₂) (CopyDiscardCategory.comonObj (A₁ ⊗ A₂)) ▷ (W₁ ⊗ W₂) ≫
        (λ_ (W₁ ⊗ W₂)).hom =
      (ε[A₁] ▷ W₁ ≫ (λ_ W₁).hom) ⊗ₘ (ε[A₂] ▷ W₂ ≫ (λ_ W₂).hom) :=
  tensorμ_comp_snd A₁ W₁ A₂ W₂

example {A₁ A₂ X₁ W₁ Y₁ X₂ W₂ Y₂ : C} (g₁ : A₁ ⟶ W₁) (h₁ : A₁ ⊗ W₁ ⟶ X₁) (k₁ : W₁ ⊗ A₁ ⟶ Y₁)
    (g₂ : A₂ ⟶ W₂) (h₂ : A₂ ⊗ W₂ ⟶ X₂) (k₂ : W₂ ⊗ A₂ ⟶ Y₂) :
    (condIndepForm g₁ h₁ k₁ ⊗ₘ condIndepForm g₂ h₂ k₂) ≫
        (tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom =
      condIndepForm (g₁ ⊗ₘ g₂) (tensorδ A₁ W₁ A₂ W₂ ≫ (h₁ ⊗ₘ h₂))
        ((β_ (W₁ ⊗ W₂) (A₁ ⊗ A₂)).hom ≫ tensorδ A₁ W₁ A₂ W₂ ≫
          (((β_ A₁ W₁).hom ≫ k₁) ⊗ₘ ((β_ A₂ W₂).hom ≫ k₂))) :=
  condIndepForm_tensorHom_comp_tensorTripleInterchange g₁ h₁ k₁ g₂ h₂ k₂

example {A₁ A₂ X₁ W₁ Y₁ X₂ W₂ Y₂ : C} {f₁ : A₁ ⟶ X₁ ⊗ (W₁ ⊗ Y₁)} {f₂ : A₂ ⟶ X₂ ⊗ (W₂ ⊗ Y₂)}
    (hf₁ : DisplaysCondIndep f₁) (hf₂ : DisplaysCondIndep f₂) :
    DisplaysCondIndep ((f₁ ⊗ₘ f₂) ≫ (tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom) :=
  DisplaysCondIndep.tensor hf₁ hf₂

example {A₁ A₂ X₁ W₁ Y₁ X₂ W₂ Y₂ : C} {f₁ : A₁ ⟶ X₁ ⊗ (W₁ ⊗ Y₁)} {f₂ : A₂ ⟶ X₂ ⊗ (W₂ ⊗ Y₂)}
    (hf₁ : DisplaysCondIndep f₁) (hf₂ : DisplaysCondIndep f₂) :
    DisplaysCondIndep ((f₁ ⊗ₘ f₂) ≫ (tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom) :=
  hf₁.tensor hf₂

example {A X W Y : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X) (k : W ⊗ A ⟶ Y) :
    condIndepForm g h k = copyPair (𝟙 A) g ≫
      copyPair h (copyPair (ε[A] ▷ W ≫ (λ_ W).hom) ((β_ A W).hom ≫ k)) :=
  condIndepForm_eq_copyPair g h k

example {V X₂ W Y₂ : C} (g₂ : V ⟶ W) (h₂ : V ⊗ W ⟶ X₂) (k₂ : W ⊗ V ⟶ Y₂) :
    copyPair (𝟙 V) (condIndepForm g₂ h₂ k₂) ≫ (tensorLeftComm V X₂ (W ⊗ Y₂)).hom ≫
        X₂ ◁ (α_ V W Y₂).inv =
      copyPair (𝟙 V) g₂ ≫ copyPair h₂ (copyPair (𝟙 (V ⊗ W)) ((β_ V W).hom ≫ k₂)) :=
  copyPair_id_condIndepForm_comp_tensorLeftComm g₂ h₂ k₂

example {A X₁ V Y₁ X₂ W Y₂ : C} (g₁ : A ⟶ V) (h₁ : A ⊗ V ⟶ X₁) (k₁ : V ⊗ A ⟶ Y₁) (g₂ : V ⟶ W)
    (h₂ : V ⊗ W ⟶ X₂) (k₂ : W ⊗ V ⟶ Y₂) :
    condIndepForm g₁ h₁ k₁ ≫ X₁ ◁ ((Δ[V] ≫ V ◁ condIndepForm g₂ h₂ k₂) ▷ Y₁) ≫
        (tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom =
      condIndepForm (g₁ ≫ copyPair (𝟙 V) g₂)
        (copyPair (A ◁ (V ◁ ε[W] ≫ (ρ_ V).hom) ≫ h₁)
          (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ h₂))
        ((β_ (V ⊗ W) A).hom ≫
          copyPair (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ (β_ V W).hom ≫ k₂)
            (A ◁ (V ◁ ε[W] ≫ (ρ_ V).hom) ≫ (β_ A V).hom ≫ k₁)) :=
  condIndepForm_comp_copy_condIndepForm g₁ h₁ k₁ g₂ h₂ k₂

example {A X₁ V Y₁ X₂ W Y₂ : C} {f : A ⟶ X₁ ⊗ (V ⊗ Y₁)} {g : V ⟶ X₂ ⊗ (W ⊗ Y₂)}
    (hf : DisplaysCondIndep f) (hg : DisplaysCondIndep g) :
    DisplaysCondIndep
      (f ≫ X₁ ◁ ((Δ[V] ≫ V ◁ g) ▷ Y₁) ≫ (tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom) :=
  DisplaysCondIndep.comp hf hg

example {A X₁ V Y₁ X₂ W Y₂ : C} {f : A ⟶ X₁ ⊗ (V ⊗ Y₁)} {g : V ⟶ X₂ ⊗ (W ⊗ Y₂)}
    (hf : DisplaysCondIndep f) (hg : DisplaysCondIndep g) :
    DisplaysCondIndep
      (f ≫ X₁ ◁ ((Δ[V] ≫ V ◁ g) ▷ Y₁) ≫ (tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom) :=
  hf.comp hg

example {A X Y : C} (f : A ⟶ X ⊗ Y) (c : X ⊗ A ⟶ Y) :
    IsConditional f c ↔
      f = copyPair (marginalFst f) (𝟙 A) ≫ copyPair (X ◁ ε[A] ≫ (ρ_ X).hom) c :=
  isConditional_iff_copyPair f c

example (A V : C) : (β_ A V).hom ≫ ε[V] ▷ A ≫ (λ_ A).hom = A ◁ ε[V] ≫ (ρ_ A).hom :=
  braiding_comp_snd A V

example {A V P Q : C} (m : A ⟶ V) (x : A ⟶ P) (y : V ⊗ A ⟶ Q) :
    copyPair m (𝟙 A) ≫ copyPair ((ε[V] ▷ A ≫ (λ_ A).hom) ≫ x) y =
      copyPair x (copyPair m (𝟙 A) ≫ y) :=
  copyPair_id_right_comp_copyPair m x y

example {A V W : C} (m : A ⟶ V) (g' : V ⊗ A ⟶ W) :
    copyPair (𝟙 A) (copyPair m (𝟙 A) ≫ copyPair (V ◁ ε[A] ≫ (ρ_ V).hom) g') ≫
        (α_ A V W).inv ≫ (β_ A V).hom ▷ W =
      copyPair m (𝟙 A) ≫ copyPair (𝟙 (V ⊗ A)) g' :=
  copyPair_id_copyPair_comp m g'

example {A X V W Y : C} (g : A ⟶ V ⊗ W) (h : A ⊗ (V ⊗ W) ⟶ X) (k : (V ⊗ W) ⊗ A ⟶ Y) :
    condIndepForm g h k ≫ (tensorCondReorder X V W Y).hom =
      copyPair (𝟙 A) g ≫
        copyPair (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ V ◁ ε[W] ≫ (ρ_ V).hom)
          (copyPair h
            (copyPair (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ ε[V] ▷ W ≫ (λ_ W).hom)
              ((β_ A (V ⊗ W)).hom ≫ k))) :=
  condIndepForm_comp_tensorCondReorder_eq_copyPair g h k

example {A X V W Y : C} (m : A ⟶ V) (g' : V ⊗ A ⟶ W) (h : A ⊗ (V ⊗ W) ⟶ X)
    (k : (V ⊗ W) ⊗ A ⟶ Y) :
    condIndepForm (copyPair m (𝟙 A) ≫ copyPair (V ◁ ε[A] ≫ (ρ_ V).hom) g') h k ≫
        (tensorCondReorder X V W Y).hom =
      copyPair m (𝟙 A) ≫ copyPair (V ◁ ε[A] ≫ (ρ_ V).hom)
        (condIndepForm g' (((β_ V A).hom ▷ W ≫ (α_ A V W).hom) ≫ h)
          (((α_ W V A).inv ≫ (β_ W V).hom ▷ A) ≫ k)) :=
  condIndepForm_comp_tensorCondReorder m g' h k

example {Z P : C} (x : Z ⟶ P) : copyPair x ε[Z] ≫ (ρ_ P).hom = x :=
  copyPair_discard_comp_rightUnitor x

example {A W : C} (g : A ⟶ W) : copyPair (𝟙 A) g ≫ ε[A] ▷ W ≫ (λ_ W).hom = g :=
  copyPair_id_comp_snd g

end CopyDiscard

section Markov

variable [MarkovCategory C]

example {A X V W Y : C} (g : A ⟶ V ⊗ W) (h : A ⊗ (V ⊗ W) ⟶ X) (k : (V ⊗ W) ⊗ A ⟶ Y) :
    marginalFst (condIndepForm g h k ≫ (tensorCondReorder X V W Y).hom) = marginalFst g :=
  MarkovCategory.marginalFst_condIndepForm_comp_tensorCondReorder g h k

example {A X V W Y : C} {g : A ⟶ V ⊗ W} {g' : V ⊗ A ⟶ W} (hg : IsConditional g g')
    (h : A ⊗ (V ⊗ W) ⟶ X) (k : (V ⊗ W) ⊗ A ⟶ Y) :
    IsConditional (condIndepForm g h k ≫ (tensorCondReorder X V W Y).hom)
      (condIndepForm g' (((β_ V A).hom ▷ W ≫ (α_ A V W).hom) ≫ h)
        (((α_ W V A).inv ≫ (β_ W V).hom ▷ A) ≫ k)) :=
  CategoryTheory.CopyDiscardCategory.IsConditional.condIndepForm hg h k

example {A X V W Y : C} {g : A ⟶ V ⊗ W} {g' : V ⊗ A ⟶ W} (hg : IsConditional g g')
    (h : A ⊗ (V ⊗ W) ⟶ X) (k : (V ⊗ W) ⊗ A ⟶ Y) :
    IsConditional (condIndepForm g h k ≫ (tensorCondReorder X V W Y).hom)
      (condIndepForm g' (((β_ V A).hom ▷ W ≫ (α_ A V W).hom) ≫ h)
        (((α_ W V A).inv ≫ (β_ W V).hom ▷ A) ≫ k)) :=
  hg.condIndepForm h k

example [HasConditionals C] {A X V W Y : C} {f : A ⟶ X ⊗ ((V ⊗ W) ⊗ Y)}
    (hf : DisplaysCondIndep f) :
    ∃ c : V ⊗ A ⟶ X ⊗ (W ⊗ Y),
      IsConditional (f ≫ (tensorCondReorder X V W Y).hom) c ∧ DisplaysCondIndep c :=
  CategoryTheory.CopyDiscardCategory.DisplaysCondIndep.exists_isConditional hf

example [HasConditionals C] {A X V W Y : C} {f : A ⟶ X ⊗ ((V ⊗ W) ⊗ Y)}
    (hf : DisplaysCondIndep f) :
    ∃ c : V ⊗ A ⟶ X ⊗ (W ⊗ Y),
      IsConditional (f ≫ (tensorCondReorder X V W Y).hom) c ∧ DisplaysCondIndep c :=
  hf.exists_isConditional

end Markov

end CategoryTheory
