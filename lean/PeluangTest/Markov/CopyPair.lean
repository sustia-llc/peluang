/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Markov.CopyPair
import PeluangLint

/-!
# Tests for `Peluang.Markov.CopyPair`

`copyPair x y` against `Δ[Z] ≫ (x ⊗ₘ y)` by `rfl`. Each of `copyPair_comp_tensorHom`,
`copyPair_comp_whiskerLeft`, `copyPair_comp_whiskerRight`, `copyPair_comp_braiding`,
`copyPair_assoc`, `copyPair_assoc_inv`, `comp_copyPair`, `copyPair_comp_tensorLeftComm`,
`copyPair_fst_snd`, `copyPair_reassoc`, `comp_copyPair_of_peel`, `comp_copyPair_of_peel'`,
`copyPair_id_comp_copy_comp_fst` and `whiskerLeft_comp_copy_tensor_of_peel` applied at
variables.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

example {Z P Q : C} (x : Z ⟶ P) (y : Z ⟶ Q) : copyPair x y = Δ[Z] ≫ (x ⊗ₘ y) := rfl

example {Z P Q P' Q' : C} (x : Z ⟶ P) (y : Z ⟶ Q) (u : P ⟶ P') (v : Q ⟶ Q') :
    copyPair x y ≫ (u ⊗ₘ v) = copyPair (x ≫ u) (y ≫ v) :=
  copyPair_comp_tensorHom x y u v

example {Z P Q Q' : C} (x : Z ⟶ P) (y : Z ⟶ Q) (v : Q ⟶ Q') :
    copyPair x y ≫ P ◁ v = copyPair x (y ≫ v) :=
  copyPair_comp_whiskerLeft x y v

example {Z P Q P' : C} (x : Z ⟶ P) (y : Z ⟶ Q) (u : P ⟶ P') :
    copyPair x y ≫ u ▷ Q = copyPair (x ≫ u) y :=
  copyPair_comp_whiskerRight x y u

example {Z P Q : C} (x : Z ⟶ P) (y : Z ⟶ Q) : copyPair x y ≫ (β_ P Q).hom = copyPair y x :=
  copyPair_comp_braiding x y

example {Z P Q R : C} (x : Z ⟶ P) (y : Z ⟶ Q) (z : Z ⟶ R) :
    copyPair (copyPair x y) z ≫ (α_ P Q R).hom = copyPair x (copyPair y z) :=
  copyPair_assoc x y z

example {Z P Q R : C} (x : Z ⟶ P) (y : Z ⟶ Q) (z : Z ⟶ R) :
    copyPair x (copyPair y z) ≫ (α_ P Q R).inv = copyPair (copyPair x y) z :=
  copyPair_assoc_inv x y z

example {S Z P Q : C} (s : S ⟶ Z) [Deterministic s] (x : Z ⟶ P) (y : Z ⟶ Q) :
    s ≫ copyPair x y = copyPair (s ≫ x) (s ≫ y) :=
  comp_copyPair s x y

example {Z P Q R : C} (x : Z ⟶ P) (y : Z ⟶ Q) (z : Z ⟶ R) :
    copyPair x (copyPair y z) ≫ (tensorLeftComm P Q R).hom = copyPair y (copyPair x z) :=
  copyPair_comp_tensorLeftComm x y z

example (V W : C) :
    copyPair (V ◁ ε[W] ≫ (ρ_ V).hom) (ε[V] ▷ W ≫ (λ_ W).hom) = 𝟙 (V ⊗ W) :=
  copyPair_fst_snd V W

example {Z X₁ X₂ Zo Y₂ Y₁ : C} (x : Z ⟶ X₁) (y : Z ⟶ X₂) (u : Z ⟶ Zo) (v : Z ⟶ Y₂)
    (w : Z ⟶ Y₁) :
    copyPair x (copyPair (copyPair y (copyPair u v)) w) ≫ X₁ ◁ (α_ X₂ (Zo ⊗ Y₂) Y₁).hom ≫
        (α_ X₁ X₂ ((Zo ⊗ Y₂) ⊗ Y₁)).inv ≫ (X₁ ⊗ X₂) ◁ (α_ Zo Y₂ Y₁).hom =
      copyPair (copyPair x y) (copyPair u (copyPair v w)) :=
  copyPair_reassoc x y u v w

example {S S' P Q : C} {j : S ⟶ S'} {q : S' ⟶ S} (hjq : j ≫ Δ[S'] ≫ q ▷ S' = Δ[S] ≫ S ◁ j)
    (x : S ⟶ P) (y : S' ⟶ Q) :
    j ≫ copyPair (q ≫ x) y = copyPair x (j ≫ y) :=
  comp_copyPair_of_peel hjq x y

example {S S' P Q : C} {j : S ⟶ S'} {q : S' ⟶ S} (hjq : j ≫ Δ[S'] ≫ q ▷ S' = Δ[S] ≫ S ◁ j)
    (x : S ⟶ P) (y : S' ⟶ Q) :
    j ≫ copyPair y (q ≫ x) = copyPair (j ≫ y) x :=
  comp_copyPair_of_peel' hjq x y

example {V W : C} (g : V ⟶ W) :
    copyPair (𝟙 V) g ≫ @ComonObj.comul C _ _ (V ⊗ W) (CopyDiscardCategory.comonObj (V ⊗ W)) ≫
        (V ◁ ε[W] ≫ (ρ_ V).hom) ▷ (V ⊗ W) =
      Δ[V] ≫ V ◁ copyPair (𝟙 V) g :=
  copyPair_id_comp_copy_comp_fst g

example (A : C) {S S' : C} {j : S ⟶ S'} {q : S' ⟶ S}
    (hjq : j ≫ Δ[S'] ≫ q ▷ S' = Δ[S] ≫ S ◁ j) :
    A ◁ j ≫ @ComonObj.comul C _ _ (A ⊗ S') (CopyDiscardCategory.comonObj (A ⊗ S')) ≫
        (A ◁ q) ▷ (A ⊗ S') =
      @ComonObj.comul C _ _ (A ⊗ S) (CopyDiscardCategory.comonObj (A ⊗ S)) ≫
        (A ⊗ S) ◁ (A ◁ j) :=
  whiskerLeft_comp_copy_tensor_of_peel A hjq

end CategoryTheory
