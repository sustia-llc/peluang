/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Causal
public import Peluang.Deterministic.Lemmas
public import Peluang.Monoidal.Reorder

/-!
# The pairing of two morphisms out of one object

For `x : Z ⟶ P` and `y : Z ⟶ Q` in a copy-discard category, the pairing
`copyPair x y : Z ⟶ P ⊗ Q` is `Δ[Z] ≫ (x ⊗ₘ y)`. This file has its equations with the tensor
product of morphisms, the whiskerings, the braiding, the associator, `tensorLeftComm`,
deterministic morphisms and the two marginal projections.

## Main definitions

* `CopyDiscardCategory.copyPair` - for `x : Z ⟶ P` and `y : Z ⟶ Q` in a copy-discard category,
  the morphism `Δ[Z] ≫ (x ⊗ₘ y) : Z ⟶ P ⊗ Q`.

## Main results

* `CopyDiscardCategory.copyPair_comp_tensorHom` - in a copy-discard category,
  `copyPair x y ≫ (u ⊗ₘ v) = copyPair (x ≫ u) (y ≫ v)`.
* `CopyDiscardCategory.copyPair_comp_braiding` - in a copy-discard category,
  `copyPair x y ≫ (β_ P Q).hom = copyPair y x`.
* `CopyDiscardCategory.copyPair_assoc` - in a copy-discard category,
  `copyPair (copyPair x y) z ≫ (α_ P Q R).hom = copyPair x (copyPair y z)`.
* `CopyDiscardCategory.comp_copyPair` - in a copy-discard category, for a deterministic `s`,
  `s ≫ copyPair x y = copyPair (s ≫ x) (s ≫ y)`.
* `CopyDiscardCategory.copyPair_fst_snd` - in a copy-discard category, the pairing of the two
  marginal projections of `V ⊗ W` is `𝟙 (V ⊗ W)`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace CopyDiscardCategory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

/-- For `x : Z ⟶ P` and `y : Z ⟶ Q` in a copy-discard category `C`, the morphism
`Δ[Z] ≫ (x ⊗ₘ y) : Z ⟶ P ⊗ Q` that copies `Z` and applies `x` to the left copy and `y` to the
right copy. -/
def copyPair {Z P Q : C} (x : Z ⟶ P) (y : Z ⟶ Q) : Z ⟶ P ⊗ Q := Δ[Z] ≫ (x ⊗ₘ y)

-- WITNESS: none (step of DisplaysCondIndep.comp, IsConditional.condIndepForm)
/-- For `x : Z ⟶ P`, `y : Z ⟶ Q`, `u : P ⟶ P'` and `v : Q ⟶ Q'` in a copy-discard category
`C`, `copyPair x y ≫ (u ⊗ₘ v) = copyPair (x ≫ u) (y ≫ v)`. -/
@[reassoc]
theorem copyPair_comp_tensorHom {Z P Q P' Q' : C} (x : Z ⟶ P) (y : Z ⟶ Q) (u : P ⟶ P')
    (v : Q ⟶ Q') : copyPair x y ≫ (u ⊗ₘ v) = copyPair (x ≫ u) (y ≫ v) := by
  unfold copyPair
  rw [Category.assoc, tensorHom_comp_tensorHom]

-- WITNESS: none (step of DisplaysCondIndep.comp, IsConditional.condIndepForm)
/-- For `x : Z ⟶ P`, `y : Z ⟶ Q` and `v : Q ⟶ Q'` in a copy-discard category `C`,
`copyPair x y ≫ P ◁ v = copyPair x (y ≫ v)`. -/
@[reassoc]
theorem copyPair_comp_whiskerLeft {Z P Q Q' : C} (x : Z ⟶ P) (y : Z ⟶ Q) (v : Q ⟶ Q') :
    copyPair x y ≫ P ◁ v = copyPair x (y ≫ v) := by
  rw [← id_tensorHom, copyPair_comp_tensorHom, Category.comp_id]

-- WITNESS: none (step of DisplaysCondIndep.comp, IsConditional.condIndepForm)
/-- For `x : Z ⟶ P`, `y : Z ⟶ Q` and `u : P ⟶ P'` in a copy-discard category `C`,
`copyPair x y ≫ u ▷ Q = copyPair (x ≫ u) y`. -/
@[reassoc]
theorem copyPair_comp_whiskerRight {Z P Q P' : C} (x : Z ⟶ P) (y : Z ⟶ Q) (u : P ⟶ P') :
    copyPair x y ≫ u ▷ Q = copyPair (x ≫ u) y := by
  rw [← tensorHom_id, copyPair_comp_tensorHom, Category.comp_id]

-- WITNESS: none (step of DisplaysCondIndep.comp, IsConditional.condIndepForm)
/-- For `x : Z ⟶ P` and `y : Z ⟶ Q` in a copy-discard category `C`,
`copyPair x y ≫ (β_ P Q).hom = copyPair y x`. -/
@[reassoc]
theorem copyPair_comp_braiding {Z P Q : C} (x : Z ⟶ P) (y : Z ⟶ Q) :
    copyPair x y ≫ (β_ P Q).hom = copyPair y x := by
  unfold copyPair
  rw [Category.assoc, BraidedCategory.braiding_naturality, IsCommComonObj.comul_comm_assoc]

-- WITNESS: none (step of DisplaysCondIndep.comp, IsConditional.condIndepForm)
/-- For `x : Z ⟶ P`, `y : Z ⟶ Q` and `z : Z ⟶ R` in a copy-discard category `C`,
`copyPair (copyPair x y) z ≫ (α_ P Q R).hom = copyPair x (copyPair y z)`. -/
@[reassoc]
theorem copyPair_assoc {Z P Q R : C} (x : Z ⟶ P) (y : Z ⟶ Q) (z : Z ⟶ R) :
    copyPair (copyPair x y) z ≫ (α_ P Q R).hom = copyPair x (copyPair y z) := by
  have e1 : (Δ[Z] ≫ (x ⊗ₘ y)) ⊗ₘ z = Δ[Z] ▷ Z ≫ ((x ⊗ₘ y) ⊗ₘ z) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  have e2 : x ⊗ₘ (Δ[Z] ≫ (y ⊗ₘ z)) = Z ◁ Δ[Z] ≫ (x ⊗ₘ (y ⊗ₘ z)) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  unfold copyPair
  rw [e1, e2]
  simp only [Category.assoc]
  rw [associator_naturality, comul_assoc_assoc]

-- WITNESS: none (step of DisplaysCondIndep.comp, IsConditional.condIndepForm)
/-- For `x : Z ⟶ P`, `y : Z ⟶ Q` and `z : Z ⟶ R` in a copy-discard category `C`,
`copyPair x (copyPair y z) ≫ (α_ P Q R).inv = copyPair (copyPair x y) z`. -/
@[reassoc]
theorem copyPair_assoc_inv {Z P Q R : C} (x : Z ⟶ P) (y : Z ⟶ Q) (z : Z ⟶ R) :
    copyPair x (copyPair y z) ≫ (α_ P Q R).inv = copyPair (copyPair x y) z := by
  rw [← copyPair_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

-- WITNESS: none (step of DisplaysCondIndep.comp, IsConditional.condIndepForm)
/-- For a deterministic `s : S ⟶ Z`, and for `x : Z ⟶ P` and `y : Z ⟶ Q`, in a copy-discard
category `C`, `s ≫ copyPair x y = copyPair (s ≫ x) (s ≫ y)`. -/
theorem comp_copyPair {S Z P Q : C} (s : S ⟶ Z) [Deterministic s] (x : Z ⟶ P) (y : Z ⟶ Q) :
    s ≫ copyPair x y = copyPair (s ≫ x) (s ≫ y) := by
  unfold copyPair
  rw [reassoc_of% (Deterministic.copy_natural s), tensorHom_comp_tensorHom]

-- WITNESS: none (step of DisplaysCondIndep.comp, IsConditional.condIndepForm)
/-- For `x : Z ⟶ P`, `y : Z ⟶ Q` and `z : Z ⟶ R` in a copy-discard category `C`,
`copyPair x (copyPair y z) ≫ (tensorLeftComm P Q R).hom = copyPair y (copyPair x z)`. -/
@[reassoc]
theorem copyPair_comp_tensorLeftComm {Z P Q R : C} (x : Z ⟶ P) (y : Z ⟶ Q) (z : Z ⟶ R) :
    copyPair x (copyPair y z) ≫ (tensorLeftComm P Q R).hom = copyPair y (copyPair x z) := by
  rw [tensorLeftComm_hom, copyPair_assoc_inv_assoc, copyPair_comp_whiskerRight_assoc,
    copyPair_comp_braiding, copyPair_assoc]

-- WITNESS: none (step of DisplaysCondIndep.comp, IsConditional.condIndepForm)
/-- For objects `V`, `W` of a copy-discard category `C`, the pairing of the first projection
`V ◁ ε[W] ≫ (ρ_ V).hom` and the second projection `ε[V] ▷ W ≫ (λ_ W).hom` of `V ⊗ W` is
`𝟙 (V ⊗ W)`. -/
theorem copyPair_fst_snd (V W : C) :
    copyPair (V ◁ ε[W] ≫ (ρ_ V).hom) (ε[V] ▷ W ≫ (λ_ W).hom) = 𝟙 (V ⊗ W) :=
  copy_comp_fst_tensorHom_snd V W

-- WITNESS: none (step of DisplaysCondIndep.comp; witnessed through it)
/-- For `x : Z ⟶ X₁`, `y : Z ⟶ X₂`, `u : Z ⟶ Zo`, `v : Z ⟶ Y₂` and `w : Z ⟶ Y₁` in a
copy-discard category `C`, `copyPair x (copyPair (copyPair y (copyPair u v)) w)` followed by
`X₁ ◁ (α_ X₂ (Zo ⊗ Y₂) Y₁).hom ≫ (α_ X₁ X₂ ((Zo ⊗ Y₂) ⊗ Y₁)).inv ≫ (X₁ ⊗ X₂) ◁ (α_ Zo Y₂ Y₁).hom`
equals `copyPair (copyPair x y) (copyPair u (copyPair v w))`. -/
theorem copyPair_reassoc {Z X₁ X₂ Zo Y₂ Y₁ : C} (x : Z ⟶ X₁) (y : Z ⟶ X₂) (u : Z ⟶ Zo)
    (v : Z ⟶ Y₂) (w : Z ⟶ Y₁) :
    copyPair x (copyPair (copyPair y (copyPair u v)) w) ≫ X₁ ◁ (α_ X₂ (Zo ⊗ Y₂) Y₁).hom ≫
        (α_ X₁ X₂ ((Zo ⊗ Y₂) ⊗ Y₁)).inv ≫ (X₁ ⊗ X₂) ◁ (α_ Zo Y₂ Y₁).hom =
      copyPair (copyPair x y) (copyPair u (copyPair v w)) := by
  rw [copyPair_comp_whiskerLeft_assoc, copyPair_assoc, copyPair_assoc_inv_assoc,
    copyPair_comp_whiskerLeft, copyPair_assoc]

-- WITNESS: none (step of DisplaysCondIndep.comp, IsConditional.condIndepForm)
/-- For `j : S ⟶ S'` and `q : S' ⟶ S` in a copy-discard category `C` with
`j ≫ Δ[S'] ≫ q ▷ S' = Δ[S] ≫ S ◁ j`, and for `x : S ⟶ P` and `y : S' ⟶ Q`,
`j ≫ copyPair (q ≫ x) y = copyPair x (j ≫ y)`. -/
@[reassoc]
theorem comp_copyPair_of_peel {S S' P Q : C} {j : S ⟶ S'} {q : S' ⟶ S}
    (hjq : j ≫ Δ[S'] ≫ q ▷ S' = Δ[S] ≫ S ◁ j) (x : S ⟶ P) (y : S' ⟶ Q) :
    j ≫ copyPair (q ≫ x) y = copyPair x (j ≫ y) := by
  have e1 : (q ≫ x) ⊗ₘ y = q ▷ S' ≫ (x ⊗ₘ y) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  have e2 : x ⊗ₘ (j ≫ y) = S ◁ j ≫ (x ⊗ₘ y) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  unfold copyPair
  rw [e1, e2, reassoc_of% hjq]

-- WITNESS: none (step of DisplaysCondIndep.comp; witnessed through it)
/-- For `j : S ⟶ S'` and `q : S' ⟶ S` in a copy-discard category `C` with
`j ≫ Δ[S'] ≫ q ▷ S' = Δ[S] ≫ S ◁ j`, and for `x : S ⟶ P` and `y : S' ⟶ Q`,
`j ≫ copyPair y (q ≫ x) = copyPair (j ≫ y) x`. -/
theorem comp_copyPair_of_peel' {S S' P Q : C} {j : S ⟶ S'} {q : S' ⟶ S}
    (hjq : j ≫ Δ[S'] ≫ q ▷ S' = Δ[S] ≫ S ◁ j) (x : S ⟶ P) (y : S' ⟶ Q) :
    j ≫ copyPair y (q ≫ x) = copyPair (j ≫ y) x := by
  rw [← copyPair_comp_braiding (q ≫ x) y, comp_copyPair_of_peel_assoc hjq x y,
    copyPair_comp_braiding]

-- WITNESS: none (step of DisplaysCondIndep.comp, IsConditional.condIndepForm)
/-- For `g : V ⟶ W` in a copy-discard category `C`, `copyPair (𝟙 V) g : V ⟶ V ⊗ W` followed by
the copy of `V ⊗ W` and the first projection `V ◁ ε[W] ≫ (ρ_ V).hom` on the left copy equals
`Δ[V] ≫ V ◁ copyPair (𝟙 V) g`. -/
theorem copyPair_id_comp_copy_comp_fst {V W : C} (g : V ⟶ W) :
    copyPair (𝟙 V) g ≫ @ComonObj.comul C _ _ (V ⊗ W) (CopyDiscardCategory.comonObj (V ⊗ W)) ≫
        (V ◁ ε[W] ≫ (ρ_ V).hom) ▷ (V ⊗ W) =
      Δ[V] ≫ V ◁ copyPair (𝟙 V) g := by
  unfold copyPair
  rw [id_tensorHom, Category.assoc, copy_comp_fst_whiskerRight, whisker_exchange_assoc,
    associator_naturality_right, ← comul_assoc_assoc, whiskerLeft_comp]

-- WITNESS: none (step of DisplaysCondIndep.comp; witnessed through it)
/-- For an object `A`, and for `j : S ⟶ S'` and `q : S' ⟶ S` with
`j ≫ Δ[S'] ≫ q ▷ S' = Δ[S] ≫ S ◁ j`, in a copy-discard category `C`, `A ◁ j` followed by the
copy of `A ⊗ S'` and `A ◁ q` on the left copy equals the copy of `A ⊗ S` followed by `A ◁ j`
on the right copy. -/
theorem whiskerLeft_comp_copy_tensor_of_peel (A : C) {S S' : C} {j : S ⟶ S'} {q : S' ⟶ S}
    (hjq : j ≫ Δ[S'] ≫ q ▷ S' = Δ[S] ≫ S ◁ j) :
    A ◁ j ≫ @ComonObj.comul C _ _ (A ⊗ S') (CopyDiscardCategory.comonObj (A ⊗ S')) ≫
        (A ◁ q) ▷ (A ⊗ S') =
      @ComonObj.comul C _ _ (A ⊗ S) (CopyDiscardCategory.comonObj (A ⊗ S)) ≫
        (A ⊗ S) ◁ (A ◁ j) := by
  have e1 : (A ◁ q) ▷ (A ⊗ S') = (𝟙 A ⊗ₘ q) ⊗ₘ (𝟙 A ⊗ₘ 𝟙 S') := by
    simp only [id_tensorHom, tensorHom_id, id_whiskerRight]
  have e2 : (A ⊗ S) ◁ (A ◁ j) = (𝟙 A ⊗ₘ 𝟙 S) ⊗ₘ (𝟙 A ⊗ₘ j) := by
    simp only [id_tensorHom, whiskerLeft_id]
  have hjq' : j ≫ Δ[S'] ≫ (q ⊗ₘ 𝟙 S') = Δ[S] ≫ (𝟙 S ⊗ₘ j) := by
    rw [tensorHom_id, id_tensorHom]
    exact hjq
  calc
    _ = A ◁ j ≫ (Δ[A] ⊗ₘ Δ[S']) ≫ ((𝟙 A ⊗ₘ 𝟙 A) ⊗ₘ (q ⊗ₘ 𝟙 S')) ≫ tensorμ A A S S' := by
      rw [copy_tensor, e1, Category.assoc, ← tensorμ_natural]
    _ = ((Δ[A] ≫ (𝟙 A ⊗ₘ 𝟙 A)) ⊗ₘ (j ≫ Δ[S'] ≫ (q ⊗ₘ 𝟙 S'))) ≫ tensorμ A A S S' := by
      rw [← id_tensorHom A j, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
      simp only [Category.assoc, Category.id_comp]
    _ = ((Δ[A] ≫ (𝟙 A ⊗ₘ 𝟙 A)) ⊗ₘ (Δ[S] ≫ (𝟙 S ⊗ₘ j))) ≫ tensorμ A A S S' := by
      rw [hjq']
    _ = (Δ[A] ⊗ₘ Δ[S]) ≫ ((𝟙 A ⊗ₘ 𝟙 A) ⊗ₘ (𝟙 S ⊗ₘ j)) ≫ tensorμ A A S S' := by
      rw [tensorHom_comp_tensorHom_assoc]
    _ = _ := by
      rw [copy_tensor, e2, Category.assoc, ← tensorμ_natural]

end CopyDiscardCategory

end CategoryTheory
