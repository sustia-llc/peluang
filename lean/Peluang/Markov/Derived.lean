/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.MarkovCategory.Basic

/-!
# Derived Markov-category structure

Coherence of the comonoid instance on a tensor product, discard naturality at
that instance, and the marginals of a morphism into a tensor product.

## Main definitions

* `MarkovCategory.marginalFst`, `MarkovCategory.marginalSnd` - the marginals of
  `f : A ⟶ X ⊗ Y` (Fritz 2020, Notation 2.8). The pushforward of `ψ` along `f`
  (Fritz 2020, Notation 2.8) is the composite `ψ ≫ f` and gets no definition.

## Main results

* `CopyDiscardCategory.comonObj_tensor` - the comonoid structure a copy-discard
  category assigns to `X ⊗ Y` is the tensor product comonoid structure.
* `MarkovCategory.discard_natural_tensor` - discard naturality into `X ⊗ Y` at
  the tensor product comonoid structure.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

-- WITNESS: none (instance coherence; no engine meaning)
/-- In a copy-discard category, the comonoid structure on `X ⊗ Y` given by the
category equals the tensor product of the comonoid structures on `X` and `Y`. -/
theorem CopyDiscardCategory.comonObj_tensor [CopyDiscardCategory C] (X Y : C) :
    CopyDiscardCategory.comonObj (X ⊗ Y) = Comon.instComonObjTensorObj X Y := by
  have h1 := CopyDiscardCategory.copy_tensor X Y
  have h2 := CopyDiscardCategory.discard_tensor X Y
  rw [← Comon.tensorObj_comul] at h1
  rw [← Comon.tensorObj_counit] at h2
  revert h1 h2
  generalize CopyDiscardCategory.comonObj (X ⊗ Y) = I
  generalize Comon.instComonObjTensorObj X Y = J
  rcases I with ⟨_, _⟩
  rcases J with ⟨_, _⟩
  rintro rfl rfl
  rfl

-- WITNESS: none (Mathlib discard_natural at the tensor instance)
/-- In a Markov category, every morphism into `X ⊗ Y` followed by discarding
`X ⊗ Y` (at the tensor product comonoid structure) is discarding its domain. -/
@[reassoc (attr := simp)]
theorem MarkovCategory.discard_natural_tensor [MarkovCategory C] {A X Y : C}
    (f : A ⟶ X ⊗ Y) : f ≫ ε[X ⊗ Y] = ε[A] := by
  have h := MarkovCategory.discard_natural f
  rwa [CopyDiscardCategory.comonObj_tensor] at h

namespace MarkovCategory

/-- The first marginal of `f : A ⟶ X ⊗ Y`: discard the `Y` output
(Fritz 2020, Notation 2.8). -/
def marginalFst [CopyDiscardCategory C] {A X Y : C} (f : A ⟶ X ⊗ Y) : A ⟶ X :=
  f ≫ X ◁ ε[Y] ≫ (ρ_ X).hom

/-- The second marginal of `f : A ⟶ X ⊗ Y`: discard the `X` output
(Fritz 2020, Notation 2.8). -/
def marginalSnd [CopyDiscardCategory C] {A X Y : C} (f : A ⟶ X ⊗ Y) : A ⟶ Y :=
  f ≫ ε[X] ▷ Y ≫ (λ_ Y).hom

section CopyDiscard

variable [CopyDiscardCategory C] {A B X Y : C}

-- WITNESS: none (Phase 2R witness)
/-- The first marginal commutes with precomposition. -/
@[simp]
theorem marginalFst_comp (k : B ⟶ A) (f : A ⟶ X ⊗ Y) :
    marginalFst (k ≫ f) = k ≫ marginalFst f := by
  simp [marginalFst]

-- WITNESS: none (Phase 2R witness)
/-- The second marginal commutes with precomposition. -/
@[simp]
theorem marginalSnd_comp (k : B ⟶ A) (f : A ⟶ X ⊗ Y) :
    marginalSnd (k ≫ f) = k ≫ marginalSnd f := by
  simp [marginalSnd]

-- WITNESS: none (Phase 2R witness)
/-- The first marginal of copying is the identity. -/
@[simp]
theorem marginalFst_copy (X : C) : marginalFst Δ[X] = 𝟙 X := by
  simp [marginalFst]

-- WITNESS: none (Phase 2R witness)
/-- The second marginal of copying is the identity. -/
@[simp]
theorem marginalSnd_copy (X : C) : marginalSnd Δ[X] = 𝟙 X := by
  simp [marginalSnd]

end CopyDiscard

section Markov

variable [MarkovCategory C] {A X Y : C}

-- WITNESS: none (Phase 2R witness)
/-- In a Markov category, the first marginal of `Δ[A] ≫ (g ⊗ₘ h)` is `g`. -/
@[simp]
theorem marginalFst_copy_comp_tensorHom (g : A ⟶ X) (h : A ⟶ Y) :
    marginalFst (Δ[A] ≫ (g ⊗ₘ h)) = g := by
  rw [marginalFst, Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.comp_id, MarkovCategory.discard_natural, comul_counit_hom_assoc, Iso.inv_hom_id,
    Category.comp_id]

-- WITNESS: none (Phase 2R witness)
/-- In a Markov category, the second marginal of `Δ[A] ≫ (g ⊗ₘ h)` is `h`. -/
@[simp]
theorem marginalSnd_copy_comp_tensorHom (g : A ⟶ X) (h : A ⟶ Y) :
    marginalSnd (Δ[A] ≫ (g ⊗ₘ h)) = h := by
  rw [marginalSnd, Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
    Category.comp_id, MarkovCategory.discard_natural, counit_comul_hom_assoc, Iso.inv_hom_id,
    Category.comp_id]

end Markov

end MarkovCategory

end CategoryTheory
