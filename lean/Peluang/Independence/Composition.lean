/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Independence.Semigraphoid
public import Peluang.Markov.CopyPair

/-!
# The composition properties of conditional independence

The composition properties of conditional independence given an input (Fritz 2020,
Prop. 12.18): the tensor product of two morphisms that display conditional independence, their
composite along a copy of the conditioning object, the composite with two arbitrary morphisms,
and a conditional that displays conditional independence.

## Main results

* `CopyDiscardCategory.DisplaysCondIndep.tensor` - in a copy-discard category, if
  `f₁ : A₁ ⟶ X₁ ⊗ (W₁ ⊗ Y₁)` and `f₂ : A₂ ⟶ X₂ ⊗ (W₂ ⊗ Y₂)` display conditional independence,
  then `(f₁ ⊗ₘ f₂) ≫ (tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom` displays conditional
  independence (Fritz 2020, Prop. 12.18 (a)).
* `CopyDiscardCategory.DisplaysCondIndep.comp` - in a copy-discard category, if
  `f : A ⟶ X₁ ⊗ (V ⊗ Y₁)` and `g : V ⟶ X₂ ⊗ (W ⊗ Y₂)` display conditional independence, then
  `f ≫ X₁ ◁ ((Δ[V] ≫ V ◁ g) ▷ Y₁) ≫ (tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom` displays
  conditional independence (Fritz 2020, Prop. 12.18 (b)).
* `CopyDiscardCategory.DisplaysCondIndep.comp_tensorHom` - in a copy-discard category, if
  `f : A ⟶ X₁ ⊗ (W ⊗ Y₁)` displays conditional independence, then for `u : A ⊗ X₁ ⟶ X₂` and
  `v : Y₁ ⊗ A ⟶ Y₂` the composite
  `Δ[A] ≫ A ◁ Δ[A] ≫ A ◁ (f ▷ A) ≫ (tensorCompAssoc A X₁ W Y₁ A).hom ≫ (u ⊗ₘ W ◁ v)` displays
  conditional independence (Fritz 2020, Prop. 12.18 (c)).
* `CopyDiscardCategory.IsConditional.condIndepForm` - in a Markov category, if `g'` is a
  conditional of `g : A ⟶ V ⊗ W` on `V`, then a `condIndepForm` on `g'` is a conditional of
  `condIndepForm g h k ≫ (tensorCondReorder X V W Y).hom` on `V` (Fritz 2020, Prop. 12.18 (d)
  and Def. 11.5).
* `CopyDiscardCategory.DisplaysCondIndep.exists_isConditional` - in a Markov category with
  conditionals, if `f : A ⟶ X ⊗ ((V ⊗ W) ⊗ Y)` displays conditional independence, then
  `f ≫ (tensorCondReorder X V W Y).hom` has a conditional on `V` that displays conditional
  independence (Fritz 2020, Prop. 12.18 (d)).

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

-- WITNESS: none (step of DisplaysCondIndep.comp_tensorHom; witnessed through it)
/-- For an object `A` of a copy-discard category `C`, the composite
`Δ[A] ≫ A ◁ Δ[A] ≫ A ◁ (Δ[A] ▷ A) ≫ A ◁ ((A ◁ Δ[A]) ▷ A) : A ⟶ A ⊗ ((A ⊗ (A ⊗ A)) ⊗ A)` of
four copy morphisms equals `Δ[A] ≫ A ◁ Δ[A] ≫ Δ[A] ▷ (A ⊗ A) ≫ (A ⊗ A) ◁ (A ◁ Δ[A])` followed by
associators. -/
theorem copy_comp_whiskerLeft_copy_five (A : C) :
    Δ[A] ≫ A ◁ Δ[A] ≫ A ◁ (Δ[A] ▷ A) ≫ A ◁ ((A ◁ Δ[A]) ▷ A) =
      Δ[A] ≫ A ◁ Δ[A] ≫ Δ[A] ▷ (A ⊗ A) ≫ (A ⊗ A) ◁ (A ◁ Δ[A]) ≫
        (α_ A A (A ⊗ (A ⊗ A))).hom ≫ A ◁ (A ◁ (α_ A A A).inv) ≫
        A ◁ (α_ A (A ⊗ A) A).inv := by
  calc
    _ = Δ[A] ≫ A ◁ ((Δ[A] ≫ Δ[A] ▷ A) ≫ (A ◁ Δ[A]) ▷ A) := by
      simp only [whiskerLeft_comp, Category.assoc]
    _ = Δ[A] ≫ A ◁ (Δ[A] ≫ A ◁ (Δ[A] ≫ Δ[A] ▷ A) ≫ (α_ A (A ⊗ A) A).inv) := by
      conv_lhs => rw [comul_assoc_flip A]
      monoidal
    _ = (Δ[A] ≫ A ◁ Δ[A] ≫ (α_ A A A).inv) ≫ (A ⊗ A) ◁ (Δ[A] ≫ A ◁ Δ[A]) ≫
          (α_ A A (A ⊗ (A ⊗ A))).hom ≫ A ◁ (A ◁ (α_ A A A).inv) ≫
          A ◁ (α_ A (A ⊗ A) A).inv := by
      conv_lhs => rw [comul_assoc_flip A]
      monoidal
    _ = _ := by
      rw [← comul_assoc_flip A]
      simp only [whiskerLeft_comp, Category.assoc]
      rw [← whisker_exchange_assoc Δ[A] Δ[A]]

-- WITNESS: none (step of DisplaysCondIndep.comp_tensorHom; witnessed through it)
/-- For `g : A ⟶ W`, `h : A ⊗ W ⟶ X₁`, `k : W ⊗ A ⟶ Y₁`, `u : A ⊗ X₁ ⟶ X₂` and
`v : Y₁ ⊗ A ⟶ Y₂` in a copy-discard category `C`, the composite
`Δ[A] ≫ A ◁ Δ[A] ≫ A ◁ (condIndepForm g h k ▷ A) ≫ (tensorCompAssoc A X₁ W Y₁ A).hom ≫
(u ⊗ₘ W ◁ v) : A ⟶ X₂ ⊗ (W ⊗ Y₂)` equals
`condIndepForm g (Δ[A] ▷ W ≫ (α_ A A W).hom ≫ A ◁ h ≫ u) (W ◁ Δ[A] ≫ (α_ W A A).inv ≫ k ▷ A ≫ v)`
(Fritz 2020, Prop. 12.18 (c)). -/
theorem copy_comp_condIndepForm_comp_tensorHom {A X₁ W Y₁ X₂ Y₂ : C} (g : A ⟶ W)
    (h : A ⊗ W ⟶ X₁) (k : W ⊗ A ⟶ Y₁) (u : A ⊗ X₁ ⟶ X₂) (v : Y₁ ⊗ A ⟶ Y₂) :
    Δ[A] ≫ A ◁ Δ[A] ≫ A ◁ (condIndepForm g h k ▷ A) ≫ (tensorCompAssoc A X₁ W Y₁ A).hom ≫
        (u ⊗ₘ W ◁ v) =
      condIndepForm g (Δ[A] ▷ W ≫ (α_ A A W).hom ≫ A ◁ h ≫ u)
        (W ◁ Δ[A] ≫ (α_ W A A).inv ≫ k ▷ A ≫ v) := by
  obtain ⟨G, hG⟩ : ∃ G, G = g ≫ Δ[W] ≫ W ◁ Δ[W] := ⟨_, rfl⟩
  have x1 : A ◁ (G ▷ A) ≫ Δ[A] ▷ ((W ⊗ (W ⊗ W)) ⊗ A) =
      Δ[A] ▷ (A ⊗ A) ≫ (A ⊗ A) ◁ (G ▷ A) := whisker_exchange _ _
  have x2 : G ▷ A ≫ (W ⊗ (W ⊗ W)) ◁ Δ[A] = A ◁ Δ[A] ≫ G ▷ (A ⊗ A) :=
    (whisker_exchange _ _).symm
  have e : (Δ[A] ▷ W ≫ (α_ A A W).hom ≫ A ◁ h ≫ u) ⊗ₘ
        W ◁ (W ◁ Δ[A] ≫ (α_ W A A).inv ≫ k ▷ A ≫ v) =
      (Δ[A] ▷ W ⊗ₘ W ◁ W ◁ Δ[A]) ≫
        (((α_ A A W).hom ≫ A ◁ h) ⊗ₘ W ◁ ((α_ W A A).inv ≫ k ▷ A)) ≫ (u ⊗ₘ W ◁ v) := by
    simp only [tensorHom_comp_tensorHom, ← whiskerLeft_comp, Category.assoc]
  symm
  calc
    _ = Δ[A] ≫ A ◁ Δ[A] ≫ (A ◁ (G ▷ A) ≫ Δ[A] ▷ ((W ⊗ (W ⊗ W)) ⊗ A)) ≫
          (A ⊗ A) ◁ ((W ⊗ (W ⊗ W)) ◁ Δ[A]) ⊗≫ (A ⊗ (A ⊗ W)) ◁ W ◁ (k ▷ A) ≫
          (A ◁ h) ▷ (W ⊗ (Y₁ ⊗ A)) ≫ u ▷ (W ⊗ (Y₁ ⊗ A)) ≫ X₂ ◁ W ◁ v := by
      unfold condIndepForm
      rw [e, tensorHom_def (Δ[A] ▷ W), tensorHom_def' ((α_ A A W).hom ≫ A ◁ h),
        tensorHom_def u, hG]
      monoidal
    _ = Δ[A] ≫ A ◁ Δ[A] ≫ Δ[A] ▷ (A ⊗ A) ≫
          (A ⊗ A) ◁ (G ▷ A ≫ (W ⊗ (W ⊗ W)) ◁ Δ[A]) ⊗≫ (A ⊗ (A ⊗ W)) ◁ W ◁ (k ▷ A) ≫
          (A ◁ h) ▷ (W ⊗ (Y₁ ⊗ A)) ≫ u ▷ (W ⊗ (Y₁ ⊗ A)) ≫ X₂ ◁ W ◁ v := by
      rw [x1]
      monoidal
    _ = Δ[A] ≫ A ◁ Δ[A] ≫ Δ[A] ▷ (A ⊗ A) ≫ (A ⊗ A) ◁ (A ◁ Δ[A]) ≫
          (A ⊗ A) ◁ (G ▷ (A ⊗ A)) ⊗≫ (A ⊗ (A ⊗ W)) ◁ W ◁ (k ▷ A) ≫
          (A ◁ h) ▷ (W ⊗ (Y₁ ⊗ A)) ≫ u ▷ (W ⊗ (Y₁ ⊗ A)) ≫ X₂ ◁ W ◁ v := by
      rw [x2]
      monoidal
    _ = (Δ[A] ≫ A ◁ Δ[A] ≫ A ◁ (Δ[A] ▷ A) ≫ A ◁ ((A ◁ Δ[A]) ▷ A)) ≫
          A ◁ ((A ◁ (G ▷ A)) ▷ A) ⊗≫ (A ⊗ (A ⊗ W)) ◁ W ◁ (k ▷ A) ≫
          (A ◁ h) ▷ (W ⊗ (Y₁ ⊗ A)) ≫ u ▷ (W ⊗ (Y₁ ⊗ A)) ≫ X₂ ◁ W ◁ v := by
      rw [copy_comp_whiskerLeft_copy_five A]
      monoidal
    _ = _ := by
      unfold condIndepForm
      rw [tensorCompAssoc_hom, tensorHom_def' h, tensorHom_def u, hG]
      monoidal

/-- For `f : A ⟶ X₁ ⊗ (W ⊗ Y₁)` in a copy-discard category `C`, if `f` displays the conditional
independence of `X₁` and `Y₁` given `W` and `A`, then for arbitrary `u : A ⊗ X₁ ⟶ X₂` and
`v : Y₁ ⊗ A ⟶ Y₂` the composite
`Δ[A] ≫ A ◁ Δ[A] ≫ A ◁ (f ▷ A) ≫ (tensorCompAssoc A X₁ W Y₁ A).hom ≫ (u ⊗ₘ W ◁ v) :
A ⟶ X₂ ⊗ (W ⊗ Y₂)`, which copies `A` three times, applies `f` to the middle copy, `u` to the
first copy and `X₁`, and `v` to `Y₁` and the third copy, displays the conditional independence
of `X₂` and `Y₂` given `W` and `A` (Fritz 2020, Prop. 12.18 (c)). -/
theorem DisplaysCondIndep.comp_tensorHom {A X₁ W Y₁ X₂ Y₂ : C}
    {f : A ⟶ X₁ ⊗ (W ⊗ Y₁)} (hf : DisplaysCondIndep f)
    (u : A ⊗ X₁ ⟶ X₂) (v : Y₁ ⊗ A ⟶ Y₂) :
    DisplaysCondIndep
      (Δ[A] ≫ A ◁ Δ[A] ≫ A ◁ (f ▷ A) ≫ (tensorCompAssoc A X₁ W Y₁ A).hom ≫
        (u ⊗ₘ W ◁ v)) := by
  obtain ⟨g, h, k, rfl⟩ := hf
  exact ⟨g, Δ[A] ▷ W ≫ (α_ A A W).hom ≫ A ◁ h ≫ u, W ◁ Δ[A] ≫ (α_ W A A).inv ≫ k ▷ A ≫ v,
    copy_comp_condIndepForm_comp_tensorHom g h k u v⟩

-- WITNESS: none (restates the Deterministic instance of a composite)
/-- For deterministic `f : X ⟶ Y` and `g : Y ⟶ Z` in a copy-discard category `C`, with the two
facts as explicit arguments, `f ≫ g` is deterministic. -/
theorem deterministic_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Deterministic f)
    (hg : Deterministic g) : Deterministic (f ≫ g) := by
  have := hf
  have := hg
  infer_instance

-- WITNESS: none (step of DisplaysCondIndep.tensor; witnessed through it)
/-- For objects `X₁`, `X₂`, `Y₁`, `Y₂` of a copy-discard category `C`, the morphism
`tensorμ X₁ X₂ Y₁ Y₂ : (X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂) ⟶ (X₁ ⊗ Y₁) ⊗ (X₂ ⊗ Y₂)` is deterministic. -/
theorem deterministic_tensorμ (X₁ X₂ Y₁ Y₂ : C) : Deterministic (tensorμ X₁ X₂ Y₁ Y₂) := by
  unfold tensorμ
  exact deterministic_comp inferInstance (deterministic_comp inferInstance
    (deterministic_comp inferInstance (deterministic_comp inferInstance inferInstance)))

-- WITNESS: none (step of DisplaysCondIndep.tensor; witnessed through it)
/-- For a deterministic `s : P ⟶ Q` in a copy-discard category `C`, `s` followed by
`Δ[Q] ≫ Q ◁ Δ[Q] : Q ⟶ Q ⊗ (Q ⊗ Q)` equals `Δ[P] ≫ P ◁ Δ[P]` followed by `s ⊗ₘ (s ⊗ₘ s)`. -/
theorem comp_copy_comp_whiskerLeft_copy {P Q : C} (s : P ⟶ Q) [Deterministic s] :
    s ≫ Δ[Q] ≫ Q ◁ Δ[Q] = Δ[P] ≫ P ◁ Δ[P] ≫ (s ⊗ₘ (s ⊗ₘ s)) := by
  calc
    _ = Δ[P] ≫ (s ⊗ₘ s) ≫ (𝟙 Q ⊗ₘ Δ[Q]) := by
      rw [reassoc_of% (Deterministic.copy_natural s), id_tensorHom]
    _ = Δ[P] ≫ (s ⊗ₘ (s ≫ Δ[Q])) := by
      rw [tensorHom_comp_tensorHom, Category.comp_id]
    _ = Δ[P] ≫ ((𝟙 P ≫ s) ⊗ₘ (Δ[P] ≫ (s ⊗ₘ s))) := by
      rw [Deterministic.copy_natural s, Category.id_comp]
    _ = _ := by
      rw [← tensorHom_comp_tensorHom, id_tensorHom]

-- WITNESS: none (step of DisplaysCondIndep.tensor; witnessed through it)
/-- For objects `B₁`, `B₂` of a copy-discard category `C`, copying `B₁ ⊗ B₂` and then copying
the right copy equals `(Δ[B₁] ≫ B₁ ◁ Δ[B₁]) ⊗ₘ (Δ[B₂] ≫ B₂ ◁ Δ[B₂])` followed by
`(tensorTripleInterchange B₁ B₁ B₁ B₂ B₂ B₂).hom`. -/
theorem copy_tensor_comp_whiskerLeft_copy_tensor (B₁ B₂ : C) :
    @ComonObj.comul C _ _ (B₁ ⊗ B₂) (CopyDiscardCategory.comonObj (B₁ ⊗ B₂)) ≫
        (B₁ ⊗ B₂) ◁ @ComonObj.comul C _ _ (B₁ ⊗ B₂) (CopyDiscardCategory.comonObj (B₁ ⊗ B₂)) =
      ((Δ[B₁] ≫ B₁ ◁ Δ[B₁]) ⊗ₘ (Δ[B₂] ≫ B₂ ◁ Δ[B₂])) ≫
        (tensorTripleInterchange B₁ B₁ B₁ B₂ B₂ B₂).hom := by
  have T : (tensorTripleInterchange B₁ B₁ B₁ B₂ B₂ B₂).hom =
      tensorμ B₁ (B₁ ⊗ B₁) B₂ (B₂ ⊗ B₂) ≫ (B₁ ⊗ B₂) ◁ tensorμ B₁ B₁ B₂ B₂ := rfl
  have e : (B₁ ⊗ B₂) ◁ (Δ[B₁] ⊗ₘ Δ[B₂]) = (𝟙 B₁ ⊗ₘ 𝟙 B₂) ⊗ₘ (Δ[B₁] ⊗ₘ Δ[B₂]) := by
    simp only [id_tensorHom, whiskerLeft_id]
  rw [T, copy_tensor, whiskerLeft_comp, e, Category.assoc, ← tensorμ_natural_assoc,
    tensorHom_comp_tensorHom_assoc]
  simp only [id_tensorHom]

-- WITNESS: none (step of DisplaysCondIndep.tensor; witnessed through it)
/-- For `g₁ : A₁ ⟶ W₁` and `g₂ : A₂ ⟶ W₂` in a copy-discard category `C`, copying `A₁ ⊗ A₂` and
applying `g₁ ⊗ₘ g₂` to the right copy equals `(Δ[A₁] ≫ A₁ ◁ g₁) ⊗ₘ (Δ[A₂] ≫ A₂ ◁ g₂)` followed
by `tensorμ A₁ W₁ A₂ W₂`. -/
theorem copy_tensor_comp_whiskerLeft_tensorHom {A₁ A₂ W₁ W₂ : C} (g₁ : A₁ ⟶ W₁)
    (g₂ : A₂ ⟶ W₂) :
    @ComonObj.comul C _ _ (A₁ ⊗ A₂) (CopyDiscardCategory.comonObj (A₁ ⊗ A₂)) ≫
        (A₁ ⊗ A₂) ◁ (g₁ ⊗ₘ g₂) =
      ((Δ[A₁] ≫ A₁ ◁ g₁) ⊗ₘ (Δ[A₂] ≫ A₂ ◁ g₂)) ≫ tensorμ A₁ W₁ A₂ W₂ := by
  have e : (A₁ ⊗ A₂) ◁ (g₁ ⊗ₘ g₂) = (𝟙 A₁ ⊗ₘ 𝟙 A₂) ⊗ₘ (g₁ ⊗ₘ g₂) := by
    simp only [id_tensorHom, whiskerLeft_id]
  rw [copy_tensor, e, Category.assoc, ← tensorμ_natural, tensorHom_comp_tensorHom_assoc]
  simp only [id_tensorHom]

-- WITNESS: none (step of DisplaysCondIndep.tensor; witnessed through it)
/-- For objects `A₁`, `W₁`, `A₂`, `W₂` of a copy-discard category `C`, `tensorμ A₁ W₁ A₂ W₂`
followed by the second projection of `(A₁ ⊗ A₂) ⊗ (W₁ ⊗ W₂)`, which discards `A₁ ⊗ A₂`, equals
the tensor product of the second projections `ε[A₁] ▷ W₁ ≫ (λ_ W₁).hom` and
`ε[A₂] ▷ W₂ ≫ (λ_ W₂).hom`. -/
theorem tensorμ_comp_snd (A₁ W₁ A₂ W₂ : C) :
    tensorμ A₁ W₁ A₂ W₂ ≫
        @ComonObj.counit C _ _ (A₁ ⊗ A₂) (CopyDiscardCategory.comonObj (A₁ ⊗ A₂)) ▷ (W₁ ⊗ W₂) ≫
        (λ_ (W₁ ⊗ W₂)).hom =
      (ε[A₁] ▷ W₁ ≫ (λ_ W₁).hom) ⊗ₘ (ε[A₂] ▷ W₂ ≫ (λ_ W₂).hom) := by
  have e : @ComonObj.counit C _ _ (A₁ ⊗ A₂) (CopyDiscardCategory.comonObj (A₁ ⊗ A₂)) ▷
        (W₁ ⊗ W₂) =
      ((ε[A₁] ⊗ₘ ε[A₂]) ⊗ₘ (𝟙 W₁ ⊗ₘ 𝟙 W₂)) ≫ (λ_ (𝟙_ C)).hom ▷ (W₁ ⊗ W₂) := by
    rw [discard_tensor]
    simp only [tensorHom_id, id_whiskerRight, comp_whiskerRight]
  rw [e, Category.assoc, ← tensorμ_natural_assoc]
  simp only [tensorHom_id]
  simp only [tensorμ, braiding_tensorUnit_right, tensorHom_def]
  monoidal

-- WITNESS: none (step of DisplaysCondIndep.tensor; witnessed through it)
/-- For `g₁ : A₁ ⟶ W₁`, `h₁ : A₁ ⊗ W₁ ⟶ X₁`, `k₁ : W₁ ⊗ A₁ ⟶ Y₁`, `g₂ : A₂ ⟶ W₂`,
`h₂ : A₂ ⊗ W₂ ⟶ X₂` and `k₂ : W₂ ⊗ A₂ ⟶ Y₂` in a copy-discard category `C`,
`(condIndepForm g₁ h₁ k₁ ⊗ₘ condIndepForm g₂ h₂ k₂) ≫
(tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom :
A₁ ⊗ A₂ ⟶ (X₁ ⊗ X₂) ⊗ ((W₁ ⊗ W₂) ⊗ (Y₁ ⊗ Y₂))` equals the `condIndepForm` of `g₁ ⊗ₘ g₂`,
`tensorδ A₁ W₁ A₂ W₂ ≫ (h₁ ⊗ₘ h₂)` and `(β_ (W₁ ⊗ W₂) (A₁ ⊗ A₂)).hom ≫ tensorδ A₁ W₁ A₂ W₂ ≫
(((β_ A₁ W₁).hom ≫ k₁) ⊗ₘ ((β_ A₂ W₂).hom ≫ k₂))` (Fritz 2020, Prop. 12.18 (a)). -/
theorem condIndepForm_tensorHom_comp_tensorTripleInterchange {A₁ A₂ X₁ W₁ Y₁ X₂ W₂ Y₂ : C}
    (g₁ : A₁ ⟶ W₁) (h₁ : A₁ ⊗ W₁ ⟶ X₁) (k₁ : W₁ ⊗ A₁ ⟶ Y₁) (g₂ : A₂ ⟶ W₂)
    (h₂ : A₂ ⊗ W₂ ⟶ X₂) (k₂ : W₂ ⊗ A₂ ⟶ Y₂) :
    (condIndepForm g₁ h₁ k₁ ⊗ₘ condIndepForm g₂ h₂ k₂) ≫
        (tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom =
      condIndepForm (g₁ ⊗ₘ g₂) (tensorδ A₁ W₁ A₂ W₂ ≫ (h₁ ⊗ₘ h₂))
        ((β_ (W₁ ⊗ W₂) (A₁ ⊗ A₂)).hom ≫ tensorδ A₁ W₁ A₂ W₂ ≫
          (((β_ A₁ W₁).hom ≫ k₁) ⊗ₘ ((β_ A₂ W₂).hom ≫ k₂))) := by
  have := deterministic_tensorμ A₁ W₁ A₂ W₂
  rw [condIndepForm_eq_copy_tensor g₁ h₁ k₁, condIndepForm_eq_copy_tensor g₂ h₂ k₂,
    condIndepForm_eq_copy_tensor (g₁ ⊗ₘ g₂)]
  symm
  calc
    _ = ((Δ[A₁] ≫ A₁ ◁ g₁) ⊗ₘ (Δ[A₂] ≫ A₂ ◁ g₂)) ≫
          (tensorμ A₁ W₁ A₂ W₂ ≫
            @ComonObj.comul C _ _ ((A₁ ⊗ A₂) ⊗ (W₁ ⊗ W₂))
              (CopyDiscardCategory.comonObj ((A₁ ⊗ A₂) ⊗ (W₁ ⊗ W₂))) ≫
            ((A₁ ⊗ A₂) ⊗ (W₁ ⊗ W₂)) ◁
              @ComonObj.comul C _ _ ((A₁ ⊗ A₂) ⊗ (W₁ ⊗ W₂))
                (CopyDiscardCategory.comonObj ((A₁ ⊗ A₂) ⊗ (W₁ ⊗ W₂)))) ≫
          ((tensorδ A₁ W₁ A₂ W₂ ≫ (h₁ ⊗ₘ h₂)) ⊗ₘ
            ((@ComonObj.counit C _ _ (A₁ ⊗ A₂) (CopyDiscardCategory.comonObj (A₁ ⊗ A₂)) ▷
                  (W₁ ⊗ W₂) ≫ (λ_ (W₁ ⊗ W₂)).hom) ⊗ₘ
              ((β_ (A₁ ⊗ A₂) (W₁ ⊗ W₂)).hom ≫ (β_ (W₁ ⊗ W₂) (A₁ ⊗ A₂)).hom ≫
                tensorδ A₁ W₁ A₂ W₂ ≫ (((β_ A₁ W₁).hom ≫ k₁) ⊗ₘ ((β_ A₂ W₂).hom ≫ k₂))))) := by
      rw [reassoc_of% copy_tensor_comp_whiskerLeft_tensorHom g₁ g₂]
      simp only [Category.assoc]
    _ = ((Δ[A₁] ≫ A₁ ◁ g₁) ⊗ₘ (Δ[A₂] ≫ A₂ ◁ g₂)) ≫
          (@ComonObj.comul C _ _ ((A₁ ⊗ W₁) ⊗ (A₂ ⊗ W₂))
              (CopyDiscardCategory.comonObj ((A₁ ⊗ W₁) ⊗ (A₂ ⊗ W₂))) ≫
            ((A₁ ⊗ W₁) ⊗ (A₂ ⊗ W₂)) ◁
              @ComonObj.comul C _ _ ((A₁ ⊗ W₁) ⊗ (A₂ ⊗ W₂))
                (CopyDiscardCategory.comonObj ((A₁ ⊗ W₁) ⊗ (A₂ ⊗ W₂)))) ≫
          ((tensorμ A₁ W₁ A₂ W₂ ≫ tensorδ A₁ W₁ A₂ W₂ ≫ (h₁ ⊗ₘ h₂)) ⊗ₘ
            ((tensorμ A₁ W₁ A₂ W₂ ≫
                @ComonObj.counit C _ _ (A₁ ⊗ A₂) (CopyDiscardCategory.comonObj (A₁ ⊗ A₂)) ▷
                  (W₁ ⊗ W₂) ≫ (λ_ (W₁ ⊗ W₂)).hom) ⊗ₘ
              (tensorμ A₁ W₁ A₂ W₂ ≫ (β_ (A₁ ⊗ A₂) (W₁ ⊗ W₂)).hom ≫
                (β_ (W₁ ⊗ W₂) (A₁ ⊗ A₂)).hom ≫ tensorδ A₁ W₁ A₂ W₂ ≫
                (((β_ A₁ W₁).hom ≫ k₁) ⊗ₘ ((β_ A₂ W₂).hom ≫ k₂))))) := by
      rw [comp_copy_comp_whiskerLeft_copy (tensorμ A₁ W₁ A₂ W₂)]
      simp only [Category.assoc, tensorHom_comp_tensorHom]
    _ = ((Δ[A₁] ≫ A₁ ◁ g₁) ⊗ₘ (Δ[A₂] ≫ A₂ ◁ g₂)) ≫
          (@ComonObj.comul C _ _ ((A₁ ⊗ W₁) ⊗ (A₂ ⊗ W₂))
              (CopyDiscardCategory.comonObj ((A₁ ⊗ W₁) ⊗ (A₂ ⊗ W₂))) ≫
            ((A₁ ⊗ W₁) ⊗ (A₂ ⊗ W₂)) ◁
              @ComonObj.comul C _ _ ((A₁ ⊗ W₁) ⊗ (A₂ ⊗ W₂))
                (CopyDiscardCategory.comonObj ((A₁ ⊗ W₁) ⊗ (A₂ ⊗ W₂)))) ≫
          ((h₁ ⊗ₘ h₂) ⊗ₘ
            (((ε[A₁] ▷ W₁ ≫ (λ_ W₁).hom) ⊗ₘ (ε[A₂] ▷ W₂ ≫ (λ_ W₂).hom)) ⊗ₘ
              (((β_ A₁ W₁).hom ≫ k₁) ⊗ₘ ((β_ A₂ W₂).hom ≫ k₂)))) := by
      rw [tensorμ_comp_snd, tensorμ_tensorδ_assoc, SymmetricCategory.symmetry_assoc,
        tensorμ_tensorδ_assoc]
    _ = _ := by
      rw [copy_tensor_comp_whiskerLeft_copy_tensor, Category.assoc,
        ← tensorTripleInterchange_hom_natural]
      simp only [tensorHom_comp_tensorHom_assoc, Category.assoc]

/-- For `f₁ : A₁ ⟶ X₁ ⊗ (W₁ ⊗ Y₁)` and `f₂ : A₂ ⟶ X₂ ⊗ (W₂ ⊗ Y₂)` in a copy-discard category
`C`, if `f₁` displays the conditional independence of `X₁` and `Y₁` given `W₁` and `A₁`, and
`f₂` displays the conditional independence of `X₂` and `Y₂` given `W₂` and `A₂`, then
`(f₁ ⊗ₘ f₂) ≫ (tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom :
A₁ ⊗ A₂ ⟶ (X₁ ⊗ X₂) ⊗ ((W₁ ⊗ W₂) ⊗ (Y₁ ⊗ Y₂))` displays the conditional independence of
`X₁ ⊗ X₂` and `Y₁ ⊗ Y₂` given `W₁ ⊗ W₂` and `A₁ ⊗ A₂` (Fritz 2020, Prop. 12.18 (a)). -/
theorem DisplaysCondIndep.tensor {A₁ A₂ X₁ W₁ Y₁ X₂ W₂ Y₂ : C}
    {f₁ : A₁ ⟶ X₁ ⊗ (W₁ ⊗ Y₁)} {f₂ : A₂ ⟶ X₂ ⊗ (W₂ ⊗ Y₂)}
    (hf₁ : DisplaysCondIndep f₁) (hf₂ : DisplaysCondIndep f₂) :
    DisplaysCondIndep
      ((f₁ ⊗ₘ f₂) ≫ (tensorTripleInterchange X₁ W₁ Y₁ X₂ W₂ Y₂).hom) := by
  obtain ⟨g₁, h₁, k₁, rfl⟩ := hf₁
  obtain ⟨g₂, h₂, k₂, rfl⟩ := hf₂
  exact ⟨g₁ ⊗ₘ g₂, tensorδ A₁ W₁ A₂ W₂ ≫ (h₁ ⊗ₘ h₂),
    (β_ (W₁ ⊗ W₂) (A₁ ⊗ A₂)).hom ≫ tensorδ A₁ W₁ A₂ W₂ ≫
      (((β_ A₁ W₁).hom ≫ k₁) ⊗ₘ ((β_ A₂ W₂).hom ≫ k₂)),
    condIndepForm_tensorHom_comp_tensorTripleInterchange g₁ h₁ k₁ g₂ h₂ k₂⟩

-- WITNESS: none (step of DisplaysCondIndep.comp, IsConditional.condIndepForm)
/-- For `g : A ⟶ W`, `h : A ⊗ W ⟶ X` and `k : W ⊗ A ⟶ Y` in a copy-discard category `C`,
`condIndepForm g h k` equals `copyPair (𝟙 A) g : A ⟶ A ⊗ W` followed by
`copyPair h (copyPair (ε[A] ▷ W ≫ (λ_ W).hom) ((β_ A W).hom ≫ k)) : A ⊗ W ⟶ X ⊗ (W ⊗ Y)`
(Fritz 2020, Def. 12.16). -/
theorem condIndepForm_eq_copyPair {A X W Y : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X) (k : W ⊗ A ⟶ Y) :
    condIndepForm g h k = copyPair (𝟙 A) g ≫
      copyPair h (copyPair (ε[A] ▷ W ≫ (λ_ W).hom) ((β_ A W).hom ≫ k)) := by
  have e : h ⊗ₘ (@ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        ((ε[A] ▷ W ≫ (λ_ W).hom) ⊗ₘ ((β_ A W).hom ≫ k))) =
      (A ⊗ W) ◁ @ComonObj.comul C _ _ (A ⊗ W) (CopyDiscardCategory.comonObj (A ⊗ W)) ≫
        (h ⊗ₘ ((ε[A] ▷ W ≫ (λ_ W).hom) ⊗ₘ ((β_ A W).hom ≫ k))) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  rw [condIndepForm_eq_copy_tensor]
  unfold copyPair
  rw [id_tensorHom, Category.assoc, e]

-- WITNESS: none (step of DisplaysCondIndep.comp; witnessed through it)
/-- For `g₂ : V ⟶ W`, `h₂ : V ⊗ W ⟶ X₂` and `k₂ : W ⊗ V ⟶ Y₂` in a copy-discard category `C`,
`copyPair (𝟙 V) (condIndepForm g₂ h₂ k₂) ≫ (tensorLeftComm V X₂ (W ⊗ Y₂)).hom ≫
X₂ ◁ (α_ V W Y₂).inv : V ⟶ X₂ ⊗ ((V ⊗ W) ⊗ Y₂)` equals `copyPair (𝟙 V) g₂` followed by
`copyPair h₂ (copyPair (𝟙 (V ⊗ W)) ((β_ V W).hom ≫ k₂))`. -/
theorem copyPair_id_condIndepForm_comp_tensorLeftComm {V X₂ W Y₂ : C} (g₂ : V ⟶ W)
    (h₂ : V ⊗ W ⟶ X₂) (k₂ : W ⊗ V ⟶ Y₂) :
    copyPair (𝟙 V) (condIndepForm g₂ h₂ k₂) ≫ (tensorLeftComm V X₂ (W ⊗ Y₂)).hom ≫
        X₂ ◁ (α_ V W Y₂).inv =
      copyPair (𝟙 V) g₂ ≫ copyPair h₂ (copyPair (𝟙 (V ⊗ W)) ((β_ V W).hom ≫ k₂)) := by
  rw [condIndepForm_eq_copyPair,
    ← comp_copyPair_of_peel (copyPair_id_comp_copy_comp_fst g₂) (𝟙 V), Category.comp_id,
    Category.assoc, copyPair_comp_tensorLeftComm_assoc, copyPair_comp_whiskerLeft,
    copyPair_assoc_inv, copyPair_fst_snd]

-- WITNESS: none (step of DisplaysCondIndep.comp; witnessed through it)
/-- For `g₁ : A ⟶ V`, `h₁ : A ⊗ V ⟶ X₁`, `k₁ : V ⊗ A ⟶ Y₁`, `g₂ : V ⟶ W`, `h₂ : V ⊗ W ⟶ X₂` and
`k₂ : W ⊗ V ⟶ Y₂` in a copy-discard category `C`,
`condIndepForm g₁ h₁ k₁ ≫ X₁ ◁ ((Δ[V] ≫ V ◁ condIndepForm g₂ h₂ k₂) ▷ Y₁) ≫
(tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom : A ⟶ (X₁ ⊗ X₂) ⊗ ((V ⊗ W) ⊗ (Y₂ ⊗ Y₁))` equals the
`condIndepForm` of `g₁ ≫ copyPair (𝟙 V) g₂ : A ⟶ V ⊗ W`, a pairing
`A ⊗ (V ⊗ W) ⟶ X₁ ⊗ X₂` of `h₁` and `h₂`, and the braiding followed by a pairing
`A ⊗ (V ⊗ W) ⟶ Y₂ ⊗ Y₁` of `k₂` and `k₁` (Fritz 2020, Prop. 12.18 (b)). -/
theorem condIndepForm_comp_copy_condIndepForm {A X₁ V Y₁ X₂ W Y₂ : C} (g₁ : A ⟶ V)
    (h₁ : A ⊗ V ⟶ X₁) (k₁ : V ⊗ A ⟶ Y₁) (g₂ : V ⟶ W) (h₂ : V ⊗ W ⟶ X₂) (k₂ : W ⊗ V ⟶ Y₂) :
    condIndepForm g₁ h₁ k₁ ≫ X₁ ◁ ((Δ[V] ≫ V ◁ condIndepForm g₂ h₂ k₂) ▷ Y₁) ≫
        (tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom =
      condIndepForm (g₁ ≫ copyPair (𝟙 V) g₂)
        (copyPair (A ◁ (V ◁ ε[W] ≫ (ρ_ V).hom) ≫ h₁)
          (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ h₂))
        ((β_ (V ⊗ W) A).hom ≫
          copyPair (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ (β_ V W).hom ≫ k₂)
            (A ◁ (V ◁ ε[W] ≫ (ρ_ V).hom) ≫ (β_ A V).hom ≫ k₁)) := by
  have hj := whiskerLeft_comp_copy_tensor_of_peel A (copyPair_id_comp_copy_comp_fst g₂)
  have hπ : A ◁ copyPair (𝟙 V) g₂ ≫ ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom =
      ε[A] ▷ V ≫ (λ_ V).hom ≫ copyPair (𝟙 V) g₂ := by
    rw [whisker_exchange_assoc, leftUnitor_naturality]
  have hd : Deterministic (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom) :=
    deterministic_comp inferInstance inferInstance
  have hdet : copyPair (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ h₂)
        (copyPair (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom)
          (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ (β_ V W).hom ≫ k₂)) =
      (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom) ≫
        copyPair h₂ (copyPair (𝟙 (V ⊗ W)) ((β_ V W).hom ≫ k₂)) := by
    rw [comp_copyPair, comp_copyPair]
    simp only [Category.assoc, Category.comp_id]
  have hR : X₁ ◁ ((Δ[V] ≫ V ◁ condIndepForm g₂ h₂ k₂) ▷ Y₁) ≫
        (tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom =
      (𝟙 X₁ ⊗ₘ ((copyPair (𝟙 V) (condIndepForm g₂ h₂ k₂) ≫
          (tensorLeftComm V X₂ (W ⊗ Y₂)).hom ≫ X₂ ◁ (α_ V W Y₂).inv) ⊗ₘ 𝟙 Y₁)) ≫
        X₁ ◁ (α_ X₂ ((V ⊗ W) ⊗ Y₂) Y₁).hom ≫ (α_ X₁ X₂ (((V ⊗ W) ⊗ Y₂) ⊗ Y₁)).inv ≫
        (X₁ ⊗ X₂) ◁ (α_ (V ⊗ W) Y₂ Y₁).hom := by
    unfold copyPair
    rw [tensorCompReorder_hom, tensorLeftComm_hom, id_tensorHom, id_tensorHom, tensorHom_id]
    monoidal
  calc
    _ = copyPair (𝟙 A) g₁ ≫ copyPair h₁ (copyPair (ε[A] ▷ V ≫ (λ_ V).hom ≫
            copyPair (𝟙 V) g₂ ≫ copyPair h₂ (copyPair (𝟙 (V ⊗ W)) ((β_ V W).hom ≫ k₂)))
          ((β_ A V).hom ≫ k₁)) ≫
          X₁ ◁ (α_ X₂ ((V ⊗ W) ⊗ Y₂) Y₁).hom ≫ (α_ X₁ X₂ (((V ⊗ W) ⊗ Y₂) ⊗ Y₁)).inv ≫
          (X₁ ⊗ X₂) ◁ (α_ (V ⊗ W) Y₂ Y₁).hom := by
      rw [hR, copyPair_id_condIndepForm_comp_tensorLeftComm,
        condIndepForm_eq_copyPair g₁ h₁ k₁, Category.assoc, copyPair_comp_tensorHom_assoc,
        copyPair_comp_tensorHom, Category.comp_id, Category.comp_id]
      simp only [Category.assoc]
    _ = _ := by
      rw [condIndepForm_eq_copyPair (g₁ ≫ copyPair (𝟙 V) g₂), SymmetricCategory.symmetry_assoc,
        ← copyPair_reassoc, hdet, ← copyPair_comp_whiskerLeft (𝟙 A) g₁ (copyPair (𝟙 V) g₂),
        Category.assoc, comp_copyPair_of_peel_assoc hj h₁, comp_copyPair_of_peel' hj]
      simp only [Category.assoc]
      rw [reassoc_of% hπ]

/-- For `f : A ⟶ X₁ ⊗ (V ⊗ Y₁)` and `g : V ⟶ X₂ ⊗ (W ⊗ Y₂)` in a copy-discard category `C`, if
`f` displays the conditional independence of `X₁` and `Y₁` given `V` and `A`, and `g` displays
the conditional independence of `X₂` and `Y₂` given `W` and `V`, then
`f ≫ X₁ ◁ ((Δ[V] ≫ V ◁ g) ▷ Y₁) ≫ (tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom :
A ⟶ (X₁ ⊗ X₂) ⊗ ((V ⊗ W) ⊗ (Y₂ ⊗ Y₁))`, which copies the output `V` of `f` and applies `g` to
the right copy, displays the conditional independence of `X₁ ⊗ X₂` and `Y₂ ⊗ Y₁` given `V ⊗ W`
and `A` (Fritz 2020, Prop. 12.18 (b)). -/
theorem DisplaysCondIndep.comp {A X₁ V Y₁ X₂ W Y₂ : C}
    {f : A ⟶ X₁ ⊗ (V ⊗ Y₁)} {g : V ⟶ X₂ ⊗ (W ⊗ Y₂)}
    (hf : DisplaysCondIndep f) (hg : DisplaysCondIndep g) :
    DisplaysCondIndep
      (f ≫ X₁ ◁ ((Δ[V] ≫ V ◁ g) ▷ Y₁) ≫ (tensorCompReorder X₁ V X₂ W Y₂ Y₁).hom) := by
  obtain ⟨g₁, h₁, k₁, rfl⟩ := hf
  obtain ⟨g₂, h₂, k₂, rfl⟩ := hg
  exact ⟨g₁ ≫ copyPair (𝟙 V) g₂,
    copyPair (A ◁ (V ◁ ε[W] ≫ (ρ_ V).hom) ≫ h₁) (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ h₂),
    (β_ (V ⊗ W) A).hom ≫
      copyPair (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ (β_ V W).hom ≫ k₂)
        (A ◁ (V ◁ ε[W] ≫ (ρ_ V).hom) ≫ (β_ A V).hom ≫ k₁),
    condIndepForm_comp_copy_condIndepForm g₁ h₁ k₁ g₂ h₂ k₂⟩

-- WITNESS: none (step of IsConditional.condIndepForm; witnessed through it)
/-- For `f : A ⟶ X ⊗ Y` and `c : X ⊗ A ⟶ Y` in a copy-discard category `C`, `c` is a
conditional of `f` on `X` if and only if `f` equals `copyPair (marginalFst f) (𝟙 A) : A ⟶ X ⊗ A`
followed by `copyPair (X ◁ ε[A] ≫ (ρ_ X).hom) c : X ⊗ A ⟶ X ⊗ Y` (Fritz 2020, Def. 11.5). -/
theorem isConditional_iff_copyPair {A X Y : C} (f : A ⟶ X ⊗ Y) (c : X ⊗ A ⟶ Y) :
    IsConditional f c ↔
      f = copyPair (marginalFst f) (𝟙 A) ≫ copyPair (X ◁ ε[A] ≫ (ρ_ X).hom) c := by
  have e : copyPair (marginalFst f) (𝟙 A) ≫ copyPair (X ◁ ε[A] ≫ (ρ_ X).hom) c =
      Δ[A] ≫ (marginalFst f ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ c) := by
    unfold copyPair
    rw [tensorHom_id, tensorHom_def, reassoc_of% copy_comp_fst_whiskerRight X A, Category.assoc]
  unfold IsConditional
  rw [e]

-- WITNESS: none (step of IsConditional.condIndepForm; witnessed through it)
/-- For objects `A`, `V` of a copy-discard category `C`, the braiding `(β_ A V).hom` followed
by the second projection `ε[V] ▷ A ≫ (λ_ A).hom` of `V ⊗ A` equals the first projection
`A ◁ ε[V] ≫ (ρ_ A).hom` of `A ⊗ V`. -/
theorem braiding_comp_snd (A V : C) :
    (β_ A V).hom ≫ ε[V] ▷ A ≫ (λ_ A).hom = A ◁ ε[V] ≫ (ρ_ A).hom := by
  rw [← BraidedCategory.braiding_naturality_right_assoc, braiding_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

-- WITNESS: none (step of IsConditional.condIndepForm; witnessed through it)
/-- For `m : A ⟶ V`, `x : A ⟶ P` and `y : V ⊗ A ⟶ Q` in a copy-discard category `C`,
`copyPair m (𝟙 A)` followed by the pairing of `(ε[V] ▷ A ≫ (λ_ A).hom) ≫ x`, the second
projection of `V ⊗ A` and then `x`, with `y` equals `copyPair x (copyPair m (𝟙 A) ≫ y)`. -/
theorem copyPair_id_right_comp_copyPair {A V P Q : C} (m : A ⟶ V) (x : A ⟶ P)
    (y : V ⊗ A ⟶ Q) :
    copyPair m (𝟙 A) ≫ copyPair ((ε[V] ▷ A ≫ (λ_ A).hom) ≫ x) y =
      copyPair x (copyPair m (𝟙 A) ≫ y) := by
  calc
    _ = copyPair (𝟙 A) m ≫
          copyPair (((β_ A V).hom ≫ ε[V] ▷ A ≫ (λ_ A).hom) ≫ x) ((β_ A V).hom ≫ y) := by
      rw [← copyPair_comp_braiding (𝟙 A) m, Category.assoc, comp_copyPair]
      simp only [Category.assoc]
    _ = copyPair (𝟙 A) m ≫
          copyPair ((A ◁ ε[V] ≫ (ρ_ A).hom) ≫ x) ((β_ A V).hom ≫ y) := by
      rw [braiding_comp_snd]
    _ = copyPair x (copyPair (𝟙 A) m ≫ (β_ A V).hom ≫ y) :=
      comp_copyPair_of_peel (copyPair_id_comp_copy_comp_fst m) x _
    _ = _ := by
      rw [← copyPair_comp_braiding (𝟙 A) m, Category.assoc]

-- WITNESS: none (step of IsConditional.condIndepForm; witnessed through it)
/-- For `m : A ⟶ V` and `g' : V ⊗ A ⟶ W` in a copy-discard category `C`, the pairing of `𝟙 A`
with `copyPair m (𝟙 A) ≫ copyPair (V ◁ ε[A] ≫ (ρ_ V).hom) g' : A ⟶ V ⊗ W`, followed by
`(α_ A V W).inv ≫ (β_ A V).hom ▷ W`, equals `copyPair m (𝟙 A)` followed by
`copyPair (𝟙 (V ⊗ A)) g' : V ⊗ A ⟶ (V ⊗ A) ⊗ W`. -/
theorem copyPair_id_copyPair_comp {A V W : C} (m : A ⟶ V) (g' : V ⊗ A ⟶ W) :
    copyPair (𝟙 A) (copyPair m (𝟙 A) ≫ copyPair (V ◁ ε[A] ≫ (ρ_ V).hom) g') ≫
        (α_ A V W).inv ≫ (β_ A V).hom ▷ W =
      copyPair m (𝟙 A) ≫ copyPair (𝟙 (V ⊗ A)) g' := by
  rw [← copyPair_id_right_comp_copyPair m (𝟙 A), Category.comp_id, Category.assoc,
    copyPair_assoc_inv_assoc, copyPair_comp_whiskerRight, copyPair_comp_braiding,
    copyPair_fst_snd]

-- WITNESS: none (step of IsConditional.condIndepForm; witnessed through it)
/-- For `g : A ⟶ V ⊗ W`, `h : A ⊗ (V ⊗ W) ⟶ X` and `k : (V ⊗ W) ⊗ A ⟶ Y` in a copy-discard
category `C`, `condIndepForm g h k ≫ (tensorCondReorder X V W Y).hom : A ⟶ V ⊗ (X ⊗ (W ⊗ Y))`
equals `copyPair (𝟙 A) g : A ⟶ A ⊗ (V ⊗ W)` followed by the pairing of the projection of
`A ⊗ (V ⊗ W)` to `V` with the pairing of `h`, the projection to `W`, and
`(β_ A (V ⊗ W)).hom ≫ k`. -/
theorem condIndepForm_comp_tensorCondReorder_eq_copyPair {A X V W Y : C} (g : A ⟶ V ⊗ W)
    (h : A ⊗ (V ⊗ W) ⟶ X) (k : (V ⊗ W) ⊗ A ⟶ Y) :
    condIndepForm g h k ≫ (tensorCondReorder X V W Y).hom =
      copyPair (𝟙 A) g ≫
        copyPair (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ V ◁ ε[W] ≫ (ρ_ V).hom)
          (copyPair h
            (copyPair (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ ε[V] ▷ W ≫ (λ_ W).hom)
              ((β_ A (V ⊗ W)).hom ≫ k))) := by
  have hd : Deterministic (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom) :=
    deterministic_comp inferInstance inferInstance
  have hπZ : ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom =
      copyPair (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ V ◁ ε[W] ≫ (ρ_ V).hom)
        (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ ε[V] ▷ W ≫ (λ_ W).hom) := by
    have h1 := comp_copyPair (ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom) (V ◁ ε[W] ≫ (ρ_ V).hom)
      (ε[V] ▷ W ≫ (λ_ W).hom)
    rw [copyPair_fst_snd, Category.comp_id] at h1
    simpa only [Category.assoc] using h1
  have hr : (tensorCondReorder X V W Y).hom =
      X ◁ (α_ V W Y).hom ≫ (tensorLeftComm X V (W ⊗ Y)).hom := rfl
  rw [condIndepForm_eq_copyPair g h k, hr, Category.assoc (copyPair (𝟙 A) g),
    copyPair_comp_whiskerLeft_assoc, hπZ, copyPair_assoc, copyPair_comp_tensorLeftComm]

-- WITNESS: none (step of IsConditional.condIndepForm; witnessed through it)
/-- For `m : A ⟶ V`, `g' : V ⊗ A ⟶ W`, `h : A ⊗ (V ⊗ W) ⟶ X` and `k : (V ⊗ W) ⊗ A ⟶ Y` in a
copy-discard category `C`, the `condIndepForm` of
`copyPair m (𝟙 A) ≫ copyPair (V ◁ ε[A] ≫ (ρ_ V).hom) g' : A ⟶ V ⊗ W`, `h` and `k`, followed by
`(tensorCondReorder X V W Y).hom`, equals `copyPair m (𝟙 A) : A ⟶ V ⊗ A` followed by the
pairing of the first projection `V ◁ ε[A] ≫ (ρ_ V).hom` with
`condIndepForm g' (((β_ V A).hom ▷ W ≫ (α_ A V W).hom) ≫ h)
(((α_ W V A).inv ≫ (β_ W V).hom ▷ A) ≫ k) : V ⊗ A ⟶ X ⊗ (W ⊗ Y)` (Fritz 2020,
Prop. 12.18 (d)). -/
theorem condIndepForm_comp_tensorCondReorder {A X V W Y : C} (m : A ⟶ V) (g' : V ⊗ A ⟶ W)
    (h : A ⊗ (V ⊗ W) ⟶ X) (k : (V ⊗ W) ⊗ A ⟶ Y) :
    condIndepForm (copyPair m (𝟙 A) ≫ copyPair (V ◁ ε[A] ≫ (ρ_ V).hom) g') h k ≫
        (tensorCondReorder X V W Y).hom =
      copyPair m (𝟙 A) ≫ copyPair (V ◁ ε[A] ≫ (ρ_ V).hom)
        (condIndepForm g' (((β_ V A).hom ▷ W ≫ (α_ A V W).hom) ≫ h)
          (((α_ W V A).inv ≫ (β_ W V).hom ▷ A) ≫ k)) := by
  obtain ⟨g, hg⟩ : ∃ g, g = copyPair m (𝟙 A) ≫ copyPair (V ◁ ε[A] ≫ (ρ_ V).hom) g' := ⟨_, rfl⟩
  have hD : copyPair (𝟙 A) g ≫ (α_ A V W).inv ≫ (β_ A V).hom ▷ W =
      copyPair m (𝟙 A) ≫ copyPair (𝟙 (V ⊗ A)) g' := by
    rw [hg]
    exact copyPair_id_copyPair_comp m g'
  have hD' : ∀ {T : C} (t : (V ⊗ A) ⊗ W ⟶ T),
      copyPair m (𝟙 A) ≫ copyPair (𝟙 (V ⊗ A)) g' ≫ t =
        copyPair (𝟙 A) g ≫ ((α_ A V W).inv ≫ (β_ A V).hom ▷ W) ≫ t := fun t => by
    rw [← Category.assoc (copyPair m (𝟙 A)) (copyPair (𝟙 (V ⊗ A)) g') t, ← hD, Category.assoc]
  have hσ : Deterministic ((α_ A V W).inv ≫ (β_ A V).hom ▷ W) :=
    deterministic_comp inferInstance inferInstance
  have i1 : ((α_ A V W).inv ≫ (β_ A V).hom ▷ W) ≫ ((β_ V A).hom ▷ W ≫ (α_ A V W).hom) ≫ h =
      h := by
    simp only [Category.assoc]
    rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry, id_whiskerRight,
      Category.id_comp, Iso.inv_hom_id_assoc]
  have i2 : ((α_ A V W).inv ≫ (β_ A V).hom ▷ W) ≫ (β_ (V ⊗ A) W).hom ≫
        ((α_ W V A).inv ≫ (β_ W V).hom ▷ A) ≫ k = (β_ A (V ⊗ W)).hom ≫ k := by
    rw [BraidedCategory.braiding_tensor_left_hom, BraidedCategory.braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry, id_whiskerRight,
      Category.id_comp]
  have i3 : ((α_ A V W).inv ≫ (β_ A V).hom ▷ W) ≫
        @ComonObj.counit C _ _ (V ⊗ A) (CopyDiscardCategory.comonObj (V ⊗ A)) ▷ W ≫
        (λ_ W).hom =
      ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ ε[V] ▷ W ≫ (λ_ W).hom := by
    have hb : (β_ A V).hom ≫
          @ComonObj.counit C _ _ (V ⊗ A) (CopyDiscardCategory.comonObj (V ⊗ A)) =
        @ComonObj.counit C _ _ (A ⊗ V) (CopyDiscardCategory.comonObj (A ⊗ V)) :=
      Deterministic.discard_natural _
    simp only [Category.assoc]
    rw [← comp_whiskerRight_assoc, hb, discard_tensor, tensorHom_def]
    monoidal
  have i4 : ((α_ A V W).inv ≫ (β_ A V).hom ▷ W) ≫
        ((V ⊗ A) ◁ ε[W] ≫ (ρ_ (V ⊗ A)).hom) ≫ V ◁ ε[A] ≫ (ρ_ V).hom =
      ε[A] ▷ (V ⊗ W) ≫ (λ_ (V ⊗ W)).hom ≫ V ◁ ε[W] ≫ (ρ_ V).hom := by
    have P' : (β_ A V).hom ≫ V ◁ ε[A] ≫ (ρ_ V).hom = ε[A] ▷ V ≫ (λ_ V).hom := by
      rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_tensorUnit_left]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    calc
      _ = (α_ A V W).inv ≫ ((A ⊗ V) ◁ ε[W] ≫ (ρ_ (A ⊗ V)).hom) ≫ (β_ A V).hom ≫
            V ◁ ε[A] ≫ (ρ_ V).hom := by
        simp only [Category.assoc]
        rw [← whisker_exchange_assoc, rightUnitor_naturality_assoc]
      _ = A ◁ (V ◁ ε[W] ≫ (ρ_ V).hom) ≫ ε[A] ▷ V ≫ (λ_ V).hom := by
        rw [P']
        monoidal
      _ = _ := by
        rw [whisker_exchange_assoc, leftUnitor_naturality]
  rw [← hg, condIndepForm_comp_tensorCondReorder_eq_copyPair, condIndepForm_eq_copyPair g',
    ← comp_copyPair_of_peel (copyPair_id_comp_copy_comp_fst g') (V ◁ ε[A] ≫ (ρ_ V).hom), hD',
    comp_copyPair ((α_ A V W).inv ≫ (β_ A V).hom ▷ W),
    comp_copyPair ((α_ A V W).inv ≫ (β_ A V).hom ▷ W),
    comp_copyPair ((α_ A V W).inv ≫ (β_ A V).hom ▷ W), i4, i1, i3, i2]

-- WITNESS: none (step of IsConditional.condIndepForm; witnessed through it)
/-- For `x : Z ⟶ P` in a copy-discard category `C`,
`copyPair x ε[Z] ≫ (ρ_ P).hom = x`. -/
theorem copyPair_discard_comp_rightUnitor {Z P : C} (x : Z ⟶ P) :
    copyPair x ε[Z] ≫ (ρ_ P).hom = x := by
  unfold copyPair
  rw [comul_counit_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

-- WITNESS: none (step of IsConditional.condIndepForm; witnessed through it)
/-- For `g : A ⟶ W` in a copy-discard category `C`, `copyPair (𝟙 A) g : A ⟶ A ⊗ W` followed by
the second projection `ε[A] ▷ W ≫ (λ_ W).hom` equals `g`. -/
@[reassoc]
theorem copyPair_id_comp_snd {A W : C} (g : A ⟶ W) :
    copyPair (𝟙 A) g ≫ ε[A] ▷ W ≫ (λ_ W).hom = g := by
  rw [copyPair_comp_whiskerRight_assoc, Category.id_comp]
  unfold copyPair
  rw [counit_comul_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CopyDiscardCategory

namespace MarkovCategory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

-- WITNESS: none (step of IsConditional.condIndepForm; witnessed through it)
/-- For `g : A ⟶ V ⊗ W`, `h : A ⊗ (V ⊗ W) ⟶ X` and `k : (V ⊗ W) ⊗ A ⟶ Y` in a Markov category
`C`, the first marginal of
`condIndepForm g h k ≫ (tensorCondReorder X V W Y).hom : A ⟶ V ⊗ (X ⊗ (W ⊗ Y))` equals the
first marginal of `g`. -/
theorem marginalFst_condIndepForm_comp_tensorCondReorder {A X V W Y : C} (g : A ⟶ V ⊗ W)
    (h : A ⊗ (V ⊗ W) ⟶ X) (k : (V ⊗ W) ⊗ A ⟶ Y) :
    marginalFst (condIndepForm g h k ≫ (tensorCondReorder X V W Y).hom) = marginalFst g := by
  rw [condIndepForm_comp_tensorCondReorder_eq_copyPair]
  unfold marginalFst
  simp only [Category.assoc]
  rw [copyPair_comp_whiskerLeft_assoc, MarkovCategory.discard_natural,
    copyPair_discard_comp_rightUnitor, copyPair_id_comp_snd_assoc]

end MarkovCategory

namespace CopyDiscardCategory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

/-- For `g : A ⟶ V ⊗ W`, `h : A ⊗ (V ⊗ W) ⟶ X` and `k : (V ⊗ W) ⊗ A ⟶ Y` in a Markov category
`C`, if `g' : V ⊗ A ⟶ W` is a conditional of `g` on `V`, then
`condIndepForm g' (((β_ V A).hom ▷ W ≫ (α_ A V W).hom) ≫ h)
(((α_ W V A).inv ≫ (β_ W V).hom ▷ A) ≫ k) : V ⊗ A ⟶ X ⊗ (W ⊗ Y)` is a conditional on `V` of
`condIndepForm g h k ≫ (tensorCondReorder X V W Y).hom : A ⟶ V ⊗ (X ⊗ (W ⊗ Y))`, whose first
factor is `V` (Fritz 2020, Prop. 12.18 (d) and Def. 11.5). -/
theorem IsConditional.condIndepForm {A X V W Y : C} {g : A ⟶ V ⊗ W} {g' : V ⊗ A ⟶ W}
    (hg : IsConditional g g') (h : A ⊗ (V ⊗ W) ⟶ X) (k : (V ⊗ W) ⊗ A ⟶ Y) :
    IsConditional (condIndepForm g h k ≫ (tensorCondReorder X V W Y).hom)
      (condIndepForm g' (((β_ V A).hom ▷ W ≫ (α_ A V W).hom) ≫ h)
        (((α_ W V A).inv ≫ (β_ W V).hom ▷ A) ≫ k)) := by
  rw [isConditional_iff_copyPair] at hg ⊢
  rw [MarkovCategory.marginalFst_condIndepForm_comp_tensorCondReorder]
  generalize marginalFst g = m at hg ⊢
  subst hg
  exact condIndepForm_comp_tensorCondReorder m g' h k

/-- For `f : A ⟶ X ⊗ ((V ⊗ W) ⊗ Y)` in a Markov category `C` with conditionals, if `f` displays
the conditional independence of `X` and `Y` given `V ⊗ W` and `A`, then some
`c : V ⊗ A ⟶ X ⊗ (W ⊗ Y)` is a conditional on `V` of
`f ≫ (tensorCondReorder X V W Y).hom : A ⟶ V ⊗ (X ⊗ (W ⊗ Y))` and displays the conditional
independence of `X` and `Y` given `W` and `V ⊗ A` (Fritz 2020, Prop. 12.18 (d)). -/
theorem DisplaysCondIndep.exists_isConditional [HasConditionals C] {A X V W Y : C}
    {f : A ⟶ X ⊗ ((V ⊗ W) ⊗ Y)} (hf : DisplaysCondIndep f) :
    ∃ c : V ⊗ A ⟶ X ⊗ (W ⊗ Y),
      IsConditional (f ≫ (tensorCondReorder X V W Y).hom) c ∧ DisplaysCondIndep c := by
  obtain ⟨g, h, k, rfl⟩ := hf
  obtain ⟨g', hg'⟩ := HasConditionals.exists_isConditional g
  exact ⟨_, hg'.condIndepForm h k, _, _, _, rfl⟩

end CopyDiscardCategory

end CategoryTheory
