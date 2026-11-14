/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Conditional

/-!
# Independence and conditional independence

Independence and conditional independence of morphisms into tensor products, in a
copy-discard category.

## Main definitions

* `CopyDiscardCategory.DisplaysIndep` - `f : A ⟶ X ⊗ Y` displays the independence of `X` and
  `Y` given `A` (Fritz 2020, Def. 12.12, in the form of Lemma 12.11 (a)).
* `CopyDiscardCategory.condIndepForm` - the composite of the factorization in Fritz 2020,
  Def. 12.16, built from `g : A ⟶ W`, `h : A ⊗ W ⟶ X` and `k : W ⊗ A ⟶ Y`.
* `CopyDiscardCategory.DisplaysCondIndep` - `f : A ⟶ X ⊗ (W ⊗ Y)` displays the conditional
  independence of `X` and `Y` given `W` and `A` (Fritz 2020, Def. 12.16).
* `CopyDiscardCategory.DisplaysCondIndepState` - `ψ : 𝟙_ C ⟶ X ⊗ (W ⊗ Y)` displays the
  conditional independence of `X` and `Y` given `W` (Fritz 2020, Def. 12.1).

## Main results

* `MarkovCategory.displaysIndep_iff_exists` - in a Markov category, `f` displays independence
  if and only if `f = Δ[A] ≫ (g ⊗ₘ h)` for some `g` and `h` (Fritz 2020, Lemma 12.11).
* `CopyDiscardCategory.displaysIndep_iff_isConditional` - `f` displays independence if and only
  if discarding `X` and applying `marginalSnd f` is a conditional of `f` on `X` (the
  n-Category Café post "Introduction to Categorical Probability", D19; Fritz 2020, Def. 11.5).
* `MarkovCategory.displaysCondIndep_unit_iff` - Fritz 2020, Def. 12.16 at `W = 𝟙_ C` is
  Def. 12.12.
* `CopyDiscardCategory.displaysCondIndep_iff_state` - Fritz 2020, Def. 12.16 at `A = 𝟙_ C` is
  Def. 12.1.

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

/-- For `f : A ⟶ X ⊗ Y` in a copy-discard category, `f` displays the independence of `X` and
`Y` given `A`: `f` equals copying `A` and applying the two marginals of `f` to the two copies
(Fritz 2020, Def. 12.12, in the form of Lemma 12.11 (a)). -/
def DisplaysIndep {A X Y : C} (f : A ⟶ X ⊗ Y) : Prop :=
  f = Δ[A] ≫ (marginalFst f ⊗ₘ marginalSnd f)

/-- For `g : A ⟶ W`, `h : A ⊗ W ⟶ X` and `k : W ⊗ A ⟶ Y`, the morphism `A ⟶ X ⊗ (W ⊗ Y)`
that copies `A` three times, applies `g` to the middle copy, copies its output three times,
and applies `h` to the first copy of `A` and of `W`, outputs the second copy of `W`, and
applies `k` to the third copy of `W` and of `A` (the factorization of Fritz 2020,
Def. 12.16). -/
def condIndepForm {A X W Y : C} (g : A ⟶ W) (h : A ⊗ W ⟶ X) (k : W ⊗ A ⟶ Y) :
    A ⟶ X ⊗ (W ⊗ Y) :=
  Δ[A] ≫ (A ◁ Δ[A]) ≫ (A ◁ (g ▷ A)) ≫ (A ◁ ((Δ[W] ≫ (W ◁ Δ[W])) ▷ A)) ≫
    (A ◁ (α_ W (W ⊗ W) A).hom) ≫ (A ◁ W ◁ (α_ W W A).hom) ≫
    (α_ A W (W ⊗ (W ⊗ A))).inv ≫ (h ⊗ₘ (W ◁ k))

/-- For `f : A ⟶ X ⊗ (W ⊗ Y)` in a copy-discard category, `f` displays the conditional
independence of `X` and `Y` given `W` and `A`: `f = condIndepForm g h k` for some
`g : A ⟶ W`, `h : A ⊗ W ⟶ X` and `k : W ⊗ A ⟶ Y` (Fritz 2020, Def. 12.16). -/
def DisplaysCondIndep {A X W Y : C} (f : A ⟶ X ⊗ (W ⊗ Y)) : Prop :=
  ∃ (g : A ⟶ W) (h : A ⊗ W ⟶ X) (k : W ⊗ A ⟶ Y), f = condIndepForm g h k

/-- For a state `ψ : 𝟙_ C ⟶ X ⊗ (W ⊗ Y)` in a copy-discard category, `ψ` displays the
conditional independence of `X` and `Y` given `W`: `ψ` equals a state `φ` on `W`, copied three
times, with `f : W ⟶ X` applied to the first copy and `g : W ⟶ Y` to the third, for some
`φ`, `f` and `g` (Fritz 2020, Def. 12.1). -/
def DisplaysCondIndepState {X W Y : C} (ψ : 𝟙_ C ⟶ X ⊗ (W ⊗ Y)) : Prop :=
  ∃ (φ : 𝟙_ C ⟶ W) (f : W ⟶ X) (g : W ⟶ Y),
    ψ = φ ≫ Δ[W] ≫ (W ◁ Δ[W]) ≫ (f ⊗ₘ (W ◁ g))

-- WITNESS: none (step of displaysIndep_iff_isConditional; witnessed through it)
/-- For `m : A ⟶ X` and `s : A ⟶ Y`, the conditional form of Fritz 2020, Def. 11.5 with first
marginal `m` and conditional `(ε[X] ▷ A) ≫ (λ_ A).hom ≫ s` equals `Δ[A] ≫ (m ⊗ₘ s)`. -/
theorem conditional_form_discard {A X Y : C} (m : A ⟶ X) (s : A ⟶ Y) :
    Δ[A] ≫ (m ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ ((ε[X] ▷ A) ≫ (λ_ A).hom ≫ s)) =
      Δ[A] ≫ (m ⊗ₘ s) := by
  have e : (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ ((ε[X] ▷ A) ≫ (λ_ A).hom ≫ s)) = X ◁ s := by
    calc _ = ((Δ[X] ≫ X ◁ ε[X]) ▷ A) ⊗≫ X ◁ s := by monoidal
      _ = _ := by rw [comul_counit]; monoidal
  rw [e, tensorHom_def]

/-- For `f : A ⟶ X ⊗ Y` in a copy-discard category, `f` displays independence if and only if
`(ε[X] ▷ A) ≫ (λ_ A).hom ≫ marginalSnd f` is a conditional of `f` on `X` (the form of the
n-Category Café post "Introduction to Categorical Probability", D19, with Fritz 2020,
Def. 11.5). -/
theorem displaysIndep_iff_isConditional {A X Y : C} (f : A ⟶ X ⊗ Y) :
    DisplaysIndep f ↔ IsConditional f ((ε[X] ▷ A) ≫ (λ_ A).hom ≫ marginalSnd f) := by
  unfold DisplaysIndep IsConditional
  rw [conditional_form_discard]

-- WITNESS: none (step of displaysCondIndep_iff_state; witnessed through it)
/-- For a state `φ : 𝟙_ C ⟶ W`, `h : 𝟙_ C ⊗ W ⟶ X` and `k : W ⊗ 𝟙_ C ⟶ Y`,
`condIndepForm φ h k` equals `φ` copied three times, with `(λ_ W).inv ≫ h` applied to the first
copy and `(ρ_ W).inv ≫ k` to the third. -/
theorem condIndepForm_unit_left {X W Y : C} (φ : 𝟙_ C ⟶ W) (h : 𝟙_ C ⊗ W ⟶ X)
    (k : W ⊗ 𝟙_ C ⟶ Y) :
    condIndepForm φ h k =
      φ ≫ Δ[W] ≫ (W ◁ Δ[W]) ≫ (((λ_ W).inv ≫ h) ⊗ₘ (W ◁ ((ρ_ W).inv ≫ k))) := by
  unfold condIndepForm
  rw [copy_unit]
  monoidal

/-- For a state `ψ : 𝟙_ C ⟶ X ⊗ (W ⊗ Y)` in a copy-discard category, `ψ` displays conditional
independence in the sense of Fritz 2020, Def. 12.16 at `A = 𝟙_ C` if and only if it does in
the sense of Def. 12.1. -/
theorem displaysCondIndep_iff_state {X W Y : C} (ψ : 𝟙_ C ⟶ X ⊗ (W ⊗ Y)) :
    DisplaysCondIndep ψ ↔ DisplaysCondIndepState ψ := by
  constructor
  · rintro ⟨φ, h, k, rfl⟩
    exact ⟨φ, _, _, condIndepForm_unit_left φ h k⟩
  · rintro ⟨φ, f, g, rfl⟩
    refine ⟨φ, (λ_ W).hom ≫ f, (ρ_ W).hom ≫ g, ?_⟩
    rw [condIndepForm_unit_left]
    simp only [Iso.inv_hom_id_assoc]

-- WITNESS: none (step of displaysCondIndep_unit_iff; witnessed through it)
/-- For `h : A ⊗ 𝟙_ C ⟶ X` and `k : 𝟙_ C ⊗ A ⟶ Y`, `condIndepForm ε[A] h k` equals copying `A`
and applying `(ρ_ A).inv ≫ h` and `(λ_ A).inv ≫ k ≫ (λ_ Y).inv` to the two copies. -/
theorem condIndepForm_discard {A X Y : C} (h : A ⊗ 𝟙_ C ⟶ X) (k : 𝟙_ C ⊗ A ⟶ Y) :
    condIndepForm ε[A] h k =
      Δ[A] ≫ (((ρ_ A).inv ≫ h) ⊗ₘ ((λ_ A).inv ≫ k ≫ (λ_ Y).inv)) := by
  unfold condIndepForm
  rw [copy_unit, ← whiskerLeft_comp_assoc A Δ[A] (ε[A] ▷ A), counit_comul]
  monoidal

end CopyDiscardCategory

namespace MarkovCategory

open MonoidalCategory ComonObj CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

/-- In a Markov category, `f : A ⟶ X ⊗ Y` displays independence if and only if
`f = Δ[A] ≫ (g ⊗ₘ h)` for some `g : A ⟶ X` and `h : A ⟶ Y` (Fritz 2020, Lemma 12.11). -/
theorem displaysIndep_iff_exists {A X Y : C} (f : A ⟶ X ⊗ Y) :
    DisplaysIndep f ↔ ∃ (g : A ⟶ X) (h : A ⟶ Y), f = Δ[A] ≫ (g ⊗ₘ h) := by
  constructor
  · intro hf
    exact ⟨_, _, hf⟩
  · rintro ⟨g, h, rfl⟩
    unfold DisplaysIndep
    rw [MarkovCategory.marginalFst_copy_comp_tensorHom,
      MarkovCategory.marginalSnd_copy_comp_tensorHom]

/-- In a Markov category, `f : A ⟶ X ⊗ (𝟙_ C ⊗ Y)` displays conditional independence (Fritz
2020, Def. 12.16 at `W = 𝟙_ C`) if and only if `f ≫ (X ◁ (λ_ Y).hom) : A ⟶ X ⊗ Y` displays
independence (Def. 12.12). -/
theorem displaysCondIndep_unit_iff {A X Y : C} (f : A ⟶ X ⊗ (𝟙_ C ⊗ Y)) :
    DisplaysCondIndep f ↔ DisplaysIndep (f ≫ (X ◁ (λ_ Y).hom)) := by
  constructor
  · rintro ⟨g, h, k, rfl⟩
    rw [MarkovCategory.eq_discard A g, condIndepForm_discard, displaysIndep_iff_exists]
    refine ⟨(ρ_ A).inv ≫ h, (λ_ A).inv ≫ k, ?_⟩
    monoidal
  · intro hf
    refine ⟨ε[A], (ρ_ A).hom ≫ marginalFst (f ≫ (X ◁ (λ_ Y).hom)),
      (λ_ A).hom ≫ marginalSnd (f ≫ (X ◁ (λ_ Y).hom)), ?_⟩
    rw [condIndepForm_discard]
    simp only [Iso.inv_hom_id_assoc]
    have e : f = (f ≫ X ◁ (λ_ Y).hom) ≫ X ◁ (λ_ Y).inv := by simp
    conv_lhs => rw [e, hf]
    generalize marginalFst (f ≫ X ◁ (λ_ Y).hom) = m
    generalize marginalSnd (f ≫ X ◁ (λ_ Y).hom) = s
    monoidal

end MarkovCategory

end CategoryTheory
