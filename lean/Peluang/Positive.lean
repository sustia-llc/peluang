/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.MarkovCategory.Positive
public import Peluang.Causal
public import Peluang.Deterministic.Lemmas

/-!
# Relatively positive Markov categories

Markov categories in which a `p`-almost surely deterministic composite `f ≫ g` makes
`f ≫ Δ[Y] ≫ (g ▷ Y)` and `Δ[X] ≫ ((f ≫ g) ⊗ₘ f)` `p`-almost surely equal.

## Main definitions

* `RelativelyPositiveCategory` - a Markov category `C` is relatively positive
  (Fritz 2020, Def. 13.16; arXiv:2211.02507, equation (78)).
* `instRelativelyPositiveCategoryOfCausalCategory` - a causal Markov category is relatively
  positive (arXiv:2211.02507, Corollary 2.28).
* `instPositiveCategoryOfRelativelyPositiveCategory` - a relatively positive Markov category is
  positive (arXiv:2211.02507, Remark 2.27).

## Main results

* `CopyDiscardCategory.copy_comp_natural_of_relativelyPositive` - in a relatively positive
  Markov category, `f ≫ Δ[Y] ≫ (g ▷ Y) = Δ[X] ≫ ((f ≫ g) ⊗ₘ f)` for a deterministic `f ≫ g`
  (Fritz 2020, Def. 11.22, equation (11.8)).
* `CopyDiscardCategory.IsAlmostSurelyDeterministic.of_comp` - in a relatively positive Markov
  category, a `p`-almost surely deterministic `f ≫ g` has a `(p ≫ f)`-almost surely
  deterministic `g` (Fritz 2020, Remark 13.17 (b)).

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
* [Fritz, Gonda, Houghton-Larsen, Lorenzin, Perrone, Stein, *Dilations and information flow
  axioms in categorical probability*][fritz_et_al_dilations], arXiv:2211.02507
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj CopyDiscardCategory

/-- A Markov category `C` is relatively positive: for `p : A ⟶ X`, `f : X ⟶ Y` and
`g : Y ⟶ Z` with `f ≫ g` `p`-almost surely deterministic, the morphisms `f ≫ Δ[Y] ≫ (g ▷ Y)`
and `Δ[X] ≫ ((f ≫ g) ⊗ₘ f)` are `p`-almost surely equal (Fritz 2020, Def. 13.16, where the
name is "strictly positive"; arXiv:2211.02507, equation (78), where the name is "relatively
positive"). -/
class RelativelyPositiveCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] extends
    MarkovCategory C where
  /-- For `p : A ⟶ X`, `f : X ⟶ Y` and `g : Y ⟶ Z` with `f ≫ g` `p`-almost surely
  deterministic, `f ≫ Δ[Y] ≫ (g ▷ Y)` and `Δ[X] ≫ ((f ≫ g) ⊗ₘ f)` are `p`-almost surely
  equal. -/
  copy_comp_natural_as : ∀ {A X Y Z : C} (p : A ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
    IsAlmostSurelyDeterministic p (f ≫ g) →
      AlmostSurelyEq p (f ≫ Δ[Y] ≫ (g ▷ Y)) (Δ[X] ≫ ((f ≫ g) ⊗ₘ f))

namespace CopyDiscardCategory

section CopyDiscard

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

-- WITNESS: none (structural step; tensors the AlmostSurelyEq equation on the right)
/-- For `p : A ⟶ X`, `p`-almost surely equal `f g : X ⟶ Y` and `k : X ⟶ W`,
`p ≫ Δ[X] ≫ (f ⊗ₘ k) = p ≫ Δ[X] ≫ (g ⊗ₘ k)`. -/
theorem AlmostSurelyEq.copy_comp_tensorHom {A X Y W : C} {p : A ⟶ X} {f g : X ⟶ Y}
    (h : AlmostSurelyEq p f g) (k : X ⟶ W) :
    p ≫ Δ[X] ≫ (f ⊗ₘ k) = p ≫ Δ[X] ≫ (g ⊗ₘ k) := by
  unfold AlmostSurelyEq at h
  rw [tensorHom_def, tensorHom_def, reassoc_of% h]

-- WITNESS: none (structural step; tensors the AlmostSurelyEq equation on the left)
/-- For `p : A ⟶ X`, `p`-almost surely equal `f g : X ⟶ Y` and `k : X ⟶ W`,
`p ≫ Δ[X] ≫ (k ⊗ₘ f) = p ≫ Δ[X] ≫ (k ⊗ₘ g)`. -/
theorem AlmostSurelyEq.copy_comp_tensorHom' {A X Y W : C} {p : A ⟶ X} {f g : X ⟶ Y}
    (h : AlmostSurelyEq p f g) (k : X ⟶ W) :
    p ≫ Δ[X] ≫ (k ⊗ₘ f) = p ≫ Δ[X] ≫ (k ⊗ₘ g) := by
  have key : ∀ t : X ⟶ Y, Δ[X] ≫ (k ⊗ₘ t) = Δ[X] ≫ (t ⊗ₘ k) ≫ (β_ Y W).hom := by
    intro t
    rw [BraidedCategory.braiding_naturality, IsCommComonObj.comul_comm_assoc]
  rw [key f, key g, reassoc_of% (h.copy_comp_tensorHom k)]

-- WITNESS: none (structural step; no engine meaning)
/-- For an object `X`, the two projections `X ⊗ X ⟶ X` are `Δ[X]`-almost surely equal. -/
theorem almostSurelyEq_copy_fst_snd (X : C) :
    AlmostSurelyEq Δ[X] (X ◁ ε[X] ≫ (ρ_ X).hom) (ε[X] ▷ X ≫ (λ_ X).hom) := by
  have h1 : (Δ[X] ⊗ₘ Δ[X]) ≫ ((X ◁ ε[X] ≫ (ρ_ X).hom) ▷ (X ⊗ X)) = X ◁ Δ[X] := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom]
    simp
  have h2 : (Δ[X] ⊗ₘ Δ[X]) ≫ ((ε[X] ▷ X ≫ (λ_ X).hom) ▷ (X ⊗ X)) = X ◁ Δ[X] := by
    rw [← tensorHom_id (ε[X] ▷ X ≫ (λ_ X).hom), tensorHom_comp_tensorHom]
    simp
  unfold AlmostSurelyEq
  rw [reassoc_of% (Deterministic.copy_natural Δ[X]),
    reassoc_of% (Deterministic.copy_natural Δ[X]), h1, h2]

-- WITNESS: none (structural step; no engine meaning)
/-- For a deterministic `s : M ⟶ Y` and `g : Y ⟶ Z`,
`Δ[M] ≫ ((s ≫ g) ▷ M) ≫ (Z ◁ s) = s ≫ Δ[Y] ≫ (g ▷ Y)`. -/
theorem copy_comp_whiskerRight_comp_whiskerLeft {M Y Z : C} (s : M ⟶ Y)
    [Deterministic s] (g : Y ⟶ Z) :
    Δ[M] ≫ ((s ≫ g) ▷ M) ≫ (Z ◁ s) = s ≫ Δ[Y] ≫ (g ▷ Y) := by
  rw [reassoc_of% (Deterministic.copy_natural s)]
  simp only [tensorHom_def, comp_whiskerRight, Category.assoc, whisker_exchange]

-- WITNESS: none (structural step; no engine meaning)
/-- For `a : X ⟶ Y`, `b : X ⟶ Z` and `c : X ⟶ W`,
`Δ[X] ≫ ((Δ[X] ≫ (a ⊗ₘ b)) ⊗ₘ c) = Δ[X] ≫ (a ⊗ₘ (Δ[X] ≫ (b ⊗ₘ c))) ≫ (α_ Y Z W).inv`. -/
theorem copy_comp_copy_tensorHom_tensorHom {X Y Z W : C} (a : X ⟶ Y) (b : X ⟶ Z) (c : X ⟶ W) :
    Δ[X] ≫ ((Δ[X] ≫ (a ⊗ₘ b)) ⊗ₘ c) =
      Δ[X] ≫ (a ⊗ₘ (Δ[X] ≫ (b ⊗ₘ c))) ≫ (α_ Y Z W).inv := by
  calc _ = (Δ[X] ≫ Δ[X] ▷ X) ≫ ((a ⊗ₘ b) ⊗ₘ c) := by
        simp only [tensorHom_def]
        monoidal
    _ = (Δ[X] ≫ X ◁ Δ[X] ≫ (α_ X X X).inv) ≫ ((a ⊗ₘ b) ⊗ₘ c) := by rw [comul_assoc_flip]
    _ = Δ[X] ≫ (X ◁ Δ[X] ≫ a ▷ (X ⊗ X)) ≫ (Y ◁ (b ▷ X ≫ Z ◁ c)) ≫ (α_ Y Z W).inv := by
        simp only [tensorHom_def]
        monoidal
    _ = Δ[X] ≫ (a ▷ X ≫ Y ◁ Δ[X]) ≫ (Y ◁ (b ▷ X ≫ Z ◁ c)) ≫ (α_ Y Z W).inv := by
        rw [whisker_exchange]
    _ = _ := by
        simp only [tensorHom_def]
        monoidal

end CopyDiscard

section RelativelyPositive

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [RelativelyPositiveCategory C]

/-- In a relatively positive Markov category, for `f : X ⟶ Y` and `g : Y ⟶ Z` with `f ≫ g`
deterministic, `f ≫ Δ[Y] ≫ (g ▷ Y) = Δ[X] ≫ ((f ≫ g) ⊗ₘ f)` (Fritz 2020, Def. 11.22,
equation (11.8); arXiv:2211.02507, Remark 2.27). -/
theorem copy_comp_natural_of_relativelyPositive {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Deterministic (f ≫ g)] :
    f ≫ Δ[Y] ≫ (g ▷ Y) = Δ[X] ≫ ((f ≫ g) ⊗ₘ f) := by
  have h := (RelativelyPositiveCategory.copy_comp_natural_as (𝟙 X) f g
    (isAlmostSurelyDeterministic_of_deterministic (𝟙 X) (f ≫ g))).comp_eq_comp
  simpa only [Category.id_comp] using h

/-- In a relatively positive Markov category, for `p : A ⟶ X`, `f : X ⟶ Y` and `g : Y ⟶ Z`
with `f ≫ g` `p`-almost surely deterministic, `g` is `(p ≫ f)`-almost surely deterministic
(Fritz 2020, Remark 13.17 (b)). -/
theorem IsAlmostSurelyDeterministic.of_comp {A X Y Z : C}
    {p : A ⟶ X} {f : X ⟶ Y} {g : Y ⟶ Z} (h : IsAlmostSurelyDeterministic p (f ≫ g)) :
    IsAlmostSurelyDeterministic (p ≫ f) g := by
  have R := RelativelyPositiveCategory.copy_comp_natural_as p f g h
  have R0 : p ≫ f ≫ Δ[Y] ≫ (g ▷ Y) = p ≫ Δ[X] ≫ ((f ≫ g) ⊗ₘ f) := R.comp_eq_comp
  unfold IsAlmostSurelyDeterministic at h ⊢
  have hL : p ≫ Δ[X] ≫ (((f ≫ g) ≫ Δ[Z]) ⊗ₘ f) =
      p ≫ Δ[X] ≫ ((Δ[X] ≫ ((f ≫ g) ⊗ₘ (f ≫ g))) ⊗ₘ f) := h.copy_comp_tensorHom f
  have hR : p ≫ Δ[X] ≫ ((f ≫ g) ⊗ₘ (f ≫ Δ[Y] ≫ (g ▷ Y))) =
      p ≫ Δ[X] ≫ ((f ≫ g) ⊗ₘ (Δ[X] ≫ ((f ≫ g) ⊗ₘ f))) := R.copy_comp_tensorHom' (f ≫ g)
  have e1 : ((f ≫ g) ⊗ₘ f) ≫ (Δ[Z] ▷ Y) = ((f ≫ g) ≫ Δ[Z]) ⊗ₘ f := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  have e2 : (f ≫ g) ⊗ₘ (f ≫ Δ[Y] ≫ (g ▷ Y)) = ((f ≫ g) ⊗ₘ f) ≫ (Z ◁ (Δ[Y] ≫ (g ▷ Y))) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  have B : Δ[Y] ≫ ((Δ[Y] ≫ (g ⊗ₘ g)) ▷ Y) =
      Δ[Y] ≫ (g ▷ Y) ≫ (Z ◁ (Δ[Y] ≫ (g ▷ Y))) ≫ (α_ Z Z Y).inv := by
    calc _ = (Δ[Y] ≫ Δ[Y] ▷ Y) ≫ ((g ⊗ₘ g) ▷ Y) := by
          simp only [tensorHom_def]
          monoidal
      _ = (Δ[Y] ≫ Y ◁ Δ[Y] ≫ (α_ Y Y Y).inv) ≫ ((g ⊗ₘ g) ▷ Y) := by rw [comul_assoc_flip]
      _ = Δ[Y] ≫ (Y ◁ Δ[Y] ≫ g ▷ (Y ⊗ Y)) ≫ (Z ◁ (g ▷ Y)) ≫ (α_ Z Z Y).inv := by
          simp only [tensorHom_def]
          monoidal
      _ = Δ[Y] ≫ (g ▷ Y ≫ Z ◁ Δ[Y]) ≫ (Z ◁ (g ▷ Y)) ≫ (α_ Z Z Y).inv := by
          rw [whisker_exchange]
      _ = _ := by monoidal
  unfold AlmostSurelyEq
  calc (p ≫ f) ≫ Δ[Y] ≫ ((g ≫ Δ[Z]) ▷ Y)
      = (p ≫ f ≫ Δ[Y] ≫ (g ▷ Y)) ≫ (Δ[Z] ▷ Y) := by
        simp only [Category.assoc, comp_whiskerRight]
    _ = (p ≫ Δ[X] ≫ ((f ≫ g) ⊗ₘ f)) ≫ (Δ[Z] ▷ Y) := by rw [R0]
    _ = p ≫ Δ[X] ≫ (((f ≫ g) ≫ Δ[Z]) ⊗ₘ f) := by
        rw [Category.assoc, Category.assoc, e1]
    _ = p ≫ Δ[X] ≫ ((Δ[X] ≫ ((f ≫ g) ⊗ₘ (f ≫ g))) ⊗ₘ f) := hL
    _ = (p ≫ Δ[X] ≫ ((f ≫ g) ⊗ₘ (Δ[X] ≫ ((f ≫ g) ⊗ₘ f)))) ≫ (α_ Z Z Y).inv := by
        rw [copy_comp_copy_tensorHom_tensorHom]
        simp only [Category.assoc]
    _ = (p ≫ Δ[X] ≫ ((f ≫ g) ⊗ₘ (f ≫ Δ[Y] ≫ (g ▷ Y)))) ≫ (α_ Z Z Y).inv := by rw [hR]
    _ = (p ≫ Δ[X] ≫ ((f ≫ g) ⊗ₘ f)) ≫ (Z ◁ (Δ[Y] ≫ (g ▷ Y))) ≫ (α_ Z Z Y).inv := by
        rw [e2]
        simp only [Category.assoc]
    _ = (p ≫ f ≫ Δ[Y] ≫ (g ▷ Y)) ≫ (Z ◁ (Δ[Y] ≫ (g ▷ Y))) ≫ (α_ Z Z Y).inv := by rw [R0]
    _ = (p ≫ f) ≫ Δ[Y] ≫ ((Δ[Y] ≫ (g ⊗ₘ g)) ▷ Y) := by
        rw [B]
        simp only [Category.assoc]

end RelativelyPositive

end CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- A causal Markov category `C` is relatively positive, with the Markov category structure of
`C` (arXiv:2211.02507, Corollary 2.28). -/
instance instRelativelyPositiveCategoryOfCausalCategory [CausalCategory C] :
    RelativelyPositiveCategory C where
  copy_comp_natural_as {A X Y Z} p f g hdet := by
    have hdet' := hdet
    unfold IsAlmostSurelyDeterministic at hdet'
    have hp : p ≫ (f ≫ g) ≫ Δ[Z] = p ≫ Δ[X] ≫ ((f ≫ g) ⊗ₘ (f ≫ g)) := hdet'.comp_eq_comp
    have e0 : (p ≫ Δ[X] ≫ ((f ≫ g) ⊗ₘ f)) ≫ (Z ◁ g) = (p ≫ f ≫ g) ≫ Δ[Z] := by
      have e : ((f ≫ g) ⊗ₘ f) ≫ (Z ◁ g) = (f ≫ g) ⊗ₘ (f ≫ g) := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
      rw [Category.assoc, Category.assoc, e, ← hp]
      simp only [Category.assoc]
    have E0 : AlmostSurelyEq ((p ≫ Δ[X] ≫ ((f ≫ g) ⊗ₘ f)) ≫ (Z ◁ g))
        (Z ◁ ε[Z] ≫ (ρ_ Z).hom) (ε[Z] ▷ Z ≫ (λ_ Z).hom) := by
      rw [e0]
      exact (almostSurelyEq_copy_fst_snd Z).precomp _
    have E1 := E0.of_comp
    have E2 := (CausalCategory.causal p (Δ[X] ≫ ((f ≫ g) ⊗ₘ f)) _ _ E1).comp
      (Z ◁ (ε[Z] ▷ Y ≫ (λ_ Y).hom))
    have fstg : Z ◁ g ≫ Z ◁ ε[Z] ≫ (ρ_ Z).hom = Z ◁ ε[Y] ≫ (ρ_ Z).hom := by
      rw [← whiskerLeft_comp_assoc, MarkovCategory.discard_natural]
    have sndg : Z ◁ g ≫ ε[Z] ▷ Z ≫ (λ_ Z).hom = (ε[Z] ▷ Y ≫ (λ_ Y).hom) ≫ g := by
      rw [whisker_exchange_assoc, leftUnitor_naturality, Category.assoc]
    have hv : (Δ[X] ≫ ((f ≫ g) ⊗ₘ f)) ≫ ε[Z] ▷ Y ≫ (λ_ Y).hom = f :=
      MarkovCategory.marginalSnd_copy_comp_tensorHom (f ≫ g) f
    have key : ∀ {t₁ t₂ : X ⟶ Z ⊗ Y}, AlmostSurelyEq p t₁ t₂ →
        t₁ = Δ[X] ≫ ((f ≫ g) ⊗ₘ f) → t₂ = f ≫ Δ[Y] ≫ (g ▷ Y) →
          AlmostSurelyEq p (f ≫ Δ[Y] ≫ (g ▷ Y)) (Δ[X] ≫ ((f ≫ g) ⊗ₘ f)) := by
      rintro _ _ h rfl rfl
      exact (almostSurelyEq_equivalence p).symm h
    refine key E2 ?_ ?_
    · simp only [Category.assoc]
      rw [fstg, ← tensorHom_def, copy_comp_fst_tensorHom_snd, Category.comp_id]
    · simp only [Category.assoc]
      rw [sndg, copy_comp_whiskerRight_comp_whiskerLeft]
      simp only [Category.assoc]
      rw [reassoc_of% hv]

/-- A relatively positive Markov category `C` is positive, with the Markov category structure
of `C` (arXiv:2211.02507, Remark 2.27). -/
instance instPositiveCategoryOfRelativelyPositiveCategory [RelativelyPositiveCategory C] :
    PositiveCategory C where
  copy_comp_natural f g := by
    rw [tensorHom_id]
    exact copy_comp_natural_of_relativelyPositive f g

end CategoryTheory
