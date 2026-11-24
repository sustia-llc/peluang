/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.MarkovCategory.Basic
public import Peluang.AlmostSure.Deterministic
public import Peluang.BayesianInverse

/-!
# Causal Markov categories

Markov categories in which an almost sure equality with respect to a composite `f ≫ g` gives
an almost sure equality with respect to `f`.

## Main definitions

* `CausalCategory` - a Markov category `C` is causal (Fritz 2020, Def. 11.31).
* `CausalCategory.ofHasConditionals` - the causal structure of a Markov category with
  conditionals (Fritz 2020, Prop. 11.34).

## Main results

* `CausalCategory.causal_eq` - the causality axiom as an equation of morphisms
  (Fritz 2020, equation (11.12)).
* `CopyDiscardCategory.almostSurelyEq_copy_whiskerRight_of_hasConditionals` - the causality
  implication in a copy-discard category with conditionals (Fritz 2020, Prop. 11.34).
* `CopyDiscardCategory.AlmostSurelyEq.of_comp` - in a causal Markov category,
  `(f ≫ g)`-almost surely equal `h₁ h₂` have `f`-almost surely equal `g ≫ h₁` and `g ≫ h₂`.
* `CopyDiscardCategory.IsAlmostSurelyDeterministic.comp` - in a causal Markov category, a
  `p`-almost surely deterministic `f` followed by a `(p ≫ f)`-almost surely deterministic `g`
  is `p`-almost surely deterministic (Fritz 2020, Remark 13.14).

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

/-- A Markov category `C` is causal: for `f : A ⟶ W`, `g : W ⟶ X` and `(f ≫ g)`-almost surely
equal `h₁ h₂ : X ⟶ Y`, the morphisms `g ≫ Δ[X] ≫ (h₁ ▷ X)` and `g ≫ Δ[X] ≫ (h₂ ▷ X)` are
`f`-almost surely equal (Fritz 2020, Def. 11.31; arXiv:2211.02507, Def. 2.15). -/
class CausalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] extends
    MarkovCategory C where
  /-- For `f : A ⟶ W`, `g : W ⟶ X` and `(f ≫ g)`-almost surely equal `h₁ h₂ : X ⟶ Y`,
  `g ≫ Δ[X] ≫ (h₁ ▷ X)` and `g ≫ Δ[X] ≫ (h₂ ▷ X)` are `f`-almost surely equal. -/
  causal : ∀ {A W X Y : C} (f : A ⟶ W) (g : W ⟶ X) (h₁ h₂ : X ⟶ Y),
    AlmostSurelyEq (f ≫ g) h₁ h₂ →
      AlmostSurelyEq f (g ≫ Δ[X] ≫ (h₁ ▷ X)) (g ≫ Δ[X] ≫ (h₂ ▷ X))

/-- In a causal Markov category, for `f : A ⟶ W`, `g : W ⟶ X` and `h₁ h₂ : X ⟶ Y` with
`f ≫ g ≫ Δ[X] ≫ (h₁ ▷ X) = f ≫ g ≫ Δ[X] ≫ (h₂ ▷ X)`, copying `W` after `f` and applying
`g ≫ Δ[X] ≫ (h₁ ▷ X)` to the left copy equals the same with `h₂` for `h₁`
(Fritz 2020, equation (11.12)). -/
theorem CausalCategory.causal_eq {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
    [CausalCategory C] {A W X Y : C} (f : A ⟶ W) (g : W ⟶ X)
    (h₁ h₂ : X ⟶ Y) (e : f ≫ g ≫ Δ[X] ≫ (h₁ ▷ X) = f ≫ g ≫ Δ[X] ≫ (h₂ ▷ X)) :
    f ≫ Δ[W] ≫ ((g ≫ Δ[X] ≫ (h₁ ▷ X)) ▷ W) = f ≫ Δ[W] ≫ ((g ≫ Δ[X] ≫ (h₂ ▷ X)) ▷ W) :=
  CausalCategory.causal f g h₁ h₂ (by unfold AlmostSurelyEq; simpa only [Category.assoc] using e)

namespace CopyDiscardCategory

section CopyDiscard

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

-- WITNESS: none (structural step; discards the copy in the AlmostSurelyEq equation)
/-- For `p : A ⟶ X` and `p`-almost surely equal `f g : X ⟶ Y`, `p ≫ f = p ≫ g`. -/
theorem AlmostSurelyEq.comp_eq_comp {A X Y : C} {p : A ⟶ X} {f g : X ⟶ Y}
    (h : AlmostSurelyEq p f g) : p ≫ f = p ≫ g := by
  unfold AlmostSurelyEq at h
  rw [← marginalFst_comp_copy_whiskerRight p f, ← marginalFst_comp_copy_whiskerRight p g, h]

-- WITNESS: none (structural step; precomposes the AlmostSurelyEq equation)
/-- For `p : A ⟶ X`, `p`-almost surely equal `f g : X ⟶ Y` and `q : B ⟶ A`, `f` and `g` are
`(q ≫ p)`-almost surely equal. -/
theorem AlmostSurelyEq.precomp {A B X Y : C} {p : A ⟶ X} {f g : X ⟶ Y}
    (h : AlmostSurelyEq p f g) (q : B ⟶ A) : AlmostSurelyEq (q ≫ p) f g := by
  unfold AlmostSurelyEq at h ⊢
  rw [Category.assoc, Category.assoc, h]

-- WITNESS: none (structural step; no engine meaning)
/-- For objects `A` and `B`, copying `A ⊗ B`, discarding `B` from the left copy and `A` from
the right copy is the identity of `A ⊗ B`. -/
theorem copy_comp_fst_tensorHom_snd (A B : C) :
    @ComonObj.comul C _ _ (A ⊗ B) (CopyDiscardCategory.comonObj (A ⊗ B)) ≫
      ((A ◁ ε[B] ≫ (ρ_ A).hom) ⊗ₘ (ε[A] ▷ B ≫ (λ_ B).hom)) = 𝟙 (A ⊗ B) := by
  rw [tensorHom_def, reassoc_of% copy_comp_fst_whiskerRight]
  calc _ = ((Δ[A] ≫ A ◁ ε[A]) ▷ B) ⊗≫ 𝟙 (A ⊗ B) := by monoidal
    _ = _ := by
      rw [comul_counit]
      monoidal

/-- In a copy-discard category with conditionals, for `f : A ⟶ W`, `g : W ⟶ X` and
`(f ≫ g)`-almost surely equal `h₁ h₂ : X ⟶ Y`, the morphisms `g ≫ Δ[X] ≫ (h₁ ▷ X)` and
`g ≫ Δ[X] ≫ (h₂ ▷ X)` are `f`-almost surely equal (Fritz 2020, Prop. 11.34). -/
theorem almostSurelyEq_copy_whiskerRight_of_hasConditionals [HasConditionals C] {A W X Y : C}
    (f : A ⟶ W) (g : W ⟶ X) (h₁ h₂ : X ⟶ Y) (h : AlmostSurelyEq (f ≫ g) h₁ h₂) :
    AlmostSurelyEq f (g ≫ Δ[X] ≫ (h₁ ▷ X)) (g ≫ Δ[X] ≫ (h₂ ▷ X)) := by
  have e : f ≫ g ≫ Δ[X] ≫ (h₁ ▷ X) = f ≫ g ≫ Δ[X] ≫ (h₂ ▷ X) := by
    unfold AlmostSurelyEq at h
    simpa only [Category.assoc] using h
  unfold AlmostSurelyEq
  obtain ⟨s, hs⟩ := HasConditionals.exists_isConditional (f ≫ Δ[W] ≫ (g ▷ W))
  unfold IsConditional at hs
  rw [marginalFst_comp_copy_whiskerRight] at hs
  have aux : ∀ h : X ⟶ Y, Δ[X] ≫ ((Δ[X] ≫ (h ▷ X)) ▷ X) =
      Δ[X] ≫ (h ▷ X) ≫ (Y ◁ Δ[X]) ≫ (α_ Y X X).inv := by
    intro h
    calc _ = (Δ[X] ≫ Δ[X] ▷ X) ≫ ((h ▷ X) ▷ X) := by monoidal
      _ = (Δ[X] ≫ X ◁ Δ[X] ≫ (α_ X X X).inv) ≫ ((h ▷ X) ▷ X) := by rw [comul_assoc_flip]
      _ = Δ[X] ≫ (X ◁ Δ[X] ≫ h ▷ (X ⊗ X)) ≫ (α_ Y X X).inv := by monoidal
      _ = Δ[X] ≫ (h ▷ X ≫ Y ◁ Δ[X]) ≫ (α_ Y X X).inv := by rw [whisker_exchange]
      _ = _ := by simp only [Category.assoc]
  have key : ∀ h : X ⟶ Y, f ≫ Δ[W] ≫ ((g ≫ Δ[X] ≫ (h ▷ X)) ▷ W) =
      Δ[A] ≫ ((f ≫ g ≫ Δ[X] ≫ (h ▷ X)) ▷ A) ≫ ((Y ◁ Δ[X]) ▷ A) ≫ ((α_ Y X X).inv ▷ A) ≫
        (α_ (Y ⊗ X) X A).hom ≫ ((Y ⊗ X) ◁ s) := by
    intro h
    calc _ = (f ≫ Δ[W] ≫ (g ▷ W)) ≫ ((Δ[X] ≫ (h ▷ X)) ▷ W) := by
          simp only [comp_whiskerRight, Category.assoc]
      _ = (Δ[A] ≫ ((f ≫ g) ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫ (X ◁ s)) ≫
            ((Δ[X] ≫ (h ▷ X)) ▷ W) := by rw [← hs]
      _ = Δ[A] ≫ ((f ≫ g) ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫
            (X ◁ s ≫ (Δ[X] ≫ (h ▷ X)) ▷ W) := by simp only [Category.assoc]
      _ = Δ[A] ≫ ((f ≫ g) ▷ A) ≫ (Δ[X] ▷ A) ≫ (α_ X X A).hom ≫
            ((Δ[X] ≫ (h ▷ X)) ▷ (X ⊗ A) ≫ (Y ⊗ X) ◁ s) := by rw [whisker_exchange]
      _ = Δ[A] ≫ ((f ≫ g) ▷ A) ≫ ((Δ[X] ≫ ((Δ[X] ≫ (h ▷ X)) ▷ X)) ▷ A) ≫
            (α_ (Y ⊗ X) X A).hom ≫ ((Y ⊗ X) ◁ s) := by monoidal
      _ = _ := by
          rw [aux]
          simp only [comp_whiskerRight, Category.assoc]
  rw [key h₁, key h₂, e]

end CopyDiscard

section Causal

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CausalCategory C]

/-- In a causal Markov category, for `f : A ⟶ W`, `g : W ⟶ X` and `(f ≫ g)`-almost surely
equal `h₁ h₂ : X ⟶ Y`, `g ≫ h₁` and `g ≫ h₂` are `f`-almost surely equal. -/
theorem AlmostSurelyEq.of_comp {A W X Y : C} {f : A ⟶ W} {g : W ⟶ X}
    {h₁ h₂ : X ⟶ Y} (h : AlmostSurelyEq (f ≫ g) h₁ h₂) :
    AlmostSurelyEq f (g ≫ h₁) (g ≫ h₂) := by
  have key := (CausalCategory.causal f g h₁ h₂ h).comp (Y ◁ ε[X] ≫ (ρ_ Y).hom)
  have e : ∀ t : X ⟶ Y, (g ≫ Δ[X] ≫ (t ▷ X)) ≫ Y ◁ ε[X] ≫ (ρ_ Y).hom = g ≫ t := by
    intro t
    exact marginalFst_comp_copy_whiskerRight g t
  rwa [e, e] at key

/-- In a causal Markov category, for `p : A ⟶ X`, a `p`-almost surely deterministic
`f : X ⟶ Y` and a `(p ≫ f)`-almost surely deterministic `g : Y ⟶ Z`, `f ≫ g` is `p`-almost
surely deterministic (Fritz 2020, Remark 13.14). -/
theorem IsAlmostSurelyDeterministic.comp {A X Y Z : C} {p : A ⟶ X}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsAlmostSurelyDeterministic p f)
    (hg : IsAlmostSurelyDeterministic (p ≫ f) g) :
    IsAlmostSurelyDeterministic p (f ≫ g) := by
  unfold IsAlmostSurelyDeterministic at hf hg ⊢
  have h1 : AlmostSurelyEq p (f ≫ g ≫ Δ[Z]) (f ≫ Δ[Y] ≫ (g ⊗ₘ g)) := hg.of_comp
  have h2 : AlmostSurelyEq p (f ≫ Δ[Y] ≫ (g ⊗ₘ g)) (Δ[X] ≫ ((f ≫ g) ⊗ₘ (f ≫ g))) := by
    simpa only [Category.assoc, tensorHom_comp_tensorHom] using hf.comp (g ⊗ₘ g)
  have h3 := (almostSurelyEq_equivalence p).trans h1 h2
  simpa only [Category.assoc] using h3

end Causal

end CopyDiscardCategory

/-- The causal Markov category structure on a Markov category `C` with conditionals, with the
Markov category structure of `C` (Fritz 2020, Prop. 11.34). -/
abbrev CausalCategory.ofHasConditionals {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
    [MarkovCategory C] [HasConditionals C] : CausalCategory C where
  causal := almostSurelyEq_copy_whiskerRight_of_hasConditionals

end CategoryTheory
