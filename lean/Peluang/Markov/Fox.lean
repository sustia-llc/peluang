/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Peluang.Causal
public import Peluang.Deterministic.Wide
public import Peluang.Markov.Derived

/-!
# Markov categories with only deterministic morphisms are cartesian

A Markov category in which every morphism is deterministic is cartesian monoidal, with the
marginal projections as the projections and `Δ[T] ≫ (f ⊗ₘ g)` as the pairing of `f : T ⟶ X`
and `g : T ⟶ Y` (Heunen–Vicary 2019, Theorem 4.28). The deterministic morphisms of a Markov
category form such a category (Fritz 2020, Remark 10.13).

## Main definitions

* `MarkovCategory.cartesianMonoidalCategoryOfDeterministic` - the cartesian monoidal structure
  on a Markov category in which every morphism is deterministic, for use as a local instance
  (Heunen–Vicary 2019, Theorem 4.28, (b) ⇒ (a)).
* `MarkovCategory.cartesianMonoidalCategoryDeterministic` - the cartesian monoidal structure
  on the wide subcategory of deterministic morphisms of a Markov category, for use as a local
  instance (Fritz 2020, Remark 10.13).

## Main results

* `CopyDiscardCategory.eq_copy_comp_tensorHom_of_deterministic` - in a copy-discard category,
  a deterministic `m : T ⟶ X ⊗ Y` is the pairing of its two marginals.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
* [Heunen, Vicary, *Categories for Quantum Theory*][heunen_vicary2019], Oxford University
  Press, 2019
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj

namespace CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory C]

-- WITNESS: none (structural step; no engine meaning)
/-- For a deterministic `m : T ⟶ X ⊗ Y` in a copy-discard category, `m` equals the copy of `T`
followed by the tensor product of `m` with `Y` discarded and `m` with `X` discarded. -/
theorem eq_copy_comp_tensorHom_of_deterministic {T X Y : C} (m : T ⟶ X ⊗ Y) [Deterministic m] :
    m = Δ[T] ≫ ((m ≫ X ◁ ε[Y] ≫ (ρ_ X).hom) ⊗ₘ (m ≫ ε[X] ▷ Y ≫ (λ_ Y).hom)) := by
  calc m = m ≫ 𝟙 (X ⊗ Y) := (Category.comp_id m).symm
    _ = m ≫ @ComonObj.comul C _ _ (X ⊗ Y) (CopyDiscardCategory.comonObj (X ⊗ Y)) ≫
        ((X ◁ ε[Y] ≫ (ρ_ X).hom) ⊗ₘ (ε[X] ▷ Y ≫ (λ_ Y).hom)) := by
      rw [copy_comp_fst_tensorHom_snd]
    _ = (Δ[T] ≫ (m ⊗ₘ m)) ≫
        ((X ◁ ε[Y] ≫ (ρ_ X).hom) ⊗ₘ (ε[X] ▷ Y ≫ (λ_ Y).hom)) := by
      rw [← Category.assoc, Deterministic.copy_natural m]
    _ = _ := by
      rw [Category.assoc, tensorHom_comp_tensorHom]

end CopyDiscardCategory

namespace MarkovCategory

open CopyDiscardCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [MarkovCategory C]

/-- The cartesian monoidal structure on a Markov category `C` in which every morphism is
deterministic, with the monoidal structure of `C`, the projections `X ◁ ε[Y] ≫ (ρ_ X).hom`
and `ε[X] ▷ Y ≫ (λ_ Y).hom`, and the pairing `Δ[T] ≫ (f ⊗ₘ g)` of `f : T ⟶ X` and
`g : T ⟶ Y` (Heunen–Vicary 2019, Theorem 4.28, (b) ⇒ (a); T10 of the n-Category Café post
"Introduction to Categorical Probability", where a comment names it Fox's theorem), for use
as a local instance. -/
@[expose, instance_reducible]
def cartesianMonoidalCategoryOfDeterministic
    (h : ∀ {X Y : C} (f : X ⟶ Y), Deterministic f) : CartesianMonoidalCategory C where
  isTerminalTensorUnit := isTerminalUnit
  fst X Y := X ◁ ε[Y] ≫ (ρ_ X).hom
  snd X Y := ε[X] ▷ Y ≫ (λ_ Y).hom
  fst_def X Y := by congr 2
  snd_def X Y := by congr 2
  tensorProductIsBinaryProduct X Y := Limits.BinaryFan.IsLimit.mk _
    (fun {T} f g => Δ[T] ≫ (f ⊗ₘ g))
    (fun f g => marginalFst_copy_comp_tensorHom f g)
    (fun f g => marginalSnd_copy_comp_tensorHom f g)
    (fun {T} f g m hf hg => by
      subst hf hg
      exact @eq_copy_comp_tensorHom_of_deterministic C _ _ _ T X Y m (h m))

/-- The cartesian monoidal structure on the wide subcategory of deterministic morphisms of a
Markov category `C`, with the monoidal structure of that wide subcategory (Fritz 2020,
Remark 10.13), for use as a local instance. -/
@[expose, instance_reducible]
def cartesianMonoidalCategoryDeterministic :
    CartesianMonoidalCategory (WideSubcategory (MorphismProperty.deterministic C)) :=
  cartesianMonoidalCategoryOfDeterministic fun {X Y} f =>
    { hom_counit := by
        ext
        exact @Deterministic.discard_natural C _ _ _ _ _ f.hom f.property
      hom_comul := by
        ext
        exact @Deterministic.copy_natural C _ _ _ _ _ f.hom f.property }

end MarkovCategory

end CategoryTheory
