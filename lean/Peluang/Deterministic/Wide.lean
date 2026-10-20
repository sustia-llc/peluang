/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Widesubcategory
public import Peluang.Deterministic.Lemmas

/-!
# The wide subcategory of deterministic morphisms

The deterministic morphisms of a copy-discard category form a morphism property
stable under the monoidal structure, the braiding and the comonoid structure maps.
A wide subcategory of a Markov category cut out by such a property is a Markov
category; in particular the deterministic morphisms of a Markov category form a
Markov category (Fritz 2020, Remark 10.13).

## Main definitions

* `MorphismProperty.deterministic` - the deterministic morphisms of a copy-discard
  category.

## Main results

* `WideSubcategory.instMarkovCategory` - the Markov category structure on
  `WideSubcategory P` for `P` stable under braiding and the comonoid structure maps.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj

/-- The deterministic morphisms of a copy-discard category (Fritz 2020, Def. 10.1). -/
abbrev MorphismProperty.deterministic (C : Type u) [Category.{v} C]
    [MonoidalCategory.{v} C] [CopyDiscardCategory C] : MorphismProperty C :=
  fun _ _ f => Deterministic f

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

namespace MorphismProperty

section CopyDiscard

variable [CopyDiscardCategory C]

/-- The deterministic morphisms contain the identities and are closed under composition
and whiskering, and contain the associators, unitors and braidings
together with their inverses (Fritz 2020, Lemma 10.12). -/
instance : (MorphismProperty.deterministic C).IsStableUnderBraiding where
  id_mem X := show Deterministic (𝟙 X) from inferInstance
  comp_mem f g (_ : Deterministic f) (_ : Deterministic g) :=
    show Deterministic (f ≫ g) from inferInstance
  whiskerLeft X _ _ g (_ : Deterministic g) := show Deterministic (X ◁ g) from inferInstance
  whiskerRight f (_ : Deterministic f) Y := show Deterministic (f ▷ Y) from inferInstance
  associator_hom_mem X Y Z := show Deterministic (α_ X Y Z).hom from inferInstance
  associator_inv_mem X Y Z := show Deterministic (α_ X Y Z).inv from inferInstance
  leftUnitor_hom_mem X := show Deterministic (λ_ X).hom from inferInstance
  leftUnitor_inv_mem X := show Deterministic (λ_ X).inv from inferInstance
  rightUnitor_hom_mem X := show Deterministic (ρ_ X).hom from inferInstance
  rightUnitor_inv_mem X := show Deterministic (ρ_ X).inv from inferInstance
  braiding_hom_mem X Y := show Deterministic (β_ X Y).hom from inferInstance
  braiding_inv_mem X Y := show Deterministic (β_ X Y).inv from inferInstance

/-- Copy and discard on every object are deterministic (Fritz 2020, Remark 10.2). -/
instance (c : C) : (MorphismProperty.deterministic C).IsStableUnderComonoid c where
  counit_mem := show Deterministic ε[c] from inferInstance
  comul_mem := show Deterministic Δ[c] from inferInstance

end CopyDiscard

end MorphismProperty

/-- A wide subcategory of a Markov category, cut out by a morphism property stable under
braiding and under the comonoid structure maps, is a Markov category. For
`P = MorphismProperty.deterministic C` this is the Markov category of deterministic
morphisms (Fritz 2020, Remark 10.13). -/
instance WideSubcategory.instMarkovCategory [MarkovCategory C] (P : MorphismProperty C)
    [P.IsStableUnderBraiding] [∀ c, P.IsStableUnderComonoid c] :
    MarkovCategory (WideSubcategory P) where
  discard_natural f := by
    ext
    exact MarkovCategory.discard_natural f.1

end CategoryTheory
