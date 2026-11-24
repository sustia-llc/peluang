/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Instances.FinStoch.BayesianInverse
import PeluangLint

/-!
# Tests for `Peluang.Instances.FinStoch.BayesianInverse`

`FinStoch.bayesInv p f` unfolds to its body, `isBayesianInverse_bayesInv` applied once,
`HasConditionals FinStoch` found by instance search and `exists_isBayesianInverse` at
`FinStoch`, `isBayesianInverse_id_ofFun_const` at `boolObj`, the entries of `𝟙 boolObj` and
`Hom.ofFun fun _ => true : boolObj ⟶ boolObj` at input `false` and output `false`, and
`isBayesianInverse_not_unique` applied once.
-/

public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory
open scoped NNRat

namespace FinStoch

variable {X Y : FinStoch}

example (p : 𝟙_ FinStoch ⟶ X) (f : X ⟶ Y) :
    bayesInv p f = (ρ_ Y).inv ≫ cond (p ≫ Δ[X] ≫ (f ▷ X)) :=
  rfl

example (p : 𝟙_ FinStoch ⟶ X) (f : X ⟶ Y) : IsBayesianInverse p f (bayesInv p f) :=
  isBayesianInverse_bayesInv p f

example : HasConditionals FinStoch := inferInstance

example (p : 𝟙_ FinStoch ⟶ X) (f : X ⟶ Y) : ∃ g, IsBayesianInverse p f g :=
  exists_isBayesianInverse p f

example : IsBayesianInverse (Hom.ofFun (fun _ => true) : 𝟙_ FinStoch ⟶ boolObj) (𝟙 boolObj)
    (Hom.ofFun fun _ => true) :=
  isBayesianInverse_id_ofFun_const (X := boolObj) true

example : (𝟙 boolObj : boolObj ⟶ boolObj).mass false false = 1 :=
  rfl

example : (Hom.ofFun fun _ => true : boolObj ⟶ boolObj).mass false false = 0 :=
  rfl

example : ∃ (p : 𝟙_ FinStoch ⟶ boolObj) (f : boolObj ⟶ boolObj) (g₁ g₂ : boolObj ⟶ boolObj),
    IsBayesianInverse p f g₁ ∧ IsBayesianInverse p f g₂ ∧ g₁ ≠ g₂ :=
  isBayesianInverse_not_unique

end FinStoch
