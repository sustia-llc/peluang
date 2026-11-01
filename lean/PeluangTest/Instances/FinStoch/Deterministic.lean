/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Deterministic.Lemmas
public import Peluang.Instances.FinStoch.Deterministic
meta import Peluang.Instances.FinStoch.Deterministic
import PeluangLint

/-!
# Tests for `Peluang.Instances.FinStoch.Deterministic`

The statements of `FinStoch.deterministic_iff_mass` and `FinStoch.deterministic_iff_exists_ofFun`
at tensor and nested tensor objects, and in the `IsComonHom` form. `Δ[X]`, `ε[X]` and `𝟙 X` through
`FinStoch.deterministic_iff_mass`. The inverse of `FinStoch.detHomEquiv`, both round trips, its
computable value on a concrete morphism by `#guard`, and the entries of `FinStoch.bernoulli`, which
is no `Hom.ofFun`.
-/

public section

open CategoryTheory MonoidalCategory ComonObj
open scoped NNRat

namespace FinStoch

variable {A B X Y Z : FinStoch}

example (f : X ⟶ Y) : IsComonHom f ↔ ∀ x y, f.mass x y = 0 ∨ f.mass x y = 1 :=
  deterministic_iff_mass f

example (f : X ⊗ Y ⟶ Z) : Deterministic f ↔ ∀ x y, f.mass x y = 0 ∨ f.mass x y = 1 :=
  deterministic_iff_mass f

example (f : (X ⊗ Y) ⊗ Z ⟶ A ⊗ B) : Deterministic f ↔ ∀ x y, f.mass x y = 0 ∨ f.mass x y = 1 :=
  deterministic_iff_mass f

example (f : (X ⊗ Y) ⊗ Z ⟶ A ⊗ B) : IsComonHom f ↔ ∀ x y, f.mass x y = 0 ∨ f.mass x y = 1 :=
  deterministic_iff_mass f

example (f : X ⊗ (Y ⊗ Z) ⟶ A) : Deterministic f ↔ ∃ g, f = Hom.ofFun g :=
  deterministic_iff_exists_ofFun f

example (f : (X ⊗ Y) ⊗ Z ⟶ A ⊗ B) : IsComonHom f ↔ ∃ g, f = Hom.ofFun g :=
  deterministic_iff_exists_ofFun f

example : ∀ x y, (Δ[X]).mass x y = 0 ∨ (Δ[X]).mass x y = 1 :=
  (deterministic_iff_mass _).1 inferInstance

example : ∀ x y, (ε[X]).mass x y = 0 ∨ (ε[X]).mass x y = 1 :=
  (deterministic_iff_mass _).1 inferInstance

example : ∀ x y, (𝟙 X : X ⟶ X).mass x y = 0 ∨ (𝟙 X : X ⟶ X).mass x y = 1 :=
  (deterministic_iff_mass _).1 inferInstance

example (g : X.carrier → Y.carrier) : (detHomEquiv.symm g).1 = Hom.ofFun g :=
  rfl

example (g : X.carrier → Y.carrier) : detHomEquiv (detHomEquiv.symm g) = g :=
  detHomEquiv.apply_symm_apply g

example (f : { f : X ⟶ Y // Deterministic f }) : detHomEquiv.symm (detHomEquiv f) = f :=
  detHomEquiv.symm_apply_apply f

example (g : (X ⊗ Y).carrier → (A ⊗ B).carrier) : (detHomEquiv.symm g).1 = Hom.ofFun g :=
  rfl

example : bernoulli.mass PUnit.unit true = 1 / 2 :=
  rfl

example : bernoulli.mass PUnit.unit false = 1 / 2 :=
  rfl

example (g : (𝟙_ FinStoch).carrier → boolObj.carrier) : bernoulli ≠ Hom.ofFun g := fun h =>
  not_deterministic_bernoulli ((deterministic_iff_exists_ofFun _).2 ⟨g, h⟩)

example : ¬ ∀ x y, bernoulli.mass x y = 0 ∨ bernoulli.mass x y = 1 := fun h =>
  not_deterministic_bernoulli ((deterministic_iff_mass _).2 h)

set_option linter.hashCommand false in
#guard
  let f : { f : boolObj ⟶ boolObj // Deterministic f } := detHomEquiv.symm not
  (detHomEquiv f true : Bool) == false && (detHomEquiv f false : Bool) == true

set_option linter.hashCommand false in
#guard
  let f : { f : boolObj ⟶ boolObj // Deterministic f } := detHomEquiv.symm fun _ => true
  (detHomEquiv f true : Bool) == true && (detHomEquiv f false : Bool) == true

set_option linter.hashCommand false in
#guard
  bernoulli.mass PUnit.unit true == 1 / 2 && bernoulli.mass PUnit.unit false == 1 / 2

end FinStoch
