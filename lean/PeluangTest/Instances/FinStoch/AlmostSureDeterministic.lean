/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Instances.FinStoch.AlmostSureDeterministic
import PeluangLint

/-!
# Tests for `Peluang.Instances.FinStoch.AlmostSureDeterministic`

`FinStoch.isAlmostSurelyDeterministic_iff` applied in each direction, the four entries of
`FinStoch.halfDet`, `halfDet` almost surely deterministic with respect to the constant state at
`true` through `isAlmostSurelyDeterministic_iff`, `eq_of_ofFun_const_mass_ne_zero` at a state of
`boolObj`, `rw [ofFun_mass]` failing at a constant map into `boolObj` written with `true`, and
`exists_isAlmostSurelyDeterministic_not_deterministic` applied once.
-/

public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory
open scoped NNRat

namespace FinStoch

variable {A X Y : FinStoch}

example (p : A ⟶ X) (f : X ⟶ Y) (h : IsAlmostSurelyDeterministic p f) (a : A.carrier)
    (x : X.carrier) (hp : p.mass a x ≠ 0) (y : Y.carrier) : f.mass x y = 0 ∨ f.mass x y = 1 :=
  (isAlmostSurelyDeterministic_iff p f).1 h a x hp y

example (p : A ⟶ X) (f : X ⟶ Y)
    (h : ∀ a x, p.mass a x ≠ 0 → ∀ y, f.mass x y = 0 ∨ f.mass x y = 1) :
    IsAlmostSurelyDeterministic p f :=
  (isAlmostSurelyDeterministic_iff p f).2 h

example : halfDet.mass true true = 1 :=
  rfl

example : halfDet.mass true false = 0 :=
  rfl

example : halfDet.mass false true = 1 / 2 :=
  rfl

example : halfDet.mass false false = 1 / 2 :=
  rfl

example (x : boolObj.carrier)
    (h : (Hom.ofFun (fun _ => true) : 𝟙_ FinStoch ⟶ boolObj).mass PUnit.unit x ≠ 0) : true = x :=
  eq_of_ofFun_const_mass_ne_zero (X := boolObj) h

example : IsAlmostSurelyDeterministic (Hom.ofFun fun _ => true : 𝟙_ FinStoch ⟶ boolObj)
    halfDet := by
  rw [isAlmostSurelyDeterministic_iff]
  intro a x hp y
  have hx : true = x := eq_of_ofFun_const_mass_ne_zero (X := boolObj) hp
  subst hx
  rcases y with _ | _
  · exact Or.inl rfl
  · exact Or.inr rfl

example : (Hom.ofFun (fun _ => true) : 𝟙_ FinStoch ⟶ boolObj).mass PUnit.unit true = 1 := by
  fail_if_success rw [ofFun_mass]
  exact (ofFun_mass _ _ _).trans (ite_eq_left rfl)

example : ∃ (p : 𝟙_ FinStoch ⟶ boolObj) (f : boolObj ⟶ boolObj),
    IsAlmostSurelyDeterministic p f ∧ ¬ Deterministic f :=
  exists_isAlmostSurelyDeterministic_not_deterministic

end FinStoch
