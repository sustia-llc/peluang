/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Instances.FinStoch.Basic
meta import Peluang.Instances.FinStoch.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import PeluangLint

/-!
# Tests for `Peluang.Instances.FinStoch.Basic`

Instance search for `Category FinStoch` and for `Fintype` and `DecidableEq` on carriers, `ext` on
`X ⟶ Y`, each `simp` lemma on its own statement and its failure without that lemma, the two forms
that need a type ascription to elaborate, and the value of a composite in `ℚ≥0` by `#guard`.
-/

public section

open CategoryTheory
open scoped NNRat

namespace FinStoch

variable {X Y Z : FinStoch}

example : Category FinStoch := inferInstance

example (X : FinStoch) : Fintype X.carrier := inferInstance

example (X : FinStoch) : DecidableEq X.carrier := inferInstance

example : Fintype (FinStoch.mk Bool).carrier := inferInstance

example : DecidableEq (FinStoch.mk Bool).carrier := inferInstance

example : Fintype (FinStoch.mk (FinStoch.mk Bool).carrier).carrier := inferInstance

example : DecidableEq (FinStoch.mk (FinStoch.mk Bool).carrier).carrier := inferInstance

example {f g : X ⟶ Y} (h : ∀ x y, f.mass x y = g.mass x y) : f = g := by
  ext x y : 1
  exact h x y

attribute [-ext] hom_ext in
example {f g : X ⟶ Y} (h : ∀ x y, f.mass x y = g.mass x y) : f = g := by
  fail_if_success ext x y : 1
  exact hom_ext h

example (f : X ⟶ Y) (g : Y ⟶ Z) (x z) :
    (f ≫ g).mass x z = ∑ y, f.mass x y * g.mass y z := by
  simp

example (f : X.carrier → Y.carrier) (x y) :
    (Hom.ofFun f).mass x y = if f x = y then 1 else 0 := by
  simp

example (x y : X.carrier) : (𝟙 X : X ⟶ X).mass x y = if x = y then 1 else 0 := by
  simp

example : Hom.ofFun id = 𝟙 X := by
  simp

example (f : X.carrier → Y.carrier) (g : Y.carrier → Z.carrier) :
    (Hom.ofFun f ≫ Hom.ofFun g : X ⟶ Z) = Hom.ofFun (g ∘ f) := by
  simp

example (f : X ⟶ Y) (g : Y ⟶ Z) (x z) :
    (f ≫ g).mass x z = ∑ y, f.mass x y * g.mass y z := by
  fail_if_success simp [-comp_mass]
  simp

example (f : X.carrier → Y.carrier) (x y) :
    (Hom.ofFun f).mass x y = if f x = y then 1 else 0 := by
  fail_if_success simp [-ofFun_mass]
  simp

example (x y : X.carrier) : (𝟙 X : X ⟶ X).mass x y = if x = y then 1 else 0 := by
  fail_if_success simp [-id_mass]
  simp

example : Hom.ofFun id = 𝟙 X := by
  fail_if_success simp [-ofFun_id]
  simp

example (f : X.carrier → Y.carrier) (g : Y.carrier → Z.carrier) :
    (Hom.ofFun f ≫ Hom.ofFun g : X ⟶ Z) = Hom.ofFun (g ∘ f) := by
  fail_if_success simp [-ofFun_comp]
  simp

example (f : X.carrier → Y.carrier) (g : Y.carrier → Z.carrier) :
    (Hom.ofFun f ≫ Hom.ofFun g : X ⟶ Z) = Hom.ofFun (g ∘ f) := by
  fail_if_success exact (ofFun_comp f g : Hom.ofFun f ≫ Hom.ofFun g = Hom.ofFun (g ∘ f))
  exact ofFun_comp f g

example (x y : X.carrier) : (𝟙 X : X ⟶ X).mass x y = if x = y then 1 else 0 := by
  fail_if_success exact (id_mass x y : (𝟙 X).mass x y = if x = y then 1 else 0)
  exact id_mass x y

set_option linter.hashCommand false in
#guard
  let X : FinStoch := ⟨Bool⟩
  let f : X ⟶ X := ⟨fun _ y => if y then 1 / 3 else 2 / 3, fun _ => by
    rw [Fintype.sum_bool]
    norm_num⟩
  let g : X ⟶ X := Hom.ofFun not
  (f ≫ g).mass true true == 2 / 3 && (g ≫ f).mass true true == 1 / 3

end FinStoch
