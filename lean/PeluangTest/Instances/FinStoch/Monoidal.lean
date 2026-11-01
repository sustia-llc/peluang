/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Instances.FinStoch.Monoidal
meta import Peluang.Instances.FinStoch.Monoidal
import Mathlib.Tactic.NormNum
import PeluangLint

/-!
# Tests for `Peluang.Instances.FinStoch.Monoidal`

Instance search for the monoidal classes and for `Fintype` and `DecidableEq` on tensor carriers,
each `simp` lemma on its own statement and its failure without that lemma, each associator, unitor
and braiding map in both directions as `Hom.ofFun`, the forms that need a type ascription to
elaborate, and values of tensors and braidings in `ℚ≥0` by `#guard`.
-/

public section

open CategoryTheory MonoidalCategory
open scoped NNRat

namespace FinStoch

variable {A B C D X Y Z : FinStoch}

example : MonoidalCategoryStruct FinStoch := inferInstance

example : MonoidalCategory FinStoch := inferInstance

example : BraidedCategory FinStoch := inferInstance

example : SymmetricCategory FinStoch := inferInstance

example (X Y : FinStoch) : Fintype (X ⊗ Y).carrier := inferInstance

example (X Y : FinStoch) : DecidableEq (X ⊗ Y).carrier := inferInstance

example (X Y Z : FinStoch) : Fintype ((X ⊗ Y) ⊗ Z).carrier := inferInstance

example (X Y Z : FinStoch) : DecidableEq ((X ⊗ Y) ⊗ Z).carrier := inferInstance

example (X Y Z : FinStoch) : Fintype (X ⊗ Y ⊗ Z).carrier := inferInstance

example (X Y Z : FinStoch) : DecidableEq (X ⊗ Y ⊗ Z).carrier := inferInstance

example : Fintype (𝟙_ FinStoch).carrier := inferInstance

example : DecidableEq (𝟙_ FinStoch).carrier := inferInstance

example (X : FinStoch) : Fintype (𝟙_ FinStoch ⊗ X).carrier := inferInstance

example (X : FinStoch) : DecidableEq (X ⊗ 𝟙_ FinStoch).carrier := inferInstance

example (X Y : FinStoch) :
    (inferInstance : Fintype (X ⊗ Y).carrier) = (inferInstance : Fintype (X.carrier × Y.carrier)) :=
  rfl

example (X Y : FinStoch) :
    (inferInstance : DecidableEq (X ⊗ Y).carrier) =
      (inferInstance : DecidableEq (X.carrier × Y.carrier)) :=
  rfl

example (f : A ⟶ B) (g : C ⟶ D) (a c) (b d) :
    (f ⊗ₘ g).mass (a, c) (b, d) = f.mass a b * g.mass c d := by
  simp

example (f : A ⟶ B) (g : C ⟶ D) (a c) (b d) :
    (f ⊗ₘ g).mass (a, c) (b, d) = f.mass a b * g.mass c d := by
  fail_if_success simp [-tensorHom_mass]
  simp

example (f : A.carrier → B.carrier) (g : C.carrier → D.carrier) :
    (Hom.ofFun f ⊗ₘ Hom.ofFun g : A ⊗ C ⟶ B ⊗ D) = Hom.ofFun (Prod.map f g) := by
  simp

example (f : A.carrier → B.carrier) (g : C.carrier → D.carrier) :
    (Hom.ofFun f ⊗ₘ Hom.ofFun g : A ⊗ C ⟶ B ⊗ D) = Hom.ofFun (Prod.map f g) := by
  fail_if_success simp [-tensorHom_ofFun]
  simp

example (X : FinStoch) (f : A.carrier → B.carrier) :
    (X ◁ Hom.ofFun f : X ⊗ A ⟶ X ⊗ B) = Hom.ofFun (Prod.map id f) := by
  simp

example (X : FinStoch) (f : A.carrier → B.carrier) :
    (X ◁ Hom.ofFun f : X ⊗ A ⟶ X ⊗ B) = Hom.ofFun (Prod.map id f) := by
  fail_if_success simp [-whiskerLeft_ofFun]
  simp

example (f : A.carrier → B.carrier) (X : FinStoch) :
    (Hom.ofFun f ▷ X : A ⊗ X ⟶ B ⊗ X) = Hom.ofFun (Prod.map f id) := by
  simp

example (f : A.carrier → B.carrier) (X : FinStoch) :
    (Hom.ofFun f ▷ X : A ⊗ X ⟶ B ⊗ X) = Hom.ofFun (Prod.map f id) := by
  fail_if_success simp [-whiskerRight_ofFun]
  simp

example (X Y Z : FinStoch) :
    (α_ X Y Z).hom =
      Hom.ofFun fun p : (X.carrier × Y.carrier) × Z.carrier => (p.1.1, p.1.2, p.2) :=
  rfl

example (X Y Z : FinStoch) :
    (α_ X Y Z).inv =
      Hom.ofFun fun p : X.carrier × Y.carrier × Z.carrier => ((p.1, p.2.1), p.2.2) :=
  rfl

example (X : FinStoch) : (λ_ X).hom = Hom.ofFun Prod.snd :=
  rfl

example (X : FinStoch) : (λ_ X).inv = Hom.ofFun fun x : X.carrier => (PUnit.unit, x) :=
  rfl

example (X : FinStoch) : (ρ_ X).hom = Hom.ofFun Prod.fst :=
  rfl

example (X : FinStoch) : (ρ_ X).inv = Hom.ofFun fun x : X.carrier => (x, PUnit.unit) :=
  rfl

example : (β_ X Y).hom = Hom.ofFun Prod.swap :=
  rfl

example : (β_ X Y).inv = Hom.ofFun Prod.swap :=
  rfl

example (f : A ⟶ B) (g : C ⟶ D) (a c) (b d) :
    (f ⊗ₘ g).mass (a, c) (b, d) = f.mass a b * g.mass c d :=
  tensorHom_mass f g a c b d

example (f : A.carrier → B.carrier) (g : C.carrier → D.carrier) :
    (Hom.ofFun f ⊗ₘ Hom.ofFun g : A ⊗ C ⟶ B ⊗ D) = Hom.ofFun (Prod.map f g) := by
  fail_if_success
    exact (tensorHom_ofFun f g : Hom.ofFun f ⊗ₘ Hom.ofFun g = Hom.ofFun (Prod.map f g))
  exact tensorHom_ofFun f g

example (a c : (𝟙_ FinStoch).carrier) : a = c :=
  rfl

example (a b : A.carrier) (c d : C.carrier) (h : ((a, c) : (A ⊗ C).carrier) = (b, d)) : a = b := by
  fail_if_success simpa using h
  exact (Prod.mk_inj.mp h).1

set_option linter.hashCommand false in
#guard
  let X : FinStoch := ⟨Bool⟩
  let f : X ⟶ X := ⟨fun _ y => if y then 1 / 3 else 2 / 3, fun _ => by
    rw [Fintype.sum_bool]
    norm_num⟩
  let g : X ⟶ X := Hom.ofFun not
  (f ⊗ₘ g).mass (true, true) (true, false) == 1 / 3 &&
    (f ⊗ₘ g).mass (true, true) (false, false) == 2 / 3 &&
    (f ⊗ₘ g).mass (true, true) (true, true) == 0

set_option linter.hashCommand false in
#guard
  let X : FinStoch := ⟨Bool⟩
  (β_ X X).hom.mass (true, false) (false, true) == 1 &&
    (β_ X X).hom.mass (true, false) (true, false) == 0

end FinStoch
