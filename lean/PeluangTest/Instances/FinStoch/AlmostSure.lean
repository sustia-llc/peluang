/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Instances.FinStoch.AlmostSure
import PeluangLint

/-!
# Tests for `Peluang.Instances.FinStoch.AlmostSure`

`copy_comp_whiskerRight_mass` and `almostSurelyEq_iff` each applied once, and the reverse
direction of `almostSurelyEq_iff` on `FinStoch.mk Bool`: for `p` the point `true`, `𝟙` and the
constant `true` are `p`-almost surely equal.
-/

public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory

namespace FinStoch

variable {A X Y : FinStoch}

example (p : A ⟶ X) (f : X ⟶ Y) (a y x) :
    (p ≫ Δ[X] ≫ (f ▷ X)).mass a (y, x) = p.mass a x * f.mass x y :=
  copy_comp_whiskerRight_mass p f a y x

example (p : A ⟶ X) (f g : X ⟶ Y) (h : AlmostSurelyEq p f g) (a x) (hp : p.mass a x ≠ 0) (y) :
    f.mass x y = g.mass x y :=
  (almostSurelyEq_iff p f g).mp h a x hp y

example :
    AlmostSurelyEq (Hom.ofFun fun _ => true : 𝟙_ FinStoch ⟶ FinStoch.mk Bool)
      (𝟙 (FinStoch.mk Bool)) (Hom.ofFun fun _ => true) := by
  refine (almostSurelyEq_iff _ _ _).mpr fun a x hp y => ?_
  cases x <;> simp_all [ofFun_mass, id_mass]

end FinStoch
