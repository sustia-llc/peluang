/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Instances.FinStoch.InformationFlow
import PeluangLint

/-!
# Tests for `Peluang.Instances.FinStoch.InformationFlow`

The `CausalCategory FinStoch`, `RelativelyPositiveCategory FinStoch` and
`PositiveCategory FinStoch` instances that search finds; the `MarkovCategory` structure of each
against `FinStoch.instMarkovCategory`; the `MarkovCategory FinStoch` instance that search finds
against `FinStoch.instMarkovCategory`; `Deterministic f` for an isomorphism `f` of `FinStoch`;
and `exists_deterministic_comp_not_deterministic` and `exists_almostSurelyEq_comp_ne` applied
once each.
-/

public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory

namespace FinStoch

example : CausalCategory FinStoch :=
  inferInstance

example : RelativelyPositiveCategory FinStoch :=
  inferInstance

example : PositiveCategory FinStoch :=
  inferInstance

example : (inferInstance : CausalCategory FinStoch).toMarkovCategory =
    FinStoch.instMarkovCategory :=
  rfl

example : (inferInstance : RelativelyPositiveCategory FinStoch).toMarkovCategory =
    FinStoch.instMarkovCategory :=
  rfl

example : (inferInstance : PositiveCategory FinStoch).toMarkovCategory =
    FinStoch.instMarkovCategory :=
  rfl

example : (inferInstance : CausalCategory FinStoch).toMarkovCategory =
    FinStoch.instMarkovCategory := by
  with_reducible_and_instances rfl

example : (inferInstance : RelativelyPositiveCategory FinStoch).toMarkovCategory =
    FinStoch.instMarkovCategory := by
  with_reducible_and_instances rfl

example : (inferInstance : PositiveCategory FinStoch).toMarkovCategory =
    FinStoch.instMarkovCategory := by
  with_reducible_and_instances rfl

example : (inferInstance : MarkovCategory FinStoch) = FinStoch.instMarkovCategory :=
  rfl

example {X Y : FinStoch} (f : X ⟶ Y) [IsIso f] : Deterministic f :=
  inferInstance

example : ∃ (X Y Z : FinStoch) (f : X ⟶ Y) (g : Y ⟶ Z),
    Deterministic (f ≫ g) ∧ ¬ Deterministic f :=
  exists_deterministic_comp_not_deterministic

example : ∃ (A W X Y : FinStoch) (f : A ⟶ W) (g : W ⟶ X) (h₁ h₂ : X ⟶ Y),
    AlmostSurelyEq (f ≫ g) h₁ h₂ ∧ h₁ ≠ h₂ :=
  exists_almostSurelyEq_comp_ne

end FinStoch
