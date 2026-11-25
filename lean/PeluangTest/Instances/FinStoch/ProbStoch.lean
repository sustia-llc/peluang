/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.Instances.FinStoch.BayesianInverse
public import Peluang.Instances.FinStoch.Conditional
public import Peluang.Instances.FinStoch.ProbStoch
public import Peluang.ProbStoch.Coupling
public import Peluang.ProbStoch.Dagger
import PeluangLint

/-!
# Tests for `Peluang.Instances.FinStoch.ProbStoch`

The `Congruence (probStochRel FinStoch)`, `MonoidalCategory (ProbStoch FinStoch)`,
`SymmetricCategory (ProbStoch FinStoch)` and
`HomRel.IsStableUnderWhisker (probStochRel FinStoch)` instances that search finds;
`ProbStoch.dagger_dagger` applied to a morphism of `ProbStoch FinStoch`; `ProbStoch.dagger_map`
applied to morphisms `f : X ⟶ Y` and `g : Y ⟶ X` of `Under (𝟙_ FinStoch)` with
`g.right = bayesInv X.hom f.right`; `ProbStoch.homEquivCoupling X Y` as a term for objects `X Y`
of `Under (𝟙_ FinStoch)`; and `exists_ne_probStoch_map_eq` and `exists_probStoch_map_ne` applied
once each.
-/

public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory

namespace FinStoch

example : Congruence (probStochRel FinStoch) :=
  inferInstance

example : MonoidalCategory (ProbStoch FinStoch) :=
  inferInstance

example : SymmetricCategory (ProbStoch FinStoch) :=
  inferInstance

example : HomRel.IsStableUnderWhisker (probStochRel FinStoch) :=
  inferInstance

example {X Y : ProbStoch FinStoch} (f : X ⟶ Y) :
    ProbStoch.dagger (ProbStoch.dagger f) = f :=
  ProbStoch.dagger_dagger f

example {X Y : Under (𝟙_ FinStoch)} (f : X ⟶ Y) (g : Y ⟶ X)
    (hg : g.right = bayesInv X.hom f.right) :
    ProbStoch.dagger ((Quotient.functor (probStochRel FinStoch)).map f) =
      (Quotient.functor (probStochRel FinStoch)).map g :=
  ProbStoch.dagger_map f g (hg ▸ isBayesianInverse_bayesInv X.hom f.right)

noncomputable example (X Y : Under (𝟙_ FinStoch)) :=
  ProbStoch.homEquivCoupling X Y

example : ∃ (X Y : Under (𝟙_ FinStoch)) (f g : X ⟶ Y), f ≠ g ∧
    (Quotient.functor (probStochRel FinStoch)).map f =
      (Quotient.functor (probStochRel FinStoch)).map g :=
  exists_ne_probStoch_map_eq

example : ∃ (X Y : Under (𝟙_ FinStoch)) (f g : X ⟶ Y),
    (Quotient.functor (probStochRel FinStoch)).map f ≠
      (Quotient.functor (probStochRel FinStoch)).map g :=
  exists_probStoch_map_ne

end FinStoch
