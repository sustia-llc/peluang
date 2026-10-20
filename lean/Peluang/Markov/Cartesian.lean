/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Cartesian
public import Mathlib.CategoryTheory.MarkovCategory.Basic

/-!
# Cartesian monoidal categories are Markov categories

A braided cartesian monoidal category, with the diagonal as copy and the unique
map to the terminal unit as discard, is a Markov category (Fritz 2020,
Remark 2.4).

## Main definitions

* `MarkovCategory.ofCartesianMonoidalCategory` - the Markov category structure
  on a braided cartesian monoidal category, for use as a local instance.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]
-/

public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] CartesianCopyDiscard.instComonObjOfCartesian
  CartesianCopyDiscard.ofCartesianMonoidalCategory

/-- A braided cartesian monoidal category is a Markov category, with the copy-discard
structure `CartesianCopyDiscard.ofCartesianMonoidalCategory` (Fritz 2020, Remark 2.4),
for use as a local instance. -/
abbrev MarkovCategory.ofCartesianMonoidalCategory [CartesianMonoidalCategory.{v} C]
    [BraidedCategory C] : MarkovCategory C where
  discard_natural _ := CartesianMonoidalCategory.toUnit_unique _ _

end CategoryTheory
