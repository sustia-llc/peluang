/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Rat
public import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of finite sets and stochastic matrices

## Main definitions

* `FinStoch` - a finite type with decidable equality.
* `FinStoch.Hom` - a stochastic matrix with entries in `ℚ≥0`.
* `FinStoch.Hom.ofFun` - the stochastic matrix of a function.
* `FinStoch.instCategory` - identities and Chapman-Kolmogorov composition.

## Main results

* `FinStoch.comp_mass` - an entry of a composite is a sum over the middle object.
* `FinStoch.ofFun_id`, `FinStoch.ofFun_comp` - `Hom.ofFun` sends the identity function to the
  identity morphism and function composition to composition of morphisms.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020], Example 2.5 and Example 10.3.
-/

@[expose] public section

open CategoryTheory
open scoped NNRat

/-- A finite type with decidable equality, an object of the category of finite sets and stochastic
matrices (Fritz 2020, Example 2.5). -/
structure FinStoch where
  /-- The underlying type. -/
  carrier : Type
  /-- The finite enumeration of `carrier`. -/
  [fintype : Fintype carrier]
  /-- Decidable equality on `carrier`. -/
  [decEq : DecidableEq carrier]

namespace FinStoch

attribute [instance] fintype decEq

/-- A stochastic matrix from `X` to `Y` with entries in `ℚ≥0`. The entry `mass x y` is `f(y|x)`,
and each `sum_one x` sums over the target `Y` for the fixed source `x`. A product carrier is ordered
first factor major: after a fixed numbering of each factor, a Rust index `x * |Y| + y` is
`finProdFinEquiv (x, y)`. -/
@[ext] structure Hom (X Y : FinStoch) where
  /-- The entry `f(y|x)`. -/
  mass : X.carrier → Y.carrier → ℚ≥0
  /-- For each source `x`, the entries over all targets sum to `1`. -/
  sum_one : ∀ x, ∑ y, mass x y = 1

variable {X Y Z : FinStoch}

/-- The stochastic matrix of `f`: mass `1` at `f x` and `0` elsewhere. -/
def Hom.ofFun (f : X.carrier → Y.carrier) : Hom X Y where
  mass x y := if f x = y then 1 else 0
  sum_one x := by simp

/-- The Chapman-Kolmogorov product of two stochastic matrices. -/
protected def Hom.comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  mass x z := ∑ y, f.mass x y * g.mass y z
  sum_one x := by
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, g.sum_one, f.sum_one]

/-- `FinStoch` is a category with `𝟙 X = Hom.ofFun id` and Chapman-Kolmogorov composition. -/
instance : Category FinStoch where
  Hom := Hom
  id _ := Hom.ofFun id
  comp := Hom.comp
  id_comp f := by
    ext x y
    simp [Hom.comp, Hom.ofFun]
  comp_id f := by
    ext x y
    simp [Hom.comp, Hom.ofFun]
  assoc f g h := by
    ext x w
    simp only [Hom.comp, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]

-- WITNESS: none (extensionality; no engine meaning)
/-- Morphisms of `FinStoch` with equal entries are equal. -/
@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : ∀ x y, f.mass x y = g.mass x y) : f = g :=
  Hom.ext (funext fun x => funext (h x))

/-- An entry of `f ≫ g` is the sum over `y` of `f.mass x y * g.mass y z`. -/
@[simp]
theorem comp_mass (f : X ⟶ Y) (g : Y ⟶ Z) (x) (z) :
    (f ≫ g).mass x z = ∑ y, f.mass x y * g.mass y z :=
  rfl

-- WITNESS: none (unfolds Hom.ofFun; witnessed through ofFun_id and ofFun_comp)
/-- The entries of `Hom.ofFun f` are `1` at `f x` and `0` elsewhere. -/
@[simp]
theorem ofFun_mass (f : X.carrier → Y.carrier) (x) (y) :
    (Hom.ofFun f).mass x y = if f x = y then 1 else 0 :=
  rfl

-- WITNESS: none (unfolds the identity; witnessed through ofFun_id)
/-- The entries of `𝟙 X` are `1` on the diagonal and `0` elsewhere. -/
@[simp]
theorem id_mass (x y : X.carrier) : (𝟙 X : X ⟶ X).mass x y = if x = y then 1 else 0 :=
  rfl

/-- `Hom.ofFun` sends the identity function to the identity morphism. -/
@[simp]
theorem ofFun_id : Hom.ofFun id = 𝟙 X :=
  rfl

/-- `Hom.ofFun` sends `g ∘ f` to the composite of `Hom.ofFun f` and `Hom.ofFun g`. -/
@[simp]
theorem ofFun_comp (f : X.carrier → Y.carrier) (g : Y.carrier → Z.carrier) :
    (Hom.ofFun f ≫ Hom.ofFun g : X ⟶ Z) = Hom.ofFun (g ∘ f) := by
  ext x z : 1
  simp only [comp_mass, ofFun_mass, Function.comp_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end FinStoch
