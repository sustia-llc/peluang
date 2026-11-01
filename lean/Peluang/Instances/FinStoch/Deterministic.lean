/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic
public import Mathlib.Data.Fintype.Inv
public import Peluang.Instances.FinStoch.Markov
import Mathlib.Tactic.NormNum

/-!
# Deterministic morphisms of `FinStoch`

## Main definitions

* `FinStoch.detHomEquiv` - the deterministic morphisms `X ⟶ Y` are in bijection with the functions
  `X.carrier → Y.carrier`.
* `FinStoch.boolObj` - the object with carrier `Bool`.
* `FinStoch.bernoulli` - the state of `boolObj` with mass `1/2` at each point.

## Main results

* `FinStoch.deterministic_iff_mass` - a morphism is deterministic exactly when each entry is `0` or
  `1`.
* `FinStoch.deterministic_iff_exists_ofFun` - a morphism is deterministic exactly when it is
  `Hom.ofFun` of a function.
* `FinStoch.not_deterministic_bernoulli` - `bernoulli` is not deterministic.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020], Definition 10.1 and Example 10.3.
-/

@[expose] public section

open CategoryTheory MonoidalCategory ComonObj
open scoped NNRat

namespace FinStoch

variable {X Y : FinStoch}

-- WITNESS: none (structural step; witnessed through deterministic_iff_exists_ofFun)
/-- `Hom.ofFun g` is deterministic. -/
theorem deterministic_ofFun (g : X.carrier → Y.carrier) :
    Deterministic (C := FinStoch) (X := X) (Y := Y) (Hom.ofFun g) where
  hom_counit := by
    simp only [discard_eq_ofFun, ofFun_comp]
    rfl
  hom_comul := by
    simp only [copy_eq_ofFun, tensorHom_ofFun, ofFun_comp]
    rfl

-- WITNESS: none (structural step; witnessed through deterministic_iff_mass)
/-- If each entry of `f` is `0` or `1`, then for each `x` exactly one `y` has `f.mass x y = 1`. -/
theorem existsUnique_mass_eq_one (f : X ⟶ Y) (h : ∀ x y, f.mass x y = 0 ∨ f.mass x y = 1)
    (x : X.carrier) : ∃! y, f.mass x y = 1 := by
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := f.mass x) (by rw [f.sum_one]; exact one_ne_zero)
  refine ⟨y, (h x y).resolve_left hy, fun y' hy' => ?_⟩
  by_contra hne
  have hle : ∑ z ∈ {y', y}, f.mass x z ≤ ∑ z, f.mass x z :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair hne, f.sum_one, hy', (h x y).resolve_left hy] at hle
  norm_num at hle

-- WITNESS: none (structural step; witnessed through deterministic_iff_exists_ofFun)
/-- If each entry of `f` is `0` or `1`, then `f` is `Hom.ofFun` of the function that sends `x` to
the unique `y` with `f.mass x y = 1`. -/
theorem eq_ofFun_choose (f : X ⟶ Y) (h : ∀ x y, f.mass x y = 0 ∨ f.mass x y = 1) :
    f = Hom.ofFun fun x =>
      Fintype.choose (fun y => f.mass x y = 1) (existsUnique_mass_eq_one f h x) := by
  ext x y : 1
  have hc := Fintype.choose_spec (fun y => f.mass x y = 1) (existsUnique_mass_eq_one f h x)
  rw [ofFun_mass]
  split_ifs with e
  · rwa [← e]
  · exact (h x y).resolve_right fun hy => e ((existsUnique_mass_eq_one f h x).unique hc hy)

/-- A morphism of `FinStoch` is deterministic exactly when each of its entries is `0` or `1`
(Fritz 2020, Example 10.3). -/
theorem deterministic_iff_mass (f : X ⟶ Y) :
    Deterministic f ↔ ∀ x y, f.mass x y = 0 ∨ f.mass x y = 1 := by
  constructor
  · intro h x y
    have key := congrArg (fun k : X ⟶ Y ⊗ Y => k.mass x (y, y)) (IsComonHom.hom_comul f)
    have e (y' : Y.carrier) : (((y', y') : (Y ⊗ Y).carrier) = (y, y)) ↔ y' = y :=
      Prod.mk_inj.trans and_self_iff
    simp only [copy_eq_ofFun, ofFun_comp_mass] at key
    simp only [comp_mass, ofFun_mass, e, tensorHom_mass, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at key
    exact IsIdempotentElem.iff_eq_zero_or_one.1 key.symm
  · intro h
    rw [eq_ofFun_choose f h]
    exact deterministic_ofFun _

/-- A morphism of `FinStoch` is deterministic exactly when it is `Hom.ofFun` of a function
(Fritz 2020, Example 10.3). -/
theorem deterministic_iff_exists_ofFun (f : X ⟶ Y) :
    Deterministic f ↔ ∃ g, f = Hom.ofFun g :=
  ⟨fun h => ⟨_, eq_ofFun_choose f ((deterministic_iff_mass f).1 h)⟩,
    fun ⟨g, hg⟩ => hg ▸ deterministic_ofFun g⟩

/-- The deterministic morphisms `X ⟶ Y` are in bijection with the functions
`X.carrier → Y.carrier`: `g` goes to `Hom.ofFun g`, and `f` goes to the function that sends `x` to
the unique `y` with `f.mass x y = 1` (Fritz 2020, Example 10.3). -/
def detHomEquiv : { f : X ⟶ Y // Deterministic f } ≃ (X.carrier → Y.carrier) where
  toFun f x := Fintype.choose (fun y => f.1.mass x y = 1)
    (existsUnique_mass_eq_one f.1 ((deterministic_iff_mass f.1).1 f.2) x)
  invFun g := ⟨Hom.ofFun g, deterministic_ofFun g⟩
  left_inv f := Subtype.ext (eq_ofFun_choose f.1 ((deterministic_iff_mass f.1).1 f.2)).symm
  right_inv g := by
    funext x
    have h := (deterministic_iff_mass _).1 (deterministic_ofFun g)
    exact (existsUnique_mass_eq_one _ h x).unique
      (Fintype.choose_spec (fun y => (Hom.ofFun g : X ⟶ Y).mass x y = 1) _) (by simp)

/-- The object of `FinStoch` with carrier `Bool`. -/
def boolObj : FinStoch :=
  ⟨Bool⟩

/-- The state of `boolObj` with mass `1/2` at each of `true` and `false`. -/
def bernoulli : 𝟙_ FinStoch ⟶ boolObj :=
  Hom.mk (fun _ _ => 1 / 2) fun _ => by
    change ∑ _b : Bool, (1 / 2 : ℚ≥0) = 1
    rw [Fintype.sum_bool]
    norm_num

/-- `bernoulli` is not deterministic (Fritz 2020, Definition 10.1). -/
theorem not_deterministic_bernoulli : ¬ Deterministic bernoulli := fun h => by
  have key := (deterministic_iff_mass bernoulli).1 h PUnit.unit true
  change (1 / 2 : ℚ≥0) = 0 ∨ (1 / 2 : ℚ≥0) = 1 at key
  norm_num at key

end FinStoch
