/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Peluang.AlmostSure
public import Peluang.Instances.FinStoch.Markov

/-!
# Almost-sure equality in `FinStoch`

## Main results

* `FinStoch.copy_comp_whiskerRight_mass` - the entries of `p ≫ Δ[X] ≫ (f ▷ X)`.
* `FinStoch.almostSurelyEq_iff` - `f` and `g` are `p`-almost surely equal iff
  `f.mass x = g.mass x` at every `x` with `p.mass a x ≠ 0` for some `a`.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020], Def. 13.1, Example 13.2.
-/

@[expose] public section

open CategoryTheory MonoidalCategory ComonObj CopyDiscardCategory

namespace FinStoch

variable {A X Y : FinStoch}

/-- For `p : A ⟶ X` and `f : X ⟶ Y`, the entry of `p ≫ Δ[X] ≫ (f ▷ X)` at input `a` and output
`(y, x)` is `p.mass a x * f.mass x y` (Fritz 2020, Def. 13.1). -/
theorem copy_comp_whiskerRight_mass (p : A ⟶ X) (f : X ⟶ Y) (a y x) :
    (p ≫ Δ[X] ≫ (f ▷ X)).mass a (y, x) = p.mass a x * f.mass x y := by
  rw [copy_eq_ofFun, comp_mass]
  simp only [ofFun_comp_mass]
  change ∑ x₁, p.mass a x₁ * (f.mass x₁ y * (if x₁ = x then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero]
  simp

/-- For `p : A ⟶ X` and `f g : X ⟶ Y`, `f` and `g` are `p`-almost surely equal iff
`f.mass x y = g.mass x y` for every `y` and every `x` with `p.mass a x ≠ 0` for some `a`
(Fritz 2020, Example 13.2). -/
theorem almostSurelyEq_iff (p : A ⟶ X) (f g : X ⟶ Y) :
    AlmostSurelyEq p f g ↔ ∀ a x, p.mass a x ≠ 0 → ∀ y, f.mass x y = g.mass x y := by
  constructor
  · intro h a x hp y
    have := congrArg (fun k : A ⟶ Y ⊗ X => k.mass a (y, x)) h
    simp only [copy_comp_whiskerRight_mass] at this
    exact mul_left_cancel₀ hp this
  · intro h
    ext a ⟨y, x⟩ : 1
    rw [copy_comp_whiskerRight_mass, copy_comp_whiskerRight_mass]
    by_cases hp : p.mass a x = 0
    · simp [hp]
    · rw [h a x hp y]

end FinStoch
