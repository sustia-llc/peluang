/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Prod
public import Peluang.Instances.FinStoch.Basic

/-!
# The monoidal and symmetric structure of `FinStoch`

## Main definitions

* `FinStoch.Hom.tensor` - the Kronecker product of two stochastic matrices.
* `FinStoch.isoOfEquiv` - the isomorphism of an equivalence of carriers.
* `FinStoch.instMonoidalCategory` - `X ⊗ Y` has carrier `X.carrier × Y.carrier` and the unit has
  carrier `PUnit`.
* `FinStoch.instSymmetricCategory` - the braiding is `Hom.ofFun Prod.swap`.

## Main results

* `FinStoch.tensorHom_mass` - an entry of `f ⊗ₘ g` is the product of the entries of `f` and `g`.
* `FinStoch.tensorHom_ofFun`, `FinStoch.whiskerLeft_ofFun`, `FinStoch.whiskerRight_ofFun` - a
  tensor or whisker of `Hom.ofFun` is `Hom.ofFun` of `Prod.map`.
* `FinStoch.braiding_eq_ofFun` - the braiding is `Hom.ofFun Prod.swap`.

## References

* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020], Example 2.5.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped NNRat

namespace FinStoch

variable {A B C D X Y Z : FinStoch}

/-- The Kronecker product of `f` and `g`, on the products of the carriers. -/
protected def Hom.tensor (f : Hom A B) (g : Hom C D) :
    Hom ⟨A.carrier × C.carrier⟩ ⟨B.carrier × D.carrier⟩ where
  mass p q := f.mass p.1 q.1 * g.mass p.2 q.2
  sum_one p := by
    change ∑ q : B.carrier × D.carrier, f.mass p.1 q.1 * g.mass p.2 q.2 = 1
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, f.sum_one, g.sum_one]

/-- The isomorphism `X ≅ Y` with `hom = Hom.ofFun e` and `inv = Hom.ofFun e.symm`, for an
equivalence `e` of the carriers. -/
def isoOfEquiv (e : X.carrier ≃ Y.carrier) : X ≅ Y where
  hom := Hom.ofFun e
  inv := Hom.ofFun e.symm
  hom_inv_id := by rw [ofFun_comp, e.symm_comp_self, ofFun_id]
  inv_hom_id := by rw [ofFun_comp, e.self_comp_symm, ofFun_id]

-- WITNESS: none (unfolds isoOfEquiv; no engine meaning)
/-- The forward map of `isoOfEquiv e` is `Hom.ofFun e`. -/
theorem isoOfEquiv_hom (e : X.carrier ≃ Y.carrier) : (isoOfEquiv e).hom = Hom.ofFun e :=
  rfl

/-- The tensor product on `FinStoch`: `X ⊗ Y` has carrier `X.carrier × Y.carrier`, the unit has
carrier `PUnit`, `⊗ₘ` is `Hom.tensor`, and the associator and unitors are `isoOfEquiv`. -/
instance : MonoidalCategoryStruct FinStoch where
  tensorObj X Y := ⟨X.carrier × Y.carrier⟩
  tensorUnit := ⟨PUnit⟩
  tensorHom f g := Hom.tensor f g
  whiskerLeft X _ _ f := Hom.tensor (𝟙 X) f
  whiskerRight f X := Hom.tensor f (𝟙 X)
  associator _ _ _ := isoOfEquiv (Equiv.prodAssoc _ _ _)
  leftUnitor _ := isoOfEquiv (Equiv.punitProd _)
  rightUnitor _ := isoOfEquiv (Equiv.prodPUnit _)

/-- An entry of `f ⊗ₘ g` at `(a, c)` and `(b, d)` is `f.mass a b * g.mass c d`. -/
@[simp]
theorem tensorHom_mass (f : A ⟶ B) (g : C ⟶ D) (a c) (b d) :
    (f ⊗ₘ g).mass (a, c) (b, d) = f.mass a b * g.mass c d :=
  rfl

-- WITNESS: none (structural step; witnessed through CategoryTheory.Deterministic.instTensorHom)
/-- `Hom.ofFun f ⊗ₘ Hom.ofFun g` is `Hom.ofFun (Prod.map f g)`. -/
@[simp]
theorem tensorHom_ofFun (f : A.carrier → B.carrier) (g : C.carrier → D.carrier) :
    (Hom.ofFun f ⊗ₘ Hom.ofFun g : A ⊗ C ⟶ B ⊗ D) = Hom.ofFun (Prod.map f g) := by
  ext ⟨a, c⟩ ⟨b, d⟩ : 1
  have h : (((f a, g c) : (B ⊗ D).carrier) = (b, d)) ↔ f a = b ∧ g c = d := Prod.mk_inj
  simp only [tensorHom_mass, ofFun_mass, Prod.map_apply, h, ite_and]
  split_ifs <;> simp

-- WITNESS: none (structural step; witnessed through CategoryTheory.Deterministic.instWhiskerLeft)
/-- `X ◁ Hom.ofFun f` is `Hom.ofFun (Prod.map id f)`. -/
@[simp]
theorem whiskerLeft_ofFun (X : FinStoch) (f : A.carrier → B.carrier) :
    (X ◁ Hom.ofFun f : X ⊗ A ⟶ X ⊗ B) = Hom.ofFun (Prod.map id f) :=
  tensorHom_ofFun id f

-- WITNESS: none (structural step; witnessed through CategoryTheory.Deterministic.instWhiskerRight)
/-- `Hom.ofFun f ▷ X` is `Hom.ofFun (Prod.map f id)`. -/
@[simp]
theorem whiskerRight_ofFun (f : A.carrier → B.carrier) (X : FinStoch) :
    (Hom.ofFun f ▷ X : A ⊗ X ⟶ B ⊗ X) = Hom.ofFun (Prod.map f id) :=
  tensorHom_ofFun f id

-- WITNESS: none (unfolds the associator; no engine meaning)
/-- `(α_ X Y Z).hom` is `Hom.ofFun` of `((x, y), z) ↦ (x, y, z)`. -/
theorem associator_hom_eq_ofFun (X Y Z : FinStoch) :
    (α_ X Y Z).hom =
      Hom.ofFun fun p : (X.carrier × Y.carrier) × Z.carrier => (p.1.1, p.1.2, p.2) :=
  rfl

-- WITNESS: none (unfolds the associator; no engine meaning)
/-- `(α_ X Y Z).inv` is `Hom.ofFun` of `(x, y, z) ↦ ((x, y), z)`. -/
theorem associator_inv_eq_ofFun (X Y Z : FinStoch) :
    (α_ X Y Z).inv =
      Hom.ofFun fun p : X.carrier × Y.carrier × Z.carrier => ((p.1, p.2.1), p.2.2) :=
  rfl

-- WITNESS: none (unfolds the left unitor; no engine meaning)
/-- `(λ_ X).hom` is `Hom.ofFun Prod.snd`. -/
theorem leftUnitor_hom_eq_ofFun (X : FinStoch) : (λ_ X).hom = Hom.ofFun Prod.snd :=
  rfl

-- WITNESS: none (unfolds the right unitor; no engine meaning)
/-- `(ρ_ X).hom` is `Hom.ofFun Prod.fst`. -/
theorem rightUnitor_hom_eq_ofFun (X : FinStoch) : (ρ_ X).hom = Hom.ofFun Prod.fst :=
  rfl

-- WITNESS: none (reindexing step; no engine meaning)
/-- A sum over `(X ⊗ Y).carrier` is the iterated sum over `X.carrier` and `Y.carrier`. -/
theorem sum_tensor (h : (X ⊗ Y).carrier → ℚ≥0) : ∑ p, h p = ∑ x, ∑ y, h (x, y) :=
  Fintype.sum_prod_type h

-- WITNESS: none (entry step; witnessed through ofFun_comp)
/-- An entry of `Hom.ofFun f ≫ g` at `x` is the entry of `g` at `f x`. -/
theorem ofFun_comp_mass (f : X.carrier → Y.carrier) (g : Y ⟶ Z) (x z) :
    (Hom.ofFun f ≫ g : X ⟶ Z).mass x z = g.mass (f x) z := by
  simp

-- WITNESS: none (entry step; witnessed through ofFun_comp)
/-- For an equivalence `e`, an entry of `f ≫ Hom.ofFun e` at `z` is the entry of `f` at
`e.symm z`. -/
theorem comp_ofFun_mass (f : X ⟶ Y) (e : Y.carrier ≃ Z.carrier) (x z) :
    (f ≫ Hom.ofFun e : X ⟶ Z).mass x z = f.mass x (e.symm z) := by
  simp [← e.eq_symm_apply]

-- WITNESS: none (entry step; no engine meaning)
/-- For equivalences `e` and `e'` of carriers, the entries of `f ≫ (isoOfEquiv e').hom` and
`(isoOfEquiv e).hom ≫ g` at `a` and `d` agree when `f.mass a (e'.symm d) = g.mass (e a) d`. -/
theorem comp_isoOfEquiv_hom_mass_eq (f : A ⟶ B) (e' : B.carrier ≃ D.carrier)
    (e : A.carrier ≃ C.carrier) (g : C ⟶ D) {a : A.carrier} {d : D.carrier}
    (h : f.mass a (e'.symm d) = g.mass (e a) d) :
    (f ≫ (isoOfEquiv e').hom : A ⟶ D).mass a d = ((isoOfEquiv e).hom ≫ g : A ⟶ D).mass a d := by
  rw [isoOfEquiv_hom, isoOfEquiv_hom, ofFun_comp_mass, comp_ofFun_mass, h]

-- WITNESS: none (Mathlib tensorHom_comp_tensorHom at the instance)
/-- `⊗ₘ` sends a pair of composites to the composite of the tensors. -/
protected theorem tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : FinStoch} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  ext ⟨a, c⟩ ⟨e, k⟩ : 1
  simp only [comp_mass, tensorHom_mass, sum_tensor, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_mul_mul_comm ..

/-- `FinStoch` is a monoidal category. -/
instance : MonoidalCategory FinStoch where
  tensorHom_def {_ _ _ _} f g := by
    change _ = (f ⊗ₘ 𝟙 _) ≫ (𝟙 _ ⊗ₘ g)
    rw [FinStoch.tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  id_tensorHom_id _ _ := tensorHom_ofFun id id
  tensorHom_comp_tensorHom := FinStoch.tensorHom_comp_tensorHom
  whiskerLeft_id _ _ := tensorHom_ofFun id id
  id_whiskerRight _ _ := tensorHom_ofFun id id
  associator_naturality {_ _ _ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by
    ext ⟨⟨a, b⟩, c⟩ ⟨d, e, k⟩ : 1
    refine comp_isoOfEquiv_hom_mass_eq _ _ _ _ ?_
    exact mul_assoc _ _ _
  leftUnitor_naturality {X Y} f := by
    ext ⟨⟨⟩, a⟩ b : 1
    refine comp_isoOfEquiv_hom_mass_eq _ _ _ _ ?_
    change (𝟙 (𝟙_ FinStoch) ⊗ₘ f).mass (PUnit.unit, a) (PUnit.unit, b) = f.mass a b
    simp
  rightUnitor_naturality {X Y} f := by
    ext ⟨a, ⟨⟩⟩ b : 1
    refine comp_isoOfEquiv_hom_mass_eq _ _ _ _ ?_
    change (f ⊗ₘ 𝟙 (𝟙_ FinStoch)).mass (a, PUnit.unit) (b, PUnit.unit) = f.mass a b
    simp
  pentagon W X Y Z := by
    simp only [associator_hom_eq_ofFun, whiskerRight_ofFun, whiskerLeft_ofFun, ofFun_comp]
    rfl
  triangle X Y := by
    simp only [associator_hom_eq_ofFun, leftUnitor_hom_eq_ofFun, rightUnitor_hom_eq_ofFun,
      whiskerRight_ofFun, whiskerLeft_ofFun, ofFun_comp]
    rfl

/-- `FinStoch` is a symmetric monoidal category with `(β_ X Y).hom = Hom.ofFun Prod.swap`. -/
instance : SymmetricCategory FinStoch where
  braiding _ _ := isoOfEquiv (Equiv.prodComm _ _)
  braiding_naturality_right X Y Z f := by
    ext ⟨a, b⟩ ⟨c, d⟩ : 1
    rw [isoOfEquiv_hom, isoOfEquiv_hom, ofFun_comp_mass, comp_ofFun_mass]
    exact mul_comm _ _
  braiding_naturality_left f Z := by
    ext ⟨a, b⟩ ⟨c, d⟩ : 1
    rw [isoOfEquiv_hom, isoOfEquiv_hom, ofFun_comp_mass, comp_ofFun_mass]
    exact mul_comm _ _
  hexagon_forward X Y Z := by
    simp only [isoOfEquiv_hom, associator_hom_eq_ofFun, whiskerRight_ofFun, whiskerLeft_ofFun,
      ofFun_comp]
    rfl
  hexagon_reverse X Y Z := by
    simp only [isoOfEquiv_hom, associator_inv_eq_ofFun, whiskerRight_ofFun, whiskerLeft_ofFun,
      ofFun_comp]
    rfl
  symmetry X Y := by
    simp only [isoOfEquiv_hom, ofFun_comp]
    rfl

/-- `(β_ X Y).hom` is `Hom.ofFun Prod.swap`. -/
theorem braiding_eq_ofFun : (β_ X Y).hom = Hom.ofFun Prod.swap :=
  rfl

end FinStoch
