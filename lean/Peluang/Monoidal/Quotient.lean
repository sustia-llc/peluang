/-
Copyright (c) 2026-present all contributors.
Released under the MIT license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Quotient

/-!
# The monoidal structure on a quotient of a monoidal category

For a monoidal category `D` and a relation `r : HomRel D` that both whiskerings preserve, the
quotient category `Quotient r` is monoidal. It is braided when `D` is braided, and symmetric
when `D` is symmetric.

## Main definitions

* `HomRel.IsStableUnderWhisker` - for a monoidal category `D`, a relation `r : HomRel D` is
  stable under whiskering when `r f g` gives `r (X ◁ f) (X ◁ g)` and `r (f ▷ Z) (g ▷ Z)`.
* `Quotient.monoidalCategoryStruct` - for a monoidal category `D` and a relation `r : HomRel D`
  stable under whiskering, the tensor product, unit, whiskerings, associator and unitors of
  `Quotient r`: the tensor product of `X` and `Y` is `⟨X.as ⊗ Y.as⟩`, and the unit is `⟨𝟙_ D⟩`.
* `Quotient.monoidalCategory` - for a monoidal category `D` and a relation `r : HomRel D`
  stable under whiskering, `Quotient r` is a monoidal category.
* `Quotient.braidedCategory` - for a braided monoidal category `D` and a relation
  `r : HomRel D` stable under whiskering, `Quotient r` is braided.
* `Quotient.symmetricCategory` - for a symmetric monoidal category `D` and a relation
  `r : HomRel D` stable under whiskering, `Quotient r` is symmetric.

## Main statements

* `Quotient.functor_map_tensorHom` - for a monoidal category `D`, a relation `r : HomRel D`
  stable under whiskering and morphisms `f` and `g` of `D`, `Quotient.functor r` sends `f ⊗ₘ g`
  to the tensor product of the images of `f` and `g`.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory

variable {D : Type u} [Category.{v} D] [MonoidalCategory.{v} D]

/-- For a monoidal category `D`, a relation `r : HomRel D` is stable under whiskering when
`r f g` gives `r (X ◁ f) (X ◁ g)` for each object `X` and `r (f ▷ Z) (g ▷ Z)` for each object
`Z`. -/
class HomRel.IsStableUnderWhisker (r : HomRel D) : Prop where
  /-- For an object `X` and morphisms `f` and `g` with `r f g`, `r (X ◁ f) (X ◁ g)`. -/
  whiskerLeft (X : D) {Y Z : D} {f g : Y ⟶ Z} : r f g → r (X ◁ f) (X ◁ g)
  /-- For morphisms `f` and `g` with `r f g` and an object `Z`, `r (f ▷ Z) (g ▷ Z)`. -/
  whiskerRight {X Y : D} {f g : X ⟶ Y} (Z : D) : r f g → r (f ▷ Z) (g ▷ Z)

namespace Quotient

variable (r : HomRel D) [HomRel.IsStableUnderWhisker r]

/-- For a monoidal category `D` and a relation `r : HomRel D` stable under whiskering, the
monoidal data of `Quotient r`: the tensor product of `X` and `Y` is `⟨X.as ⊗ Y.as⟩`, the unit
is `⟨𝟙_ D⟩`, the whiskerings send the class of `f` to the classes of `X.as ◁ f` and of
`f ▷ Y.as`, and the associator and the unitors are the images of those of `D` under
`Quotient.functor r`. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct (Quotient r) where
  tensorObj X Y := ⟨X.as ⊗ Y.as⟩
  whiskerLeft X _ _ f := (Quotient.lift r (tensorLeft X.as ⋙ functor r)
    (fun _ _ _ _ h => Quotient.sound r (HomRel.IsStableUnderWhisker.whiskerLeft X.as h))).map f
  whiskerRight f Y := (Quotient.lift r (tensorRight Y.as ⋙ functor r)
    (fun _ _ _ _ h => Quotient.sound r (HomRel.IsStableUnderWhisker.whiskerRight Y.as h))).map f
  tensorUnit := ⟨𝟙_ D⟩
  associator X Y Z := (functor r).mapIso (α_ X.as Y.as Z.as)
  leftUnitor X := (functor r).mapIso (λ_ X.as)
  rightUnitor X := (functor r).mapIso (ρ_ X.as)

/-- For a monoidal category `D` and a relation `r : HomRel D` stable under whiskering, the
quotient category `Quotient r` is monoidal. -/
instance monoidalCategory : MonoidalCategory (Quotient r) where
  tensorHom_def _ _ := rfl
  id_tensorHom_id X Y := congrArg (functor r).map
    (show 𝟙 X.as ▷ Y.as ≫ X.as ◁ 𝟙 Y.as = 𝟙 (X.as ⊗ Y.as) by simp)
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ := by
    obtain ⟨f₁⟩ := f₁
    obtain ⟨f₂⟩ := f₂
    obtain ⟨g₁⟩ := g₁
    obtain ⟨g₂⟩ := g₂
    exact congrArg (functor r).map
      (show (f₁ ▷ X₂.as ≫ Y₁.as ◁ f₂) ≫ (g₁ ▷ Y₂.as ≫ Z₁.as ◁ g₂) =
          (f₁ ≫ g₁) ▷ X₂.as ≫ Z₁.as ◁ (f₂ ≫ g₂) by
        simpa only [tensorHom_def] using MonoidalCategory.tensorHom_comp_tensorHom f₁ f₂ g₁ g₂)
  whiskerLeft_id X Y := congrArg (functor r).map (MonoidalCategory.whiskerLeft_id X.as Y.as)
  id_whiskerRight X Y := congrArg (functor r).map (MonoidalCategory.id_whiskerRight X.as Y.as)
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by
    obtain ⟨f₁⟩ := f₁
    obtain ⟨f₂⟩ := f₂
    obtain ⟨f₃⟩ := f₃
    exact congrArg (functor r).map
      (show ((f₁ ▷ X₂.as ≫ Y₁.as ◁ f₂) ▷ X₃.as ≫ (Y₁.as ⊗ Y₂.as) ◁ f₃) ≫
            (α_ Y₁.as Y₂.as Y₃.as).hom =
          (α_ X₁.as X₂.as X₃.as).hom ≫
            (f₁ ▷ (X₂.as ⊗ X₃.as) ≫ Y₁.as ◁ (f₂ ▷ X₃.as ≫ Y₂.as ◁ f₃)) by
        simpa only [tensorHom_def] using MonoidalCategory.associator_naturality f₁ f₂ f₃)
  leftUnitor_naturality f := by
    obtain ⟨f⟩ := f
    exact congrArg (functor r).map (MonoidalCategory.leftUnitor_naturality f)
  rightUnitor_naturality f := by
    obtain ⟨f⟩ := f
    exact congrArg (functor r).map (MonoidalCategory.rightUnitor_naturality f)
  pentagon W X Y Z := congrArg (functor r).map (MonoidalCategory.pentagon W.as X.as Y.as Z.as)
  triangle X Y := congrArg (functor r).map (MonoidalCategory.triangle X.as Y.as)

-- WITNESS: none (witnessed through ProbStoch.functor_map_tensorHom)
/-- For a monoidal category `D`, a relation `r : HomRel D` stable under whiskering and
morphisms `f : X ⟶ Y` and `g : X' ⟶ Y'` of `D`, `Quotient.functor r` sends `f ⊗ₘ g` to the
tensor product of the images of `f` and `g`. -/
theorem functor_map_tensorHom {X Y X' Y' : D} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (functor r).map (f ⊗ₘ g) = (functor r).map f ⊗ₘ (functor r).map g :=
  congrArg (functor r).map (MonoidalCategory.tensorHom_def f g)

/-- For a braided monoidal category `D` and a relation `r : HomRel D` stable under whiskering,
the quotient category `Quotient r` is braided: the braiding of `X` and `Y` is the image of
`β_ X.as Y.as` under `Quotient.functor r`. -/
instance braidedCategory [BraidedCategory D] : BraidedCategory (Quotient r) where
  braiding X Y := (functor r).mapIso (β_ X.as Y.as)
  braiding_naturality_right X _ _ f := by
    obtain ⟨f⟩ := f
    exact congrArg (functor r).map (BraidedCategory.braiding_naturality_right X.as f)
  braiding_naturality_left f Z := by
    obtain ⟨f⟩ := f
    exact congrArg (functor r).map (BraidedCategory.braiding_naturality_left f Z.as)
  hexagon_forward X Y Z :=
    congrArg (functor r).map (BraidedCategory.hexagon_forward X.as Y.as Z.as)
  hexagon_reverse X Y Z :=
    congrArg (functor r).map (BraidedCategory.hexagon_reverse X.as Y.as Z.as)

/-- For a symmetric monoidal category `D` and a relation `r : HomRel D` stable under
whiskering, the quotient category `Quotient r` is symmetric. -/
instance symmetricCategory [SymmetricCategory D] : SymmetricCategory (Quotient r) where
  symmetry X Y := congrArg (functor r).map (SymmetricCategory.symmetry X.as Y.as)

end Quotient

end CategoryTheory
