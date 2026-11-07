/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat.Op

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Subdivision/Basic.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The subdivision category

Objects are arrows `A ⟶ B`. A morphism from `i : A ⟶ B` to `j : A' ⟶ B'`
is a pair `h : A' ⟶ A`, `k : B ⟶ B'` satisfying `h ≫ i ≫ k = j`.
The existing Grothendieck construction on `B ↦ (Over B)ᵒᵖ` supplies the category
laws, so this does not introduce a competing category structure on arrows.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory Opposite
namespace CategoryTheory

/-- Grayson's subdivision, expressed using the existing strict Grothendieck construction. -/
abbrev Subdivision (C : Type u) [Category.{v} C] :=
  Grothendieck (Over.mapFunctor C ⋙ Cat.opFunctor)

namespace Subdivision
variable {C : Type u} [Category.{v} C]

/-- An arrow as a subdivision object. -/
def of {A B : C} (i : A ⟶ B) : Subdivision C := ⟨B, op (Over.mk i)⟩

/-- The projection to the codomain of the represented arrow. -/
def codomain : Subdivision C ⥤ C := Grothendieck.forget _

/-- A commuting factorization gives an actual subdivision morphism. -/
def mkHom {A B A' B' : C} {i : A ⟶ B} {j : A' ⟶ B'}
    (h : A' ⟶ A) (k : B ⟶ B') (w : h ≫ i ≫ k = j) : of i ⟶ of j :=
  ⟨k, (Over.homMk h w).op⟩

/-- The reversed-domain component of a subdivision arrow. -/
def domainMap {X Y : Subdivision C} (f : X ⟶ Y) :
    Y.fiber.unop.left ⟶ X.fiber.unop.left := f.fiber.unop.left

/-- The factorization square is part of every actual subdivision morphism. -/
theorem factorization {X Y : Subdivision C} (f : X ⟶ Y) :
    domainMap f ≫ X.fiber.unop.hom ≫ f.base = Y.fiber.unop.hom :=
  Over.w f.fiber.unop

@[simp] theorem mkHom_id {A B : C} (i : A ⟶ B) :
    mkHom (i := i) (j := i) (𝟙 A) (𝟙 B) (by simp) = 𝟙 (of i) := by
  refine Grothendieck.ext _ _ ?_ ?_
  · rfl
  apply Quiver.Hom.unop_inj
  apply Over.OverMorphism.ext
  simp [mkHom, of]

/-- Composition reverses the domain components and preserves the codomain order. -/
@[simp] theorem mkHom_comp {A B A' B' A'' B'' : C}
    {i : A ⟶ B} {j : A' ⟶ B'} {l : A'' ⟶ B''}
    (h : A' ⟶ A) (k : B ⟶ B') (w : h ≫ i ≫ k = j)
    (h' : A'' ⟶ A') (k' : B' ⟶ B'') (w' : h' ≫ j ≫ k' = l) :
    mkHom h k w ≫ mkHom h' k' w' =
      mkHom (h' ≫ h) (k ≫ k') (by
        calc
          (h' ≫ h) ≫ i ≫ (k ≫ k') = h' ≫ (h ≫ i ≫ k) ≫ k' := by
            simp only [Category.assoc]
          _ = l := by rw [w, w']) := by
  refine Grothendieck.ext _ _ ?_ ?_
  · rfl
  apply Quiver.Hom.unop_inj
  apply Over.OverMorphism.ext
  simp [Grothendieck.comp_fiber, mkHom]

@[simp] theorem codomain_obj_of {A B : C} (i : A ⟶ B) :
    codomain.obj (of i) = B := rfl

@[simp] theorem codomain_map_mkHom {A B A' B' : C} {i : A ⟶ B} {j : A' ⟶ B'}
    (h : A' ⟶ A) (k : B ⟶ B') (w : h ≫ i ≫ k = j) :
    codomain.map (mkHom h k w) = k := rfl

end Subdivision
end CategoryTheory
