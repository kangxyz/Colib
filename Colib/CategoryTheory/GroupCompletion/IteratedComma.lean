/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.IteratedTranslation
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/IteratedComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The iterated fiber entry and translation in the actual comma categories -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction

/-- The actual identity-arrow entry of the group-completion fiber into its
costructured comma category. -/
def iteratedCommaEntry (X : D) :
    Localization C C ⥤ CostructuredArrow (iteratedSecondProjection (C := C)) ⟨X⟩ where
  obj A := CostructuredArrow.mk
    (S := iteratedSecondProjection (C := C) (D := D))
    (Y := (iteratedFiberEntry X).obj A) (𝟙 (⟨X⟩ : ActionLocalization C D))
  map f := CostructuredArrow.homMk ((iteratedFiberEntry X).map f) (by
    change iteratedSecondProjection.map ((iteratedFiberEntry X).map f) ≫
      𝟙 (⟨X⟩ : ActionLocalization C D) = 𝟙 (⟨X⟩ : ActionLocalization C D)
    rw [iteratedFiberEntry_projection_map]
    exact Category.id_comp _)
  map_id A := by
    apply CostructuredArrow.hom_ext
    exact (iteratedFiberEntry X).map_id A
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact (iteratedFiberEntry X).map_comp f g

/-- The lift natural transformation in the actual comma category gives the
comparison with the existing second translation on `C⁻¹C`. -/
def iteratedCommaTranslation {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) :
    iteratedCommaEntry X ⋙ CostructuredArrow.map (ActionLocalization.mkHom ⟨s, g⟩) ⟶
      secondTranslation s ⋙ iteratedCommaEntry Y where
  app A := CostructuredArrow.homMk (iteratedRightLift s g A.obj.1 A.obj.2) (by
    change iteratedSecondProjection.map (iteratedRightLift s g A.obj.1 A.obj.2) ≫ 𝟙 _ =
      𝟙 _ ≫ ActionLocalization.mkHom ⟨s, g⟩
    rw [iteratedSecondProjection_iteratedRightLift, Category.id_comp, Category.comp_id])
  naturality {_ _} f := by
    apply CostructuredArrow.hom_ext
    exact iteratedRightLift_naturality s g f

end CategoryTheory.GroupCompletion.Localization
