/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.ClassifyingSpace.ProjectionTranslations
public import Colib.Topology.ClassifyingSpace.ActionTranslations
public import Colib.CategoryTheory.GroupCompletion.FirstCoordinateAction

/-! # Invertible transitions of the iterated first projection -/
@[expose] public section
noncomputable section
universe u v u' v'
open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction

omit [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful] in
/-- The first action is the original first-coordinate translation functor. -/
lemma firstCoordinateActionLeft_eq (s : C) :
    MonoidalLeftAction.actionLeft (Localization C D) s =
      firstCoordinateTranslation s := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  change (firstCoordinateTranslation s).map f =
    𝟙 _ ≫ (firstCoordinateTranslation s).map f ≫ 𝟙 _
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- Every prescribed comma transition for the iterated first projection is
an actual homotopy equivalence, without assumptions on the acted-on category. -/
theorem exists_iteratedFirstTransitionHomotopyEquiv
    {A B : ActionLocalization C C} (f : A ⟶ B) :
    ∃ h : ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CostructuredArrow (projection (D := Localization C D)) A))
      (ClassifyingSpace (CostructuredArrow (projection (D := Localization C D)) B)),
      h.toFun = classifyingSpaceMapUniversal
        (CostructuredArrow.map (S := projection (D := Localization C D)) f) := by
  apply exists_projectionTransitionHomotopyEquiv
    (fun s ↦ actionTranslationClassifyingHomotopyEquiv (D := D) s)
  intro s
  rw [firstCoordinateActionLeft_eq]
  rfl

end CategoryTheory.GroupCompletion.Localization
