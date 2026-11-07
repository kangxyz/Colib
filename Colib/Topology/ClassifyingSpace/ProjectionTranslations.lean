/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.ProjectionTranslations
public import Colib.Topology.ClassifyingSpace.UniverseHomotopy
public import Colib.Topology.Homotopy.Equiv.HomotopySquare

/-! # The prescribed first-projection transition maps -/
@[expose] public section
noncomputable section
universe u v u' v'
open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]
  [∀ A : C, (tensorRight A).Faithful]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- The original comma entry is a homotopy equivalence in arbitrary universes. -/
def commaEntryClassifyingHomotopyEquiv (A : C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace D)
      (ClassifyingSpace (CostructuredArrow (projection (D := D)) ⟨A⟩)) :=
  (adjunctionClassifyingHomotopyEquivUniversal (commaTransportAdjunction A)).symm

@[simp]
lemma commaEntryClassifyingHomotopyEquiv_toFun (A : C) :
    (commaEntryClassifyingHomotopyEquiv (D := D) A).toFun =
      classifyingSpaceMapUniversal (commaEntry A) := rfl

/-- Realization of the actual representative-level transport square. -/
def commaTranslationHomotopy {A B : C} (s : C) (f : s ⊗ A ⟶ B) :
    ((classifyingSpaceMapUniversal (CostructuredArrow.map
      (S := projection (D := D)) (ActionLocalization.mkHom ⟨s, f⟩))).comp
        (classifyingSpaceMapUniversal (commaEntry A))).Homotopy
      ((classifyingSpaceMapUniversal (commaEntry B)).comp
        (classifyingSpaceMapUniversal (MonoidalLeftAction.actionLeft D s))) :=
  (classifyingSpaceUniversalHomotopy (commaTranslation (D := D) s f)).cast
    (classifyingSpaceMapUniversal_comp _ _) (classifyingSpaceMapUniversal_comp _ _)

/-- If the original action translations have specified homotopy inverses,
then the prescribed comma transitions do too. -/
theorem exists_projectionTransitionHomotopyEquiv
    (e : ∀ _ : C, ContinuousMap.HomotopyEquiv (ClassifyingSpace D) (ClassifyingSpace D))
    (he : ∀ s, (e s).toFun =
      classifyingSpaceMapUniversal (MonoidalLeftAction.actionLeft D s))
    {A B : ActionLocalization C C} (f : A ⟶ B) :
    ∃ h : ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CostructuredArrow (projection (D := D)) A))
      (ClassifyingSpace (CostructuredArrow (projection (D := D)) B)),
      h.toFun = classifyingSpaceMapUniversal
        (CostructuredArrow.map (S := projection (D := D)) f) := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective A.obj B.obj f
  refine ⟨ContinuousMap.HomotopyEquiv.ofHomotopySquare
    (commaEntryClassifyingHomotopyEquiv A.obj)
    (commaEntryClassifyingHomotopyEquiv B.obj) (e r.denom) _ ?_, rfl⟩
  rw [commaEntryClassifyingHomotopyEquiv_toFun, commaEntryClassifyingHomotopyEquiv_toFun, he]
  exact ⟨commaTranslationHomotopy r.denom r.map⟩

end CategoryTheory.GroupCompletion.Localization
