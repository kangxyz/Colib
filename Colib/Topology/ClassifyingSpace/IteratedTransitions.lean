/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.IteratedCommaAdjunction
public import Colib.Topology.ClassifyingSpace.IteratedTranslation

/-! # Actual transition homotopy equivalences for the iterated projection

The strict fiber equivalence, its actual comma adjunction, and the explicit
translation homotopy square identify each prescribed comma transition as a
homotopy equivalence. No contractibility or Theorem B hypothesis is assumed.
-/
@[expose] public section
noncomputable section
universe u v u' v'
open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
  [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f]
attribute [local instance] firstCoordinateLeftAction

/-- The actual group-completion entry is a homotopy equivalence onto the
original costructured comma classifying space. -/
def iteratedCommaEntryClassifyingHomotopyEquiv (X : D) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Localization C C))
      (ClassifyingSpace (CostructuredArrow (iteratedSecondProjection (C := C)) ⟨X⟩)) :=
  (equivalenceClassifyingHomotopyEquivUniversal (iteratedSecondFiberEquivalence X)).trans
    (adjunctionClassifyingHomotopyEquivUniversal
      (iteratedFiberCommaAdjunction (⟨X⟩ : ActionLocalization C D))).symm

@[simp]
theorem iteratedCommaEntryClassifyingHomotopyEquiv_toFun (X : D) :
    (iteratedCommaEntryClassifyingHomotopyEquiv (C := C) X).toFun =
      classifyingSpaceMapUniversal (iteratedCommaEntry X) := by
  change (classifyingSpaceMapUniversal
    (CategoryTheory.Fiber.toCostructured iteratedSecondProjection ⟨X⟩)).comp
      (classifyingSpaceMapUniversal (iteratedStrictFiberEntry X)) = _
  rw [← classifyingSpaceMapUniversal_comp, iteratedCommaEntry_factorization]

/-- Every original comma transition admits a homotopy inverse. The forward
map is the prescribed transition, not a chosen equivalent map. -/
theorem exists_iteratedCommaTransitionHomotopyEquiv {X Y : ActionLocalization C D}
    (f : X ⟶ Y) :
    ∃ e : ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CostructuredArrow iteratedSecondProjection X))
      (ClassifyingSpace (CostructuredArrow iteratedSecondProjection Y)),
      e.toFun = classifyingSpaceMapUniversal (CostructuredArrow.map
        (S := iteratedSecondProjection (C := C) (D := D)) f) := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X.obj Y.obj f
  refine ⟨ContinuousMap.HomotopyEquiv.ofHomotopySquare
    (iteratedCommaEntryClassifyingHomotopyEquiv X.obj)
    (iteratedCommaEntryClassifyingHomotopyEquiv Y.obj)
    (translationClassifyingHomotopyEquiv r.denom).symm _ ?_, rfl⟩
  rw [iteratedCommaEntryClassifyingHomotopyEquiv_toFun,
    iteratedCommaEntryClassifyingHomotopyEquiv_toFun]
  exact ⟨iteratedCommaTranslationHomotopy r.denom r.map⟩

/-- A homotopy equivalence for the actual transition, chosen only after its
explicit existence with the original forward map has been proved. -/
def iteratedCommaTransitionHomotopyEquiv {X Y : ActionLocalization C D} (f : X ⟶ Y) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CostructuredArrow iteratedSecondProjection X))
      (ClassifyingSpace (CostructuredArrow iteratedSecondProjection Y)) :=
  (exists_iteratedCommaTransitionHomotopyEquiv f).choose

@[simp]
theorem iteratedCommaTransitionHomotopyEquiv_toFun {X Y : ActionLocalization C D}
    (f : X ⟶ Y) :
    (iteratedCommaTransitionHomotopyEquiv f).toFun =
      classifyingSpaceMapUniversal (CostructuredArrow.map
        (S := iteratedSecondProjection (C := C) (D := D)) f) :=
  (exists_iteratedCommaTransitionHomotopyEquiv f).choose_spec

end CategoryTheory.GroupCompletion.Localization
