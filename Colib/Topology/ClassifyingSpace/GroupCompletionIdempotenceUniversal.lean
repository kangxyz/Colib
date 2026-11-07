/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.UnitEntry
public import Colib.Topology.ClassifyingSpace.IteratedFirstTransitions
public import Colib.CategoryTheory.TheoremB.UniverseWeakComparison
public import Colib.Topology.ClassifyingSpace.Contraction

/-! # Actual localization idempotence in arbitrary category universes -/
@[expose] public section
noncomputable section
open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory
open scoped MonoidalLeftAction
universe u v u' v'
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction

/-- The actual iterated first projection satisfies weak transitions in arbitrary universes. -/
theorem iteratedFirstTransitionWeakEquivalencesUniversal :
    TheoremB.TransitionWeakEquivalencesUniversal
      (projection (C := C) (D := Localization C D)) := by
  intro A B f
  obtain ⟨e, he⟩ := exists_iteratedFirstTransitionHomotopyEquiv (D := D) f
  have h := isWeakHomotopyEquivalence_of_homotopyEquiv e
  rw [he] at h
  exact h

/-- The canonical original unit entry is a weak equivalence after one localization,
without restrictions on the object or morphism universes of either category. -/
theorem unitEntry_iterated_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence
      (classifyingSpaceMapUniversal (unitEntry (C := C) (D := Localization C D))) := by
  let : ContractibleSpace (ClassifyingSpace (ActionLocalization C C)) :=
    classifyingSpace_contractible_of_isInitial (ActionLocalization.selfUnitIsInitial (C := C))
  obtain ⟨e⟩ := ContractibleSpace.hequiv
    (ClassifyingSpace (ActionLocalization C C)) PUnit.{max u v + 1}
  have he : e.toFun = ContinuousMap.const _ PUnit.unit := by
    ext x
  have hb := isWeakHomotopyEquivalence_of_homotopyEquiv e
  rw [he] at hb
  have hp := TheoremB.commaProjectionUniversal_isWeakHomotopyEquivalence_of_weakBase
    (projection (C := C) (D := Localization C D))
    iteratedFirstTransitionWeakEquivalencesUniversal (⟨𝟙_ C⟩ : ActionLocalization C C) hb
  have hi := isWeakHomotopyEquivalence_of_homotopyEquiv
    (commaEntryClassifyingHomotopyEquiv (D := Localization C D) (𝟙_ C))
  rw [commaEntryClassifyingHomotopyEquiv_toFun] at hi
  rw [unitEntry_eq_comma, classifyingSpaceMapUniversal_comp]
  exact hp.comp hi

end CategoryTheory.GroupCompletion.Localization
