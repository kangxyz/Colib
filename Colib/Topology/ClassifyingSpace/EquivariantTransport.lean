/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.LocalizationLinear
public import Colib.Topology.ClassifyingSpace.IteratedTransitions
public import Colib.Topology.ClassifyingSpace.GroupCompletionIdempotenceUniversal

/-! # Weak equivalences induced by equivariant transport -/
@[expose] public section
noncomputable section
universe u v u₁ v₁ u₂ v₂ w₁ w₂
open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful]
  {D : Type u₁} [Category.{v₁} D] [MonoidalLeftAction C D]
  [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f]
attribute [local instance] firstCoordinateLeftAction

omit [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful] in
/-- The actual iterated fiber entry is a weak equivalence when the original
action category is weakly contractible. -/
theorem iteratedFiberEntry_isWeakHomotopyEquivalence_of_weakBase (X : D)
    (hD : IsWeakHomotopyEquivalence (ContinuousMap.const
      (ClassifyingSpace (ActionLocalization C D)) (PUnit.unit : PUnit.{w₁ + 1}))) :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (iteratedFiberEntry (C := C) X)) := by
  have ht : TheoremB.TransitionWeakEquivalencesUniversal
      (iteratedSecondProjection (C := C) (D := D)) := by
    intro A B f
    have h := isWeakHomotopyEquivalence_of_homotopyEquiv
      (iteratedCommaTransitionHomotopyEquiv (C := C) (D := D) f)
    rw [iteratedCommaTransitionHomotopyEquiv_toFun] at h
    exact h
  have hp := TheoremB.commaProjectionUniversal_isWeakHomotopyEquivalence_of_weakBase
    (iteratedSecondProjection (C := C) (D := D)) ht ⟨X⟩ hD
  have hi := isWeakHomotopyEquivalence_of_homotopyEquiv
    (iteratedCommaEntryClassifyingHomotopyEquiv (C := C) X)
  rw [iteratedCommaEntryClassifyingHomotopyEquiv_toFun] at hi
  have h := hp.comp hi
  rw [← classifyingSpaceMapUniversal_comp] at h
  exact h

variable {E : Type u₂} [Category.{v₂} E] [MonoidalLeftAction C E]
  [∀ X : E, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : E) (f : X ⟶ Y), Mono f]
  (F : D ⥤ E) [F.LaxLeftLinear C]

/-- Equivariant transport between weakly contractible action categories
induces a weak equivalence on the original localizations. All maps are the
actual quotient-descended functors and canonical unit entries. -/
theorem map_isWeakHomotopyEquivalence_of_weakBases (X : D)
    (hD : IsWeakHomotopyEquivalence (ContinuousMap.const
      (ClassifyingSpace (ActionLocalization C D)) (PUnit.unit : PUnit.{w₁ + 1})))
    (hE : IsWeakHomotopyEquivalence (ContinuousMap.const
      (ClassifyingSpace (ActionLocalization C E)) (PUnit.unit : PUnit.{w₂ + 1}))) :
    IsWeakHomotopyEquivalence
      (classifyingSpaceMapUniversal (actedMapFunctor (C := C) F)) := by
  have hiD := iteratedFiberEntry_isWeakHomotopyEquivalence_of_weakBase X hD
  have hiE := iteratedFiberEntry_isWeakHomotopyEquivalence_of_weakBase (F.obj X) hE
  rw [← iteratedFiberEntry_map F X, classifyingSpaceMapUniversal_comp] at hiE
  have hFF := hiE.of_comp_left hiD
  have hkD := unitEntry_iterated_isWeakHomotopyEquivalence (C := C) (D := D)
  have hkE := unitEntry_iterated_isWeakHomotopyEquivalence (C := C) (D := E)
  have h := hFF.comp hkD
  rw [← classifyingSpaceMapUniversal_comp, iteratedMap_unitEntry,
    classifyingSpaceMapUniversal_comp] at h
  exact h.of_comp_right hkE

end CategoryTheory.GroupCompletion.Localization
