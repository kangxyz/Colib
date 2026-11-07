/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionSpanComma
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionComma
public import Colib.Topology.ClassifyingSpace.UniverseHomotopy
public import Colib.Topology.ClassifyingSpace.ProjectiveExtensionSpanTransport
public import Colib.CategoryTheory.TheoremB.StructuredUniverseComparison

/-! # Weak equivalence of the original structured QConstruction transitions -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Topology SSet HomotopyGroup
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal extensionFiberDirectSumAction

/-- The original localized fixed-deflation entry realizes to a homotopy equivalence,
using its actual fiber equivalence followed by the genuine cartesian comma adjunction. -/
def localizedFixedExtensionEntryClassifyingHomotopyEquiv (C : Category.{u, u} R) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (LocalizedFixedExtensionCategory R C))
      (ClassifyingSpace (StructuredArrow
        (QConstruction.of (exactStructure R).deflation (exactStructure R).inflation C)
        (localizedExtensionProjection R))) :=
  (equivalenceClassifyingHomotopyEquivUniversal
    (localizedFixedExtensionFiberEquivalence R C)).trans
    (adjunctionClassifyingHomotopyEquivUniversal
      (localizedExtensionFiberCommaAdjunction R _))

@[simp]
lemma localizedFixedExtensionEntryClassifyingHomotopyEquiv_toFun
    (C : Category.{u, u} R) :
    (localizedFixedExtensionEntryClassifyingHomotopyEquiv R C).toFun =
      classifyingSpaceMapUniversal (localizedFixedExtensionEntry R C) := by
  change (classifyingSpaceMapUniversal
    (IsoFiber.toStructured (localizedExtensionProjection R) _)).comp
    (classifyingSpaceMapUniversal (localizedFixedExtensionFiberEquivalence R C).functor) = _
  exact (classifyingSpaceMapUniversal_comp _ _).symm

/-- The actual fixed-fiber entry is a weak equivalence on all components. -/
theorem localizedFixedExtensionEntry_isWeakHomotopyEquivalence (C : Category.{u, u} R) :
    IsWeakHomotopyEquivalence
      (classifyingSpaceMapUniversal (localizedFixedExtensionEntry R C)) := by
  have h := isWeakHomotopyEquivalence_of_homotopyEquiv
    (localizedFixedExtensionEntryClassifyingHomotopyEquiv R C)
  rw [localizedFixedExtensionEntryClassifyingHomotopyEquiv_toFun] at h
  exact h

/-- The unchanged original structured transition of every original QConstruction-span is a
weak equivalence, by its explicit localized pullback-projection natural arrow. -/
theorem localizedExtensionStructuredSpan_isWeakHomotopyEquivalence
    {X Y : Category.{u, u} R}
    (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y) :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (StructuredArrow.map
      (T := localizedExtensionProjection R)
      (QConstruction.mkHom (exactStructure R).deflation (exactStructure R).inflation s))) := by
  have h := (localizedFixedExtensionEntry_isWeakHomotopyEquivalence R X).comp
    (localizedExtensionSpanTransport_isWeakHomotopyEquivalence R s)
  rw [← classifyingSpaceMapUniversal_comp] at h
  have h' := h.of_homotopy
    (classifyingSpaceUniversalHomotopy (localizedFixedExtensionSpanComma R s))
  rw [classifyingSpaceMapUniversal_comp] at h'
  exact h'.of_comp_left (localizedFixedExtensionEntry_isWeakHomotopyEquivalence R Y)

/-- The actual localized projection satisfies the contravariant weak-transition
hypothesis of universal structured Quillen Theorem B. -/
theorem localizedExtensionProjection_structuredWeakTransitions :
    TheoremB.StructuredTransitionWeakEquivalencesUniversal (localizedExtensionProjection R) := by
  intro X Y g
  obtain ⟨⟨X⟩⟩ := X
  obtain ⟨⟨Y⟩⟩ := Y
  obtain ⟨s, rfl⟩ := Quotient.exists_rep g
  exact localizedExtensionStructuredSpan_isWeakHomotopyEquivalence R s

/-- Universal structured Theorem B applies to the actual localized projection;
this is its original homotopy-fiber comparison at every original QConstruction object. -/
theorem localizedExtensionProjection_structuredComparison_isWeakHomotopyEquivalence
    (b : QConstruction (exactStructure R).deflation (exactStructure R).inflation) :
    IsWeakHomotopyEquivalence (TheoremB.structuredFiberComparisonUniversal
      (localizedExtensionProjection R) b) :=
  TheoremB.structuredFiberComparisonUniversal_isWeakHomotopyEquivalence
    (localizedExtensionProjection R) (localizedExtensionProjection_structuredWeakTransitions R) b

end ModuleCat.FiniteProjective
