/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveExtensionTransitions
public import Colib.Topology.ClassifyingSpace.ProjectiveExtensionComma

/-! # The actual projective completion maps to the original QConstruction homotopy fiber -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Topology SSet HomotopyGroup
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]

/-- The unchanged identity-extension entry into the original structured zero comma. -/
def completionZeroStructuredEntry : GroupCompletionCategory R ⥤
    StructuredArrow (exactStructure R).qZero (localizedExtensionProjection R) :=
  completionZeroIsoFiberEntry R ⋙
    IsoFiber.toStructured (localizedExtensionProjection R) (exactStructure R).qZero

@[simp]
lemma completionZeroCommaClassifyingHomotopyEquiv_toFun :
    (completionZeroCommaClassifyingHomotopyEquiv R).toFun =
      classifyingSpaceMapUniversal (completionZeroStructuredEntry R) := by
  change (classifyingSpaceMapUniversal
    (IsoFiber.toStructured (localizedExtensionProjection R) _)).comp
    (classifyingSpaceMapUniversal (completionZeroIsoFiberEntry R)) = _
  exact (classifyingSpaceMapUniversal_comp _ _).symm

/-- The original completion-to-fiber map retains the actual projection and QConstruction zero. -/
def completionToOriginalQHomotopyFiber :
    C(ClassifyingSpace (GroupCompletionCategory R),
      HomotopyFiber (classifyingSpaceMapUniversal (localizedExtensionProjection R))
        (classifyingSpacePoint (exactStructure R).qZero)) :=
  (TheoremB.structuredFiberComparisonUniversal (localizedExtensionProjection R)
    (exactStructure R).qZero).comp
      (classifyingSpaceMapUniversal (completionZeroStructuredEntry R))

/-- At an object vertex the source is its original localized identity extension. -/
theorem completionToOriginalQHomotopyFiber_vertex_source (U : GroupCompletionCategory R) :
    (completionToOriginalQHomotopyFiber R (classifyingSpacePoint U)).1.1 =
      classifyingSpacePoint ((completionIdentityEntry R).obj U) := by
  change (TheoremB.structuredFiberComparisonUniversal _ _
    (classifyingSpaceMapUniversal _ (classifyingSpacePoint U))).1.1 = _
  rw [classifyingSpaceMapUniversal_point]
  change classifyingSpaceMapUniversal (StructuredArrow.proj _ _)
    (classifyingSpacePoint ((completionZeroStructuredEntry R).obj U)) = _
  exact classifyingSpaceMapUniversal_point _ _

/-- The vertex path is the reversed original quotient isomorphism edge. -/
theorem completionToOriginalQHomotopyFiber_vertex_path
    (U : GroupCompletionCategory R) (t : unitInterval) :
    (completionToOriginalQHomotopyFiber R (classifyingSpacePoint U)).1.2 t =
      classifyingSpacePath ((completionIdentityProjectionIsoZero R).inv.app U)
        (unitInterval.symm t) := by
  change (TheoremB.structuredFiberComparisonUniversal _ _
    (classifyingSpaceMapUniversal _ (classifyingSpacePoint U))).1.2 t = _
  rw [classifyingSpaceMapUniversal_point,
    TheoremB.structuredFiberComparisonUniversal_vertex_path]
  rfl

/-- The genuine original comparison is a weak equivalence on all components. -/
theorem completionToOriginalQHomotopyFiber_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (completionToOriginalQHomotopyFiber R) := by
  have h := isWeakHomotopyEquivalence_of_homotopyEquiv
    (completionZeroCommaClassifyingHomotopyEquiv R)
  rw [completionZeroCommaClassifyingHomotopyEquiv_toFun] at h
  exact (localizedExtensionProjection_structuredComparison_isWeakHomotopyEquivalence R
    (exactStructure R).qZero).comp h

end ModuleCat.FiniteProjective
