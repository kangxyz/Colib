/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionHomotopyFiber
public import Colib.CategoryTheory.TheoremB.StructuredIsoHomotopy

/-!
# The original completion comparison as its full iso-nullhomotopy lift

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/ProjectiveCompletionFiberFormula.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology SSet HomotopyGroup
open CategoryTheory
universe u
namespace ModuleCat.FiniteProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (R : Type u) [Ring R]

/-- The direct original quotient-isomorphism nullhomotopy, at every realization point. -/
def completionDirectNullhomotopy :
    ((classifyingSpaceMapUniversal (localizedExtensionProjection R)).comp
      (classifyingSpaceMapUniversal (completionIdentityEntry R))).Homotopy
        (ContinuousMap.const _ (classifyingSpacePoint (exactStructure R).qZero)) :=
  (classifyingSpaceUniversalHomotopy (completionIdentityProjectionIsoZero R).hom).cast
    (classifyingSpaceMapUniversal_comp _ _) (classifyingSpaceMapUniversal_const _)

/-- The reversed inverse isomorphism is the nullhomotopy used by original structured Theorem B. -/
def completionInverseNullhomotopy :
    ((classifyingSpaceMapUniversal (localizedExtensionProjection R)).comp
      (classifyingSpaceMapUniversal (completionIdentityEntry R))).Homotopy
        (ContinuousMap.const _ (classifyingSpacePoint (exactStructure R).qZero)) :=
  (classifyingSpaceUniversalHomotopy (completionIdentityProjectionIsoZero R).inv).symm.cast
    (classifyingSpaceMapUniversal_comp _ _) (classifyingSpaceMapUniversal_const _)

/-- The identity-extension structured entry retains its original source functor. -/
lemma completionZeroStructuredEntry_projection :
    completionZeroStructuredEntry R ⋙
      StructuredArrow.proj (exactStructure R).qZero (localizedExtensionProjection R) =
        completionIdentityEntry R := rfl

/-- The whole original comparison, including every stored path, is the inverse-iso lift. -/
theorem completionToOriginalQHomotopyFiber_eq_inverseLift :
    completionToOriginalQHomotopyFiber R =
      HomotopyFiber.lift (classifyingSpaceMapUniversal (localizedExtensionProjection R))
        (classifyingSpacePoint (exactStructure R).qZero)
        (classifyingSpaceMapUniversal (completionIdentityEntry R))
        (completionInverseNullhomotopy R) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · change classifyingSpaceMapUniversal (StructuredArrow.proj _ _)
      (classifyingSpaceMapUniversal (completionZeroStructuredEntry R) x) = _
    rw [← ContinuousMap.comp_apply, ← classifyingSpaceMapUniversal_comp,
      completionZeroStructuredEntry_projection]
    rfl
  · apply ContinuousMap.ext
    intro t
    change classifyingSpaceUniversalHomotopy
      (TheoremB.structuredCommaTransformationUniversal (localizedExtensionProjection R)
        (exactStructure R).qZero)
          (unitInterval.symm t,
            classifyingSpaceMapUniversal (completionZeroStructuredEntry R) x) = _
    rw [classifyingSpaceUniversalHomotopy_eq, classifyingSpaceMapUniversal_eq,
      ← classifyingSpaceNaturalTransformationHomotopy_whiskerLeft]
    change classifyingSpaceNaturalTransformationHomotopy
      (completionIdentityProjectionIsoZero R).inv (unitInterval.symm t, x) = _
    exact (classifyingSpaceUniversalHomotopy_eq
      (completionIdentityProjectionIsoZero R).inv (unitInterval.symm t) x).symm

/-- At every realization point, the source coordinate is the original identity entry. -/
@[simp]
theorem completionToOriginalQHomotopyFiber_source
    (x : ClassifyingSpace (GroupCompletionCategory R)) :
    (completionToOriginalQHomotopyFiber R x).1.1 =
      classifyingSpaceMapUniversal (completionIdentityEntry R) x := by
  rw [completionToOriginalQHomotopyFiber_eq_inverseLift]
  rfl

/-- The full path at every point is the reversed original inverse-isomorphism homotopy. -/
theorem completionToOriginalQHomotopyFiber_path
    (x : ClassifyingSpace (GroupCompletionCategory R)) (t : unitInterval) :
    (completionToOriginalQHomotopyFiber R x).1.2 t =
      classifyingSpaceUniversalHomotopy (completionIdentityProjectionIsoZero R).inv
        (unitInterval.symm t, x) := by
  rw [completionToOriginalQHomotopyFiber_eq_inverseLift]
  rfl

/-- The direct and reversed-inverse nullhomotopies are joined relative to both path ends. -/
def completionDirectInverseNullhomotopyHomotopy :
    (completionDirectNullhomotopy R).toContinuousMap.HomotopyRel
      (completionInverseNullhomotopy R).toContinuousMap
      (fun z : unitInterval × ClassifyingSpace (GroupCompletionCategory R) ↦
        z.1 = 0 ∨ z.1 = 1) :=
  (CategoryTheory.naturalIsoInverseHomotopy
    (completionIdentityProjectionIsoZero R).symm).cast
      (by ext z; exact (classifyingSpaceUniversalHomotopy_eq
        (completionIdentityProjectionIsoZero R).hom z.1 z.2).symm)
      (by ext z; exact (classifyingSpaceUniversalHomotopy_eq
        (completionIdentityProjectionIsoZero R).inv (unitInterval.symm z.1) z.2).symm)

/-- The direct and reversed-inverse original quotient lifts are canonically homotopic. -/
def completionDirectInverseLiftHomotopy :
    (HomotopyFiber.lift (classifyingSpaceMapUniversal (localizedExtensionProjection R))
      (classifyingSpacePoint (exactStructure R).qZero)
      (classifyingSpaceMapUniversal (completionIdentityEntry R))
      (completionDirectNullhomotopy R)).Homotopy
        (completionToOriginalQHomotopyFiber R) :=
  (HomotopyFiber.fiberLiftNullhomotopyHomotopy _ _ _ _ _
    (completionDirectInverseNullhomotopyHomotopy R)).cast rfl
      (completionToOriginalQHomotopyFiber_eq_inverseLift R).symm

/-- The whole comparison homotopy fixes the actual identity-entry source coordinate. -/
@[simp]
theorem completionDirectInverseLiftHomotopy_source
    (s : unitInterval) (x : ClassifyingSpace (GroupCompletionCategory R)) :
    (completionDirectInverseLiftHomotopy R (s, x)).1.1 =
      classifyingSpaceMapUniversal (completionIdentityEntry R) x := rfl

/-- The stored path family is the literal relative two-parameter isomorphism homotopy. -/
theorem completionDirectInverseLiftHomotopy_path
    (s t : unitInterval) (x : ClassifyingSpace (GroupCompletionCategory R)) :
    (completionDirectInverseLiftHomotopy R (s, x)).1.2 t =
      completionDirectInverseNullhomotopyHomotopy R (s, (t, x)) := rfl

end ModuleCat.FiniteProjective
