/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionRetraction
public import Colib.Topology.ClassifyingSpace.UniverseHomotopy
public import Colib.Topology.Homotopy.Equiv.HomotopySquare
public import Colib.Topology.ClassifyingSpace.LocalizationTelescopeHomotopyEquiv

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveCompletionRetractionHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; original functors and arrows retained.

# The original completed retraction is a homotopy equivalence

The actual completed stage-zero inclusion is a homotopy equivalence. Its
composite with the prescribed inverse cocone is identified with the identity
by the original unitor natural isomorphism. The resulting homotopy square
therefore makes the original retraction itself a homotopy equivalence.
The chosen forward map and original stage-zero inverse are retained.
-/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
universe u
namespace ModuleCat.FiniteProjective.StableFreeRight
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
variable (R : Type u) [Ring R]

/-- The prescribed completed base is the original zero pair in stage zero. -/
def completedTelescopeBase : Grothendieck (projectiveCompletedTelescopeDiagram R) :=
  (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0).obj
    (StableCompletion.stageObject R 0)

/-- The original completed stage-zero inclusion has a genuine homotopy inverse. -/
def completedStageZeroHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (StableCompletion.Completion R))
      (ClassifyingSpace (Grothendieck (projectiveCompletedTelescopeDiagram R))) :=
  TranslationTelescope.completedStageInclusionHomotopyEquiv.{u + 1, u}
    (freeIso Rᵐᵒᵖ 1) 0

/-- The stage-zero equivalence retains the original inclusion as its forward map. -/
lemma completedStageZeroHomotopyEquiv_toFun :
    (completedStageZeroHomotopyEquiv R).toFun =
      classifyingSpaceMapUniversal (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0) :=
  TranslationTelescope.completedStageInclusionHomotopyEquiv_toFun.{u + 1, u}
    (freeIso Rᵐᵒᵖ 1) 0

/-- The specified natural unitor realizes the original retraction-inclusion homotopy. -/
def completedRetractionStageZeroHomotopy :
    ((classifyingSpaceMapUniversal (completedRetraction R)).comp
      (classifyingSpaceMapUniversal
        (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0))).Homotopy
      (ContinuousMap.id (ClassifyingSpace (StableCompletion.Completion R))) :=
  (classifyingSpaceUniversalHomotopy (completedRetractionZeroIso R).hom).cast
    (classifyingSpaceMapUniversal_comp _ _) classifyingSpaceMapUniversal_id

/-- The actual completed retraction is the forward map of a genuine homotopy equivalence. -/
def completedRetractionHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (Grothendieck (projectiveCompletedTelescopeDiagram R)))
      (ClassifyingSpace (StableCompletion.Completion R)) :=
  ContinuousMap.HomotopyEquiv.ofHomotopySquare
    (completedStageZeroHomotopyEquiv R)
    (ContinuousMap.HomotopyEquiv.refl (ClassifyingSpace (StableCompletion.Completion R)))
    (ContinuousMap.HomotopyEquiv.refl (ClassifyingSpace (StableCompletion.Completion R)))
    (classifyingSpaceMapUniversal (completedRetraction R)) (by
      rw [completedStageZeroHomotopyEquiv_toFun]
      change ((classifyingSpaceMapUniversal (completedRetraction R)).comp
        (classifyingSpaceMapUniversal
          (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0))).Homotopic
        ((ContinuousMap.id _).comp (ContinuousMap.id _))
      rw [ContinuousMap.id_comp]
      exact ⟨completedRetractionStageZeroHomotopy R⟩)

/-- No replacement of the retraction map occurs in the homotopy-square construction. -/
@[simp]
lemma completedRetractionHomotopyEquiv_toFun :
    (completedRetractionHomotopyEquiv R).toFun =
      classifyingSpaceMapUniversal (completedRetraction R) := rfl

/-- The chosen inverse retains exactly the original stage-zero inclusion. -/
lemma completedRetractionHomotopyEquiv_invFun :
    (completedRetractionHomotopyEquiv R).invFun =
      classifyingSpaceMapUniversal (Grothendieck.ι (projectiveCompletedTelescopeDiagram R) 0) := by
  change (completedStageZeroHomotopyEquiv R).toFun.comp
    ((ContinuousMap.id _).comp (ContinuousMap.id _)) = _
  rw [ContinuousMap.id_comp, ContinuousMap.comp_id, completedStageZeroHomotopyEquiv_toFun]

end ModuleCat.FiniteProjective.StableFreeRight
