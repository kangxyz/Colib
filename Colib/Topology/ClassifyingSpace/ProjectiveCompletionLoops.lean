/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionHomotopyFiber
public import Colib.Topology.ClassifyingSpace.ProjectiveExtensionLocalization
public import Colib.Topology.HomotopyFiber.ContractibleSourcePath
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.Reversal

/-! # The original projective completion and loops in the original QConstruction space

The chosen fiber point and its entire path are retained. The comparison has
weak-equivalence strength; no Whitehead upgrade or plus assertion is used.
-/
@[expose] public section
noncomputable section
open scoped Topology ZeroObject
universe u
open CategoryTheory Topology SSet HomotopyGroup CategoryTheory.Limits
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]

/-- The actual image of a specified completion vertex in the original homotopy fiber. -/
def completionQFiberPoint (U : GroupCompletionCategory R) :
    HomotopyFiber (classifyingSpaceMapUniversal (localizedExtensionProjection R))
      (classifyingSpacePoint (exactStructure R).qZero) :=
  completionToOriginalQHomotopyFiber R (classifyingSpacePoint U)

/-- Contractibility of the actual localized total space gives an explicit loop/fiber
homotopy equivalence, corrected by the original vertex path. -/
def originalQLoopFiberHomotopyEquiv (U : GroupCompletionCategory R) :
    ContinuousMap.HomotopyEquiv
      (Path (classifyingSpacePoint (exactStructure R).qZero)
        (classifyingSpacePoint (exactStructure R).qZero))
      (HomotopyFiber (classifyingSpaceMapUniversal (localizedExtensionProjection R))
        (classifyingSpacePoint (exactStructure R).qZero)) := by
  let : ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory R)) :=
    localizedExtension_classifyingSpace_contractible R
  exact HomotopyFiber.loopEquivOfContractibleSourcePath _ (completionQFiberPoint R U).1.1 _
    (HomotopyFiber.toPath _ _ (completionQFiberPoint R U))

/-- The original additive zero pair fixes the canonical based comparison. -/
def completionZeroPair : GroupCompletionCategory R :=
  completionPair R ⟨0⟩ ⟨0⟩

/-- The standard completion comparison applies the loop/fiber inverse and reverses
its loop parameter exactly once. -/
def completionToOriginalQLoops (U : GroupCompletionCategory R) :
    C(ClassifyingSpace (GroupCompletionCategory R),
      Path (classifyingSpacePoint (exactStructure R).qZero)
        (classifyingSpacePoint (exactStructure R).qZero)) :=
  loopReversal.comp ((originalQLoopFiberHomotopyEquiv R U).invFun.comp
    (completionToOriginalQHomotopyFiber R))

/-- The standard comparison is pointwise reversal of the actual loop/fiber inverse. -/
@[simp] theorem completionToOriginalQLoops_apply (U : GroupCompletionCategory R)
    (x : ClassifyingSpace (GroupCompletionCategory R)) :
    completionToOriginalQLoops R U x =
      ((originalQLoopFiberHomotopyEquiv R U).invFun
        (completionToOriginalQHomotopyFiber R x)).symm := rfl

/-- The original loop/fiber inverse is unchanged; the canonical map adds one loop reversal. -/
theorem completionToOriginalQLoops_eq_reversal_fiberInverse (U : GroupCompletionCategory R) :
    completionToOriginalQLoops R U = loopReversal.comp
      ((originalQLoopFiberHomotopyEquiv R U).invFun.comp
        (completionToOriginalQHomotopyFiber R)) := rfl

/-- The specified standard track reverses each inner loop, preserving the outer path direction. -/
def completionToOriginalQLoopsBasepointPath (U : GroupCompletionCategory R) :
    Path (completionToOriginalQLoops R U (classifyingSpacePoint U))
      (Path.refl (classifyingSpacePoint (exactStructure R).qZero)) := by
  let : ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory R)) :=
    localizedExtension_classifyingSpace_contractible R
  exact loopReversalPath
    (HomotopyFiber.loopEquivOfContractibleSourcePathInverseBasepointPath _
      (completionQFiberPoint R U).1.1 _
      (HomotopyFiber.toPath _ _ (completionQFiberPoint R U)))

/-- The standard track is obtained from the specified loop/fiber track by reversing
the inner loop coordinate; its outer path direction is unchanged. -/
theorem completionToOriginalQLoopsBasepointPath_eq_reversal_fiberInverse
    (U : GroupCompletionCategory R) :
    letI : ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory R)) :=
      localizedExtension_classifyingSpace_contractible R
    completionToOriginalQLoopsBasepointPath R U =
      loopReversalPath
        (HomotopyFiber.loopEquivOfContractibleSourcePathInverseBasepointPath _
          (completionQFiberPoint R U).1.1 _
          (HomotopyFiber.toPath _ _ (completionQFiberPoint R U))) := rfl

/-- The standard comparison remains a weak equivalence on every component. -/
theorem completionToOriginalQLoops_isWeakHomotopyEquivalence (U : GroupCompletionCategory R) :
    IsWeakHomotopyEquivalence (completionToOriginalQLoops R U) :=
  (isWeakHomotopyEquivalence_of_homotopyEquiv
    (loopReversalHomeomorph (classifyingSpacePoint (exactStructure R).qZero)).toHomotopyEquiv).comp
    ((isWeakHomotopyEquivalence_of_homotopyEquiv
      (originalQLoopFiberHomotopyEquiv R U).symm).comp
        (completionToOriginalQHomotopyFiber_isWeakHomotopyEquivalence R))

/-- The standard canonical comparison uses the unchanged additive zero pair. -/
def originalQComparison :
    C(ClassifyingSpace (GroupCompletionCategory R),
      Path (classifyingSpacePoint (exactStructure R).qZero)
        (classifyingSpacePoint (exactStructure R).qZero)) :=
  completionToOriginalQLoops R (completionZeroPair R)

/-- The standard zero-based comparison is a weak equivalence, including dimension zero. -/
theorem originalQComparison_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (originalQComparison R) :=
  completionToOriginalQLoops_isWeakHomotopyEquivalence R (completionZeroPair R)

/-- The canonical comparison carries the pointwise reversed original zero track. -/
def originalQComparisonBasepointPath :
    Path (originalQComparison R (classifyingSpacePoint (completionZeroPair R)))
      (Path.refl (classifyingSpacePoint (exactStructure R).qZero)) :=
  completionToOriginalQLoopsBasepointPath R (completionZeroPair R)

end ModuleCat.FiniteProjective
