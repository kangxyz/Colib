/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionFiberNaturality
public import Colib.RingTheory.KTheory.Quillen.ProjectiveCompletion
public import Colib.KTheory.Quillen.Map.Basic
public import Colib.Topology.HomotopyFiber.LoopComparisonNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.PathComponentPositiveNaturality

/-!
# Naturality of the standard positive Quillen comparison

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/ProjectiveCompletionPositiveKNaturality.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology SSet HomotopyGroup
open CategoryTheory
open scoped Topology
universe u
namespace ModuleCat.FiniteProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

private theorem loopReversal_pathTransport
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (c : C(X, Path y y)) (p : Path (c x) (Path.refl y)) (n : ℕ)
    (a : HomotopyGroup.Pi n X x) :
    pathTransport (loopReversalPath p) n
      (HomotopyGroup.map (loopReversal.comp c) rfl a) =
    HomotopyGroup.map loopReversal loopReversal_refl
      (pathTransport p n (HomotopyGroup.map c rfl a)) := by
  exact (congrArg (pathTransport (loopReversalPath p) n)
    (HomotopyGroup.map_comp c rfl loopReversal rfl a)).trans
      (pathTransport_naturality_of_track loopReversal p (loopReversalPath p)
        rfl loopReversal_refl (fun _ ↦ rfl) n _)

/-- Naturality of the standard comparison with its mapped prescribed basepoint tracks. -/
theorem completionToOriginalQLoops_baseChange (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace (StableCompletion.Completion R))
      (StableCompletion.zeroPoint R)) :
    HomotopyGroup.map
      (basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
        (completionNormalizedQ_basepoint f))
      (basedLoopMap_refl _ (completionNormalizedQ_basepoint f))
      (pathTransport (completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ
        (StableCompletion.stageObject R 0)) n
        (HomotopyGroup.map (completionToOriginalQLoops Rᵐᵒᵖ
          (StableCompletion.stageObject R 0)) rfl a)) =
    pathTransport (completionToOriginalQLoopsBasepointPath Sᵐᵒᵖ
      (StableCompletion.stageObject S 0)) n
      (HomotopyGroup.map (completionToOriginalQLoops Sᵐᵒᵖ
        (StableCompletion.stageObject S 0)) rfl
        (pathTransport (completionBaseChangeBasepointPath f) n
          (HomotopyGroup.map (completionBaseChangeMap f) rfl a))) := by
  let := localizedExtension_classifyingSpace_contractible Rᵐᵒᵖ
  let := localizedExtension_classifyingSpace_contractible Sᵐᵒᵖ
  let cR := (originalQLoopFiberHomotopyEquiv Rᵐᵒᵖ
    (StableCompletion.stageObject R 0)).invFun.comp (completionToOriginalQHomotopyFiber Rᵐᵒᵖ)
  let cS := (originalQLoopFiberHomotopyEquiv Sᵐᵒᵖ
    (StableCompletion.stageObject S 0)).invFun.comp (completionToOriginalQHomotopyFiber Sᵐᵒᵖ)
  let pR := HomotopyFiber.loopEquivOfContractibleSourcePathInverseBasepointPath _
    (completionQFiberPoint Rᵐᵒᵖ (StableCompletion.stageObject R 0)).1.1 _
    (HomotopyFiber.toPath _ _
      (completionQFiberPoint Rᵐᵒᵖ (StableCompletion.stageObject R 0)))
  let pS := HomotopyFiber.loopEquivOfContractibleSourcePathInverseBasepointPath _
    (completionQFiberPoint Sᵐᵒᵖ (StableCompletion.stageObject S 0)).1.1 _
    (HomotopyFiber.toPath _ _
      (completionQFiberPoint Sᵐᵒᵖ (StableCompletion.stageObject S 0)))
  have h : HomotopyGroup.map
      (basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
        (completionNormalizedQ_basepoint f))
      (basedLoopMap_refl _ (completionNormalizedQ_basepoint f))
      (pathTransport pR n (HomotopyGroup.map cR rfl a)) =
    pathTransport pS n (HomotopyGroup.map cS rfl
      (pathTransport (completionBaseChangeBasepointPath f) n
        (HomotopyGroup.map (completionBaseChangeMap f) rfl a))) := by
    have hfiber := HomotopyFiber.loopComparison_naturality_pi
      (classifyingSpaceMapUniversal (localizedExtensionBaseChange f))
      (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
      (completionNormalizedProjectionHomotopy f)
      (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero)
      (classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero)
      (completionNormalizedQ_basepoint f)
      (completionToOriginalQHomotopyFiber Rᵐᵒᵖ)
      (completionToOriginalQHomotopyFiber Sᵐᵒᵖ) (completionBaseChangeMap f)
      (completionFiberNaturality f) (StableCompletion.zeroPoint R)
      (StableCompletion.zeroPoint S) (completionBaseChangeBasepointPath f) n a
    have hr := HomotopyGroup.map_comp
      (completionToOriginalQHomotopyFiber Rᵐᵒᵖ) rfl
      (originalQLoopFiberHomotopyEquiv Rᵐᵒᵖ (StableCompletion.stageObject R 0)).invFun rfl a
    have hs := HomotopyGroup.map_comp
      (completionToOriginalQHomotopyFiber Sᵐᵒᵖ) rfl
      (originalQLoopFiberHomotopyEquiv Sᵐᵒᵖ (StableCompletion.stageObject S 0)).invFun rfl
      (pathTransport (completionBaseChangeBasepointPath f) n
        (HomotopyGroup.map (completionBaseChangeMap f) rfl a))
    exact (congrArg (fun b ↦ HomotopyGroup.map
      (basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
        (completionNormalizedQ_basepoint f))
      (basedLoopMap_refl _ (completionNormalizedQ_basepoint f))
        (pathTransport pR n b)) hr).trans
      (hfiber.trans (congrArg (pathTransport pS n) hs.symm))
  change HomotopyGroup.map
      (basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
        (completionNormalizedQ_basepoint f))
      (basedLoopMap_refl _ (completionNormalizedQ_basepoint f))
      (pathTransport (loopReversalPath pR) n
        (HomotopyGroup.map (loopReversal.comp cR) rfl a)) =
    pathTransport (loopReversalPath pS) n
      (HomotopyGroup.map (loopReversal.comp cS) rfl
        (pathTransport (completionBaseChangeBasepointPath f) n
          (HomotopyGroup.map (completionBaseChangeMap f) rfl a)))
  have hcomm (b : HomotopyGroup.Pi n
      (Path (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero)
        (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero))
      (Path.refl (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero))) :
      HomotopyGroup.map
        (basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
          (completionNormalizedQ_basepoint f))
        (basedLoopMap_refl _ (completionNormalizedQ_basepoint f))
        (HomotopyGroup.map loopReversal loopReversal_refl b) =
      HomotopyGroup.map loopReversal loopReversal_refl
        (HomotopyGroup.map
          (basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
            (completionNormalizedQ_basepoint f))
          (basedLoopMap_refl _ (completionNormalizedQ_basepoint f)) b) := by
    refine Quotient.inductionOn b (fun p ↦ ?_)
    rfl
  exact ((congrArg (HomotopyGroup.map
      (basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
        (completionNormalizedQ_basepoint f))
      (basedLoopMap_refl _ (completionNormalizedQ_basepoint f)))
        (loopReversal_pathTransport cR pR n a)).trans
      ((hcomm _).trans (congrArg (HomotopyGroup.map loopReversal loopReversal_refl) h))).trans
    (loopReversal_pathTransport cS pS n
      (pathTransport (completionBaseChangeBasepointPath f) n
        (HomotopyGroup.map (completionBaseChangeMap f) rfl a))).symm

/-- The actual completion comparison commutes with the original exact-functor K-map
in every positive degree, retaining the actual monoidal-unit basepoint edge. -/
theorem completionPositiveKEquiv_baseChange (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ClassifyingSpace (StableCompletion.Completion R))
      (StableCompletion.zeroPoint R)) :
    completionPositiveKEquiv Sᵐᵒᵖ (StableCompletion.stageObject S 0) n
      (pathTransportMulEquiv (completionBaseChangeBasepointPath f) n
        (HomotopyGroup.mapHom (N := Fin (n + 1)) (completionBaseChangeMap f) rfl a)) =
    (rightBaseChangeExact f).KMap (n + 1)
      (completionPositiveKEquiv Rᵐᵒᵖ (StableCompletion.stageObject R 0) n a) := by
  apply (loopShiftMulEquiv n).injective
  rw [completionPositiveKEquiv_apply, MulEquiv.apply_symm_apply]
  have hn := completionToOriginalQLoops_baseChange f (n + 1) a
  have hs := loopShiftEquiv_natural (n + 1)
    (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
    (completionNormalizedQ_basepoint f)
    (completionPositiveKEquiv Rᵐᵒᵖ (StableCompletion.stageObject R 0) n a)
  have hr : loopShiftEquiv (n + 1)
      (completionPositiveKEquiv Rᵐᵒᵖ (StableCompletion.stageObject R 0) n a) =
    pathTransport (completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ
      (StableCompletion.stageObject R 0)) (n + 1)
      (HomotopyGroup.map (completionToOriginalQLoops Rᵐᵒᵖ
        (StableCompletion.stageObject R 0)) rfl a) :=
    (loopShiftMulEquiv n).apply_symm_apply _
  rw [hr] at hs
  exact hn.symm.trans hs.symm

namespace StableCompletion

/-- The standard zero-component comparison is natural for the actual ring map and
its actual restricted monoidal-unit path, in every positive original K-degree. -/
theorem zeroCompletionPositiveKEquiv_baseChange (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ZeroComponent R) (zeroBase R)) :
    zeroCompletionPositiveKEquiv S n
      (pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) n
        (HomotopyGroup.mapHom (N := Fin (n + 1)) (zeroCompletionBaseChangeMap f) rfl a)) =
    (rightBaseChangeExact f).KMap (n + 1) (zeroCompletionPositiveKEquiv R n a) := by
  change completionPositiveKEquiv Sᵐᵒᵖ (stageObject S 0) n
    (pathComponentPiMulEquiv (zeroPoint S) n
      (pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) n
        (HomotopyGroup.mapHom (N := Fin (n + 1)) (zeroCompletionBaseChangeMap f) rfl a))) = _
  exact (congrArg (completionPositiveKEquiv Sᵐᵒᵖ (stageObject S 0) n)
    (pathComponentPiMulEquiv_naturality_apply (completionBaseChangeMap f)
      (zeroPoint R) (zeroPoint S) (completionBaseChangeBasepointPath f) n a)).trans
      (completionPositiveKEquiv_baseChange f n _)

end StableCompletion
end ModuleCat.FiniteProjective
