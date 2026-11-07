/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Quillen.ProjectiveCompletion
public import Colib.Topology.HomotopyFiber.LoopPrefixBasepointNaturality

/-!
# Actual basepoint transport for the original positive comparison

The original loop-fiber inverse, unit-removal track and one loop reversal
commute with the displayed completion-vertex path. The proof uses the actual
forward-prefix cancellation, without replacing any comparison map.

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/ProjectiveCompletionBasepoint.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section

noncomputable section
open CategoryTheory Topology SSet HomotopyGroup
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open scoped Topology
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]

/-- One inner-loop reversal retains the supplied original correction track. -/
private theorem reversalCorrected {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (c : C(X, Path y y)) (p : Path (c x) (Path.refl y)) (n : ℕ)
    (a : HomotopyGroup.Pi n X x) :
    pathTransport (loopReversalPath p) n (HomotopyGroup.map (loopReversal.comp c) rfl a) =
      HomotopyGroup.map loopReversal loopReversal_refl
        (pathTransport p n (HomotopyGroup.map c rfl a)) := by
  exact (congrArg (pathTransport (loopReversalPath p) n)
    (HomotopyGroup.map_comp c rfl loopReversal rfl a)).trans
      (pathTransport_naturality_of_track loopReversal p (loopReversalPath p)
        rfl loopReversal_refl (fun _ => rfl) n _)

/-- Changing completion vertices along the displayed path preserves the original positive
comparison. -/
theorem completionPositiveKEquiv_pathTransport {U V : GroupCompletionCategory R}
    (p : Path (classifyingSpacePoint U) (classifyingSpacePoint V)) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ClassifyingSpace (GroupCompletionCategory R))
      (classifyingSpacePoint U)) :
    completionPositiveKEquiv R V n (pathTransport p (n + 1) a) =
      completionPositiveKEquiv R U n a := by
  let : ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory R)) :=
    localizedExtension_classifyingSpace_contractible R
  let c := completionToOriginalQHomotopyFiber R
  let IU := (originalQLoopFiberHomotopyEquiv R U).invFun
  let IV := (originalQLoopFiberHomotopyEquiv R V).invFun
  let cU := IU.comp c
  let cV := IV.comp c
  let pU := HomotopyFiber.loopEquivOfContractibleSourcePathInverseBasepointPath _
    (completionQFiberPoint R U).val.1 _ (HomotopyFiber.toPath _ _ (completionQFiberPoint R U))
  let pV := HomotopyFiber.loopEquivOfContractibleSourcePathInverseBasepointPath _
    (completionQFiberPoint R V).val.1 _ (HomotopyFiber.toPath _ _ (completionQFiberPoint R V))
  have h : pathTransport pU (n + 1) (HomotopyGroup.map cU rfl a) =
      pathTransport pV (n + 1) (HomotopyGroup.map cV rfl (pathTransport p (n + 1) a)) := by
    have hi := HomotopyFiber.loopInverse_pathTransport_pi (p.map c.continuous) (n + 1)
      (HomotopyGroup.map c rfl a)
    rw [pathTransport_naturality] at hi
    change pathTransport pU (n + 1) (HomotopyGroup.map IU rfl (HomotopyGroup.map c rfl a)) =
      pathTransport pV (n + 1)
        (HomotopyGroup.map IV rfl (HomotopyGroup.map c rfl (pathTransport p (n + 1) a))) at hi
    rw [← HomotopyGroup.map_comp c rfl IU rfl a,
      ← HomotopyGroup.map_comp c rfl IV rfl (pathTransport p (n + 1) a)] at hi
    exact hi
  change (loopShiftMulEquiv n).symm
    (pathTransport (loopReversalPath pV) (n + 1)
      (HomotopyGroup.map (loopReversal.comp cV) rfl (pathTransport p (n + 1) a))) =
    (loopShiftMulEquiv n).symm
      (pathTransport (loopReversalPath pU) (n + 1)
        (HomotopyGroup.map (loopReversal.comp cU) rfl a))
  exact (congrArg (loopShiftMulEquiv n).symm
    (reversalCorrected cV pV (n + 1) (pathTransport p (n + 1) a))).trans
      ((congrArg (fun b => (loopShiftMulEquiv n).symm
        (HomotopyGroup.map loopReversal loopReversal_refl b)) h.symm).trans
          (congrArg (loopShiftMulEquiv n).symm (reversalCorrected cU pU (n + 1) a).symm))

end ModuleCat.FiniteProjective
