/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionLoops
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionBased
public import Colib.Topology.Homotopy.HomotopyGroup.PathComponentPositive
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportGroup
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift
public import Colib.KTheory.Quillen.Basic

/-! # Positive original Quillen K-groups of the independent completion candidate

These are group isomorphisms induced by the actual completion-to-loop map,
its specified basepoint path, and the existing loop-degree shift. The zero
component is the original stable completion component. No plus property or
identification of components with the Grothendieck group is asserted here.
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Topology HomotopyGroup
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]

/-- Positive homotopy groups of the original completion identify with the original
Quillen K-groups, using the displayed vertex and its actual comparison track. -/
def completionPositiveKEquiv (U : GroupCompletionCategory R) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (ClassifyingSpace (GroupCompletionCategory R))
      (classifyingSpacePoint U) ≃* (exactStructure R).K (n + 1) :=
  (MulEquiv.ofBijective
    (HomotopyGroup.mapHom (N := Fin (n + 1)) (completionToOriginalQLoops R U)
      (x := classifyingSpacePoint U) rfl)
    ((completionToOriginalQLoops_isWeakHomotopyEquivalence R U).homotopy_bijective
      (classifyingSpacePoint U) (n + 1))).trans
        ((pathTransportMulEquiv (completionToOriginalQLoopsBasepointPath R U) n).trans
          (loopShiftMulEquiv n).symm)

/-- The group isomorphism retains postcomposition, the specified path transport,
and the original inverse loop-degree shift in that order. -/
theorem completionPositiveKEquiv_apply (U : GroupCompletionCategory R) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ClassifyingSpace (GroupCompletionCategory R))
      (classifyingSpacePoint U)) :
    completionPositiveKEquiv R U n a =
      (loopShiftMulEquiv n).symm
        (pathTransportMulEquiv (completionToOriginalQLoopsBasepointPath R U) n
          (HomotopyGroup.mapHom (N := Fin (n + 1)) (completionToOriginalQLoops R U)
            (x := classifyingSpacePoint U) rfl a)) := rfl

namespace StableCompletion

/-- The genuine zero-component candidate has the positive original K-groups of
finite projective right modules. The actual monoidal-unit stage object is retained. -/
def zeroCompletionPositiveKEquiv (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (ZeroComponent R) (zeroBase R) ≃*
      (exactStructure Rᵐᵒᵖ).K (n + 1) :=
  (pathComponentPiMulEquiv (zeroPoint R) n).trans
    (completionPositiveKEquiv Rᵐᵒᵖ (stageObject R 0) n)

/-- The zero-component isomorphism starts with the unchanged component inclusion. -/
theorem zeroCompletionPositiveKEquiv_apply (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ZeroComponent R) (zeroBase R)) :
    zeroCompletionPositiveKEquiv R n a =
      completionPositiveKEquiv Rᵐᵒᵖ (stageObject R 0) n
        (HomotopyGroup.mapHom (N := Fin (n + 1)) (pathComponentInclusion (zeroPoint R))
          (x := zeroBase R) rfl a) := rfl

end StableCompletion
end ModuleCat.FiniteProjective
