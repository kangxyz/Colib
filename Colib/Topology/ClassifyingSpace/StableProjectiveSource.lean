/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.StableProjectiveZeroComponent
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionBasedSurjectivity

/-!
Adapted from `Quillen/KTheory/Plus/StableProjectiveSource.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual objects,
functors, coefficient universes and comparison maps.

# The original stable general linear space and projective telescope zero component -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace ModuleCat.FiniteProjective.StableFreeRight
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type u) [Ring R]

/-- The original stable general linear classifying space models the true zero component. -/
def stableProjectiveZeroHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)))
      (pathComponent (classifyingSpacePoint (projectiveTelescopeBase R))) :=
  (StableCompletion.originalStableTelescopeEquiv R).trans
    (matrixTelescopeZeroComponentHomotopyEquiv R)

/-- The forward map retains the previously chosen original stable-to-telescope inverse. -/
@[simp]
theorem stableProjectiveZeroHomotopyEquiv_val
    (x : ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))) :
    (stableProjectiveZeroHomotopyEquiv R x).val =
      classifyingSpaceMapUniversal (telescopeFunctor R)
        (StableCompletion.originalStableToTelescope R x) :=
  matrixTelescopeZeroComponentHomotopyEquiv_val R _

/-- The actual matrix comparison sends its rank-zero vertex to the original projective zero. -/
@[simp]
theorem matrixTelescopeZeroComponentHomotopyEquiv_point :
    matrixTelescopeZeroComponentHomotopyEquiv R
      (classifyingSpacePoint (StableCompletion.telescopeBase R)) =
        (⟨classifyingSpacePoint (projectiveTelescopeBase R), Joined.refl _⟩ :
          pathComponent (classifyingSpacePoint (projectiveTelescopeBase R))) := by
  apply Subtype.ext
  rw [matrixTelescopeZeroComponentHomotopyEquiv_val, classifyingSpaceMapUniversal_point]
  rfl

/-- The original chosen inverse-homotopy track gives the based source comparison. -/
def stableProjectiveZeroBasepointPath :
    Path (stableProjectiveZeroHomotopyEquiv R (StableCompletion.stableBase R))
      (⟨classifyingSpacePoint (projectiveTelescopeBase R), Joined.refl _⟩ :
        pathComponent (classifyingSpacePoint (projectiveTelescopeBase R))) :=
  ((StableCompletion.sourceBasepointPath R).map
    (matrixTelescopeZeroComponentHomotopyEquiv R).toFun.continuous).cast rfl
      (matrixTelescopeZeroComponentHomotopyEquiv_point R).symm

end ModuleCat.FiniteProjective.StableFreeRight
