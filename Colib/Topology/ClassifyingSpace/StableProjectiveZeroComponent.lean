/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.StableProjectiveTelescope
public import Colib.Topology.ClassifyingSpace.GrothendieckZeroComponent
public import Colib.Topology.ClassifyingSpace.UniverseLift

/-!
Adapted from `Quillen/KTheory/Plus/StableProjectiveZeroComponent.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual objects,
functors, coefficient universes and comparison maps.

# The original matrix telescope models the projective telescope zero component

The comparison uses the original matrix stabilization arrows and their explicit
braiding alignment with right addition. No invariant basis number assumption is
used. The target is the actual path-component subspace of the zero vertex.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace ModuleCat.FiniteProjective.StableFreeRight
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (R : Type u) [Ring R]

/-- The original matrix telescope is preconnected through its identity-matrix chain. -/
instance matrixTelescope_isPreconnected :
    IsPreconnected (StableGeneralLinear.GrothendieckModel.Telescope R) := by
  apply zigzag_isPreconnected
  intro X Y
  obtain ⟨n, rfl⟩ := exists_matrixSequence_obj R X
  obtain ⟨m, rfl⟩ := exists_matrixSequence_obj R Y
  exact (Zigzag.of_hom ((matrixSequence R).map (homOfLE (Nat.zero_le n)))).symm.trans
    (Zigzag.of_hom ((matrixSequence R).map (homOfLE (Nat.zero_le m))))

/-- A universe lift of the original matrix bridge, retaining all its arrows. -/
def liftedTelescopeFunctor :
    AsSmall.{u + 1} (StableGeneralLinear.GrothendieckModel.Telescope R) ⥤
      ProjectiveTelescope R := AsSmall.down ⋙ telescopeFunctor R

/-- The lifted original bridge remains full. -/
instance liftedTelescopeFunctor_full : (liftedTelescopeFunctor R).Full := by
  change ((AsSmall.equiv (C :=
    StableGeneralLinear.GrothendieckModel.Telescope R)).inverse ⋙ telescopeFunctor R).Full
  infer_instance

/-- The lifted original bridge remains faithful. -/
instance liftedTelescopeFunctor_faithful : (liftedTelescopeFunctor R).Faithful := by
  change ((AsSmall.equiv (C :=
    StableGeneralLinear.GrothendieckModel.Telescope R)).inverse ⋙ telescopeFunctor R).Faithful
  infer_instance

/-- Universe lifting preserves the matrix telescope's preconnectedness. -/
instance liftedMatrixTelescope_isPreconnected :
    IsPreconnected (AsSmall.{u + 1} (StableGeneralLinear.GrothendieckModel.Telescope R)) :=
  isPreconnected_of_equivalent (AsSmall.equiv (C :=
    StableGeneralLinear.GrothendieckModel.Telescope R))

/-- The original free-stage comparison is a homotopy equivalence onto the zero component. -/
def matrixTelescopeZeroComponentHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (StableGeneralLinear.GrothendieckModel.Telescope R))
      (pathComponent (classifyingSpacePoint (projectiveTelescopeBase R))) := by
  exact (classifyingSpaceUniverseHomeomorph.{u, u, u + 1}
    (StableGeneralLinear.GrothendieckModel.Telescope R)).toHomotopyEquiv.trans
      (Grothendieck.zeroComponentHomotopyEquiv
        (projectiveTelescopeDiagram R) (liftedTelescopeFunctor R)
        (matrixSequence R ⋙ AsSmall.up) (fun _ ↦ rfl))

/-- The forward map is exactly the original finite-matrix telescope map. -/
@[simp]
theorem matrixTelescopeZeroComponentHomotopyEquiv_val
    (x : ClassifyingSpace (StableGeneralLinear.GrothendieckModel.Telescope R)) :
    (matrixTelescopeZeroComponentHomotopyEquiv R x).val =
      classifyingSpaceMapUniversal (telescopeFunctor R) x := by
  change (Grothendieck.zeroComponentHomotopyEquiv
    (projectiveTelescopeDiagram R) (liftedTelescopeFunctor R)
    (matrixSequence R ⋙ AsSmall.up) (fun _ ↦ rfl)
    (classifyingSpaceMapUniversal AsSmall.up x)).val = _
  rw [Grothendieck.zeroComponentHomotopyEquiv_val]
  change (classifyingSpaceMap (liftedTelescopeFunctor R)).hom
    (classifyingSpaceMapUniversal AsSmall.up x) = _
  rw [← classifyingSpaceMapUniversal_eq]
  change ((classifyingSpaceMapUniversal (liftedTelescopeFunctor R)).comp
    (classifyingSpaceMapUniversal AsSmall.up)) x = _
  rw [← classifyingSpaceMapUniversal_comp]
  rfl

end ModuleCat.FiniteProjective.StableFreeRight
