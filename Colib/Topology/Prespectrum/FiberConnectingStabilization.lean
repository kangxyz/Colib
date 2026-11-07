/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Colib.Topology.Prespectrum.FiberSequence
public import Colib.Topology.HomotopyFiber.LES

/-!
# The sign of stabilization for the levelwise fiber boundary

The original connecting homomorphism anti-commutes with the actual structure maps of arbitrary
loop prespectra. The inversion comes from interchanging the structure and fiber-path parameters.
No Omega-spectrum hypothesis or replacement of either connecting map is used.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/FiberConnectingStabilization.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual fiber coordinates, strict
structure maps, specified whole nullhomotopies, integer grading and connecting signs
are retained. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u
namespace Topology.LoopPrespectrum

/-- The levelwise fiber boundary anti-commutes with one original stabilization step. -/
theorem connectingHom_structurePiMap_sign {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (l k : ℕ) (a : HomotopyGroup.Pi (k + 2) (F.space l) (F.point l)) :
    HomotopyFiber.connectingHom (f.map (l + 1)) (F.point (l + 1)) (E.point (l + 1))
        (f.map_point (l + 1)) (k + 1) (structurePiMap F l (k + 1) a) =
      (structurePiMap (homotopyFiber f) l k
        (HomotopyFiber.connectingHom (f.map l) (F.point l) (E.point l)
          (f.map_point l) k a))⁻¹ := by
  have hs : loopShiftMulEquiv (x := F.point (l + 1)) (k + 1)
      (structurePiMap F l (k + 1) a) =
      (structurePiMap (parameterLooping F) l k
        (loopShiftMulEquiv (x := F.point l) k a))⁻¹ := by
    apply (loopShiftMulEquiv (x := F.point (l + 1)) (k + 1)).symm.injective
    simpa only [MulEquiv.symm_apply_apply, map_inv, inv_inv] using
      (congrArg Inv.inv (parameterLooping_structurePiMap_sign F l k
        (loopShiftMulEquiv (x := F.point l) k a))).symm
  have hn := congrArg (fun h ↦ h (loopShiftMulEquiv (x := F.point l) k a))
    (structurePiMap_naturality (homotopyFiberLoopInclusion f) l k)
  change HomotopyGroup.piMap (k + 1) ((homotopyFiberLoopInclusion f).map (l + 1))
    ((homotopyFiberLoopInclusion f).map_point (l + 1))
    (loopShiftMulEquiv (x := F.point (l + 1)) (k + 1)
      (structurePiMap F l (k + 1) a)) = _
  rw [hs, map_inv]
  exact congrArg Inv.inv hn.symm

end Topology.LoopPrespectrum
