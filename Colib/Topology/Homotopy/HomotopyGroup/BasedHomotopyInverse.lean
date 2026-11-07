/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportComposition
public import Colib.Topology.Homotopy.HomotopyGroup.MovingBasepoint
/-!
Implementation provenance:
`Quillen/Topology/HomotopyGroups/BasedHomotopyInverse.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Corrected inverses with the original basepoint tracks

A homotopy equivalence need not preserve a chosen point strictly. Its inverse,
corrected by the image of the original point path and the displayed inverse
homotopy track, is the inverse on homotopy classes. No naturality of chosen
contractions or a fixed-point homotopy is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The based inverse correction uses precisely the given path and inverse homotopy. -/
theorem pathTransport_homotopyEquiv_inverse
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) (y : Y) (p : Path (e x) y)
    (H : (e.invFun.comp e.toFun).Homotopy (ContinuousMap.id X))
    (n : ℕ) (a : HomotopyGroup.Pi n X x) :
    pathTransport ((p.symm.map e.invFun.continuous).trans (H.evalAt x)) n
      (HomotopyGroup.map e.invFun rfl
        (pathTransport p n (HomotopyGroup.map e.toFun rfl a))) = a := by
  rw [pathTransport_trans, ← pathTransport_naturality e.invFun p n,
    ← Path.map_symm, pathTransport_symm_apply]
  rw [← HomotopyGroup.map_comp e.toFun rfl e.invFun rfl]
  exact (pathTransport_homotopyGroupMap_homotopy H x n a).trans
    (HomotopyGroup.map_id a)
/-- The same corrected inverse is also a right inverse, by actual forward bijectivity. -/
theorem pathTransport_homotopyEquiv_forward
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) (y : Y) (p : Path (e x) y)
    (H : (e.invFun.comp e.toFun).Homotopy (ContinuousMap.id X))
    (n : ℕ) (b : HomotopyGroup.Pi n Y y) :
    pathTransport p n (HomotopyGroup.map e.toFun rfl
      (pathTransport ((p.symm.map e.invFun.continuous).trans (H.evalAt x)) n
        (HomotopyGroup.map e.invFun rfl b))) = b := by
  obtain ⟨a, rfl⟩ := (pathTransport p n).surjective.comp
    (homotopyGroupMap_bijective_of_homotopyEquiv e rfl n).surjective b
  dsimp only [Function.comp_apply]
  rw [pathTransport_homotopyEquiv_inverse]

end Topology
