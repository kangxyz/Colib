/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackClass

/-!
# Transport of the actual fixed-cube self-track normalization

Moving the original cube along a specified path conjugates its fundamental
group. The explicit inverse-prefix normalization removes precisely that
conjugation. No nullhomotopy or arbitrary component representative is chosen.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/GenLoopSelfTrackTransport.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, basepoints,
coordinate order and signs are retained under native Colib ownership. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u v
namespace Topology

/-- Postcomposition preserves conjugation along the actual image path. -/
theorem fundamentalGroup_mapOfEq_transport {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {x₀ x₁ : X} (β : Path x₀ x₁) (a : FundamentalGroup X x₀) :
    FundamentalGroup.mapOfEq f rfl (FundamentalGroup.fundamentalGroupMulEquivOfPath β a) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (β.map f.continuous)
        (FundamentalGroup.mapOfEq f rfl a) := by
  have h := congrArg HomotopyGroup.pi1MulEquivFundamentalGroup
    (pathTransport_naturality f β 1 (HomotopyGroup.pi1MulEquivFundamentalGroup.symm a))
  simp only [piOneEquivFundamentalGroup_pathTransport,
    HomotopyGroup.pi1MulEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The normalization follows the specified path of original cubes without changing its class. -/
theorem genLoopSelfTrackNormalization_transport {X : Type u} [TopologicalSpace X] {x : X}
    (m : ℕ) {p q : GenLoop (Fin (m + 1)) X x} (β : Path p q)
    (a : FundamentalGroup (GenLoop (Fin (m + 1)) X x) p) :
    genLoopSelfTrackNormalization m q
        (FundamentalGroup.fundamentalGroupMulEquivOfPath β a) =
      genLoopSelfTrackNormalization m p a := by
  let G := GenLoop (Fin (m + 1)) X x
  let B := GenLoop {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x
  let L : G ≃ₜ Path (GenLoop.const : B) GenLoop.const := GenLoop.loopHomeo (0 : Fin (m + 1))
  have hL : L.toHomotopyEquiv.toFun (GenLoop.const : G) = Path.refl GenLoop.const := by
    ext s z
    rfl
  let M := {j : Fin (m + 2) // j ≠ (0 : Fin (m + 2))}
  let e : GenLoop M X x ≃ₜ G :=
    GenLoop.congr x (finSuccAboveEquiv (0 : Fin (m + 2))).symm
  have he : e.toHomotopyEquiv.toFun GenLoop.const = (GenLoop.const : G) := by ext z; rfl
  let K : HomotopyGroup.Pi 2 B GenLoop.const ≃ HomotopyGroup.Pi (m + 2) X x :=
    (loopShiftMulEquiv 0).toEquiv.trans
      ((homotopyEquivPiEquiv L.toHomotopyEquiv hL 0).symm.toEquiv.trans
        ((homotopyEquivPiEquiv e.toHomotopyEquiv he 0).symm.toEquiv.trans
          (HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.trans
            (homotopyGroupEquivFundamentalGroup (0 : Fin (m + 2))).symm)))
  change K (loopKOneNormalization (L.toHomotopyEquiv.toFun q)
      (HomotopyGroup.pi1MulEquivFundamentalGroup
        (HomotopyGroup.map L.toHomotopyEquiv.toFun rfl
          (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
          (FundamentalGroup.fundamentalGroupMulEquivOfPath β a))))) =
    K (loopKOneNormalization (L.toHomotopyEquiv.toFun p)
      (HomotopyGroup.pi1MulEquivFundamentalGroup
        (HomotopyGroup.map L.toHomotopyEquiv.toFun rfl
          (HomotopyGroup.pi1MulEquivFundamentalGroup.symm a))))
  simp only [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply]
  rw [fundamentalGroup_mapOfEq_transport]
  exact congrArg K (loopKOneNormalization_transport (β.map L.toHomotopyEquiv.toFun.continuous)
    (FundamentalGroup.mapOfEq L.toHomotopyEquiv.toFun rfl a))

end Topology
