/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.CoordinateFundamentalGroup
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackClass

/-! # Multiplication and reversal in the original self-track time -/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/GenLoopSelfTrackTimeOperations.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, basepoints,
coordinate order and signs are retained under native Colib ownership. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The fixed-cube normalization preserves multiplication of actual track classes. -/
theorem genLoopSelfTrackNormalization_mul (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x)
    (a b : FundamentalGroup (GenLoop (Fin (m + 1)) X x) p) :
    genLoopSelfTrackNormalization m p (a * b) =
      genLoopSelfTrackNormalization m p a * genLoopSelfTrackNormalization m p b := by
  let G := GenLoop (Fin (m + 1)) X x
  let B := GenLoop {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x
  let L : G ≃ₜ Path (GenLoop.const : B) GenLoop.const := GenLoop.loopHomeo (0 : Fin (m + 1))
  have hL : L (GenLoop.const : G) = Path.refl GenLoop.const := by ext s z; rfl
  let M := {j : Fin (m + 2) // j ≠ (0 : Fin (m + 2))}
  let e : GenLoop M X x ≃ₜ G :=
    GenLoop.congr x (finSuccAboveEquiv (0 : Fin (m + 2))).symm
  have he : e GenLoop.const = (GenLoop.const : G) := by ext z; rfl
  let E : FundamentalGroup G p ≃* HomotopyGroup.Pi (m + 2) X x :=
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans
      ((homotopyEquivPiEquiv L.toHomotopyEquiv (x := p) rfl 0).trans
        (HomotopyGroup.pi1MulEquivFundamentalGroup.trans
          ((loopKOneNormalization (L p)).trans
            ((loopShiftMulEquiv 0).trans
              ((homotopyEquivPiEquiv L.toHomotopyEquiv hL 0).symm.trans
                ((homotopyEquivPiEquiv e.toHomotopyEquiv he 0).symm.trans
                  (HomotopyGroup.pi1MulEquivFundamentalGroup.trans
                    (coordinateFundamentalGroupMulEquiv (0 : Fin (m + 2))).symm)))))))
  exact map_mul E a b

/-- The fixed-cube normalization preserves reversal of the actual track class. -/
theorem genLoopSelfTrackNormalization_inv (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x)
    (a : FundamentalGroup (GenLoop (Fin (m + 1)) X x) p) :
    genLoopSelfTrackNormalization m p a⁻¹ = (genLoopSelfTrackNormalization m p a)⁻¹ := by
  let G := GenLoop (Fin (m + 1)) X x
  let B := GenLoop {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x
  let L : G ≃ₜ Path (GenLoop.const : B) GenLoop.const := GenLoop.loopHomeo (0 : Fin (m + 1))
  have hL : L (GenLoop.const : G) = Path.refl GenLoop.const := by ext s z; rfl
  let M := {j : Fin (m + 2) // j ≠ (0 : Fin (m + 2))}
  let e : GenLoop M X x ≃ₜ G :=
    GenLoop.congr x (finSuccAboveEquiv (0 : Fin (m + 2))).symm
  have he : e GenLoop.const = (GenLoop.const : G) := by ext z; rfl
  let E : FundamentalGroup G p ≃* HomotopyGroup.Pi (m + 2) X x :=
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans
      ((homotopyEquivPiEquiv L.toHomotopyEquiv (x := p) rfl 0).trans
        (HomotopyGroup.pi1MulEquivFundamentalGroup.trans
          ((loopKOneNormalization (L p)).trans
            ((loopShiftMulEquiv 0).trans
              ((homotopyEquivPiEquiv L.toHomotopyEquiv hL 0).symm.trans
                ((homotopyEquivPiEquiv e.toHomotopyEquiv he 0).symm.trans
                  (HomotopyGroup.pi1MulEquivFundamentalGroup.trans
                    (coordinateFundamentalGroupMulEquiv (0 : Fin (m + 2))).symm)))))))
  exact map_inv E a

/-- Reversing the literal track gives the inverse higher class. -/
theorem genLoopSelfTrackClass_symm (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (α : Path p p) :
    genLoopSelfTrackClass m p α.symm = (genLoopSelfTrackClass m p α)⁻¹ :=
  genLoopSelfTrackNormalization_inv m p (FundamentalGroup.fromPath ⟦α⟧)

/-- Track concatenation retains the library's reversed fundamental-group product order. -/
theorem genLoopSelfTrackClass_trans (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (α β : Path p p) :
    genLoopSelfTrackClass m p (α.trans β) =
      genLoopSelfTrackClass m p β * genLoopSelfTrackClass m p α :=
  genLoopSelfTrackNormalization_mul m p (FundamentalGroup.fromPath ⟦β⟧)
    (FundamentalGroup.fromPath ⟦α⟧)

end Topology
