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
  simp only [genLoopSelfTrackNormalization, Equiv.trans_apply, MulEquiv.toEquiv_eq_coe,
    MulEquiv.coe_toEquiv, map_mul]
  exact (coordinateFundamentalGroupMulEquiv (0 : Fin (m + 2))).symm.map_mul _ _

/-- The fixed-cube normalization preserves reversal of the actual track class. -/
theorem genLoopSelfTrackNormalization_inv (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x)
    (a : FundamentalGroup (GenLoop (Fin (m + 1)) X x) p) :
    genLoopSelfTrackNormalization m p a⁻¹ = (genLoopSelfTrackNormalization m p a)⁻¹ := by
  simp only [genLoopSelfTrackNormalization, Equiv.trans_apply, MulEquiv.toEquiv_eq_coe,
    MulEquiv.coe_toEquiv, map_inv]
  exact (coordinateFundamentalGroupMulEquiv (0 : Fin (m + 2))).symm.map_inv _

/-- Reversing the literal track gives the inverse higher class. -/
theorem genLoopSelfTrackClass_symm (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (α : Path p p) :
    genLoopSelfTrackClass m p α.symm = (genLoopSelfTrackClass m p α)⁻¹ :=
  genLoopSelfTrackNormalization_inv m p ⟦α⟧

/-- Track concatenation retains the library's reversed fundamental-group product order. -/
theorem genLoopSelfTrackClass_trans (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (α β : Path p p) :
    genLoopSelfTrackClass m p (α.trans β) =
      genLoopSelfTrackClass m p β * genLoopSelfTrackClass m p α :=
  genLoopSelfTrackNormalization_mul m p ⟦β⟧ ⟦α⟧

end Topology
