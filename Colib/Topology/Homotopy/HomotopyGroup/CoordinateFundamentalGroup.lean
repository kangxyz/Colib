/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-! # The actual coordinate loop equivalence preserves the installed group structure -/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/CoordinateFundamentalGroup.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, basepoints,
coordinate order and signs are retained under native Colib ownership. -/
@[expose] public section
noncomputable section
open scoped Topology
universe u v
namespace Topology
variable {N : Type v} [DecidableEq N] [Nonempty N]
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The original coordinate equivalence, with the coordinate-independent group law. -/
def coordinateFundamentalGroupMulEquiv (i : N) :
    HomotopyGroup N X x ≃* FundamentalGroup
      (GenLoop {j : N // j ≠ i} X x) GenLoop.const where
  toEquiv := homotopyGroupEquivFundamentalGroup i
  map_mul' a b := by
    change homotopyGroupEquivFundamentalGroup i
      ((HomotopyGroup.auxGroup (Classical.arbitrary N)).mul a b) = _
    rw [HomotopyGroup.auxGroup_indep (Classical.arbitrary N) i]
    exact (homotopyGroupEquivFundamentalGroup i).apply_symm_apply _

/-- The upgraded equivalence does not change the underlying original map. -/
theorem coordinateFundamentalGroupMulEquiv_toEquiv (i : N) :
    (coordinateFundamentalGroupMulEquiv (X := X) (x := x) i).toEquiv =
      homotopyGroupEquivFundamentalGroup i := rfl

@[simp] private theorem coordinateFundamentalGroupMulEquiv_coe (i : N) :
    (coordinateFundamentalGroupMulEquiv (X := X) (x := x) i :
        HomotopyGroup N X x ≃ FundamentalGroup (GenLoop {j : N // j ≠ i} X x) GenLoop.const) =
      homotopyGroupEquivFundamentalGroup i := rfl

end Topology
