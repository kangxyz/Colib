/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-! # Closed boundaries of finite cubes

Adapted from Quillen/Topology/FilteredRealization/Homotopy.lean:112-119 at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The boundary is Mathlib's actual cube boundary.
-/
@[expose] public section

namespace Cube

/-- The whole boundary of a finite-dimensional cube is closed. -/
theorem isClosed_boundary (N : Type*) [Finite N] : IsClosed (boundary N) := by
  have h (i : N) : IsClosed (Set.ofPred (fun x : N → unitInterval ↦ x i = 0 ∨ x i = 1)) :=
    (isClosed_eq (continuous_apply i) continuous_const).union
      (isClosed_eq (continuous_apply i) continuous_const)
  convert isClosed_iUnion_of_finite h using 1
  ext x
  simp only [boundary, Set.mem_iUnion]
  rfl

end Cube
