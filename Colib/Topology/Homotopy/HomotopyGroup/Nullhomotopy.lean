/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.Homotopy.HomotopyGroup.Constant
public import Colib.Topology.Homotopy.HomotopyGroup.BasedHomotopy

/-! The based nullhomotopy consequence from Quillen/Topology/HomotopyGroups/Map.lean
at c561118b7795eb9780be9ed391c3251d6a4d0afd, using the existing actual piMap. -/
@[expose] public section
universe u v
namespace HomotopyGroup
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}

/-- A nullhomotopy that fixes the displayed point induces the trivial homomorphism. -/
theorem piMap_eq_one_of_based_nullhomotopy (n : ℕ) {f : C(X, Y)}
    (hf : f x = y) (H : f.Homotopy (ContinuousMap.const X y))
    (hH : ∀ t, H (t, x) = y) : piMap n f hf = 1 := by
  exact (piMap_eq_of_based_homotopy n hf rfl H hH).trans (piMap_const n)

end HomotopyGroup
