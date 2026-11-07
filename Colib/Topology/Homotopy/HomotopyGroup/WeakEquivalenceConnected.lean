/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransport
public import Colib.Topology.Homotopy.HomotopyGroup.ZeroDetection

/-! # Testing a weak equivalence at one point of a connected space

The actual zero-dimensional bijection and component surjectivity follow from
path connectedness; only the positive-degree bijections are inputs.

Source: the last theorem of `Quillen/Topology/HomotopyGroups/WeakEquivalenceProperty.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

open scoped Topology
universe u v
namespace Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Positive-degree tests at one actual point suffice for connected source and target. -/
theorem isWeakHomotopyEquivalence_of_connected [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) (x₀ : X)
    (h : ∀ n : ℕ, Function.Bijective (HomotopyGroup.piMap n f (x := x₀) rfl)) :
    IsWeakHomotopyEquivalence f := by
  apply isWeakHomotopyEquivalence_of_point f x₀
  intro x n
  cases n with
  | zero => exact homotopyGroupMap_zero_bijective f x
  | succ n => exact homotopyGroupMap_bijective_at_all_points f x₀ (n + 1) (h n) x

end Topology
