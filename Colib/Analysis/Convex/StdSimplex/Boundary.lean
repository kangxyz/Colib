/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Topology.UnitInterval

/-! # The geometric boundary of the native standard simplex

Adapted directly from the coordinate boundary in
`Quillen/Topology/Realization/SimplexBoundary.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The coordinates are the weights of the native Mathlib
`Convexity.StdSimplex` used by actual singular simplices.
-/
@[expose] public section
namespace Convexity.StdSimplex

/-- A finite real simplex point is on its boundary when a coordinate is zero. -/
def boundary (n : ℕ) : Set (StdSimplex ℝ (Fin (n + 1))) :=
  {x | ∃ i, x.weights i = 0}

/-- The geometric boundary is closed in the original native simplex. -/
theorem isClosed_boundary (n : ℕ) : IsClosed (boundary n) := by
  have h : boundary n = ⋃ i : Fin (n + 1), {x | x.weights i = (0 : ℝ)} := by
    ext x
    simp [boundary]
  rw [h]
  exact isClosed_iUnion_of_finite fun i ↦ isClosed_eq
    (continuous_weights_apply ℝ i) continuous_const

/-- The zero-dimensional simplex has no boundary. -/
theorem isEmpty_boundary_zero : IsEmpty (boundary 0) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := x.property
  have hi0 : i = 0 := Fin.eq_zero i
  subst i
  have h : x.val.weights (0 : Fin 1) = 1 := by simp
  exact zero_ne_one (hi.symm.trans h)

end Convexity.StdSimplex
