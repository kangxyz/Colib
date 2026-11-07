/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.Analysis.Convex.StdSimplex.PathHomotopy
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Connectivity of the native topological standard simplex

Adapted from `Quillen/Topology/Realization/SimplexConnectivity.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Here the simplex is the actual
function-subtype `stdSimplex` used by the pinned Mathlib singular-set functor,
not the newer finitely supported convex-space simplex. Its native convexity
proves contractibility and local path connectedness directly.
-/

@[expose] public noncomputable section

namespace stdSimplex

/-- Every nonempty native finite standard simplex is contractible. -/
theorem contractibleSpace (M : Type*) [Fintype M] [Nonempty M] :
    ContractibleSpace (_root_.stdSimplex ℝ M) := by
  classical
  exact (convex_stdSimplex ℝ M).contractibleSpace
    ⟨Pi.single (Classical.arbitrary M) 1, single_mem_stdSimplex ℝ _⟩

/-- Every native finite standard simplex is locally path connected. -/
theorem locallyPathConnectedSpace (M : Type*) [Fintype M] :
    LocallyPathConnectedSpace (_root_.stdSimplex ℝ M) :=
  (convex_stdSimplex ℝ M).locallyPathConnectedSpace

/-- The actual nonempty finite standard simplex is simply connected. -/
theorem simplyConnectedSpace (M : Type*) [Fintype M] [Nonempty M] :
    SimplyConnectedSpace (_root_.stdSimplex ℝ M) := by
  let := contractibleSpace M
  infer_instance


end stdSimplex
