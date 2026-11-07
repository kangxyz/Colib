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
finite-support `Convexity.StdSimplex` used by the pinned Mathlib singular-set functor.
Native convex interpolation proves contractibility. The actual weights embedding
identifies its topology with that of its convex image for local path connectedness.
-/

@[expose] public noncomputable section

open Convexity
open scoped unitInterval

namespace Convexity.StdSimplex

/-- Every nonempty native finite standard simplex is contractible. -/
theorem contractibleSpace (M : Type*) [Finite M] [Nonempty M] :
    ContractibleSpace (StdSimplex ℝ M) := by
  classical
  let center : StdSimplex ℝ M := .single (Classical.arbitrary M)
  refine (contractible_iff_id_nullhomotopic _).mpr ⟨center, ⟨{
    toFun z := convexCombPair (R := ℝ) (unitInterval.symm z.1) z.1
      (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) z.2 center
    continuous_toFun := ?_
    map_zero_left := by intro x; simp
    map_one_left := by intro x; simp }⟩⟩
  rw [(isEmbedding_toFun_comp_weights ℝ M).continuous_iff]
  unfold Function.comp
  refine continuous_pi (fun i ↦ ?_)
  simp only [unitInterval.coe_symm_eq, weights_convexCombPair,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

private theorem convex_range_weights (M : Type*) :
    Convex ℝ (Set.range (fun x : StdSimplex ℝ M ↦ (x.weights : M → ℝ))) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ a b ha hb hab
  refine ⟨convexCombPair a b ha hb hab x y, ?_⟩
  ext i
  simp [weights_convexCombPair]

/-- Every native finite standard simplex is locally path connected. -/
theorem locallyPathConnectedSpace (M : Type*) [Finite M] :
    LocallyPathConnectedSpace (StdSimplex ℝ M) := by
  let := (convex_range_weights M).locallyPathConnectedSpace
  exact (isEmbedding_toFun_comp_weights ℝ M).toHomeomorph.symm.locallyPathConnectedSpace

/-- The actual nonempty finite standard simplex is simply connected. -/
theorem simplyConnectedSpace (M : Type*) [Finite M] [Nonempty M] :
    SimplyConnectedSpace (Convexity.StdSimplex ℝ M) := by
  let := contractibleSpace M
  infer_instance


end Convexity.StdSimplex
