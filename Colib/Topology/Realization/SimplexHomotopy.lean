/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Topology.Homotopy.Path

/-!
# Explicit relative homotopies in finite simplices

Extracted from `Quillen/Topology/Realization/SimplexHomotopy.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, endpoints,
relative homotopies, universe parameters and multiplication order are retained.
Only native namespace and import ownership change unless noted below.

-/

@[expose] public noncomputable section

universe u

open scoped Topology unitInterval
open Convexity

namespace Convexity.StdSimplex

/-- Jointly continuous convex interpolation of two moving points in a finite simplex. -/
def pathHomotopy {M : Type*} [Finite M]
    {x y : StdSimplex ℝ M} (p q : Path x y) : p.Homotopy q where
  toFun z := convexCombPair (R := ℝ) (unitInterval.symm z.1) z.1
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) (p z.2) (q z.2)
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ M).continuous_iff]
    unfold Function.comp
    refine continuous_pi (fun i ↦ ?_)
    simp only [unitInterval.coe_symm_eq, StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  map_zero_left t := by simp
  map_one_left t := by simp
  prop' t z hz := by
    rcases hz with hz | hz
    · subst z
      simp
    · rw [Set.mem_singleton_iff] at hz
      subst z
      simp

/-- Any two paths in a finite topological standard simplex with fixed
endpoints are homotopic relative to the endpoints. -/
theorem paths_homotopic {M : Type*} [Finite M]
    {x y : StdSimplex ℝ M} (p q : Path x y) : p.Homotopic q :=
  ⟨pathHomotopy p q⟩

end Convexity.StdSimplex

attribute [colib_tag "COL-0082",
  colib_ref "HatcherAT" "Section 1.1, Example 1.1, page 25"
    "adaptation"
    "Endpoint-fixed linear interpolation in finite real barycentric simplices"]
  Convexity.StdSimplex.pathHomotopy
  Convexity.StdSimplex.paths_homotopic
