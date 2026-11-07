/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Geometry.Convex.ConvexSpace.Module
public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Affine interpolation in the native standard simplex

Adapted from `Quillen/Topology/LocalCoefficients/BarycentricGeometry.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Interpolation is the native free-convex-space
map `StdSimplex.affineMapMk`. Its weights are exactly the original finite coordinate sum.
-/

@[expose] public noncomputable section

open scoped BigOperators Topology

namespace Convexity.StdSimplex

/-- The weights of a native affine simplex are the finite weighted sum of its vertices. -/
theorem affineMapMk_weights_of_fintype {I J : Type*} [Fintype I]
    (v : I → StdSimplex ℝ J) (x : StdSimplex ℝ I) :
    (StdSimplex.affineMapMk v x).weights = ∑ i, x.weights i • (v i).weights := by
  calc
    _ = iConvexComb x (fun i ↦ (v i).weights) :=
      (StdSimplex.isAffineMap_weights ℝ J).map_iConvexComb x v
    _ = ∑ i, x.weights i • (v i).weights := by
      rw [iConvexComb_eq_sum, Finsupp.sum_fintype _ _ (by simp)]

namespace BarycentricSubdivision

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- The continuous affine simplex with the prescribed native vertices. -/
def affineSimplex (v : I → StdSimplex ℝ J) :
    C(StdSimplex ℝ I, StdSimplex ℝ J) where
  toFun := StdSimplex.affineMapMk v
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ J).continuous_iff]
    apply continuous_pi
    intro j
    change Continuous (fun x : StdSimplex ℝ I ↦ (StdSimplex.affineMapMk v x).weights j)
    simp only [affineMapMk_weights_of_fintype, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    fun_prop

/-- Each affine coordinate is the original weighted sum of vertex coordinates. -/
theorem affineSimplex_weights (v : I → StdSimplex ℝ J)
    (x : StdSimplex ℝ I) (j : J) :
    (affineSimplex v x).weights j = ∑ i, x.weights i * (v i).weights j := by
  change (StdSimplex.affineMapMk v x).weights j = _
  simp only [affineMapMk_weights_of_fintype, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]

/-- Interpolation at a vertex recovers the specified vertex. -/
@[simp]
theorem affineSimplex_single (v : I → StdSimplex ℝ J) (i : I) :
    affineSimplex v (StdSimplex.single i) = v i := by
  change StdSimplex.affineMapMk (R := ℝ) v (StdSimplex.single i) = v i
  exact StdSimplex.affineMapMk_single (R := ℝ) v i

/-- The affine simplex on the original vertices is the identity. -/
@[simp]
theorem affineSimplex_identity :
    affineSimplex (fun i : I ↦ StdSimplex.single i) = ContinuousMap.id _ := by
  ext x : 1
  exact StdSimplex.iConvexComb_single x

/-- Reindexing vertices is exactly precomposition by the native simplex map. -/
theorem affineSimplex_map (v : I → StdSimplex ℝ J) (f : K → I)
    (x : StdSimplex ℝ K) :
    affineSimplex v (x.map f) = affineSimplex (v ∘ f) x :=
  Convexity.iConvexComb_map x f v

/-- Composition applies the outer affine map to each original vertex. -/
theorem affineSimplex_comp (v : I → StdSimplex ℝ J)
    (w : J → StdSimplex ℝ K) :
    (affineSimplex w).comp (affineSimplex v) =
      affineSimplex (affineSimplex w ∘ v) := by
  ext x : 1
  exact (Convexity.iConvexComb_assoc x v w).symm

/-- The barycenter of a nonempty tuple, with repeated vertices retained. -/
def tupleBarycenter [Nonempty I] (v : I → StdSimplex ℝ J) :
    StdSimplex ℝ J :=
  affineSimplex v StdSimplex.barycenter

/-- Coordinates of the uniform average of the given vertices. -/
theorem tupleBarycenter_weights [Nonempty I]
    (v : I → StdSimplex ℝ J) (j : J) :
    (tupleBarycenter v).weights j = (Fintype.card I : ℝ)⁻¹ * ∑ i, (v i).weights j := by
  simp only [tupleBarycenter, affineSimplex_weights, StdSimplex.weights_barycenter_apply]
  exact (Finset.mul_sum _ _ _).symm

/-- A genuine affine simplex commutes with the uniform average. -/
theorem tupleBarycenter_natural [Nonempty I]
    (v : I → StdSimplex ℝ J) (w : J → StdSimplex ℝ K) :
    affineSimplex w (tupleBarycenter v) = tupleBarycenter (affineSimplex w ∘ v) :=
  ContinuousMap.congr_fun (affineSimplex_comp v w) StdSimplex.barycenter

end BarycentricSubdivision
end Convexity.StdSimplex
