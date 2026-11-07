/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Affine interpolation in the native standard simplex

Adapted from `Quillen/Topology/LocalCoefficients/BarycentricGeometry.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The coordinates are the actual
function-subtype standard simplex used by the pinned singular-set functor.
Affine interpolation is the finite coordinate sum, not a transported model.
-/

@[expose] public noncomputable section

open scoped BigOperators Topology

namespace stdSimplex.BarycentricSubdivision

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- The continuous affine simplex with the prescribed native vertices. -/
def affineSimplex (v : I → _root_.stdSimplex ℝ J) :
    C(_root_.stdSimplex ℝ I, _root_.stdSimplex ℝ J) where
  toFun x := ⟨fun j ↦ ∑ i, x i * v i j,
    fun j ↦ Finset.sum_nonneg fun i _ ↦
      mul_nonneg (stdSimplex.zero_le x i) (stdSimplex.zero_le (v i) j), by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    have h (i : I) : Continuous (fun x : _root_.stdSimplex ℝ I ↦ x i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact continuous_finsetSum _ fun i _ ↦ (h i).mul_const (v i j)

/-- Each affine coordinate is the original weighted sum of vertex coordinates. -/
theorem affineSimplex_weights (v : I → _root_.stdSimplex ℝ J)
    (x : _root_.stdSimplex ℝ I) (j : J) :
    affineSimplex v x j = ∑ i, x i * v i j := rfl

/-- Interpolation at a vertex recovers the specified vertex. -/
@[simp]
theorem affineSimplex_single [DecidableEq I] (v : I → _root_.stdSimplex ℝ J) (i : I) :
    affineSimplex v (stdSimplex.vertex i) = v i := by
  ext j
  simp [affineSimplex_weights, stdSimplex.vertex, Pi.single_apply]

/-- The affine simplex on the original vertices is the identity. -/
@[simp]
theorem affineSimplex_identity [DecidableEq I] :
    affineSimplex (fun i : I ↦ stdSimplex.vertex i) = ContinuousMap.id _ := by
  ext x j
  simp [affineSimplex_weights, stdSimplex.vertex, Pi.single_apply]

/-- Reindexing vertices is exactly precomposition by the native simplex map. -/
theorem affineSimplex_map (v : I → _root_.stdSimplex ℝ J) (f : K → I)
    (x : _root_.stdSimplex ℝ K) :
    affineSimplex v (stdSimplex.map f x) = affineSimplex (v ∘ f) x := by
  classical
  ext j
  simp only [affineSimplex_weights, Function.comp_apply]
  change (∑ i, (FunOnFinite.linearMap ℝ ℝ f (x : K → ℝ)) i * v i j) = _
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_mul]
  calc
    ∑ i, ∑ k ∈ Finset.univ with f k = i, x k * v i j =
        ∑ i, ∑ k ∈ Finset.univ with f k = i, x k * v (f k) j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k hk
      rw [(Finset.mem_filter.mp hk).2]
    _ = ∑ k, x k * v (f k) j := Finset.sum_fiberwise _ _ _

/-- Composition applies the outer affine map to each original vertex. -/
theorem affineSimplex_comp (v : I → _root_.stdSimplex ℝ J)
    (w : J → _root_.stdSimplex ℝ K) :
    (affineSimplex w).comp (affineSimplex v) =
      affineSimplex (affineSimplex w ∘ v) := by
  ext x k
  change (∑ j, (∑ i, x i * v i j) * w j k) =
    ∑ i, x i * ∑ j, v i j * w j k
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- The barycenter of a nonempty tuple, with repeated vertices retained. -/
def tupleBarycenter [Nonempty I] (v : I → _root_.stdSimplex ℝ J) :
    _root_.stdSimplex ℝ J :=
  affineSimplex v stdSimplex.barycenter

/-- Coordinates of the uniform average of the given vertices. -/
theorem tupleBarycenter_weights [Nonempty I]
    (v : I → _root_.stdSimplex ℝ J) (j : J) :
    tupleBarycenter v j = (Fintype.card I : ℝ)⁻¹ * ∑ i, v i j := by
  simp only [tupleBarycenter, affineSimplex_weights]
  change (∑ i, (Fintype.card I : ℝ)⁻¹ * v i j) = _
  exact (Finset.mul_sum _ _ _).symm

/-- A genuine affine simplex commutes with the uniform average. -/
theorem tupleBarycenter_natural [Nonempty I]
    (v : I → _root_.stdSimplex ℝ J) (w : J → _root_.stdSimplex ℝ K) :
    affineSimplex w (tupleBarycenter v) = tupleBarycenter (affineSimplex w ∘ v) :=
  ContinuousMap.congr_fun (affineSimplex_comp v w) stdSimplex.barycenter

end stdSimplex.BarycentricSubdivision
