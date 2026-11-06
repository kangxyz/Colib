/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.SimplexBoundary.VertexStars

/-!
# Overlap Stars

Strict coordinate positivity is preserved by the actual simplex segment.
-/

@[expose] public section

noncomputable section
open Set Convexity Convexity.StdSimplex
open scoped unitInterval
namespace Convexity.StdSimplex.Boundary
variable {n : ℕ}

/-- Strict coordinate positivity is preserved by the actual simplex segment. -/
theorem segment_coordinate_pos {x y : StdSimplex ℝ (Fin (n + 3))} (k : Fin (n + 3))
    (hx : 0 < x.weights k) (hy : 0 < y.weights k) (t : I) :
    0 < (simplexSegment x y t).weights k := by
  rw [simplexSegment_weights]
  have ht0 := t.property.1
  have ht1 := t.property.2
  by_cases ht : (t : ℝ) = 0
  · simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hx
  · have hp : 0 < (t : ℝ) * y.weights k :=
      mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) hy
    have hn : 0 ≤ (1 - (t : ℝ)) * x.weights k := mul_nonneg (by linarith) hx.le
    linarith

/-- The prescribed midpoint of the original geometric edge. -/
def edgeMidpoint (i j : Fin (n + 3)) : simplexBoundary (n + 2) := by
  refine ⟨simplexSegment (vertex i).val (vertex j).val ⟨1 / 2, by norm_num⟩, ?_⟩
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  refine ⟨k, ?_⟩
  rw [simplexSegment_weights]
  simp [vertex, StdSimplex.weights_single, Ne.symm hki, Ne.symm hkj]

/-- Both original edge-endpoint coordinates are positive at its midpoint. -/
theorem edgeMidpoint_mem (i j : Fin (n + 3)) : edgeMidpoint i j ∈ vertexStar i ∩ vertexStar j := by
  change 0 < (simplexSegment (vertex i).val (vertex j).val _).weights i ∧
    0 < (simplexSegment (vertex i).val (vertex j).val _).weights j
  rw [simplexSegment_weights, simplexSegment_weights]
  by_cases h : i = j
  · subst j
    norm_num [vertex, StdSimplex.weights_single]
  · norm_num [vertex, StdSimplex.weights_single, h, Ne.symm h]

/-- Actual overlap segments to the specified midpoint stay on the boundary. -/
theorem overlap_segment_boundary (i j : Fin (n + 3)) (x : ↥(vertexStar i ∩ vertexStar j))
    (t : I) : simplexSegment x.val.val (edgeMidpoint i j).val t ∈ simplexBoundary (n + 2) := by
  obtain ⟨k, hk⟩ := x.val.property
  have hki : k ≠ i := by
    intro h
    subst k
    exact (ne_of_gt x.property.1) hk
  have hkj : k ≠ j := by
    intro h
    subst k
    exact (ne_of_gt x.property.2) hk
  refine ⟨k, ?_⟩
  rw [simplexSegment_weights]
  have hm : (edgeMidpoint i j).val.weights k = 0 := by
    change (simplexSegment (vertex i).val (vertex j).val _).weights k = 0
    rw [simplexSegment_weights]
    simp [vertex, StdSimplex.weights_single, Ne.symm hki, Ne.symm hkj]
  simp [hk, hm]

/-- The actual overlap contracts to the specified original edge midpoint. -/
def overlapContraction (i j : Fin (n + 3)) :
    (ContinuousMap.id ↥(vertexStar i ∩ vertexStar j)).Homotopy
      (ContinuousMap.const ↥(vertexStar i ∩ vertexStar j)
        ⟨edgeMidpoint i j, edgeMidpoint_mem i j⟩) where
  toFun z := ⟨⟨simplexSegment z.2.val.val (edgeMidpoint i j).val z.1,
    overlap_segment_boundary i j z.2 z.1⟩,
    segment_coordinate_pos i z.2.property.1 (edgeMidpoint_mem i j).1 z.1,
    segment_coordinate_pos j z.2.property.2 (edgeMidpoint_mem i j).2 z.1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 3))).continuous_iff]
    unfold Function.comp
    refine continuous_pi (fun k => ?_)
    simp only [simplexSegment_weights]
    fun_prop
  map_zero_left x := Subtype.ext (Subtype.ext (simplexSegment _ _).source)
  map_one_left x := Subtype.ext (Subtype.ext (simplexSegment _ _).target)

/-- Every actual pairwise star overlap is contractible, hence path-connected. -/
theorem contractible_overlap (i j :
    Fin (n + 3)) : ContractibleSpace ↥(vertexStar i ∩ vertexStar j) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨⟨edgeMidpoint i j, edgeMidpoint_mem i j⟩, ⟨overlapContraction i j⟩⟩

end Convexity.StdSimplex.Boundary
