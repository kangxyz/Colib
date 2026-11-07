/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.SimplexCharts
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Vertex Stars

The actual open vertex star in the geometric simplex boundary.
-/

@[expose] public section

noncomputable section
open Set Convexity Convexity.StdSimplex
open scoped unitInterval
namespace Convexity.StdSimplex.Boundary
variable {n : ℕ}

/-- The actual open vertex star in the geometric simplex boundary. -/
def vertexStar (i : Fin (n + 3)) : Set (boundary (n + 2)) := {x | 0 < x.val.weights i}

/-- The original simplex vertex, regarded as an actual boundary point. -/
def vertex (i : Fin (n + 3)) : boundary (n + 2) := by
  refine ⟨StdSimplex.single i, ?_⟩
  obtain ⟨j, hji, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
  exact ⟨j, by simp [StdSimplex.weights_single, Ne.symm hji]⟩

@[simp]
theorem vertex_mem (i : Fin (n + 3)) : vertex i ∈ vertexStar i := by
  simp [vertexStar, vertex, StdSimplex.weights_single]

/-- These are genuinely open sets of the boundary, not closed geometric faces. -/
theorem isOpen_vertexStar (i : Fin (n + 3)) : IsOpen (vertexStar i) :=
  isOpen_lt continuous_const ((StdSimplex.continuous_weights_apply ℝ i).comp
    continuous_subtype_val)

/-- The open vertex stars cover every actual boundary point. -/
theorem vertexStars_cover (x : boundary (n + 2)) : x ∈ ⋃ i, vertexStar i := by
  obtain ⟨i, hi⟩ := x.val.support_weights_nonempty
  refine mem_iUnion.mpr ⟨i, ?_⟩
  exact lt_of_le_of_ne (x.val.weights_nonneg i) (Finsupp.mem_support_iff.mp hi).symm

/-- The actual segment to its star vertex stays in the original boundary. -/
theorem segment_mem_boundary (i : Fin (n + 3)) (x : vertexStar i) (t : I) :
    simplexSegment x.val.val (vertex i).val t ∈ boundary (n + 2) := by
  obtain ⟨j, hj⟩ := x.val.property
  have hji : j ≠ i := by
    intro h
    subst j
    exact (ne_of_gt x.property) hj
  refine ⟨j, ?_⟩
  rw [simplexSegment_apply]
  simp [hj, vertex, StdSimplex.weights_single, Ne.symm hji]

/-- The same segment stays strictly in the chosen open star, including endpoints. -/
theorem segment_weight_pos (i : Fin (n + 3)) (x : vertexStar i) (t : I) :
    0 < (simplexSegment x.val.val (vertex i).val t).weights i := by
  rw [simplexSegment_apply]
  have hx : 0 < x.val.val.weights i := x.property
  have hv : (vertex i).val.weights i = 1 := by simp [vertex, StdSimplex.weights_single]
  rw [hv]
  have ht0 := t.property.1
  have ht1 := t.property.2
  by_cases ht : (t : ℝ) = 0
  · simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hx
  · have hp : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hn : 0 ≤ (1 - (t : ℝ)) * x.val.val.weights i :=
      mul_nonneg (by linarith) hx.le
    linarith

/-- A contraction through actual boundary points; the formula is the original
straight barycentric segment and its image remains in the specified open star. -/
def vertexStarContraction (i : Fin (n + 3)) :
    (ContinuousMap.id (vertexStar i)).Homotopy
      (ContinuousMap.const (vertexStar i) ⟨vertex i, vertex_mem i⟩) where
  toFun z := ⟨⟨simplexSegment z.2.val.val (vertex i).val z.1,
    segment_mem_boundary i z.2 z.1⟩, segment_weight_pos i z.2 z.1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 3))).continuous_iff]
    unfold Function.comp
    refine continuous_pi (fun j => ?_)
    simp only [simplexSegment_apply]
    fun_prop
  map_zero_left x := Subtype.ext (Subtype.ext (simplexSegment _ _).source)
  map_one_left x := Subtype.ext (Subtype.ext (simplexSegment _ _).target)

/-- Contractibility is proved for the actual open star, not assumed for a chart. -/
theorem contractible_vertexStar (i : Fin (n + 3)) : ContractibleSpace (vertexStar i) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨⟨vertex i, vertex_mem i⟩,
    ⟨vertexStarContraction i⟩⟩

end Convexity.StdSimplex.Boundary
