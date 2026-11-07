/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.SimplexBoundary.StarTrivializations

/-!
# Boundary Edges

Every actual geometric edge lies in a zero-coordinate boundary face.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory stdSimplex FundamentalGroupoid.OpenCover
open scoped unitInterval
namespace stdSimplex.Boundary
variable {n : ℕ}

/-- Every actual geometric edge lies in a zero-coordinate boundary face. -/
theorem boundaryEdge_mem (i j : Fin (n + 3)) (t : I) :
    simplexSegment (vertex i).val (vertex j).val t ∈ boundary (n + 2) := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  refine ⟨k, ?_⟩
  rw [simplexSegment_apply]
  simp [vertex, stdSimplex.vertex_coe, Ne.symm hki, Ne.symm hkj]

/-- The actual original straight edge, with its precise boundary vertices. -/
def boundaryEdge (i j : Fin (n + 3)) : Path (vertex i) (vertex j) where
  toFun t := ⟨simplexSegment (vertex i).val (vertex j).val t, boundaryEdge_mem i j t⟩
  continuous_toFun := (simplexSegment _ _).continuous.subtype_mk _
  source' := Subtype.ext (simplexSegment _ _).source
  target' := Subtype.ext (simplexSegment _ _).target

/-- Paths in the same actual zero-coordinate face have a relative homotopy
through that face. No simple connectedness of the whole boundary is assumed. -/
def facePathHomotopy {x y : boundary (n + 2)} (p q : Path x y) (k : Fin (n + 3))
    (hp : ∀ t, (p t).val k = 0) (hq : ∀ t, (q t).val k = 0) :
    p.Homotopy q := by
  let H := stdSimplex.pathHomotopy
    (p.map continuous_subtype_val) (q.map continuous_subtype_val)
  have hH (z : I × I) : H z ∈ boundary (n + 2) := by
    refine ⟨k, ?_⟩
    change (1 - (z.1 : ℝ)) * (p z.2).val k + (z.1 : ℝ) * (q z.2).val k = 0
    simp only [hp, hq, mul_zero, add_zero]
  exact {
    toFun := fun z => ⟨H z, hH z⟩
    continuous_toFun := H.continuous.subtype_mk hH
    map_zero_left := fun t => Subtype.ext (H.map_zero_left t)
    map_one_left := fun t => Subtype.ext (H.map_one_left t)
    prop' := fun t z hz => Subtype.ext (H.prop' t z hz) }

/-- The source-directed spoke from the specified edge midpoint, in the actual boundary. -/
def midpointSpokeLeft (i j : Fin (n + 3)) : Path (edgeMidpoint i j) (vertex i) :=
  (starSpoke i ⟨edgeMidpoint i j, (edgeMidpoint_mem i j).1⟩).map
    ((ContinuousMap.subtypeVal (vertexStar i))).continuous

/-- The target-directed spoke from the very same actual midpoint. -/
def midpointSpokeRight (i j : Fin (n + 3)) : Path (edgeMidpoint i j) (vertex j) :=
  (starSpoke j ⟨edgeMidpoint i j, (edgeMidpoint_mem i j).2⟩).map
    ((ContinuousMap.subtypeVal (vertexStar j))).continuous

/-- Both midpoint spokes concatenate to the original edge class, with exact endpoints. -/
def midpointSpokesHomotopy (i j : Fin (n + 3)) :
    ((midpointSpokeLeft i j).symm.trans (midpointSpokeRight i j)).Homotopy
      (boundaryEdge i j) := by
  have hex := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  let k := Classical.choose hex
  have hki : k ≠ i := (Classical.choose_spec hex).1
  have hkj : k ≠ j := (Classical.choose_spec hex).2
  have hvi : (vertex i).val k = 0 := by
    simp [vertex, stdSimplex.vertex_coe, Ne.symm hki]
  have hvj : (vertex j).val k = 0 := by
    simp [vertex, stdSimplex.vertex_coe, Ne.symm hkj]
  have hm : (edgeMidpoint i j).val k = 0 := by
    change (simplexSegment (vertex i).val (vertex j).val _) k = 0
    rw [simplexSegment_apply]
    simp [hvi, hvj]
  have hl : range (midpointSpokeLeft i j) ⊆ {x | x.val k = 0} := by
    rintro _ ⟨t, rfl⟩
    change (simplexSegment (edgeMidpoint i j).val (vertex i).val t) k = 0
    rw [simplexSegment_apply]
    simp [hm, hvi]
  have hr : range (midpointSpokeRight i j) ⊆ {x | x.val k = 0} := by
    rintro _ ⟨t, rfl⟩
    change (simplexSegment (edgeMidpoint i j).val (vertex j).val t) k = 0
    rw [simplexSegment_apply]
    simp [hm, hvj]
  have hc : range ((midpointSpokeLeft i j).symm.trans (midpointSpokeRight i j)) ⊆
      {x | x.val k = 0} := by
    rw [Path.trans_range, Path.symm_range]
    exact union_subset hl hr
  exact facePathHomotopy _ _ k (fun t => hc (mem_range_self t)) (fun t => by
    change (simplexSegment (vertex i).val (vertex j).val t) k = 0
    rw [simplexSegment_apply]
    simp [hvi, hvj])

end stdSimplex.Boundary
