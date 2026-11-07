/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexBoundary.BoundaryEdges
public import Colib.Topology.ClassifyingSpace.NerveCompletion.StageInclusion
public import Colib.Topology.ClassifyingSpace.NerveCompletion.EdgeCoordinates

/-!
# Face Geometry

The original interval path is exactly the original straight barycentric segment.
-/

@[expose] public section

noncomputable section
open CategoryTheory stdSimplex SSet TopCat
open scoped Simplicial Topology
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment stdSimplex.Boundary

/-- The original interval path is exactly the original straight barycentric segment. -/
theorem intervalPath_segment (t : unitInterval) :
    NerveGraphData.intervalPath t =
      simplexSegment (_root_.stdSimplex.vertex (0 : Fin 2)) (_root_.stdSimplex.vertex 1) t := by
  ext k
  fin_cases k
  · change (NerveGraphData.intervalPath t) 0 =
      (simplexSegment (_root_.stdSimplex.vertex (0 : Fin 2)) (_root_.stdSimplex.vertex 1) t) 0
    rw [CategoryTheory.NerveCompletion.intervalPath_weight_zero, simplexSegment_apply]
    simp [stdSimplex.vertex_coe]
  · change (NerveGraphData.intervalPath t) 1 =
      (simplexSegment (_root_.stdSimplex.vertex (0 : Fin 2)) (_root_.stdSimplex.vertex 1) t) 1
    rw [CategoryTheory.NerveCompletion.intervalPath_weight_one, simplexSegment_apply]
    simp [stdSimplex.vertex_coe]

/-- A finite vertex map carries the actual interval to its exact straight edge. -/
theorem map_intervalPath {n : ℕ} (f : Fin 2 → Fin (n + 1)) (t : unitInterval) :
    stdSimplex.map f (NerveGraphData.intervalPath t) =
      simplexSegment (_root_.stdSimplex.vertex (f 0)) (_root_.stdSimplex.vertex (f 1)) t := by
  rw [intervalPath_segment, map_simplexSegment]
  exact congrArg₂ (fun x y ↦ simplexSegment x y t)
    (stdSimplex.map_vertex f 0) (stdSimplex.map_vertex f 1)

/-- Exact first-face formula for the actual triangle boundary edge. -/
theorem boundaryEdge_01_face (t : unitInterval) :
    (boundaryEdge 0 1 t).val =
      stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) (NerveGraphData.intervalPath t) := by
  rw [map_intervalPath]
  rfl

/-- Exact second-face formula for the actual triangle boundary edge. -/
theorem boundaryEdge_12_face (t : unitInterval) :
    (boundaryEdge 1 2 t).val =
      stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) (NerveGraphData.intervalPath t) := by
  rw [map_intervalPath]
  rfl

/-- Exact long-face formula for the actual triangle boundary edge. -/
theorem boundaryEdge_02_face (t : unitInterval) :
    (boundaryEdge 0 2 t).val =
      stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) (NerveGraphData.intervalPath t) := by
  rw [map_intervalPath]
  rfl

end CategoryTheory.NerveCompletion
