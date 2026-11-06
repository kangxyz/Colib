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
open CategoryTheory Convexity Convexity.StdSimplex SSet TopCat
open scoped Simplicial Topology
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment Convexity.StdSimplex.Boundary

/-- The original interval path is exactly the original straight barycentric segment. -/
theorem intervalPath_segment (t : unitInterval) :
    NerveGraphData.intervalPath t =
      simplexSegment (StdSimplex.single (0 : Fin 2)) (StdSimplex.single 1) t := by
  apply StdSimplex.ext
  ext k
  fin_cases k
  · change (NerveGraphData.intervalPath t).weights 0 =
      (simplexSegment (StdSimplex.single (0 : Fin 2)) (StdSimplex.single 1) t).weights 0
    rw [CategoryTheory.NerveCompletion.intervalPath_weight_zero, simplexSegment_weights]
    simp [StdSimplex.weights_single]
  · change (NerveGraphData.intervalPath t).weights 1 =
      (simplexSegment (StdSimplex.single (0 : Fin 2)) (StdSimplex.single 1) t).weights 1
    rw [CategoryTheory.NerveCompletion.intervalPath_weight_one, simplexSegment_weights]
    simp [StdSimplex.weights_single]

/-- A finite vertex map carries the actual interval to its exact straight edge. -/
theorem map_intervalPath {n : ℕ} (f : Fin 2 → Fin (n + 1)) (t : unitInterval) :
    StdSimplex.map f (NerveGraphData.intervalPath t) =
      simplexSegment (StdSimplex.single (f 0)) (StdSimplex.single (f 1)) t := by
  rw [intervalPath_segment]
  change StdSimplex.map f (convexCombPair (R := ℝ) (unitInterval.symm t) t _ _ _
    (StdSimplex.single 0) (StdSimplex.single 1)) =
      convexCombPair (R := ℝ) (unitInterval.symm t) t _ _ _
        (StdSimplex.single (f 0)) (StdSimplex.single (f 1))
  rw [(StdSimplex.isAffineMap_map ℝ f).map_convexCombPair]
  simp only [StdSimplex.map_single]

/-- Exact first-face adapter formula for the actual triangle boundary edge. -/
theorem boundaryEdge_01_face (t : unitInterval) :
    (boundaryEdge 0 1 t).val =
      StdSimplex.map (SimplexCategory.δ (2 : Fin 3)) (NerveGraphData.intervalPath t) := by
  rw [map_intervalPath]
  rfl

/-- Exact second-face adapter formula for the actual triangle boundary edge. -/
theorem boundaryEdge_12_face (t : unitInterval) :
    (boundaryEdge 1 2 t).val =
      StdSimplex.map (SimplexCategory.δ (0 : Fin 3)) (NerveGraphData.intervalPath t) := by
  rw [map_intervalPath]
  rfl

/-- Exact long-face adapter formula for the actual triangle boundary edge. -/
theorem boundaryEdge_02_face (t : unitInterval) :
    (boundaryEdge 0 2 t).val =
      StdSimplex.map (SimplexCategory.δ (1 : Fin 3)) (NerveGraphData.intervalPath t) := by
  rw [map_intervalPath]
  rfl

end CategoryTheory.NerveCompletion
