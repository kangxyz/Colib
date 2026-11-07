/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.EdgeCoordinates

/-!
# Radial Splits

The source split point as an actual geometric annulus point.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory stdSimplex
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment

/-- The source split point as an actual geometric annulus point. -/
def sourceSplit : simplexAnnulus 1 :=
  ⟨NerveGraphData.intervalPath edgeEighth,
    intervalPath_source_collar (NerveGraphData.intervalPath.subpath 0 edgeEighth).target_mem_range,
    intervalPath_middle_interior
      (NerveGraphData.intervalPath.subpath edgeEighth edgeSevenEighths).source_mem_range⟩

/-- The target split point as an actual geometric annulus point. -/
def targetSplit : simplexAnnulus 1 :=
  ⟨NerveGraphData.intervalPath edgeSevenEighths,
    intervalPath_target_collar
      (NerveGraphData.intervalPath.subpath edgeSevenEighths 1).source_mem_range,
    intervalPath_middle_interior
      (NerveGraphData.intervalPath.subpath edgeEighth edgeSevenEighths).target_mem_range⟩

/-- Radial projection is constant along every actual path in the one-simplex
collar, including paths starting or ending on its geometric boundary. -/
theorem collarBoundary_one_path_constant {a b : simplexBoundaryCollar 1}
    (p : Path a b) (t : unitInterval) :
    simplexBoundaryCollarRetraction 1 (p t) = simplexBoundaryCollarRetraction 1 a := by
  let : T2Space (_root_.stdSimplex ℝ (Fin 2)) := stdSimplexHomeomorphUnitInterval.symm.t2Space
  let : Finite (boundary 1) := finite_boundary_one
  have he := TotallyDisconnectedSpace.eq_of_continuous
    (fun t => simplexBoundaryCollarRetraction 1 (p t))
    ((simplexBoundaryCollarRetraction 1).continuous.comp p.continuous) t 0
  simpa using he

/-- The actual source split projects to the actual source boundary vertex. -/
theorem sourceSplit_boundary : annulusBoundary 1 sourceSplit = boundaryZero := by
  let p := (Path.inSubset (x := ⟨_, intervalPath_source_collar
      ((NerveGraphData.intervalPath.subpath 0 edgeEighth)).source_mem_range⟩) (y := ⟨_,
      intervalPath_source_collar ((NerveGraphData.intervalPath.subpath 0
      edgeEighth)).target_mem_range⟩) (NerveGraphData.intervalPath.subpath 0 edgeEighth)
      intervalPath_source_collar)
  have h := collarBoundary_one_path_constant p 1
  rw [p.target] at h
  have h0 : (⟨NerveGraphData.intervalPath 0,
      intervalPath_source_collar
        (NerveGraphData.intervalPath.subpath 0 edgeEighth).source_mem_range⟩ :
      simplexBoundaryCollar 1) = simplexBoundaryCollarInclusion 1 boundaryZero := by
    apply Subtype.ext
    exact NerveGraphData.intervalPath.source
  change annulusBoundary 1 sourceSplit = simplexBoundaryCollarRetraction 1
    (⟨NerveGraphData.intervalPath 0, _⟩ : simplexBoundaryCollar 1) at h
  rw [h0, simplexBoundaryCollarRetraction_inclusion] at h
  exact h

/-- The actual target split projects to the actual target boundary vertex. -/
theorem targetSplit_boundary : annulusBoundary 1 targetSplit = boundaryOne := by
  let p := (Path.inSubset (x := ⟨_, intervalPath_target_collar
      ((NerveGraphData.intervalPath.subpath edgeSevenEighths 1)).source_mem_range⟩) (y := ⟨_,
      intervalPath_target_collar ((NerveGraphData.intervalPath.subpath edgeSevenEighths
      1)).target_mem_range⟩) (NerveGraphData.intervalPath.subpath edgeSevenEighths 1)
      intervalPath_target_collar)
  have h := (collarBoundary_one_path_constant p 1).symm
  rw [p.target] at h
  have h1 : (⟨NerveGraphData.intervalPath 1,
      intervalPath_target_collar
        (NerveGraphData.intervalPath.subpath edgeSevenEighths 1).target_mem_range⟩ :
      simplexBoundaryCollar 1) = simplexBoundaryCollarInclusion 1 boundaryOne := by
    apply Subtype.ext
    exact NerveGraphData.intervalPath.target
  change annulusBoundary 1 targetSplit = simplexBoundaryCollarRetraction 1
    (⟨NerveGraphData.intervalPath 1, _⟩ : simplexBoundaryCollar 1) at h
  rw [h1, simplexBoundaryCollarRetraction_inclusion] at h
  exact h

end CategoryTheory.NerveCompletion
