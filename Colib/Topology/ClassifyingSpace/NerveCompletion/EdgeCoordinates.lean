/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveGraphVertices

/-!
# Edge Coordinates

The first interior subdivision point, strictly inside the source collar.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory stdSimplex
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment

/-- The first interior subdivision point, strictly inside the source collar. -/
def edgeEighth : unitInterval := ⟨1 / 8, by norm_num⟩
/-- The second interior subdivision point, strictly inside the target collar. -/
def edgeSevenEighths : unitInterval := ⟨7 / 8, by norm_num⟩

/-- The original geometric edge has exactly its interval parameter as weight one. -/
theorem intervalPath_weight_one (t : unitInterval) :
    (NerveGraphData.intervalPath t) 1 = (t : ℝ) := by
  rfl

/-- The complementary coordinate of the same actual edge. -/
theorem intervalPath_weight_zero (t : unitInterval) :
    (NerveGraphData.intervalPath t) 0 = 1 - (t : ℝ) := by
  have hs : (NerveGraphData.intervalPath t) 0 +
      (NerveGraphData.intervalPath t) 1 = 1 := by
    simpa only [Fin.sum_univ_two] using stdSimplex.sum_eq_one (NerveGraphData.intervalPath t)
  rw [intervalPath_weight_one] at hs
  linarith

/-- The actual first eighth of the edge stays in the strict open collar. -/
theorem intervalPath_source_collar :
    Set.range (NerveGraphData.intervalPath.subpath 0 edgeEighth) ⊆ simplexBoundaryCollar 1 := by
  rintro _ ⟨t, rfl⟩
  change 1 / 2 < simplexBoundaryDefect
    (NerveGraphData.intervalPath (Icc.convexComb 0 edgeEighth t))
  have h := le_simplexBoundaryDefect
    (NerveGraphData.intervalPath (Icc.convexComb 0 edgeEighth t)) 1
  rw [intervalPath_weight_one] at h
  have ht : ((Icc.convexComb 0 edgeEighth t : unitInterval) : ℝ) ≤ 1 / 8 := by
    norm_num [Icc.coe_convexComb, edgeEighth]
    nlinarith [t.property.2]
  simp only [Nat.cast_one] at h
  linarith

/-- The actual last eighth of the edge stays in the strict open collar. -/
theorem intervalPath_target_collar :
    Set.range (NerveGraphData.intervalPath.subpath edgeSevenEighths 1) ⊆
      simplexBoundaryCollar 1 := by
  rintro _ ⟨t, rfl⟩
  change 1 / 2 < simplexBoundaryDefect
    (NerveGraphData.intervalPath (Icc.convexComb edgeSevenEighths 1 t))
  have h := le_simplexBoundaryDefect
    (NerveGraphData.intervalPath (Icc.convexComb edgeSevenEighths 1 t)) 0
  rw [intervalPath_weight_zero] at h
  have ht : 7 / 8 ≤ ((Icc.convexComb edgeSevenEighths 1 t : unitInterval) : ℝ) := by
    norm_num [Icc.coe_convexComb, edgeSevenEighths]
    nlinarith [t.property.1]
  simp only [Nat.cast_one] at h
  linarith

/-- The whole central subpath, including both split points, lies in the actual interior. -/
theorem intervalPath_middle_interior :
    Set.range (NerveGraphData.intervalPath.subpath edgeEighth edgeSevenEighths) ⊆
      simplexInterior 1 := by
  rintro _ ⟨t, rfl⟩ i
  have hlow : 0 < ((Icc.convexComb edgeEighth edgeSevenEighths t : unitInterval) : ℝ) := by
    simp only [Icc.coe_convexComb, edgeEighth, edgeSevenEighths]
    nlinarith [t.property.1]
  have hhigh : ((Icc.convexComb edgeEighth edgeSevenEighths t : unitInterval) : ℝ) < 1 := by
    simp only [Icc.coe_convexComb, edgeEighth, edgeSevenEighths]
    nlinarith [t.property.2]
  fin_cases i
  · change 0 < (NerveGraphData.intervalPath _) 0
    rw [intervalPath_weight_zero]
    linarith
  · change 0 < (NerveGraphData.intervalPath _) 1
    rw [intervalPath_weight_one]
    exact hlow

end CategoryTheory.NerveCompletion
