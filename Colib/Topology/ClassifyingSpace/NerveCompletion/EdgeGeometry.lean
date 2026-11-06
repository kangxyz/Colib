/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.ThreeParts
public import Colib.Topology.ClassifyingSpace.NerveCompletion.RadialSplits

/-!
# Edge Geometry

The actual characteristic edge path with its exact attached old-stage endpoints.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory TopCat Convexity.StdSimplex
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment
attribute [local instance] Localization.groupoid

/-- The actual characteristic edge path with its exact attached old-stage endpoints. -/
def nerveGraphEdgePath (C : Type u) [Category.{v} C] (a : NerveGraphData.Index C) :
    Path (NerveGraphData.transition C (NerveGraphData.attaching C (a, boundaryZero)))
      (NerveGraphData.transition C (NerveGraphData.attaching C (a, boundaryOne))) where
  toFun t := NerveGraphData.characteristic C (a, NerveGraphData.intervalPath t)
  continuous_toFun := (NerveGraphData.characteristic C).hom.continuous.comp
    (continuous_const.prodMk NerveGraphData.intervalPath.continuous)
  source' := by
    change NerveGraphData.characteristic C (a, NerveGraphData.intervalPath 0) = _
    rw [Path.source]
    exact ConcreteCategory.congr_hom (NerveGraphData.pushout C).w (a, boundaryZero)
  target' := by
    change NerveGraphData.characteristic C (a, NerveGraphData.intervalPath 1) = _
    rw [Path.target]
    exact ConcreteCategory.congr_hom (NerveGraphData.pushout C).w (a, boundaryOne)

/-- The first actual edge segment lies in the actual attachment collar. -/
theorem nerveGraphEdgePath_first_contained (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    range (firstPart (nerveGraphEdgePath C a) edgeEighth) ⊆ nerveGraphCollar C := by
  rintro _ ⟨t, rfl⟩
  apply (simplexAttachmentCollar_cell_iff _ _ (NerveGraphData.pushout C)
    (a, NerveGraphData.intervalPath (Icc.convexComb 0 edgeEighth t))).mpr
  exact intervalPath_source_collar (Set.mem_range_self t)

/-- The last actual edge segment lies in the same actual collar. -/
theorem nerveGraphEdgePath_last_contained (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    range (lastPart (nerveGraphEdgePath C a) edgeSevenEighths) ⊆ nerveGraphCollar C := by
  rintro _ ⟨t, rfl⟩
  apply (simplexAttachmentCollar_cell_iff _ _ (NerveGraphData.pushout C)
    (a, NerveGraphData.intervalPath (Icc.convexComb edgeSevenEighths 1 t))).mpr
  exact intervalPath_target_collar (Set.mem_range_self t)

/-- The whole actual central edge segment lies in its specified interior chart. -/
theorem nerveGraphEdgePath_middle_contained (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    range ((nerveGraphEdgePath C a).subpath edgeEighth edgeSevenEighths) ⊆
      nerveGraphInterior C a := by
  rintro _ ⟨t, rfl⟩
  exact ⟨⟨NerveGraphData.intervalPath (Icc.convexComb edgeEighth edgeSevenEighths t),
    intervalPath_middle_interior (Set.mem_range_self t)⟩, rfl⟩

/-- The source split, as an actual overlap point, is the characteristic image
of the specified geometric annulus point. -/
def nerveGraphSourceSplit (C : Type u) [Category.{v} C] (a : NerveGraphData.Index C) :
    nerveGraphOverlap C a :=
  annulusOverlapHomeomorph (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a sourceSplit

/-- The target split has the same actual-image convention. -/
def nerveGraphTargetSplit (C : Type u) [Category.{v} C] (a : NerveGraphData.Index C) :
    nerveGraphOverlap C a :=
  annulusOverlapHomeomorph (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a targetSplit

@[simp]
theorem nerveGraphSourceSplit_val (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    (nerveGraphSourceSplit C a).val = nerveGraphEdgePath C a edgeEighth := rfl

@[simp]
theorem nerveGraphTargetSplit_val (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    (nerveGraphTargetSplit C a).val = nerveGraphEdgePath C a edgeSevenEighths := rfl

end CategoryTheory.NerveCompletion
