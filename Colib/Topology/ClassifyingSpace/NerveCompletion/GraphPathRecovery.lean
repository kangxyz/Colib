/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.GraphRestriction

/-!
# Graph Path Recovery

Every original graph path has exactly its original decoder value after
inclusion into the two-skeleton, with the constructed natural endpoint transports.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory Convexity.StdSimplex TopCat SSet FundamentalGroupoid.OpenCover
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment Convexity.StdSimplex.Boundary
attribute [local instance] Localization.groupoid

/-- Every original graph path has exactly its original decoder value after
inclusion into the two-skeleton, with the constructed natural endpoint transports. -/
theorem nerveTwoSkeleton_graph_path (C : Type u) [Category.{v} C]
    {x y : NerveGraphData.Stage C} (p : Path x y) :
    (nerveTwoSkeletonDecoder C).map (Path.Homotopic.Quotient.mk
      (p.map (nerveTwoSkeletonTransition C).hom.continuous)) =
    (nerveTwoSkeletonGraphIso C).hom.app (FundamentalGroupoid.mk x) ≫
      (nerveGraphDecoder C).map (Path.Homotopic.Quotient.mk p) ≫
      (nerveTwoSkeletonGraphIso C).inv.app (FundamentalGroupoid.mk y) := by
  have h := (nerveTwoSkeletonGraphIso C).hom.naturality (Path.Homotopic.Quotient.mk p)
  change (nerveTwoSkeletonDecoder C).map (Path.Homotopic.Quotient.mk
      (p.map (nerveTwoSkeletonTransition C).hom.continuous)) ≫
      (nerveTwoSkeletonGraphIso C).hom.app (FundamentalGroupoid.mk y) =
    (nerveTwoSkeletonGraphIso C).hom.app (FundamentalGroupoid.mk x) ≫
      (nerveGraphDecoder C).map (Path.Homotopic.Quotient.mk p) at h
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv ((nerveTwoSkeletonGraphIso C).app
    (FundamentalGroupoid.mk y))).mpr h


/-- Exact original categorical edge trace survives the actual two-cell attachment. -/
theorem nerveTwoSkeleton_original_edge (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    (nerveTwoSkeletonDecoder C).map (Path.Homotopic.Quotient.mk
      ((nerveGraphEdgePath C a).map (nerveTwoSkeletonTransition C).hom.continuous)) =
    (nerveTwoSkeletonGraphIso C).hom.app (FundamentalGroupoid.mk
      (NerveGraphData.transition C (NerveGraphData.attaching C (a, boundaryZero)))) ≫
      (nerveGraphDecoderVertexIso C (NerveGraphData.attaching C (a, boundaryZero))).hom ≫
      NerveGraphData.edge C a ≫
      (nerveGraphDecoderVertexIso C (NerveGraphData.attaching C (a, boundaryOne))).inv ≫
      (nerveTwoSkeletonGraphIso C).inv.app (FundamentalGroupoid.mk
        (NerveGraphData.transition C (NerveGraphData.attaching C (a, boundaryOne)))) := by
  rw [nerveTwoSkeleton_graph_path, nerveGraphDecoder_edge]
  simp only [Category.assoc]

end CategoryTheory.NerveCompletion
