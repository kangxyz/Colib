/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.TwoSkeletonDecoder

/-!
# Graph Restriction

The constructed two-skeleton decoder restricts along the ORIGINAL graph-stage
inclusion to the original graph decoder, naturally on every actual graph path.
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

/-- The constructed two-skeleton decoder restricts along the ORIGINAL graph-stage
inclusion to the original graph decoder, naturally on every actual graph path. -/
def nerveTwoSkeletonGraphIso (C : Type u) [Category.{v} C] :
    FundamentalGroupoid.map (nerveTwoSkeletonTransition C).hom ⋙ nerveTwoSkeletonDecoder C ≅
      nerveGraphDecoder C := by
  let inc := simplexAttachmentCollarInclusion (NerveTwoCellIndex C) 2
    (nerveTwoSkeletonPushout C)
  let r := simplexAttachmentCollarRetraction (NerveTwoCellIndex C) 2
    (nerveTwoSkeletonPushout C)
  let U := starSet (nerveTwoSkeletonCollar C) (nerveTwoCellInterior C)
  have hi : ((ContinuousMap.subtypeVal (U none))).comp inc = (nerveTwoSkeletonTransition C).hom
      := rfl
  have hr : r.comp inc = ContinuousMap.id (NerveGraphData.Stage C) := by
    apply ContinuousMap.ext
    exact simplexAttachmentCollarRetraction_inclusion _ _ (nerveTwoSkeletonPushout C)
  have e := Functor.isoWhiskerLeft (FundamentalGroupoid.map inc)
    ((nerveTwoSkeletonTransitionData C).descentChartIso (nerveTwoSkeletonCover C) none)
  have hs : FundamentalGroupoid.map inc ⋙
      (FundamentalGroupoid.map ((ContinuousMap.subtypeVal (U none))) ⋙ nerveTwoSkeletonDecoder C) =
      FundamentalGroupoid.map (nerveTwoSkeletonTransition C).hom ⋙
        nerveTwoSkeletonDecoder C := by
    rw [← Functor.assoc, ← FundamentalGroupoid.map_comp, hi]
  have ht : FundamentalGroupoid.map inc ⋙ nerveTwoSkeletonCollarDecoder C =
      nerveGraphDecoder C := by
    change FundamentalGroupoid.map inc ⋙ (FundamentalGroupoid.map r ⋙ _) = _
    rw [← Functor.assoc, ← FundamentalGroupoid.map_comp, hr, FundamentalGroupoid.map_id]
    rfl
  change FundamentalGroupoid.map inc ⋙
      (FundamentalGroupoid.map ((ContinuousMap.subtypeVal (U none))) ⋙ nerveTwoSkeletonDecoder C) ≅
      FundamentalGroupoid.map inc ⋙ nerveTwoSkeletonCollarDecoder C at e
  rw [hs, ht] at e
  exact e

end CategoryTheory.NerveCompletion
