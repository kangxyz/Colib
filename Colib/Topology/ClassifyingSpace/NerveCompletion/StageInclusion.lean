/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveBoundaryCondition

/-!
# Stage Inclusion

The actual graph-stage inclusion is injective, via the published skeletal
closed embedding and the exact relative-to-absolute stage isomorphism.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Convexity Convexity.StdSimplex SSet TopCat
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment Convexity.StdSimplex.Boundary

/-- The actual graph-stage inclusion is injective, via the published skeletal
closed embedding and the exact relative-to-absolute stage isomorphism. -/
theorem nerveGraphInclusion_injective (C : Type u) [Category.{v} C] :
    Function.Injective (NerveGraphData.inclusion C) := by
  intro x y h
  apply (TopCat.homeoOfIso (realizedSkeletonStageIso (nerve C) 2)).injective
  apply (realization_skeleton_isClosedEmbedding (nerve C) 2).injective
  exact (ConcreteCategory.congr_hom (realizedSkeletonStageIso_hom_ι (nerve C) 2) x).trans
    (h.trans (ConcreteCategory.congr_hom
      (realizedSkeletonStageIso_hom_ι (nerve C) 2) y).symm)

/-- After the unchanged graph inclusion, the actual two-cell boundary attaching
map is precisely its original simplex realization in finite barycentric coordinates. -/
theorem nerveTwoCellBoundary_inclusion (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) (x : simplexBoundary 2) :
    NerveGraphData.inclusion C (nerveTwoCellBoundaryMap C a x) =
      SSet.toTop.map (SSet.yonedaEquiv.symm a.simplex)
        ((FiniteSimplexAdapter.toTopHomeomorph ⦋2⦌).symm x.val) := by
  let i := NerveGraphData.emptyMap C
  have ht : SSet.toTop.map (SSet.relativeCellComplexOfMono.r i 2) ≫
      SSet.toTop.map (SSet.skeletonOfMono i 3).ι =
      SSet.toTop.map (SSet.skeletonOfMono i 2).ι := by
    rw [← SSet.toTop.map_comp]
    congr 1
  have hw := ConcreteCategory.congr_hom (realizedSkeletal_isPushout i 2).w (a, x)
  change realizedSkeletalCharacteristic i 2 (a, x.val) =
    SSet.toTop.map (SSet.relativeCellComplexOfMono.r i 2)
      (realizedSkeletalAttaching i 2 (a, x)) at hw
  calc
    NerveGraphData.inclusion C (nerveTwoCellBoundaryMap C a x) =
        SSet.toTop.map (SSet.skeletonOfMono i 3).ι
          (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i 2)
            (realizedSkeletalAttaching i 2 (a, x))) :=
      (ConcreteCategory.congr_hom ht (realizedSkeletalAttaching i 2 (a, x))).symm
    _ = SSet.toTop.map (SSet.skeletonOfMono i 3).ι
        (realizedSkeletalCharacteristic i 2 (a, x.val)) := congrArg _ hw.symm
    _ = _ := realizedSkeletalCharacteristic_inclusion_geometric i 2 a x.val

end CategoryTheory.NerveCompletion
