/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexAttachment.OverlapFunctor
public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveTriangle

/-!
# Two Skeleton Charts

The original realized two-skeleton, with the original relative-stage indexing.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory CategoryTheory.Limits Convexity Convexity.StdSimplex TopCat SSet
open FundamentalGroupoid.OpenCover
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment Convexity.StdSimplex.Boundary
attribute [local instance] Localization.groupoid

/-- The original realized two-skeleton, with the original relative-stage indexing. -/
abbrev nerveTwoSkeletonStage (C : Type u) [Category.{v} C] : TopCat.{max u v} :=
  |(SSet.skeletonOfMono (NerveGraphData.emptyMap C) 3 : SSet.{max u v})|

/-- The unchanged two-cell characteristic map. -/
abbrev nerveTwoCellCharacteristic (C : Type u) [Category.{v} C] :=
  realizedSkeletalCharacteristic (NerveGraphData.emptyMap C) 2

/-- The original graph-stage inclusion into the actual two-skeleton. -/
abbrev nerveTwoSkeletonTransition (C : Type u) [Category.{v} C] :=
  SSet.toTop.map (SSet.relativeCellComplexOfMono.r (NerveGraphData.emptyMap C) 2)

/-- The actual original two-cell attachment pushout. -/
theorem nerveTwoSkeletonPushout (C : Type u) [Category.{v} C] :
    IsPushout (parameterizedSimplexBoundaryInclusion (NerveTwoCellIndex C) 2)
      (realizedSkeletalAttaching (NerveGraphData.emptyMap C) 2)
      (nerveTwoCellCharacteristic C) (nerveTwoSkeletonTransition C) :=
  realizedSkeletal_isPushout (NerveGraphData.emptyMap C) 2

/-- The open collar of the old graph inside the actual two-cell attachment. -/
abbrev nerveTwoSkeletonCollar (C : Type u) [Category.{v} C] :=
  simplexAttachmentCollar (NerveTwoCellIndex C) 2 (nerveTwoSkeletonPushout C)

/-- The open interior of one original two-cell in the attachment. -/
abbrev nerveTwoCellInterior (C : Type u) [Category.{v} C] (a : NerveTwoCellIndex C) :=
  simplexAttachmentInterior (NerveTwoCellIndex C) 2 (g := nerveTwoCellCharacteristic C) a

/-- The actual old graph decoder pulled back along the original collar retraction. -/
def nerveTwoSkeletonCollarDecoder (C : Type u) [Category.{v} C] :
    FundamentalGroupoid (nerveTwoSkeletonCollar C) ⥤ (⊤ : MorphismProperty C).Localization :=
  FundamentalGroupoid.map (simplexAttachmentCollarRetraction (NerveTwoCellIndex C) 2
    (nerveTwoSkeletonPushout C)) ⋙ nerveGraphDecoder C

/-- The actual cell annulus restricted through the original collar chart. -/
def nerveTwoAnnulusDecoder (C : Type u) [Category.{v} C] (a : NerveTwoCellIndex C) :
    FundamentalGroupoid (simplexAnnulus 2) ⥤ (⊤ : MorphismProperty C).Localization :=
  FundamentalGroupoid.map (annulusToCollar (NerveTwoCellIndex C) 2
    (nerveTwoSkeletonPushout C) a) ⋙ nerveTwoSkeletonCollarDecoder C

/-- Its underlying actual collar retraction is exactly the original attaching
map composed with the original radial boundary projection. -/
theorem nerveTwoAnnulusDecoder_eq (C : Type u) [Category.{v} C] (a : NerveTwoCellIndex C) :
    nerveTwoAnnulusDecoder C a =
      FundamentalGroupoid.map (annulusBoundary 2) ⋙ nerveTwoCellBoundaryFunctor C a := by
  let r := simplexAttachmentCollarRetraction (NerveTwoCellIndex C) 2
    (nerveTwoSkeletonPushout C)
  let k := annulusToCollar (NerveTwoCellIndex C) 2 (nerveTwoSkeletonPushout C) a
  have hk : r.comp k = (nerveTwoCellBoundaryMap C a).comp (annulusBoundary 2) := by
    ext x
    exact collarRetraction_annulus (NerveTwoCellIndex C) 2 (nerveTwoSkeletonPushout C) a x
  change FundamentalGroupoid.map k ⋙ (FundamentalGroupoid.map r ⋙ nerveGraphDecoder C) = _
  rw [← Functor.assoc, ← FundamentalGroupoid.map_comp, hk, FundamentalGroupoid.map_comp]
  rfl

/-- The annulus trivialization is constructed from the proved original triangle
relation, ending at the original localization object of vertex zero. -/
def nerveTwoAnnulusTransition (C : Type u) [Category.{v} C] (a : NerveTwoCellIndex C) :
    nerveTwoAnnulusDecoder C a ≅
      (Functor.const (FundamentalGroupoid (simplexAnnulus 2))).obj
        ((⊤ : MorphismProperty C).Q.obj (a.simplex.obj 0)) :=
  eqToIso (nerveTwoAnnulusDecoder_eq C a) ≪≫ nerveTwoCellAnnulusConstantIso C a ≪≫
    (Functor.const (FundamentalGroupoid (simplexAnnulus 2))).mapIso (nerveTwoCellVertexIso C a 0)

/-- A natural isomorphism on every ACTUAL collar/interior overlap path. -/
def nerveTwoActualOverlapTransition (C : Type u) [Category.{v} C] (a : NerveTwoCellIndex C) :
    FundamentalGroupoid.map ((ContinuousMap.inclusion (s := (nerveTwoSkeletonCollar C) ∩
        (nerveTwoCellInterior C a)) Set.inter_subset_left)) ⋙ nerveTwoSkeletonCollarDecoder C ≅
      (Functor.const (FundamentalGroupoid
        ↥(nerveTwoSkeletonCollar C ∩ nerveTwoCellInterior C a))).obj
        ((⊤ : MorphismProperty C).Q.obj (a.simplex.obj 0)) :=
  actualOverlapIsoOfAnnulus (NerveTwoCellIndex C) 2 (nerveTwoSkeletonPushout C) a
    (nerveTwoSkeletonCollarDecoder C) _ (nerveTwoAnnulusTransition C a)

end CategoryTheory.NerveCompletion
