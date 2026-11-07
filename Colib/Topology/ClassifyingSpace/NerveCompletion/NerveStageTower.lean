/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexAttachment.AttachmentRestriction
public import Colib.Topology.ClassifyingSpace.NerveCompletion.GraphPathRecovery

/-!
# Nerve Stage Tower

The original relative skeletal stage, retaining the original empty-to-nerve map.
-/

@[expose] public section

noncomputable section
open CategoryTheory SSet TopCat FundamentalGroupoid.OpenCover Convexity.StdSimplex.Boundary
open scoped Simplicial
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment Convexity.StdSimplex.Boundary
attribute [local instance] Localization.groupoid

/-- The original relative skeletal stage, retaining the original empty-to-nerve map. -/
abbrev nerveFiniteStage (C : Type u) [Category.{v} C] (k : ℕ) : TopCat.{max u v} :=
  |(SSet.skeletonOfMono (NerveGraphData.emptyMap C) k : SSet.{max u v})|

/-- Extension over the actual original nerve cells of dimension n+3. -/
def nerveHigherDecoder (C : Type u) [Category.{v} C] (n : ℕ)
    (F : FundamentalGroupoid (nerveFiniteStage C (n + 3)) ⥤
      (⊤ : MorphismProperty C).Localization) :
    FundamentalGroupoid (nerveFiniteStage C (n + 4)) ⥤ (⊤ : MorphismProperty C).Localization :=
  attachmentDecoder (skeletalCellIndex (NerveGraphData.emptyMap C) (n + 3)) n
    (realizedSkeletal_isPushout (NerveGraphData.emptyMap C) (n + 3)) F

/-- The higher extension recovers the input along the original successor map. -/
def nerveHigherRestrictionIso (C : Type u) [Category.{v} C] (n : ℕ)
    (F : FundamentalGroupoid (nerveFiniteStage C (n + 3)) ⥤
      (⊤ : MorphismProperty C).Localization) :
    FundamentalGroupoid.map
        (SSet.toTop.map
          (SSet.relativeCellComplexOfMono.r (NerveGraphData.emptyMap C) (n + 3))).hom ⋙
      nerveHigherDecoder C n F ≅ F :=
  attachmentRestrictionIso (skeletalCellIndex (NerveGraphData.emptyMap C) (n + 3)) n
    (realizedSkeletal_isPushout (NerveGraphData.emptyMap C) (n + 3)) F

/-- Constructed decoders at every finite stage from the original two-skeleton onward.
This is recursion through actual cell attachments, not a chosen global decoder. -/
def nerveStageDecoder (C : Type u) [Category.{v} C] : (n : ℕ) →
    FundamentalGroupoid (nerveFiniteStage C (n + 3)) ⥤ (⊤ : MorphismProperty C).Localization :=
  fun n => match n with
  | 0 => nerveTwoSkeletonDecoder C
  | n + 1 => nerveHigherDecoder C n (nerveStageDecoder C n)

/-- Actual successor restriction natural isomorphisms for the entire finite-stage tower. -/
def nerveStageStepIso (C : Type u) [Category.{v} C] (n : ℕ) :
    FundamentalGroupoid.map
        (SSet.toTop.map
          (SSet.relativeCellComplexOfMono.r (NerveGraphData.emptyMap C) (n + 3))).hom ⋙
      nerveStageDecoder C (n + 1) ≅ nerveStageDecoder C n :=
  nerveHigherRestrictionIso C n (nerveStageDecoder C n)

/-- The initial stage recovers the original actual graph decoder. -/
def nerveStageZeroGraphIso (C : Type u) [Category.{v} C] :
    FundamentalGroupoid.map (nerveTwoSkeletonTransition C).hom ⋙ nerveStageDecoder C 0 ≅
      nerveGraphDecoder C := nerveTwoSkeletonGraphIso C

end CategoryTheory.NerveCompletion
