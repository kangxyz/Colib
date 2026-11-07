/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.ChartRecovery
public import Colib.Topology.ClassifyingSpace.NerveCompletion.TwoSkeletonCharts

/-!
# Two Skeleton Decoder

The actual open collar/interior cover of the original two-skeleton attachment.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory Convexity.StdSimplex TopCat SSet FundamentalGroupoid.OpenCover
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment Convexity.StdSimplex.Boundary
attribute [local instance] Localization.groupoid

/-- The actual open collar/interior cover of the original two-skeleton attachment. -/
theorem nerveTwoSkeletonCover (C : Type u) [Category.{v} C] :
    CoverData (starSet (nerveTwoSkeletonCollar C) (nerveTwoCellInterior C)) where
  isOpen i := by
    cases i with
    | none => exact isOpen_simplexAttachmentCollar _ _ (nerveTwoSkeletonPushout C)
    | some a => exact isOpen_simplexAttachmentInterior _ _ (nerveTwoSkeletonPushout C) a
  covers x := by
    have hx : x ∈ nerveTwoSkeletonCollar C ∪ ⋃ a, nerveTwoCellInterior C a := by
      rw [simplexAttachmentCollar_union_interiors _ _ (nerveTwoSkeletonPushout C)]
      trivial
    rcases hx with hx | hx
    · exact mem_iUnion.mpr ⟨none, hx⟩
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨some a, ha⟩

/-- Actual intersection of two cell-interior charts forces the original indices to agree. -/
theorem nerveTwoCellInterior_eq_of_mem (C : Type u) [Category.{v} C]
    (a b : NerveTwoCellIndex C) (x : nerveTwoSkeletonStage C)
    (ha : x ∈ nerveTwoCellInterior C a) (hb : x ∈ nerveTwoCellInterior C b) : a = b := by
  by_contra h
  exact Set.disjoint_left.mp
    (pairwiseDisjoint_simplexAttachmentInteriors _ _ (nerveTwoSkeletonPushout C) h) ha hb

/-- Actual compatible two-skeleton chart data, whose overlap naturality comes
from the proved original two-cell triangle equations and actual annulus homeomorphisms. -/
def nerveTwoSkeletonTransitionData (C : Type u) [Category.{v} C] :
    TransitionData (C := (⊤ : MorphismProperty C).Localization)
      (starSet (nerveTwoSkeletonCollar C) (nerveTwoCellInterior C)) :=
  starData (nerveTwoSkeletonCollar C) (nerveTwoCellInterior C)
    (nerveTwoCellInterior_eq_of_mem C) (nerveTwoSkeletonCollarDecoder C)
    (fun a => (⊤ : MorphismProperty C).Q.obj (a.simplex.obj 0))
    (nerveTwoActualOverlapTransition C)

/-- A constructed decoder on the actual original two-skeleton. This is a genuine
functor, but no full-realization extension or faithfulness is asserted. -/
def nerveTwoSkeletonDecoder (C : Type u) [Category.{v} C] :
    FundamentalGroupoid (nerveTwoSkeletonStage C) ⥤ (⊤ : MorphismProperty C).Localization :=
  (nerveTwoSkeletonTransitionData C).descent (nerveTwoSkeletonCover C)

end CategoryTheory.NerveCompletion
