/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.StarDescent
public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveActualOverlap

/-!
# Nerve Graph Decoder

The actual open collar/interior cover of the original nerve graph stage.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory TopCat stdSimplex
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment
attribute [local instance] Localization.groupoid

/-- The actual open collar/interior cover of the original nerve graph stage. -/
theorem nerveGraphCover (C : Type u) [Category.{v} C] :
    CoverData (starSet (nerveGraphCollar C) (nerveGraphInterior C)) where
  isOpen i := by
    cases i with
    | none => exact isOpen_simplexAttachmentCollar _ _ (NerveGraphData.pushout C)
    | some a => exact isOpen_simplexAttachmentInterior _ _ (NerveGraphData.pushout C) a
  covers x := by
    have hx : x ∈ nerveGraphCollar C ∪ ⋃ a, nerveGraphInterior C a := by
      rw [simplexAttachmentCollar_union_interiors _ _ (NerveGraphData.pushout C)]
      trivial
    rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨none, hx⟩
    · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨some a, ha⟩

/-- Actual interior-chart intersection forces equality of its original cell indices. -/
theorem nerveGraphInterior_eq_of_mem (C : Type u) [Category.{v} C]
    (a b : NerveGraphData.Index C) (x : NerveGraphData.Stage C)
    (ha : x ∈ nerveGraphInterior C a) (hb : x ∈ nerveGraphInterior C b) : a = b := by
  by_contra h
  exact Set.disjoint_left.mp
    (pairwiseDisjoint_simplexAttachmentInteriors _ _ (NerveGraphData.pushout C) h) ha hb

/-- The full actual graph transition data, using the original localized edges. -/
def nerveGraphTransitionData (C : Type u) [Category.{v} C] :
    TransitionData (C := (⊤ : MorphismProperty C).Localization)
      (starSet (nerveGraphCollar C) (nerveGraphInterior C)) :=
  starData (nerveGraphCollar C) (nerveGraphInterior C) (nerveGraphInterior_eq_of_mem C)
    (nerveGraphCollarDecoder C)
    (fun a => NerveGraphData.vertex C (NerveGraphData.attaching C (a, boundaryZero)))
    (nerveActualOverlapTransition C)

/-- A genuine functor from the actual nerve one-skeleton to the original groupoid
localization. Its overlap transitions use exactly the original edge morphisms.
This alone does not extend through two-cells or prove faithfulness. -/
def nerveGraphDecoder (C : Type u) [Category.{v} C] :
    FundamentalGroupoid (NerveGraphData.Stage C) ⥤ (⊤ : MorphismProperty C).Localization :=
  (nerveGraphTransitionData C).descent (nerveGraphCover C)

end CategoryTheory.NerveCompletion
