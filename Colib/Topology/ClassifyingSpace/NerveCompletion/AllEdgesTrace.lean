/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.NondegenerateTrace

/-!
# All Edges Trace

A nondegenerate original one-simplex is an actual first-stage cell; exclusion
from the empty simplicial subcomplex is proved rather than assumed.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory stdSimplex FundamentalGroupoid.OpenCover SSet
open scoped Simplicial
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment stdSimplex.Boundary
attribute [local instance] Localization.groupoid

/-- A nondegenerate original one-simplex is an actual first-stage cell; exclusion
from the empty simplicial subcomplex is proved rather than assumed. -/
def oneCellOfNondegenerate (C : Type u) [Category.{v} C]
    (s : (nerve C) _⦋1⦌) (hs : s ∈ (nerve C).nonDegenerate 1) : NerveGraphData.Index C where
  simplex := s
  nonDegenerate := hs
  notMem := by
    rintro ⟨x, _⟩
    exact x.property

/-- Every degenerate original nerve one-simplex is an actual identity-arrow simplex. -/
theorem degenerate_one_eq_identity (C : Type u) [Category.{v} C]
    (s : (nerve C) _⦋1⦌) (hs : s ∉ (nerve C).nonDegenerate 1) :
    ∃ c : C, s = ComposableArrows.mk₁ (𝟙 c) := by
  have hd := ((nerve C).mem_degenerate_iff_notMem_nonDegenerate s).mpr hs
  rw [(nerve C).degenerate_eq_iUnion_range_σ] at hd
  obtain ⟨j, hj⟩ := mem_iUnion.mp hd
  have hj0 : j = 0 := by
    apply Fin.ext
    have hjlt := j.isLt
    omega
  subst j
  obtain ⟨x, rfl⟩ := hj
  obtain ⟨c, rfl⟩ := nerveEquiv.symm.surjective x
  exact ⟨c, nerve.σ_zero_nerveEquiv_symm c⟩

/-- Actual graph-stage arrow traces for ALL original nerve one-simplices,
including the degenerate identity faces of nondegenerate two-simplices. -/
theorem decoder_trace_of_simplex (C : Type u) [Category.{v} C] (s : (nerve C) _⦋1⦌)
    (p : Path (graphVertex C (s.obj 0)) (graphVertex C (s.obj 1)))
    (hp : ∀ t, NerveGraphData.inclusion C (p t) = classifyingSpacePath (s.map' 0 1) t) :
    (nerveGraphDecoder C).map (Path.Homotopic.Quotient.mk p) =
      (graphVertexIso C (s.obj 0)).hom ≫ (⊤ : MorphismProperty C).Q.map (s.map' 0 1) ≫
        (graphVertexIso C (s.obj 1)).inv := by
  classical
  by_cases hs : s ∈ (nerve C).nonDegenerate 1
  · exact decoder_trace_of_cell C (oneCellOfNondegenerate C s hs) p hp
  · obtain ⟨c, rfl⟩ := degenerate_one_eq_identity C s hs
    have he : p = Path.refl (graphVertex C c) := by
      apply Path.ext
      funext t
      apply nerveGraphInclusion_injective C
      calc
        NerveGraphData.inclusion C (p t) = classifyingSpacePath (𝟙 c) t := hp t
        _ = classifyingSpacePoint c := by rw [classifyingSpacePath_id]; rfl
        _ = NerveGraphData.inclusion C (Path.refl (graphVertex C c) t) :=
          (graphVertex_inclusion C c).symm
    rw [he]
    change (nerveGraphDecoder C).map (𝟙 (FundamentalGroupoid.mk (graphVertex C c))) =
      (graphVertexIso C c).hom ≫ (⊤ : MorphismProperty C).Q.map (𝟙 c) ≫
        (graphVertexIso C c).inv
    rw [(nerveGraphDecoder C).map_id, (⊤ : MorphismProperty C).Q.map_id]
    simp

end CategoryTheory.NerveCompletion
