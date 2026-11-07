/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.FaceImages

/-!
# Original Faces

Every original nerve one-simplex realizes its actual categorical arrow,
including degenerate one-simplices.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory stdSimplex SSet TopCat
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment stdSimplex.Boundary

/-- Every original nerve one-simplex realizes its actual categorical arrow,
including degenerate one-simplices. -/
theorem nerveSimplexPath_image (C : Type u) [Category.{v} C]
    (s : (nerve C) _⦋1⦌) (t : unitInterval) :
    SSet.toTop.map (SSet.yonedaEquiv.symm s) (realizationInterval.{max u v} t) =
      classifyingSpacePath (s.map' 0 1) t := by
  have hs : s = ComposableArrows.mk₁ (s.map' 0 1) :=
    ComposableArrows.ext₁ rfl rfl (by simp)
  change SSet.toTop.map (SSet.yonedaEquiv.symm s) (realizationInterval t) =
    SSet.toTop.map (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (s.map' 0 1)))
      (realizationInterval t)
  exact congrArg (fun z : (nerve C) _⦋1⦌ =>
    SSet.toTop.map (SSet.yonedaEquiv.symm z) (realizationInterval t)) hs

/-- The actual attached 01 edge has the unchanged original short-arrow path. -/
theorem nerveTwoCellBoundary_01_original (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) (t : unitInterval) :
    NerveGraphData.inclusion C (nerveTwoCellBoundaryMap C a (boundaryEdge 0 1 t)) =
      classifyingSpacePath (a.simplex.map' 0 1 (hjn := by decide)) t := by
  rw [nerveTwoCellBoundary_01_inclusion, nerveSimplexPath_image]
  rfl

/-- The actual attached 12 edge has the unchanged original short-arrow path. -/
theorem nerveTwoCellBoundary_12_original (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) (t : unitInterval) :
    NerveGraphData.inclusion C (nerveTwoCellBoundaryMap C a (boundaryEdge 1 2 t)) =
      classifyingSpacePath (a.simplex.map' 1 2) t := by
  rw [nerveTwoCellBoundary_12_inclusion, nerveSimplexPath_image]
  rfl

/-- The actual attached long edge has the unchanged original composite-arrow path. -/
theorem nerveTwoCellBoundary_02_original (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) (t : unitInterval) :
    NerveGraphData.inclusion C (nerveTwoCellBoundaryMap C a (boundaryEdge 0 2 t)) =
      classifyingSpacePath (a.simplex.map' 0 2) t := by
  rw [nerveTwoCellBoundary_02_inclusion, nerveSimplexPath_image]
  rfl

/-- Exact first vertex formula, not a chosen equivalent object. -/
theorem nerveTwoCellBoundary_vertex0 (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) :
    NerveGraphData.inclusion C (nerveTwoCellBoundaryMap C a (vertex 0)) =
      classifyingSpacePoint (a.simplex.obj 0) := by
  have h := nerveTwoCellBoundary_01_original C a 0
  simp only [Path.source] at h
  exact h

/-- Exact middle vertex formula. -/
theorem nerveTwoCellBoundary_vertex1 (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) :
    NerveGraphData.inclusion C (nerveTwoCellBoundaryMap C a (vertex 1)) =
      classifyingSpacePoint (a.simplex.obj 1) := by
  have h := nerveTwoCellBoundary_01_original C a 1
  simp only [Path.target] at h
  exact h

/-- Exact final vertex formula. -/
theorem nerveTwoCellBoundary_vertex2 (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) :
    NerveGraphData.inclusion C (nerveTwoCellBoundaryMap C a (vertex 2)) =
      classifyingSpacePoint (a.simplex.obj 2) := by
  have h := nerveTwoCellBoundary_02_original C a 1
  simp only [Path.target] at h
  exact h

end CategoryTheory.NerveCompletion
