/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.OriginalFaces

/-!
# Graph Vertices

The actual graph point of an original categorical object.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory stdSimplex SSet TopCat FundamentalGroupoid.OpenCover
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment stdSimplex.Boundary
attribute [local instance] Localization.groupoid

/-- The actual graph point of an original categorical object. -/
def graphVertex (C : Type u) [Category.{v} C] (c : C) : NerveGraphData.Stage C :=
  NerveGraphData.transition C ((NerveGraphData.oldHomeomorph C).symm c)

/-- Its unchanged inclusion is the original classifying-space point. -/
theorem graphVertex_inclusion (C : Type u) [Category.{v} C] (c : C) :
    NerveGraphData.inclusion C (graphVertex C c) = classifyingSpacePoint c := by
  have h := NerveGraphData.oldObject_point C ((NerveGraphData.oldHomeomorph C).symm c)
  change classifyingSpacePoint (C := C) ((NerveGraphData.oldHomeomorph C)
    ((NerveGraphData.oldHomeomorph C).symm c)) = _ at h
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

/-- The prescribed existing decoder identification at the original object point. -/
def graphVertexIso (C : Type u) [Category.{v} C] (c : C) :
    (nerveGraphDecoder C).obj (FundamentalGroupoid.mk (graphVertex C c)) ≅
      (⊤ : MorphismProperty C).Q.obj c :=
  nerveGraphDecoderOriginalVertexIso C c

/-- All three attached two-cell vertices are their original graph-stage objects. -/
theorem nerveTwoCellBoundary_vertex_graph (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) (i : Fin 3) :
    nerveTwoCellBoundaryMap C a (vertex i) = graphVertex C (a.simplex.obj i) := by
  apply nerveGraphInclusion_injective C
  rw [graphVertex_inclusion]
  fin_cases i
  · exact nerveTwoCellBoundary_vertex0 C a
  · exact nerveTwoCellBoundary_vertex1 C a
  · exact nerveTwoCellBoundary_vertex2 C a

/-- The original two-cell vertex identification retains the exact graph-point
equality before the prescribed original localization-object isomorphism. -/
def nerveTwoCellVertexIso (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) (i : Fin 3) :
    (nerveTwoCellBoundaryFunctor C a).obj (FundamentalGroupoid.mk (vertex i)) ≅
      (⊤ : MorphismProperty C).Q.obj (a.simplex.obj i) :=
  eqToIso (congrArg (fun z => (nerveGraphDecoder C).obj (FundamentalGroupoid.mk z))
    (nerveTwoCellBoundary_vertex_graph C a i)) ≪≫ graphVertexIso C (a.simplex.obj i)

end CategoryTheory.NerveCompletion
