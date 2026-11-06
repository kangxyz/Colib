/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.PathTraceTransport

/-!
# Face Traces

Exact decoder trace of the actual attached 01 face, including degenerate faces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FundamentalGroupoid.OpenCover SSet
open scoped Simplicial
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment Convexity.StdSimplex.Boundary
attribute [local instance] Localization.groupoid

/-- Exact decoder trace of the actual attached 01 face, including degenerate faces. -/
theorem nerveTwoCell_trace_01 (C : Type u) [Category.{v} C] (a : NerveTwoCellIndex C) :
    edgeMap (nerveTwoCellBoundaryFunctor C a) 0 1 =
      (nerveTwoCellVertexIso C a 0).hom ≫
        (⊤ : MorphismProperty C).Q.map (a.simplex.map' 0 1 (hjn := by decide)) ≫
        (nerveTwoCellVertexIso C a 1).inv := by
  let p := (boundaryEdge 0 1).map (nerveTwoCellBoundaryMap C a).continuous
  have e0 := nerveTwoCellBoundary_vertex_graph C a 0
  have e1 := nerveTwoCellBoundary_vertex_graph C a 1
  let q := p.cast e0.symm e1.symm
  have hq := decoder_trace_of_simplex C ((nerve C).δ 2 a.simplex) q
    (fun t => nerveTwoCellBoundary_01_original C a t)
  have hc := functor_path_cast_trace (nerveGraphDecoder C) q e0 e1
    (graphVertexIso C (a.simplex.obj 0)) (graphVertexIso C (a.simplex.obj 1))
    ((⊤ : MorphismProperty C).Q.map (a.simplex.map' 0 1 (hjn := by decide))) hq
  have he : q.cast e0 e1 = p := by
    apply Path.ext
    funext t
    rfl
  rw [he] at hc
  exact hc

/-- Exact decoder trace of the actual attached 12 face, including degenerate faces. -/
theorem nerveTwoCell_trace_12 (C : Type u) [Category.{v} C] (a : NerveTwoCellIndex C) :
    edgeMap (nerveTwoCellBoundaryFunctor C a) 1 2 =
      (nerveTwoCellVertexIso C a 1).hom ≫ (⊤ : MorphismProperty C).Q.map (a.simplex.map' 1 2) ≫
        (nerveTwoCellVertexIso C a 2).inv := by
  let p := (boundaryEdge 1 2).map (nerveTwoCellBoundaryMap C a).continuous
  have e0 := nerveTwoCellBoundary_vertex_graph C a 1
  have e1 := nerveTwoCellBoundary_vertex_graph C a 2
  let q := p.cast e0.symm e1.symm
  have hq := decoder_trace_of_simplex C ((nerve C).δ 0 a.simplex) q
    (fun t => nerveTwoCellBoundary_12_original C a t)
  have hc := functor_path_cast_trace (nerveGraphDecoder C) q e0 e1
    (graphVertexIso C (a.simplex.obj 1)) (graphVertexIso C (a.simplex.obj 2))
    ((⊤ : MorphismProperty C).Q.map (a.simplex.map' 1 2)) hq
  have he : q.cast e0 e1 = p := by
    apply Path.ext
    funext t
    rfl
  rw [he] at hc
  exact hc

/-- Exact decoder trace of the actual attached 02 face, including degenerate faces. -/
theorem nerveTwoCell_trace_02 (C : Type u) [Category.{v} C] (a : NerveTwoCellIndex C) :
    edgeMap (nerveTwoCellBoundaryFunctor C a) 0 2 =
      (nerveTwoCellVertexIso C a 0).hom ≫ (⊤ : MorphismProperty C).Q.map (a.simplex.map' 0 2) ≫
        (nerveTwoCellVertexIso C a 2).inv := by
  let p := (boundaryEdge 0 2).map (nerveTwoCellBoundaryMap C a).continuous
  have e0 := nerveTwoCellBoundary_vertex_graph C a 0
  have e1 := nerveTwoCellBoundary_vertex_graph C a 2
  let q := p.cast e0.symm e1.symm
  have hq := decoder_trace_of_simplex C ((nerve C).δ 1 a.simplex) q
    (fun t => nerveTwoCellBoundary_02_original C a t)
  have hc := functor_path_cast_trace (nerveGraphDecoder C) q e0 e1
    (graphVertexIso C (a.simplex.obj 0)) (graphVertexIso C (a.simplex.obj 2))
    ((⊤ : MorphismProperty C).Q.map (a.simplex.map' 0 2)) hq
  have he : q.cast e0 e1 = p := by
    apply Path.ext
    funext t
    rfl
  rw [he] at hc
  exact hc

end CategoryTheory.NerveCompletion
