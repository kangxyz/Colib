/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.VertexTransport
public import Colib.Topology.ClassifyingSpace.NerveCompletion.EdgeTrace

/-!
# Nondegenerate Trace

Any graph-stage path whose actual included points are the original
nondegenerate arrow path has the exact original localized arrow trace, with
the prescribed categorical vertex identifications. Only pointwise injectivity
of the graph inclusion is used, not faithfulness on homotopy classes.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Convexity.StdSimplex FundamentalGroupoid.OpenCover
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment Convexity.StdSimplex.Boundary
attribute [local instance] Localization.groupoid

/-- Any graph-stage path whose actual included points are the original
nondegenerate arrow path has the exact original localized arrow trace, with
the prescribed categorical vertex identifications. Only pointwise injectivity
of the graph inclusion is used, not faithfulness on homotopy classes. -/
theorem decoder_trace_of_cell (C : Type u) [Category.{v} C] (a : NerveGraphData.Index C)
    (p : Path (graphVertex C (a.simplex.obj 0)) (graphVertex C (a.simplex.obj 1)))
    (hp : ∀ t, NerveGraphData.inclusion C (p t) =
      classifyingSpacePath (a.simplex.map' 0 1) t) :
    (nerveGraphDecoder C).map (Path.Homotopic.Quotient.mk p) =
      (graphVertexIso C (a.simplex.obj 0)).hom ≫
        (⊤ : MorphismProperty C).Q.map (a.simplex.map' 0 1) ≫
      (graphVertexIso C (a.simplex.obj 1)).inv := by
  have h0 := oldGraphPoint_eq_original C (NerveGraphData.attaching C (a, boundaryZero))
    (a.simplex.obj 0) (NerveGraphData.oldObject_source C a)
  have h1 := oldGraphPoint_eq_original C (NerveGraphData.attaching C (a, boundaryOne))
    (a.simplex.obj 1) (NerveGraphData.oldObject_target C a)
  have he : (nerveGraphEdgePath C a).cast h0.symm h1.symm = p := by
    apply Path.ext
    funext t
    apply nerveGraphInclusion_injective C
    exact (NerveGraphData.characteristic_path C a t).trans (hp t).symm
  rw [← he, Path.Homotopic.Quotient.mk_cast, ← FundamentalGroupoid.conj_eqToHom]
  simp only [Functor.map_comp, eqToHom_map, nerveGraphDecoder_edge,
    NerveGraphData.edge, NerveGraphData.originalEdge, Category.assoc]
  rw [oldVertexIso_source_assoc C _ _ (NerveGraphData.oldObject_source C a),
    oldVertexIso_target_assoc C _ _ (NerveGraphData.oldObject_target C a)]
  simp only [eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]

end CategoryTheory.NerveCompletion
