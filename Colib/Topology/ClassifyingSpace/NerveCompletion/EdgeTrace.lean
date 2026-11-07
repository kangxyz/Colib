/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.OverlapComponents
public import Colib.Topology.Homotopy.OpenCover.ThreePartValue
public import Colib.Topology.ClassifyingSpace.NerveCompletion.CollarTransport

/-!
# Edge Trace

The inverse transition has the same exact actual-image component convention.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory stdSimplex TopCat
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment
attribute [local instance] Localization.groupoid

/-- The inverse transition has the same exact actual-image component convention. -/
theorem nerveActualOverlapTransition_image_inv (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) (x : simplexAnnulus 1) :
    (nerveActualOverlapTransition C a).inv.app (FundamentalGroupoid.mk
      (annulusOverlapHomeomorph (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a x)) =
      (nerveAnnulusTransport C a x).inv := by
  have h : (nerveActualOverlapTransition C a).app (FundamentalGroupoid.mk
      (annulusOverlapHomeomorph (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a x)) =
      nerveAnnulusTransport C a x := Iso.ext (nerveActualOverlapTransition_image C a x)
  exact congrArg Iso.inv h

/-- Exact trace of the actual characteristic edge, with the prescribed original
vertex identifications and the unchanged localized original edge. -/
theorem nerveGraphDecoder_edge (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    (nerveGraphDecoder C).map (Path.Homotopic.Quotient.mk (nerveGraphEdgePath C a)) =
      (nerveGraphDecoderVertexIso C (NerveGraphData.attaching C (a, boundaryZero))).hom ≫
        NerveGraphData.edge C a ≫
      (nerveGraphDecoderVertexIso C (NerveGraphData.attaching C (a, boundaryOne))).inv := by
  let p := nerveGraphEdgePath C a
  let d := nerveGraphTransitionData C
  have c := nerveGraphCover C
  have hp := nerveGraphEdgePath_first_contained C a
  have hq := nerveGraphEdgePath_middle_contained C a
  have hr := nerveGraphEdgePath_last_contained C a
  have h := d.pathValue_subpath_three c p edgeEighth edgeSevenEighths
    none (some a) none hp hq hr
  change (nerveGraphDecoder C).map (Path.Homotopic.Quotient.mk p) =
      ((d.chartData c).transport none ⟨_, hp (firstPart p edgeEighth).source_mem_range⟩).hom ≫
      (nerveGraphCollarDecoder C).map
        (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hp ((firstPart p
            edgeEighth)).source_mem_range⟩) (y := ⟨_, hp ((firstPart p
            edgeEighth)).target_mem_range⟩) (firstPart p edgeEighth) hp))) ≫
      (nerveActualOverlapTransition C a).hom.app (FundamentalGroupoid.mk
        (annulusOverlapHomeomorph (NerveGraphData.Index C) 1
          (NerveGraphData.pushout C) a sourceSplit)) ≫
      𝟙 _ ≫
      (nerveActualOverlapTransition C a).inv.app (FundamentalGroupoid.mk
        (annulusOverlapHomeomorph (NerveGraphData.Index C) 1
          (NerveGraphData.pushout C) a targetSplit)) ≫
      (nerveGraphCollarDecoder C).map
        (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hr ((lastPart p
            edgeSevenEighths)).source_mem_range⟩) (y := ⟨_, hr ((lastPart p
            edgeSevenEighths)).target_mem_range⟩) (lastPart p edgeSevenEighths) hr))) ≫
      ((d.chartData c).transport none
        ⟨_, hr (lastPart p edgeSevenEighths).target_mem_range⟩).inv at h
  rw [nerveActualOverlapTransition_image, nerveActualOverlapTransition_image_inv,
    nerveAnnulusTransport_source, nerveAnnulusTransport_target] at h
  have hs := simplexAttachmentCollarRetraction_inclusion (NerveGraphData.Index C) 1
    (NerveGraphData.pushout C) (NerveGraphData.attaching C (a, boundaryZero))
  have ht := simplexAttachmentCollarRetraction_inclusion (NerveGraphData.Index C) 1
    (NerveGraphData.pushout C) (NerveGraphData.attaching C (a, boundaryOne))
  rw [nerveGraphCollarDecoder_path_same_vertex C _ _ hs (nerveSourceSplit_retraction C a),
    nerveGraphCollarDecoder_path_same_vertex C _ _ (nerveTargetSplit_retraction C a) ht] at h
  simp only [nerveGraphDecoderVertexIso, Iso.trans_hom, Iso.trans_inv,
    eqToIso.hom, eqToIso.inv, Iso.symm_inv, asIso_hom, Category.id_comp,
    Category.assoc, eqToHom_trans_assoc,
    simplexAttachmentCollarInclusion, ContinuousMap.coe_mk] at h ⊢
  exact h

end CategoryTheory.NerveCompletion
