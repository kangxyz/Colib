/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveGraphDecoder

/-!
# Nerve Graph Vertices

The chosen global graph decoder is identified with the prescribed original
vertex at every actual old-stage point, with the exact inclusion and retraction.
-/

@[expose] public section

noncomputable section
open CategoryTheory TopCat
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment
attribute [local instance] Localization.groupoid

/-- The chosen global graph decoder is identified with the prescribed original
vertex at every actual old-stage point, with the exact inclusion and retraction. -/
def nerveGraphDecoderVertexIso (C : Type u) [Category.{v} C] (x : NerveGraphData.Old C) :
    (nerveGraphDecoder C).obj (FundamentalGroupoid.mk (NerveGraphData.transition C x)) ≅
      NerveGraphData.vertex C x := by
  let z := simplexAttachmentCollarInclusion (NerveGraphData.Index C) 1
    (NerveGraphData.pushout C) x
  let d := (nerveGraphTransitionData C).chartData (nerveGraphCover C)
  exact d.transport none z ≪≫ eqToIso (congrArg (NerveGraphData.vertex C)
    (simplexAttachmentCollarRetraction_inclusion (NerveGraphData.Index C) 1
      (NerveGraphData.pushout C) x))

/-- The based original category object is exactly the original localization object
under the published oldHomeomorph, rather than an arbitrary equivalent vertex. -/
def nerveGraphDecoderOriginalVertexIso (C : Type u) [Category.{v} C] (c : C) :
    (nerveGraphDecoder C).obj (FundamentalGroupoid.mk
      (NerveGraphData.transition C ((NerveGraphData.oldHomeomorph C).symm c))) ≅
      (⊤ : MorphismProperty C).Q.obj c :=
  nerveGraphDecoderVertexIso C ((NerveGraphData.oldHomeomorph C).symm c) ≪≫
    eqToIso (NerveGraphData.vertex_oldHomeomorph_symm C c)

end CategoryTheory.NerveCompletion
