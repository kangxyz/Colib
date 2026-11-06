/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.DiscreteVertices
public import Colib.Topology.ClassifyingSpace.NerveGraphData

/-!
# Nerve Old Decoder

The actual nerve zero-stage decoder, with the original localization objects
specified by the published oldHomeomorph and NerveGraphData.vertex.
-/

@[expose] public section

noncomputable section
open CategoryTheory
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover
attribute [local instance] Localization.groupoid

/-- The actual nerve zero-stage decoder, with the original localization objects
specified by the published oldHomeomorph and NerveGraphData.vertex. -/
def nerveOldDecoder (C : Type u) [Category.{v} C] :
    FundamentalGroupoid (NerveGraphData.Old C) ⥤ (⊤ : MorphismProperty C).Localization :=
  discreteVertexFunctor (NerveGraphData.vertex C)

/-- The decoder sends each actual zero-stage point to its original localized vertex. -/
theorem nerveOldDecoder_obj (C : Type u) [Category.{v} C] (x : NerveGraphData.Old C) :
    (nerveOldDecoder C).obj (FundamentalGroupoid.mk x) = NerveGraphData.vertex C x := rfl

/-- Every actual old-stage path class is sent to the exact vertex equality transport. -/
theorem nerveOldDecoder_map (C : Type u) [Category.{v} C]
    {x y : NerveGraphData.Old C} (p : Path.Homotopic.Quotient x y) :
    (nerveOldDecoder C).map p =
      eqToHom (congrArg (NerveGraphData.vertex C) (vertexEndpoints_eq p)) := rfl

end CategoryTheory.NerveCompletion
