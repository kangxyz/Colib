/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveOldDecoder

/-!
# Nerve Graph Charts

The actual old-space collar chart of the original nerve one-skeleton attachment.
-/

@[expose] public section

noncomputable section
open CategoryTheory TopCat stdSimplex
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover
attribute [local instance] Localization.groupoid

/-- The actual old-space collar chart of the original nerve one-skeleton attachment. -/
abbrev nerveGraphCollar (C : Type u) [Category.{v} C] :=
  simplexAttachmentCollar (NerveGraphData.Index C) 1 (NerveGraphData.pushout C)

/-- Pull the zero-stage decoder back along the actual collar retraction. -/
def nerveGraphCollarDecoder (C : Type u) [Category.{v} C] :
    FundamentalGroupoid (nerveGraphCollar C) ⥤ (⊤ : MorphismProperty C).Localization :=
  FundamentalGroupoid.map
    (simplexAttachmentCollarRetraction (NerveGraphData.Index C) 1 (NerveGraphData.pushout C)) ⋙
      nerveOldDecoder C

/-- Exact object formula for the collar decoder, using the published actual retraction. -/
theorem nerveGraphCollarDecoder_obj (C : Type u) [Category.{v} C] (x : nerveGraphCollar C) :
    (nerveGraphCollarDecoder C).obj (FundamentalGroupoid.mk x) =
      NerveGraphData.vertex C
        (simplexAttachmentCollarRetraction (NerveGraphData.Index C) 1
          (NerveGraphData.pushout C) x) := rfl

/-- The actual interior chart of an original attached nerve edge. -/
abbrev nerveGraphInterior (C : Type u) [Category.{v} C] (a : NerveGraphData.Index C) :=
  simplexAttachmentInterior (NerveGraphData.Index C) 1 (g := NerveGraphData.characteristic C) a

/-- An interior chart decoder with the actual edge source as its constant object.
The nontrivial edge information belongs in its two overlap transports. -/
def nerveGraphInteriorDecoder (C : Type u) [Category.{v} C] (a : NerveGraphData.Index C) :
    FundamentalGroupoid (nerveGraphInterior C a) ⥤ (⊤ : MorphismProperty C).Localization :=
  (Functor.const (FundamentalGroupoid (nerveGraphInterior C a))).obj
    (NerveGraphData.vertex C (NerveGraphData.attaching C (a, boundaryZero)))

/-- The interior decoder sends every actual path class to the specified identity. -/
theorem nerveGraphInteriorDecoder_map (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) {x y : nerveGraphInterior C a}
    (p : Path.Homotopic.Quotient x y) :
    (nerveGraphInteriorDecoder C a).map p =
      𝟙 (NerveGraphData.vertex C (NerveGraphData.attaching C (a, boundaryZero))) := rfl

end CategoryTheory.NerveCompletion
