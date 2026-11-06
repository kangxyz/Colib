/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.SplitTransport

/-!
# Collar Transport

For an actual collar path whose endpoints retract to the same specified
old vertex, the collar decoder is exactly the resulting equality transport.
-/

@[expose] public section

noncomputable section
open CategoryTheory Convexity.StdSimplex TopCat
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment
attribute [local instance] Localization.groupoid

/-- For an actual collar path whose endpoints retract to the same specified
old vertex, the collar decoder is exactly the resulting equality transport. -/
theorem nerveGraphCollarDecoder_path_same_vertex (C : Type u) [Category.{v} C]
    {x y : nerveGraphCollar C} (p : Path x y) (a : NerveGraphData.Old C)
    (hx : simplexAttachmentCollarRetraction (NerveGraphData.Index C) 1
      (NerveGraphData.pushout C) x = a)
    (hy : simplexAttachmentCollarRetraction (NerveGraphData.Index C) 1
      (NerveGraphData.pushout C) y = a) :
    (nerveGraphCollarDecoder C).map (Path.Homotopic.Quotient.mk p) =
      eqToHom (congrArg (NerveGraphData.vertex C) (hx.trans hy.symm)) := rfl

end CategoryTheory.NerveCompletion
