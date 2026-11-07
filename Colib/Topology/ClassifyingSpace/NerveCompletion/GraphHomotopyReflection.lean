/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveHomotopyReflection
public import Colib.Topology.Homotopy.PathMap

/-!
# Graph Homotopy Reflection

The composite of the ORIGINAL graph-to-two-skeleton map and stage inclusion
is exactly the original inclusion into the full classifying space.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopCat SSet
open TopCat.SimplexAttachment Convexity.StdSimplex.Boundary FundamentalGroupoid.OpenCover
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover
open TopCat.SimplexAttachment
open Convexity.StdSimplex.Boundary
open FundamentalGroupoid.SequentialColimit
open Path
attribute [local instance] Localization.groupoid

/-- The composite of the ORIGINAL graph-to-two-skeleton map and stage inclusion
is exactly the original inclusion into the full classifying space. -/
theorem graph_twoSkeleton_inclusion (C : Type u) [Category.{v} C] :
    ((realizedSkeletonCocone (nerve C)).ι.app 3).hom.comp
      (nerveTwoSkeletonTransition C).hom = NerveGraphData.inclusion C :=
  congrArg (fun f => f.hom) ((realizedSkeletonCocone (nerve C)).w
    (homOfLE (show (2 : ℕ) ≤ 3 by decide)))

/-- Every ambient homotopy between actual graph-stage paths preserves their
original graph-decoder values. This uses a compact homotopy in one finite stage,
not an assumed decoder on the full realization or a faithfulness premise. -/
theorem graphDecoder_value_of_homotopic (C : Type u) [Category.{v} C]
    {x y : NerveGraphData.Stage C} (p q : Path x y)
    (H : (p.map (NerveGraphData.inclusion C).continuous).Homotopic
      (q.map (NerveGraphData.inclusion C).continuous)) :
    (nerveGraphDecoder C).map (Path.Homotopic.Quotient.mk p) =
      (nerveGraphDecoder C).map (Path.Homotopic.Quotient.mk q) := by
  have H3 := homotopic_map_comp_of_eq (nerveTwoSkeletonTransition C).hom
    ((realizedSkeletonCocone (nerve C)).ι.app 3).hom (NerveGraphData.inclusion C)
    (graph_twoSkeleton_inclusion C) p q H
  have hm := nerveStage_value_of_homotopic C 0
    (p.map (nerveTwoSkeletonTransition C).hom.continuous)
    (q.map (nerveTwoSkeletonTransition C).hom.continuous) H3
  let E := nerveStageZeroGraphIso C
  apply (cancel_epi (E.hom.app (FundamentalGroupoid.mk x))).mp
  have hp := E.hom.naturality (Path.Homotopic.Quotient.mk p)
  have hq := E.hom.naturality (Path.Homotopic.Quotient.mk q)
  change (nerveStageDecoder C 0).map (Path.Homotopic.Quotient.mk
      (p.map (nerveTwoSkeletonTransition C).hom.continuous)) ≫
      E.hom.app (FundamentalGroupoid.mk y) = _ at hp
  change (nerveStageDecoder C 0).map (Path.Homotopic.Quotient.mk
      (q.map (nerveTwoSkeletonTransition C).hom.continuous)) ≫
      E.hom.app (FundamentalGroupoid.mk y) = _ at hq
  exact hp.symm.trans ((congrArg (fun f => f ≫ E.hom.app (FundamentalGroupoid.mk y)) hm).trans hq)

end CategoryTheory.NerveCompletion
