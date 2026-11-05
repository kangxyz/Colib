/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.Skeleton

/-!
# Realization takes every simplicial monomorphism to a closed embedding

A simplicial monomorphism is the inclusion of the initial stage in its
relative skeletal colimit. All successor inclusions have already been
identified with actual closed simplex-boundary attachments. The sequential
closed-embedding theorem therefore applies to its realization.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits Topology
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false

namespace SSet

/-- Every simplicial monomorphism realizes to a closed embedding, with the
actual subspace topology, without finiteness or local compactness hypotheses. -/
theorem realization_mono_isClosedEmbedding {A X : SSet.{u}} (i : A ⟶ X) [Mono i] :
    IsClosedEmbedding (SSet.toTop.map i) := by
  let e := SSet.toTop.mapIso (SSet.relativeCellComplexOfMono i).isoBot
  have hi : SSet.toTop.map i =
      e.inv ≫ (realizedRelativeSkeletonCocone i).ι.app 0 := by
    change SSet.toTop.map i = SSet.toTop.map (SSet.relativeCellComplexOfMono i).isoBot.inv ≫
      SSet.toTop.map ((SSet.relativeCellComplexOfMono i).incl.app 0)
    rw [← Functor.map_comp]
    exact congrArg SSet.toTop.map (SSet.relativeCellComplexOfMono i).fac.symm
  rw [hi]
  exact (TopCat.SequentialColimit.stage_isClosedEmbedding
    (realizedRelativeSkeletonIsColimit i) (realizedRelativeSkeleton_closedEmbeddings i) 0).comp
      (TopCat.homeoOfIso e.symm).isClosedEmbedding

end SSet
