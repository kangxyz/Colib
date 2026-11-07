/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.NerveGraphData
public import Colib.Topology.ClassifyingSpace.CompletionMap
public import Colib.Topology.Realization.GraphAttachmentFullness

/-!
# Surjectivity of the actual groupoid-completion comparison

The actual one-dimensional skeleton and its original arrow paths, together with
geometric graph-path generation, make the original comparison surjective.
No injectivity, retraction or bijectivity assertion is imported or included.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/ClassifyingSpace/CompletionSurjectivity.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, endpoint equalities,
path classes and independent universe parameters are retained. Native namespace
ownership and the pinned native simplex maps replace source ownership.
Only the first two source declarations are included.
-/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory SSet TopCat
open scoped Simplicial Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory
attribute [local instance] Localization.groupoid
variable (C : Type u) [Category.{v} C]

/-- Every actual path class between original object vertices comes from an
arrow in the genuine groupoid completion, under the original comparison. -/
theorem classifyingGroupoidCompletionFunctor_map_surjective (c d : C) :
    Function.Surjective ((classifyingGroupoidCompletionFunctor C).map :
      ((⊤ : MorphismProperty C).Q.obj c ⟶ (⊤ : MorphismProperty C).Q.obj d) →
        (FundamentalGroupoid.mk (classifyingSpacePoint c) ⟶
          FundamentalGroupoid.mk (classifyingSpacePoint d))) := by
  let : (FundamentalGroupoid.map (NerveGraphData.inclusion C)).Full :=
    realizedSkeleton_fundamentalGroupoid_full (nerve C) 2 le_rfl
  obtain ⟨x, rfl⟩ := (NerveGraphData.oldHomeomorph C).surjective c
  obtain ⟨y, rfl⟩ := (NerveGraphData.oldHomeomorph C).surjective d
  exact GraphAttachment.map_surjective_of_ambient_full
    (NerveGraphData.Index C) (NerveGraphData.pushout C) (NerveGraphData.inclusion C)
    (classifyingGroupoidCompletionFunctor C) (NerveGraphData.vertex C)
    (NerveGraphData.vertexIdentification C) (NerveGraphData.edge C)
    (NerveGraphData.edge_spoke C) x y

/-- The original completed-loop comparison is surjective onto the actual
fundamental group of the nerve realization at every original object. -/
theorem classifyingGroupoidCompletionMap_surjective (c : C) :
    Function.Surjective (classifyingGroupoidCompletionMap C c) := by
  intro g
  obtain ⟨f, hf⟩ := classifyingGroupoidCompletionFunctor_map_surjective C c c g.asHom
  exact ⟨End.of f, End.ext hf⟩

end CategoryTheory

attribute [colib_tag "COL-0160",
  colib_ref "WeibelKBook" "IV, Recipe 3.1.1 and Definition 3.1.4, pages 24-25"
    "background"
    "Nerve and classifying-space construction; the actual comparison surjectivity is proved here"]
  CategoryTheory.classifyingGroupoidCompletionFunctor_map_surjective
  CategoryTheory.classifyingGroupoidCompletionMap_surjective
