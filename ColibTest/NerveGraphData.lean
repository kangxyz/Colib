/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.CompletionSurjectivity

/-! Original objects, endpoint transports, actual characteristic paths and
surjectivity of the original comparison, with independent universes. -/

@[expose] public noncomputable section

open CategoryTheory Convexity Convexity.StdSimplex TopCat SSet
open scoped Simplicial Topology unitInterval

universe u v

variable (C : Type u) [Category.{v} C]

example (c : C) :
    NerveGraphData.oldObject C ((NerveGraphData.oldHomeomorph C).symm c) = c :=
  NerveGraphData.oldObject_oldHomeomorph_symm C c

example (c : C) :
    NerveGraphData.inclusion C
      (NerveGraphData.transition C ((NerveGraphData.oldHomeomorph C).symm c)) =
        classifyingSpacePoint c :=
  NerveGraphData.inclusion_transition_oldHomeomorph_symm C c

example (a : NerveGraphData.Index C) :
    NerveGraphData.originalEdge C a =
      eqToHom (NerveGraphData.oldObject_source C a) ≫ a.simplex.map' 0 1 ≫
        eqToHom (NerveGraphData.oldObject_target C a).symm := rfl

example (a : NerveGraphData.Index C) (t : unitInterval) :
    NerveGraphData.inclusion C
      (NerveGraphData.characteristic C (a, StdSimplex.homeomorphI.symm t)) =
        classifyingSpacePath (a.simplex.map' 0 1) t :=
  NerveGraphData.characteristic_path C a t

example (c : C) : Function.Surjective (classifyingGroupoidCompletionMap C c) :=
  classifyingGroupoidCompletionMap_surjective C c
