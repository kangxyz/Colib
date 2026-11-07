/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.ClassifyingSpace.ComponentCover
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletion

/-!
# An actual simply connected cover of the original zero completion component

The cover is over the literal path-component subtype used by `stableZeroMap`.
It needs no global connectedness assumption on the completion category.
-/
/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveCompletionCover.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The literal zero-component
subtype of the original finite-projective completion is unchanged. -/
@[expose] public section

noncomputable section
open CategoryTheory
attribute [local instance] CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal
universe u

namespace ModuleCat.FiniteProjective.StableCompletion

/-- The original zero completion component has an actual surjective simply
connected covering, in its own universe. No fiber-perfectness claim is made. -/
theorem exists_simplyConnected_zeroComponent_cover (R : Type u) [Ring R] :
    ∃ T : Type (u + 1), ∃ t : TopologicalSpace T,
      letI := t
      ∃ q : C(T, ZeroComponent R),
        IsCoveringMap q ∧ Function.Surjective q ∧ SimplyConnectedSpace T := by
  exact exists_simplyConnected_classifying_component_cover.{u + 1, u + 1}
    (Completion R) (stageObject R 0)

end ModuleCat.FiniteProjective.StableCompletion
