/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.ClassifyingSpace.ConnectedComponents
public import Colib.Topology.ClassifyingSpace.SimplyConnectedCover
public import Colib.Topology.ClassifyingSpace.AsSmall

/-!
# Simply connected covers of actual classifying-space components

The categorical connected component realizes homeomorphically to the original
path-component subspace. Transporting its constructed covering along that
homeomorphism needs no connectedness assumption on the whole category.
-/
/-! Implementation source: `Quillen/Topology/ClassifyingSpace/ComponentCover.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual path-component
subtype, original forward covering map and independent universes are retained. -/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology
universe u v

namespace CategoryTheory

/-- Every original classifying-space path component has a surjective simply
connected cover in the same universe. -/
private theorem exists_simplyConnected_classifying_component_cover_small
    (C : Type u) [Category.{u} C] (b : C) :
    ∃ T : Type u, ∃ t : TopologicalSpace T,
      letI := t
      ∃ q : C(T, pathComponent (classifyingSpacePoint b)),
        IsCoveringMap q ∧ Function.Surjective q ∧ SimplyConnectedSpace T := by
  let D := (CategoryTheory.ConnectedComponents.mk b).Component
  let v : D := ⟨b, rfl⟩
  let e := classifyingSpaceComponentHomeomorph C b
  obtain ⟨T, t, q, hq, hs, hsc⟩ :=
    exists_simplyConnected_classifying_cover D v
  let := t
  refine ⟨T, t, ⟨e ∘ q, e.continuous.comp q.continuous⟩,
    hq.homeomorph_comp e, ?_, hsc⟩
  exact e.surjective.comp hs

/-- Independent object and morphism universes are retained by the actual
AsSmall nerve homeomorphism before taking the original path component. -/
theorem exists_simplyConnected_classifying_component_cover
    (C : Type u) [Category.{v} C] (b : C) :
    ∃ T : Type (max u v), ∃ t : TopologicalSpace T,
      letI := t
      ∃ q : C(T, pathComponent (classifyingSpacePoint b)),
        IsCoveringMap q ∧ Function.Surjective q ∧ SimplyConnectedSpace T := by
  let e₀ := asSmallClassifyingHomeomorph C
  let e : pathComponent (classifyingSpacePoint b) ≃ₜ
      pathComponent (classifyingSpacePoint (AsSmall.up.obj b)) :=
    (e₀.image _).trans (Homeomorph.setCongr (by
      rw [e₀.image_pathComponent, asSmallClassifyingHomeomorph_point]))
  obtain ⟨T, t, q, hq, hs, hsc⟩ :=
    exists_simplyConnected_classifying_component_cover_small (AsSmall.{0} C) (AsSmall.up.obj b)
  let := t
  exact ⟨T, t, ⟨e.symm ∘ q, e.symm.continuous.comp q.continuous⟩,
    hq.homeomorph_comp e.symm, e.symm.surjective.comp hs, hsc⟩

end CategoryTheory
