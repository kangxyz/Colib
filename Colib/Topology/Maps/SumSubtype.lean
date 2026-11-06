/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Logic.Equiv.Sum

/-! # Literal subspaces of topological sums

Implementation provenance:
`Quillen/Topology/Maps/SumSubtype.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology Set
universe u v
namespace Topology

/-- Taking a subspace of a disjoint topological sum commutes with its two
summands, with the original subtype and sum topologies. -/
def sumSubtypeHomeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (p : X ⊕ Y → Prop) :
    {z : X ⊕ Y // p z} ≃ₜ ({x : X // p (.inl x)} ⊕ {y : Y // p (.inr y)}) := by
  let i : {x : X // p (.inl x)} → {z : X ⊕ Y // p z} := fun x ↦ ⟨.inl x.1,x.2⟩
  let j : {y : Y // p (.inr y)} → {z : X ⊕ Y // p z} := fun y ↦ ⟨.inr y.1,y.2⟩
  have hi : IsOpenEmbedding i := by
    refine ⟨((IsEmbedding.inl.comp IsEmbedding.subtypeVal).codRestrict _ _),?_⟩
    have he : Set.range i = Subtype.val ⁻¹' Set.range (@Sum.inl X Y) := by
      ext z
      constructor
      · rintro ⟨x,rfl⟩
        exact ⟨x.1,rfl⟩
      · rintro ⟨x,hx⟩
        exact ⟨⟨x,hx ▸ z.2⟩,Subtype.ext hx⟩
    rw [he]
    exact isOpen_range_inl.preimage continuous_subtype_val
  have hj : IsOpenEmbedding j := by
    refine ⟨((IsEmbedding.inr.comp IsEmbedding.subtypeVal).codRestrict _ _),?_⟩
    have he : Set.range j = Subtype.val ⁻¹' Set.range (@Sum.inr X Y) := by
      ext z
      constructor
      · rintro ⟨y,rfl⟩
        exact ⟨y.1,rfl⟩
      · rintro ⟨y,hy⟩
        exact ⟨⟨y,hy ▸ z.2⟩,Subtype.ext hy⟩
    rw [he]
    exact isOpen_range_inr.preimage continuous_subtype_val
  refine ((Equiv.subtypeSum (p := p)).symm.toHomeomorphOfContinuousOpen ?_ ?_).symm
  · exact continuous_sum_dom.mpr ⟨hi.continuous,hj.continuous⟩
  · exact isOpenMap_sum.mpr ⟨hi.isOpenMap,hj.isOpenMap⟩

end Topology
