/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.Basic
public import Colib.Topology.Realization.Connectivity

/-! # Every classifying-space point is joined to an original object vertex

Implementation provenance: the object-vertex statement in
`Quillen/Topology/Realization/Connectivity.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Both category universes are retained.
-/
@[expose] public noncomputable section

universe u v
namespace CategoryTheory

/-- Every classifying-space point lies in the path component of an object vertex. -/
theorem classifyingSpace_joined_vertex {C : Type u} [Category.{v} C]
    (x : ClassifyingSpace C) :
    ∃ c : C, Joined (classifyingSpacePoint c) x := by
  obtain ⟨v, hv⟩ := SSet.realization_joined_vertex x
  obtain ⟨c, rfl⟩ := (CategoryTheory.nerveEquiv (C := C)).symm.surjective v
  exact ⟨c, hv⟩

end CategoryTheory
