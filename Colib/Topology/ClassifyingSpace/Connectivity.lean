/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ArrowPaths
public import Mathlib.CategoryTheory.IsConnected
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

/-- Categorical connectedness joins all object vertices by genuine topological paths. -/
theorem classifyingSpace_joined_points {C : Type u} [Category.{v} C]
    [IsPreconnected C] (c d : C) :
    Joined (classifyingSpacePoint c) (classifyingSpacePoint d) := by
  apply Quotient.exact (s := pathSetoid (ClassifyingSpace C))
  exact constant_of_preserves_morphisms
    (fun e : C => ZerothHomotopy.mk (classifyingSpacePoint e))
    (fun _ _ f => ZerothHomotopy.sound (classifyingSpacePath f)) c d

/-- The realization of the nerve of a connected category is path-connected. -/
instance classifyingSpace_pathConnected {C : Type u} [Category.{v} C]
    [IsConnected C] : PathConnectedSpace (ClassifyingSpace C) where
  nonempty := ⟨classifyingSpacePoint (Classical.arbitrary C)⟩
  joined x y := by
    obtain ⟨c, hc⟩ := classifyingSpace_joined_vertex x
    obtain ⟨d, hd⟩ := classifyingSpace_joined_vertex y
    exact hc.symm.trans ((classifyingSpace_joined_points c d).trans hd)

/-- A path from any chosen object vertex to any point, in a connected category. -/
def classifyingSpacePathToPoint {C : Type u} [Category.{v} C]
    [IsPreconnected C] (c : C) (x : ClassifyingSpace C) :
    Path (classifyingSpacePoint c) x := by
  apply Joined.somePath
  obtain ⟨d, hd⟩ := classifyingSpace_joined_vertex x
  exact (classifyingSpace_joined_points c d).trans hd


end CategoryTheory
