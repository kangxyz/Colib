/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.Simplex
public import Colib.Topology.Realization.EdgePath

/-! # Joining realized points to vertices

Implementation provenance: `Quillen/Topology/Realization/Connectivity.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, general simplicial-set declarations.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u
namespace SSet

/-- Realizations of standard simplices are path-connected. -/
instance realizationStandardSimplex_pathConnected (n : SimplexCategory) :
    PathConnectedSpace |SSet.stdSimplex.{u}.obj n| :=
  (SimplexCategory.toTopHomeo n).symm.pathConnectedSpace

/-- Each point of a realization can be joined to the image of a vertex. -/
theorem realization_joined_vertex {X : SSet.{u}} (x : |X|) :
    ∃ v : X _⦋0⦌, Joined (realizationPoint v) x := by
  obtain ⟨n, f, t, rfl⟩ := realization_exists_simplex x
  let v : (SSet.stdSimplex.obj n) _⦋0⦌ := SSet.stdSimplex.const n.len 0 _
  refine ⟨f.app _ v, ?_⟩
  rw [← SSet.realizationPoint_naturality]
  exact (PathConnectedSpace.joined (realizationPoint v) t).map (by fun_prop)

end SSet
