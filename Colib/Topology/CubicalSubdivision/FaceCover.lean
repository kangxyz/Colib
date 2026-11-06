/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.FaceComplex
public import Colib.Topology.CubicalSubdivision.Cover

/-! # One uniform grid controls every face in every skeleton dimension

Implementation provenance:
`Quillen/Topology/CubicalSubdivision/FaceCover.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision
universe u v

/-- Every canonical grid face lies in an actual full-dimensional grid cell.
The selected cell is uniform over all parameter points of that face. -/
theorem faceSet_subset_cellSet {n m : ℕ} (F : FaceIndex n m) :
    ∃ k : CellIndex n m, faceSet F ⊆ cellSet n m k := by
  have hc : ∀ i : Fin n, ∃ k : Fin (m+1),
      ∀ s : Active F → unitInterval, ∃ t : unitInterval, intervalCell m k t = face F s i := by
    intro i
    cases h : F i with
    | inl j =>
      obtain ⟨k,t,ht⟩ := intervalCell_covers m (gridVertex m j)
      refine ⟨k,fun s ↦ ⟨t,?_⟩⟩
      exact ht.trans (face_fixed F s i j h).symm
    | inr k =>
      exact ⟨k,fun s ↦ ⟨s ⟨i,k,h⟩,(face_moving F s i k h).symm⟩⟩
  choose k hk using hc
  refine ⟨k,?_⟩
  rintro x ⟨s,rfl⟩
  choose t ht using fun i ↦ hk i s
  exact ⟨t,funext ht⟩

/-- The same finite grid makes every whole face subordinate to the pulled-back
open cover, simultaneously in all dimensions. -/
theorem exists_grid_faces_subordinate (n : ℕ) {X : Type u} [TopologicalSpace X]
    (f : C(Cube n, X)) {J : Type v} (U : J → Set X)
    (hU : ∀ j, IsOpen (U j)) (hcover : ∀ x, ∃ j, f x ∈ U j) :
    ∃ m : ℕ, ∀ F : FaceIndex n m, ∃ j : J,
      ∀ t : Active F → unitInterval, f (face F t) ∈ U j := by
  obtain ⟨m,hm⟩ := exists_grid_map_subordinate n f U hU hcover
  refine ⟨m,fun F ↦ ?_⟩
  obtain ⟨k,hk⟩ := faceSet_subset_cellSet F
  obtain ⟨j,hj⟩ := hm k
  refine ⟨j,fun t ↦ ?_⟩
  obtain ⟨s,hs⟩ := hk ⟨t,rfl⟩
  rw [← hs]
  exact hj s

end Topology.CubicalSubdivision
