/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.Grid

/-! # Uniform finite grids subordinate to actual open covers

The grid is chosen once for the whole compact cube. Its cells are the actual
closed affine cells from `Grid`, so later gluing can use cubical faces rather
than arbitrary closed inverse images of collars.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/Cover.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision
universe u v

/-- A single finite grid is subordinate to any open cover of the whole cube,
including the zero-dimensional cube. -/
theorem exists_grid_subordinate (n : ℕ) {J : Type u} (U : J → Set (Cube n))
    (hU : ∀ j, IsOpen (U j)) (hcover : ⋃ j, U j = Set.univ) :
    ∃ m : ℕ, ∀ k : CellIndex n m, ∃ j : J, cellSet n m k ⊆ U j := by
  obtain ⟨ε,hε,hεU⟩ := CompactSpace.lebesgue_number_lemma U hU hcover
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hε
  refine ⟨m,fun k ↦ hεU (cellSet n m k) (cellSet_nonempty n m k) ?_⟩
  exact (cellSet_diam_le n m k).trans hm.le

/-- Subordination for a genuine continuous cube map into an arbitrary space. -/
theorem exists_grid_map_subordinate (n : ℕ) {X : Type v} [TopologicalSpace X]
    (f : C(Cube n, X)) {J : Type u} (U : J → Set X)
    (hU : ∀ j, IsOpen (U j)) (hcover : ∀ x, ∃ j, f x ∈ U j) :
    ∃ m : ℕ, ∀ k : CellIndex n m, ∃ j : J, ∀ t : Cube n, f (cell n m k t) ∈ U j := by
  have hc : ⋃ j, f ⁻¹' U j = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
    exact hcover x
  obtain ⟨m,hm⟩ := exists_grid_subordinate n (fun j ↦ f ⁻¹' U j)
    (fun j ↦ (hU j).preimage f.continuous) hc
  refine ⟨m,fun k ↦ ?_⟩
  obtain ⟨j,hj⟩ := hm k
  exact ⟨j,fun t ↦ hj ⟨t,rfl⟩⟩

/-- The literal two height collars admit one finite cubical subdivision.
The output is uniform over every point of each closed cell. -/
theorem exists_grid_height_collars (n : ℕ) (h : C(Cube n, unitInterval)) :
    ∃ m : ℕ, ∀ k : CellIndex n m,
      (∀ t : Cube n, (h (cell n m k t) : ℝ) < 3 / 4) ∨
      (∀ t : Cube n, (1 / 4 : ℝ) < h (cell n m k t)) := by
  let U : Bool → Set unitInterval := fun b ↦ if b then
    {x | (1 / 4 : ℝ) < x} else {x | (x : ℝ) < 3 / 4}
  have hU : ∀ b, IsOpen (U b) := by
    intro b
    cases b
    · exact isOpen_lt continuous_subtype_val continuous_const
    · exact isOpen_lt continuous_const continuous_subtype_val
  have hc : ∀ x : Cube n, ∃ b, h x ∈ U b := by
    intro x
    by_cases hx : (h x : ℝ) < 3 / 4
    · exact ⟨false,hx⟩
    · refine ⟨true,?_⟩
      change (1 / 4 : ℝ) < h x
      linarith
  obtain ⟨m,hm⟩ := exists_grid_map_subordinate n h U hU hc
  refine ⟨m,fun k ↦ ?_⟩
  obtain ⟨b,hb⟩ := hm k
  cases b
  · exact Or.inl hb
  · exact Or.inr hb

end Topology.CubicalSubdivision
