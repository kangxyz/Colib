/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Cube.ThinSupportColumns
public import Colib.Topology.CubicalSubdivision.Grid

/-!
# Thin-support avoidance along the original product-grid columns

The horizontal grid representative is chosen once for an entire column. Two different path
times can have different vertical grid representatives, but retain those same horizontal
coordinates. The explicit affine cell formula therefore reduces the global column count to
the proved finite band count, including grid walls, endpoints and zero-dimensional parameters.
This supplies the coordinate estimate; the incident-face normalization establishing its support
hypotheses and the homotopy-fiber lifting application are separate geometric tasks.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/CubicalSubdivision/ColumnAvoidance.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

open scoped Topology unitInterval

universe u

namespace Topology.CubicalSubdivision

/-- The actual grid cell separates its first, path coordinate from the parameter coordinates. -/
theorem cell_cons (d m : ℕ) (j : Fin (m + 1)) (k : CellIndex d m)
    (t : unitInterval) (x : Cube d) :
    cell (d + 1) m (Fin.cons j k) (Fin.cons t x) =
      Fin.cons (intervalCell m j t) (cell d m k x) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Two arbitrary actual times in one product-grid column cannot meet both bad sets. The
same horizontal representative is retained while the two vertical cells may be different. -/
theorem grid_column_not_mem_both (d m : ℕ) (a b c e : unitInterval) (hbc : b ≤ c)
    (p q : ℕ) (hd : d < p + q) {Y : Type u} [TopologicalSpace Y]
    (F : C(Cube (d + 1), Y)) (A B : Set Y)
    (hA : ∀ k, (F.comp (cell (d + 1) m k)) ⁻¹' A ⊆ _root_.Cube.thinSupport a b (p + 1))
    (hB : ∀ k, (F.comp (cell (d + 1) m k)) ⁻¹' B ⊆ _root_.Cube.thinSupport c e (q + 1))
    (x : Cube d) (s t : unitInterval) (hs : F (Fin.cons s x) ∈ A) :
    F (Fin.cons t x) ∉ B := by
  intro ht
  obtain ⟨k, z, rfl⟩ := cell_covers d m x
  obtain ⟨i, s', rfl⟩ := intervalCell_covers m s
  obtain ⟨j, t', rfl⟩ := intervalCell_covers m t
  have hs' : Fin.cons s' z ∈ _root_.Cube.thinSupport a b (p + 1) := by
    apply hA (Fin.cons i k)
    change F (cell (d + 1) m (Fin.cons i k) (Fin.cons s' z)) ∈ A
    rw [cell_cons]
    exact hs
  have ht' : Fin.cons t' z ∈ _root_.Cube.thinSupport c e (q + 1) := by
    apply hB (Fin.cons j k)
    change F (cell (d + 1) m (Fin.cons j k) (Fin.cons t' z)) ∈ B
    rw [cell_cons]
    exact ht
  exact _root_.Cube.column_not_mem_both a b c e hbc p q hd z s' t' hs' ht'

/-- Every original vertical path lies wholly in one original covering subset once each
actual grid cell satisfies the two proved support bounds. The parameter dimension is d;
the path cube dimension is d+1. -/
theorem grid_column_image_subset_one (d m : ℕ) (a b c e : unitInterval) (hbc : b ≤ c)
    (p q : ℕ) (hd : d < p + q) {Y : Type u} [TopologicalSpace Y]
    (F : C(Cube (d + 1), Y)) (U V : Set Y) (hcover : ∀ z, F z ∈ U ∪ V)
    (hU : ∀ k, (F.comp (cell (d + 1) m k)) ⁻¹' (U \ V) ⊆
      _root_.Cube.thinSupport a b (p + 1))
    (hV : ∀ k, (F.comp (cell (d + 1) m k)) ⁻¹' (V \ U) ⊆
      _root_.Cube.thinSupport c e (q + 1))
    (x : Cube d) :
    (∀ t, F (Fin.cons t x) ∈ U) ∨ ∀ t, F (Fin.cons t x) ∈ V := by
  classical
  by_cases h : ∃ s, F (Fin.cons s x) ∈ U \ V
  · obtain ⟨s, hs⟩ := h
    left
    intro t
    rcases hcover (Fin.cons t x) with ht | ht
    · exact ht
    · by_contra hn
      exact grid_column_not_mem_both d m a b c e hbc p q hd F (U \ V) (V \ U)
        hU hV x s t hs ⟨ht, hn⟩
  · right
    intro t
    rcases hcover (Fin.cons t x) with ht | ht
    · by_contra hn
      exact h ⟨t, ht, hn⟩
    · exact ht

end Topology.CubicalSubdivision
