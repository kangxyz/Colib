/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.Grid

/-! # Literal intersections and embeddings of finite cube cells

Distinct cells meet only on their actual coordinate faces. This supplies the
geometric boundary information for finite cubical attachment, without assuming
that an arbitrary inverse-image collar subset is a cofibration.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/Faces.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision

theorem intervalCell_injective (m : ℕ) (k : Fin (m + 1)) :
    Function.Injective (intervalCell m k) := by
  intro s t h
  have hh := congrArg (fun z : unitInterval ↦ (z : ℝ)) h
  change ((k : ℝ) + s) / (m+1) = ((k : ℝ) + t) / (m+1) at hh
  have hd : (m+1 : ℝ) ≠ 0 := by positivity
  have he := (div_left_inj' hd).mp hh
  exact Subtype.ext (add_left_cancel he)

theorem cell_injective (n m : ℕ) (k : CellIndex n m) :
    Function.Injective (cell n m k) := by
  intro s t h
  funext i
  exact intervalCell_injective m (k i) (congrFun h i)

/-- Every original affine cell map is an actual closed embedding. -/
theorem cell_isClosedEmbedding (n m : ℕ) (k : CellIndex n m) :
    Topology.IsClosedEmbedding (cell n m k) :=
  (cell n m k).continuous.isClosedEmbedding (cell_injective n m k)

/-- An intersection of ordered distinct interval cells is exactly their
shared endpoints, and forces adjacency of the grid indices. -/
theorem intervalCell_eq_endpoints_of_lt (m : ℕ) (k l : Fin (m + 1))
    (hkl : k < l) (s t : unitInterval) (he : intervalCell m k s = intervalCell m l t) :
    (k : ℕ) + 1 = l ∧ s = 1 ∧ t = 0 := by
  have hh := congrArg (fun z : unitInterval ↦ (z : ℝ)) he
  change ((k : ℝ) + s) / (m+1) = ((l : ℝ) + t) / (m+1) at hh
  have hd : (m+1 : ℝ) ≠ 0 := by positivity
  have hsum := (div_left_inj' hd).mp hh
  have hgap : (k : ℝ) + 1 ≤ l := by exact_mod_cast Nat.succ_le_of_lt hkl
  have hs : (s : ℝ) = 1 := by linarith [s.2.2,t.2.1]
  have ht : (t : ℝ) = 0 := by linarith [s.2.2,t.2.1]
  refine ⟨?_,Subtype.ext hs,Subtype.ext ht⟩
  have hk : (k : ℝ) + 1 = l := by linarith
  exact_mod_cast hk

/-- Any equality between different cell parametrizations occurs on a
literal common coordinate face, with its exact endpoint values. -/
theorem cell_eq_shared_face (n m : ℕ) (k l : CellIndex n m) (hkl : k ≠ l)
    (s t : Cube n) (he : cell n m k s = cell n m l t) :
    ∃ i : Fin n,
      ((k i : ℕ) + 1 = l i ∧ s i = 1 ∧ t i = 0) ∨
      ((l i : ℕ) + 1 = k i ∧ s i = 0 ∧ t i = 1) := by
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ l i := by
    by_contra h
    push Not at h
    exact hkl (funext h)
  have hei : intervalCell m (k i) (s i) = intervalCell m (l i) (t i) := congrFun he i
  rcases lt_or_gt_of_ne hi with h | h
  · exact ⟨i,Or.inl (intervalCell_eq_endpoints_of_lt m (k i) (l i) h (s i) (t i) hei)⟩
  · obtain ⟨hindex,ht,hs⟩ := intervalCell_eq_endpoints_of_lt m (l i) (k i) h (t i) (s i) hei.symm
    exact ⟨i,Or.inr ⟨hindex,hs,ht⟩⟩

/-- In particular, both preimages of an intersection lie on the entire
original cube boundary, including all possible lower-dimensional faces. -/
theorem cell_intersection_boundary (n m : ℕ) (k l : CellIndex n m) (hkl : k ≠ l)
    (s t : Cube n) (he : cell n m k s = cell n m l t) :
    s ∈ _root_.Cube.boundary (Fin n) ∧ t ∈ _root_.Cube.boundary (Fin n) := by
  obtain ⟨i,h | h⟩ := cell_eq_shared_face n m k l hkl s t he
  · exact ⟨⟨i,Or.inr h.2.1⟩,⟨i,Or.inl h.2.2⟩⟩
  · exact ⟨⟨i,Or.inl h.2.1⟩,⟨i,Or.inr h.2.2⟩⟩

end Topology.CubicalSubdivision
