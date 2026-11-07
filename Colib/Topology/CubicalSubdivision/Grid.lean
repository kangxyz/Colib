/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FunProp

/-! # Explicit finite affine grids of the actual unit cube

Every cell retains its literal coordinate formula. The finite closed cover,
mesh estimate and shared-face equations are proved in the original product
topology, including the zero-dimensional cube.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/Grid.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision

/-- The `n`-dimensional unit cube, with coordinates indexed by `Fin n`. -/
abbrev Cube (n : ℕ) := Fin n → unitInterval
/-- A choice of one of the `m + 1` grid intervals in each of the `n` cube coordinates. -/
abbrev CellIndex (n m : ℕ) := Fin n → Fin (m+1)

/-- The original affine parametrization of one interval of the grid. -/
def intervalCell (m : ℕ) (k : Fin (m + 1)) : C(unitInterval, unitInterval) where
  toFun t := ⟨((k : ℝ) + t) / (m+1), by
    have hd : (0 : ℝ) < m+1 := by positivity
    constructor
    · exact div_nonneg (add_nonneg (by positivity) t.2.1) hd.le
    · apply (div_le_one hd).2
      have hk : (k : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ k.isLt
      linarith [t.2.2]⟩
  continuous_toFun := by fun_prop

@[simp] theorem intervalCell_val (m : ℕ) (k : Fin (m + 1)) (t : unitInterval) :
    (intervalCell m k t : ℝ) = ((k : ℝ) + t) / (m+1) := rfl

/-- The actual affine cell of a finite product grid. -/
def cell (n m : ℕ) (k : CellIndex n m) : C(Cube n, Cube n) where
  toFun t i := intervalCell m (k i) (t i)
  continuous_toFun := by fun_prop

@[simp] theorem cell_apply (n m : ℕ) (k : CellIndex n m) (t : Cube n) (i : Fin n) :
    (cell n m k t i : ℝ) = ((k i : ℝ) + t i) / (m+1) := rfl

/-- Every actual interval point belongs to a genuine grid interval. -/
theorem intervalCell_covers (m : ℕ) (x : unitInterval) :
    ∃ k : Fin (m+1), ∃ t : unitInterval, intervalCell m k t = x := by
  have hd : (0 : ℝ) < m+1 := by positivity
  by_cases hx : (x : ℝ) = 1
  · refine ⟨⟨m, Nat.lt_succ_self m⟩, 1, ?_⟩
    apply Subtype.ext
    change ((m : ℝ) + 1) / (m+1) = (x : ℝ)
    rw [hx, div_self hd.ne']
  · have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne x.2.2 hx
    let r : ℝ := (m+1) * x
    have hr : 0 ≤ r := mul_nonneg hd.le x.2.1
    have hrlt : r < (m+1 : ℝ) := by dsimp [r]; nlinarith
    have hk : ⌊r⌋₊ < m+1 := by
      have hh : (⌊r⌋₊ : ℝ) < ((m+1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using (Nat.floor_le hr).trans_lt hrlt
      exact_mod_cast hh
    let t : unitInterval := ⟨r - ⌊r⌋₊, by
      constructor
      · exact sub_nonneg.mpr (Nat.floor_le hr)
      · linarith [Nat.lt_floor_add_one r]⟩
    refine ⟨⟨⌊r⌋₊, hk⟩, t, ?_⟩
    apply Subtype.ext
    change ((⌊r⌋₊ : ℝ) + (r - ⌊r⌋₊)) / (m+1) = (x : ℝ)
    dsimp [r]
    field_simp
    ring

/-- The finite collection of closed affine cells covers the entire cube. -/
theorem cell_covers (n m : ℕ) (x : Cube n) :
    ∃ k : CellIndex n m, ∃ t : Cube n, cell n m k t = x := by
  have h := fun i : Fin n ↦ intervalCell_covers m (x i)
  choose k t ht using h
  exact ⟨k,t,funext ht⟩

/-- The closed grid cell represented by `k`, defined as the range of its affine parametrization. -/
def cellSet (n m : ℕ) (k : CellIndex n m) : Set (Cube n) := Set.range (cell n m k)

theorem cellSet_nonempty (n m : ℕ) (k : CellIndex n m) : (cellSet n m k).Nonempty :=
  ⟨cell n m k (fun _ ↦ 0), ⟨_,rfl⟩⟩

theorem cellSet_isCompact (n m : ℕ) (k : CellIndex n m) : IsCompact (cellSet n m k) :=
  isCompact_range (cell n m k).continuous

theorem cellSet_isClosed (n m : ℕ) (k : CellIndex n m) : IsClosed (cellSet n m k) :=
  (cellSet_isCompact n m k).isClosed

theorem cellSet_iUnion (n m : ℕ) : ⋃ k : CellIndex n m, cellSet n m k = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, cellSet, Set.mem_range, Set.mem_univ, iff_true]
  exact cell_covers n m x

/-- Each coordinate has width at most the reciprocal grid size. -/
theorem intervalCell_dist_le (m : ℕ) (k : Fin (m + 1)) (s t : unitInterval) :
    dist (intervalCell m k s) (intervalCell m k t) ≤ 1 / (m+1 : ℝ) := by
  have hd : (0 : ℝ) < m+1 := by positivity
  change |((k : ℝ) + s) / (m+1) - ((k : ℝ) + t) / (m+1)| ≤ _
  rw [← sub_div, add_sub_add_left_eq_sub, abs_div, abs_of_pos hd]
  apply (div_le_div_iff_of_pos_right hd).2
  exact abs_le.mpr ⟨by linarith [s.2.1,t.2.2], by linarith [s.2.2,t.2.1]⟩

/-- The mesh estimate uses the actual finite-product metric; no positive
cube dimension is required. -/
theorem cell_dist_le (n m : ℕ) (k : CellIndex n m) (s t : Cube n) :
    dist (cell n m k s) (cell n m k t) ≤ 1 / (m+1 : ℝ) := by
  apply (dist_pi_le_iff (by positivity)).2
  intro i
  exact intervalCell_dist_le m (k i) (s i) (t i)

theorem cellSet_diam_le (n m : ℕ) (k : CellIndex n m) :
    Metric.diam (cellSet n m k) ≤ 1 / (m+1 : ℝ) := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  rintro x ⟨s,rfl⟩ y ⟨t,rfl⟩
  exact cell_dist_le n m k s t

/-- Adjacent interval cells agree on their actual common face. -/
theorem intervalCell_shared_face (m : ℕ) (k l : Fin (m + 1))
    (h : (k : ℕ) + 1 = l) : intervalCell m k 1 = intervalCell m l 0 := by
  apply Subtype.ext
  change ((k : ℝ) + 1) / (m+1) = ((l : ℝ) + 0) / (m+1)
  have hr : (k : ℝ) + 1 = l := by exact_mod_cast h
  rw [hr, add_zero]

/-- A common cubical face is the same map in both adjacent cells. -/
theorem cell_shared_face (n m : ℕ) (k l : CellIndex n m) (i : Fin n)
    (hi : (k i : ℕ) + 1 = l i) (hkl : ∀ j, j ≠ i → k j = l j)
    (t : Cube n) :
    cell n m k (Function.update t i 1) = cell n m l (Function.update t i 0) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [cell, ContinuousMap.coe_mk, Function.update_self]
    exact intervalCell_shared_face m (k i) (l i) hi
  · simp only [cell, ContinuousMap.coe_mk, Function.update_of_ne hji]
    rw [hkl j hji]

end Topology.CubicalSubdivision
