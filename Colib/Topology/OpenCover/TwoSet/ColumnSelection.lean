/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.CompactOpen

/-!
# Continuous selection on original two-chart path columns

For a continuous family of paths, the parameters whose entire path lies in a specified open
chart form an open set by compactness of the original interval. If these two sets cover a
normal parameter space, Urysohn's lemma selects a continuous original time: zero off the left
column set and one off the right column set. With endpoints in their respective charts, this
selects an actual point in the overlap. No separation hypothesis on the target space is used.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/OpenCover/TwoSet/ColumnSelection.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology

open scoped Topology unitInterval

universe u v

namespace Topology.OpenCover.TwoSet

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The parameters whose entire original path lies in the indicated subset. -/
def columnSet (b : C(unitInterval × X, Y)) (U : Set Y) : Set X :=
  {x | ∀ t, b (t, x) ∈ U}

/-- Compactness of the actual interval makes the whole-column condition open. -/
theorem isOpen_columnSet (b : C(unitInterval × X, Y)) (U : Set Y) (hU : IsOpen U) :
    IsOpen (columnSet b U) := by
  let paths : C(X, C(unitInterval, Y)) := {
    toFun x := ⟨fun t ↦ b (t, x), by fun_prop⟩
    continuous_toFun := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact b.continuous.comp continuous_swap }
  have h := (ContinuousMap.isOpen_setOfPred_range_subset (X := unitInterval) hU).preimage
    paths.continuous
  convert h using 1
  ext x
  exact ⟨fun hx y ⟨t, ht⟩ ↦ ht ▸ hx t, fun hx t ↦ hx ⟨t, rfl⟩⟩

/-- A continuous original-time selector, with exact values where only one whole-column
condition holds, evaluates the original path in the actual overlap. -/
theorem exists_column_selector [NormalSpace X]
    (b : C(unitInterval × X, Y)) (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hleft : ∀ x, b (0, x) ∈ U) (hright : ∀ x, b (1, x) ∈ V)
    (hcolumn : ∀ x, (∀ t, b (t, x) ∈ U) ∨ ∀ t, b (t, x) ∈ V) :
    ∃ a : C(X, unitInterval),
      (∀ x, x ∉ columnSet b U → a x = 0) ∧
      (∀ x, x ∉ columnSet b V → a x = 1) ∧
      ∀ x, b (a x, x) ∈ U ∩ V := by
  have hdisjoint : Disjoint (columnSet b U)ᶜ (columnSet b V)ᶜ :=
    Set.disjoint_left.mpr (fun x hx hy ↦ (hcolumn x).elim hx hy)
  obtain ⟨a, ha0, ha1, ha⟩ := exists_continuous_zero_one_of_isClosed
    (isOpen_columnSet b U hU).isClosed_compl (isOpen_columnSet b V hV).isClosed_compl hdisjoint
  let v : C(X, unitInterval) := ⟨fun x ↦ ⟨a x, ha x⟩, a.continuous.subtype_mk _⟩
  have hv0 (x : X) (hx : x ∉ columnSet b U) : v x = 0 := Subtype.ext (ha0 hx)
  have hv1 (x : X) (hx : x ∉ columnSet b V) : v x = 1 := Subtype.ext (ha1 hx)
  refine ⟨v, hv0, hv1, ?_⟩
  intro x
  constructor
  · by_cases hx : x ∈ columnSet b U
    · exact hx (v x)
    · rw [hv0 x hx]
      exact hleft x
  · by_cases hx : x ∈ columnSet b V
    · exact hx (v x)
    · rw [hv1 x hx]
      exact hright x

end Topology.OpenCover.TwoSet
