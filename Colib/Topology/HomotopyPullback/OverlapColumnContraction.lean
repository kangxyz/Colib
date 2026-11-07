/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyPullback.OverlapPaths
public import Colib.Topology.OpenCover.TwoSet.ColumnSelection

/-!
# Contracting normalized original columns to the constant-path overlap comparison

The comparison is the existing strict-square comparison for the two actual subspace inclusions.
For a family whose every path lies wholly in one chart, a continuous selected original time
gives an actual overlap map. Straight interpolation in the original interval contracts the
stored paths to their selected points; its endpoints remain in their original charts. Every
already constant original path stays fixed throughout, including all its stored coordinates.
Normality is required only of the parameter space used for continuous selection, not the target.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyPullback/OverlapColumnContraction.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u v

namespace Topology.HomotopyPullback

variable {X : Type v} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {U V : Set Y}

/-- Evaluation at the selected original time, with codomain the actual overlap. -/
def selectedOverlapMap
    (b : C(X, HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)))
    (a : C(X, unitInterval)) (ha : ∀ x, overlapColumnFamily b (a x, x) ∈ U ∩ V) : C(X, ↥(U ∩ V)) :=
  ⟨fun x ↦ ⟨overlapColumnFamily b (a x, x), ha x⟩, by fun_prop⟩

/-- Straight interpolation contracts the original stored time to the selected original time. -/
def shrinkingOverlapColumn
    (b : C(X, HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)))
    (a : C(X, unitInterval)) : C(unitInterval × (unitInterval × X), Y) :=
  ⟨fun z ↦ overlapColumnFamily b (Set.Icc.convexComb z.2.1 (a z.2.2) z.1, z.2.2), by
    unfold Set.Icc.convexComb
    fun_prop⟩

/-- The moving initial endpoint stays in the original left subspace. -/
theorem shrinkingOverlapColumn_zero_mem
    (b : C(X, HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)))
    (a : C(X, unitInterval))
    (ha : ∀ x, x ∉ OpenCover.TwoSet.columnSet (overlapColumnFamily b) U → a x = 0)
    (r : unitInterval) (x : X) : shrinkingOverlapColumn b a (r, 0, x) ∈ U := by
  by_cases hx : x ∈ OpenCover.TwoSet.columnSet (overlapColumnFamily b) U
  · exact hx _
  · change (b x).val.2.2 (Set.Icc.convexComb 0 (a x) r) ∈ U
    rw [ha x hx, Set.Icc.convexComb_eq]
    exact (b x).property.1 ▸ (b x).val.2.1.property

/-- The moving terminal endpoint stays in the original right subspace. -/
theorem shrinkingOverlapColumn_one_mem
    (b : C(X, HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)))
    (a : C(X, unitInterval))
    (ha : ∀ x, x ∉ OpenCover.TwoSet.columnSet (overlapColumnFamily b) V → a x = 1)
    (r : unitInterval) (x : X) : shrinkingOverlapColumn b a (r, 1, x) ∈ V := by
  by_cases hx : x ∈ OpenCover.TwoSet.columnSet (overlapColumnFamily b) V
  · exact hx _
  · change (b x).val.2.2 (Set.Icc.convexComb 1 (a x) r) ∈ V
    rw [ha x hx, Set.Icc.convexComb_eq]
    exact (b x).property.2 ▸ (b x).val.1.property

/-- The actual homotopy from the original normalized family to the constant-path comparison
of its selected overlap map, retaining both endpoint coordinates and every stored path value. -/
def overlapColumnContraction
    (b : C(X, HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)))
    (a : C(X, unitInterval))
    (ha0 : ∀ x, x ∉ OpenCover.TwoSet.columnSet (overlapColumnFamily b) U → a x = 0)
    (ha1 : ∀ x, x ∉ OpenCover.TwoSet.columnSet (overlapColumnFamily b) V → a x = 1)
    (ha : ∀ x, overlapColumnFamily b (a x, x) ∈ U ∩ V) :
    b.Homotopy ((overlapComparison U V).comp (selectedOverlapMap b a ha)) where
  toFun z := ⟨(⟨shrinkingOverlapColumn b a (z.1, 1, z.2),
      shrinkingOverlapColumn_one_mem b a ha1 z.1 z.2⟩,
    ⟨shrinkingOverlapColumn b a (z.1, 0, z.2),
      shrinkingOverlapColumn_zero_mem b a ha0 z.1 z.2⟩,
    ⟨fun t ↦ shrinkingOverlapColumn b a (z.1, t, z.2), by fun_prop⟩), rfl, rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × X) × unitInterval ↦
      shrinkingOverlapColumn b a (z.1.1, z.2, z.1.2))
    fun_prop
  map_zero_left x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change (b x).val.2.2 (Set.Icc.convexComb 1 (a x) 0) = (b x).val.1.val
      rw [Set.Icc.convexComb_zero]
      exact (b x).property.2
    · apply Prod.ext
      · apply Subtype.ext
        change (b x).val.2.2 (Set.Icc.convexComb 0 (a x) 0) = (b x).val.2.1.val
        rw [Set.Icc.convexComb_zero]
        exact (b x).property.1
      · apply ContinuousMap.ext
        intro t
        change (b x).val.2.2 (Set.Icc.convexComb t (a x) 0) = (b x).val.2.2 t
        rw [Set.Icc.convexComb_zero]
  map_one_left x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change (b x).val.2.2 (Set.Icc.convexComb 1 (a x) 1) = (b x).val.2.2 (a x)
      rw [Set.Icc.convexComb_one]
    · apply Prod.ext
      · apply Subtype.ext
        change (b x).val.2.2 (Set.Icc.convexComb 0 (a x) 1) = (b x).val.2.2 (a x)
        rw [Set.Icc.convexComb_one]
      · apply ContinuousMap.ext
        intro t
        change (b x).val.2.2 (Set.Icc.convexComb t (a x) 1) = (b x).val.2.2 (a x)
        rw [Set.Icc.convexComb_one]

/-- The actual contraction retains every constant original column, at every deformation time. -/
theorem overlapColumnContraction_fixed
    (b : C(X, HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)))
    (a : C(X, unitInterval))
    (ha0 : ∀ x, x ∉ OpenCover.TwoSet.columnSet (overlapColumnFamily b) U → a x = 0)
    (ha1 : ∀ x, x ∉ OpenCover.TwoSet.columnSet (overlapColumnFamily b) V → a x = 1)
    (ha : ∀ x, overlapColumnFamily b (a x, x) ∈ U ∩ V)
    (x : X) (hx : ∀ t, (b x).val.2.2 t = (b x).val.2.2 0) (r : unitInterval) :
    overlapColumnContraction b a ha0 ha1 ha (r, x) = b x := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact (hx _).trans ((hx 1).symm.trans (b x).property.2)
  · apply Prod.ext
    · apply Subtype.ext
      exact (hx _).trans (b x).property.1
    · apply ContinuousMap.ext
      intro t
      exact (hx _).trans (hx t).symm

/-- Every normalized family over a normal parameter space admits this actual contraction
through the original constant-path comparison; every original constant column stays fixed. -/
theorem exists_overlap_column_contraction [NormalSpace X]
    (b : C(X, HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)))
    (hU : IsOpen U) (hV : IsOpen V)
    (hcolumn : ∀ x, (∀ t, (b x).val.2.2 t ∈ U) ∨ ∀ t, (b x).val.2.2 t ∈ V) :
    ∃ c : C(X, ↥(U ∩ V)), ∃ H : b.Homotopy ((overlapComparison U V).comp c),
      ∀ x, (∀ t, (b x).val.2.2 t = (b x).val.2.2 0) → ∀ r, H (r, x) = b x := by
  obtain ⟨a, ha0, ha1, ha⟩ := OpenCover.TwoSet.exists_column_selector
    (overlapColumnFamily b) U V hU hV
    (fun x ↦ (b x).property.1 ▸ (b x).val.2.1.property)
    (fun x ↦ (b x).property.2 ▸ (b x).val.1.property) hcolumn
  exact ⟨selectedOverlapMap b a ha, overlapColumnContraction b a ha0 ha1 ha,
    fun x hx r ↦ overlapColumnContraction_fixed b a ha0 ha1 ha x hx r⟩

end Topology.HomotopyPullback
