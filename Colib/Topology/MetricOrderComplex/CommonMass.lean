/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.Coordinates
public import Mathlib.Topology.Algebra.Ring.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Common coordinate mass of two metric order-complex points

The pointwise minimum has support exactly the intersection of the supports.
For probability coordinates its mass is exactly one minus half the L1 distance.
Thus positive common mass is an open diagonal neighborhood even when the two
supports have a union which is not a chain. This is the first algebraic input
for a diagonal-fixed local connector, not an assumption of equiconnectivity.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/CommonMass.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual finitely supported
coordinate model, L1 topology and universe parameters are retained. -/
@[expose] public section
noncomputable section

open scoped Topology

universe u
namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- Classical equality is used only to enumerate finite supports. -/
local instance instDecidableEqCommonMass : DecidableEq P := Classical.decEq P

/-- The unnormalized weights shared by two coordinate distributions. -/
def commonWeights (x y : MetricOrderComplex P) : P →₀ ℝ :=
  Finsupp.zipWith min (min_self 0) x.weights y.weights

@[simp]
theorem commonWeights_apply (x y : MetricOrderComplex P) (v : P) :
    commonWeights x y v = min (x.weights v) (y.weights v) := rfl

theorem commonWeights_nonneg (x y : MetricOrderComplex P) (v : P) :
    0 ≤ commonWeights x y v := le_min (x.weights_nonneg v) (y.weights_nonneg v)

/-- Positive common coordinates occur exactly on the intersection, not the union. -/
theorem commonWeights_support (x y : MetricOrderComplex P) :
    (commonWeights x y).support = x.weights.support ∩ y.weights.support := by
  ext v
  simp only [Finset.mem_inter, Finsupp.mem_support_iff, commonWeights_apply]
  constructor
  · intro h
    have hp : 0 < min (x.weights v) (y.weights v) :=
      lt_of_le_of_ne (le_min (x.weights_nonneg v) (y.weights_nonneg v)) (Ne.symm h)
    exact ⟨ne_of_gt (lt_of_lt_of_le hp (min_le_left _ _)),
      ne_of_gt (lt_of_lt_of_le hp (min_le_right _ _))⟩
  · rintro ⟨hx, hy⟩
    exact ne_of_gt (lt_min
      (lt_of_le_of_ne (x.weights_nonneg v) (Ne.symm hx))
      (lt_of_le_of_ne (y.weights_nonneg v) (Ne.symm hy)))

@[simp]
theorem commonWeights_self (x : MetricOrderComplex P) : commonWeights x x = x.weights := by
  ext v
  simp

/-- The total unnormalized common mass. -/
def commonMass (x y : MetricOrderComplex P) : ℝ :=
  (commonWeights x y).sum (fun _ a ↦ a)

theorem commonMass_nonneg (x y : MetricOrderComplex P) : 0 ≤ commonMass x y :=
  Finsupp.sum_nonneg (fun v _ ↦ commonWeights_nonneg x y v)

@[simp]
theorem commonMass_self (x : MetricOrderComplex P) : commonMass x x = 1 := by
  simp [commonMass]

/-- The overlap identity uses the genuine finite-support L1 distance. -/
theorem twice_commonMass_add_dist (x y : MetricOrderComplex P) :
    2 * commonMass x y + dist x y = 2 := by
  let S := x.weights.support ∪ y.weights.support
  have hx : x.weights.support ⊆ S := Finset.subset_union_left
  have hy : y.weights.support ⊆ S := Finset.subset_union_right
  have hc : (commonWeights x y).support ⊆ S := Finsupp.support_zipWith
  have hxs : (∑ v ∈ S, x.weights v) = 1 := by
    rw [← Finsupp.sum_of_support_subset _ hx (fun _ a ↦ a) (by simp)]
    exact x.weights_total
  have hys : (∑ v ∈ S, y.weights v) = 1 := by
    rw [← Finsupp.sum_of_support_subset _ hy (fun _ a ↦ a) (by simp)]
    exact y.weights_total
  have hcs : commonMass x y = ∑ v ∈ S, min (x.weights v) (y.weights v) := by
    rw [commonMass, Finsupp.sum_of_support_subset _ hc (fun _ a ↦ a) (by simp)]
    rfl
  have hr (a b : ℝ) : 2 * min a b + dist a b = a + b := by
    rw [Real.dist_eq]
    rcases le_total a b with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  calc
    2 * commonMass x y + dist x y =
        ∑ v ∈ S, (2 * min (x.weights v) (y.weights v) +
          dist (x.weights v) (y.weights v)) := by
      rw [hcs, dist_eq_sum, Finset.mul_sum, Finset.sum_add_distrib]
    _ = ∑ v ∈ S, (x.weights v + y.weights v) := by
      apply Finset.sum_congr rfl
      intro v _
      exact hr _ _
    _ = 2 := by rw [Finset.sum_add_distrib, hxs, hys]; norm_num

/-- Common mass is a continuous metric expression despite changing finite supports. -/
theorem commonMass_eq_one_sub_half_dist (x y : MetricOrderComplex P) :
    commonMass x y = 1 - dist x y / 2 := by
  linarith [twice_commonMass_add_dist x y]

/-- Positive common mass is precisely the open distance-two domain. -/
theorem commonMass_pos_iff_dist_lt_two (x y : MetricOrderComplex P) :
    0 < commonMass x y ↔ dist x y < 2 := by
  rw [commonMass_eq_one_sub_half_dist]
  constructor <;> intro h <;> linarith

/-- The positivity domain agrees exactly with nonempty common support. -/
theorem commonMass_pos_iff_support (x y : MetricOrderComplex P) :
    0 < commonMass x y ↔ (x.weights.support ∩ y.weights.support).Nonempty := by
  constructor
  · intro h
    by_contra hn
    have hz : commonWeights x y = 0 := by
      apply Finsupp.support_eq_empty.mp
      rw [commonWeights_support]
      exact Finset.not_nonempty_iff_eq_empty.mp hn
    simp [commonMass, hz] at h
  · rintro ⟨v, hv⟩
    have hc : v ∈ (commonWeights x y).support := by rwa [commonWeights_support]
    change 0 < (commonWeights x y).sum (fun _ a ↦ a)
    apply Finsupp.sum_pos' (f := commonWeights x y) (g := fun _ a ↦ a)
      (fun w _ ↦ commonWeights_nonneg x y w)
    exact ⟨v, hc, lt_of_le_of_ne (commonWeights_nonneg x y v)
      (Ne.symm (Finsupp.mem_support_iff.mp hc))⟩

@[fun_prop]
theorem continuous_commonMass :
    Continuous (fun z : MetricOrderComplex P × MetricOrderComplex P ↦ commonMass z.1 z.2) := by
  simp only [commonMass_eq_one_sub_half_dist]
  fun_prop

/-- The natural domain for normalization is a genuine open diagonal neighborhood. -/
theorem isOpen_commonMass_pos :
    IsOpen {z : MetricOrderComplex P × MetricOrderComplex P | 0 < commonMass z.1 z.2} :=
  isOpen_lt continuous_const continuous_commonMass

end Topology.MetricOrderComplex
