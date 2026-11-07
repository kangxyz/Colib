/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Order.Preorder.Chain

import Mathlib.Tactic.Linarith

/-!
# Metric coordinates for an arbitrary order complex

`MetricOrderComplex P` consists of finitely supported, nonnegative real weights
of total mass one whose support is a chain in `P`. Its metric is the
L1 metric, defined directly by the finite sum of coordinate distances.
No countability or local finiteness of `P` is
assumed, and the carrier remains in the universe of `P`.

This file proves the coordinate distance formula and Lipschitz estimates for
coordinates and the largest weight. It does not identify this metric topology
with the weak topology of the realization of the nerve.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/Coordinates.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual finitely supported
coordinate model, L1 topology and universe parameters are retained. -/
@[expose] public section
noncomputable section

universe u

namespace Topology

/-- The strong, L1 metric coordinate model of an arbitrary order complex. -/
def MetricOrderComplex (P : Type u) [PartialOrder P] : Type u :=
  {x : Convexity.StdSimplex ℝ P // IsChain (· ≤ ·) (x.weights.support : Set P)}

namespace MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- Classical equality is used only to enumerate finite supports. -/
local instance : DecidableEq P := Classical.decEq P

/-- The finite barycentric coordinate vector. -/
def weights (x : MetricOrderComplex P) : P →₀ ℝ := x.1.weights

/-- The same coordinate vector in Mathlib's algebraic standard simplex. -/
def toStdSimplex (x : MetricOrderComplex P) : Convexity.StdSimplex ℝ P := x.1

@[simp]
theorem weights_nonneg (x : MetricOrderComplex P) (v : P) : 0 ≤ x.weights v :=
  x.1.weights_nonneg v

@[simp]
theorem weights_total (x : MetricOrderComplex P) : x.weights.sum (fun _ a ↦ a) = 1 :=
  x.1.total

theorem support_chain (x : MetricOrderComplex P) :
    IsChain (· ≤ ·) (x.weights.support : Set P) := x.2

theorem support_nonempty (x : MetricOrderComplex P) : x.weights.support.Nonempty :=
  x.toStdSimplex.support_weights_nonempty

@[ext]
theorem ext {x y : MetricOrderComplex P} (h : ∀ v, x.weights v = y.weights v) : x = y := by
  apply Subtype.ext
  exact Convexity.StdSimplex.ext (Finsupp.ext h)

/-- The L1 distance, summed over the union of the two finite supports. -/
def coordinateDistance (x y : MetricOrderComplex P) : ℝ :=
  ∑ v ∈ x.weights.support ∪ y.weights.support, dist (x.weights v) (y.weights v)

/-- A common finite support can be used to evaluate the same L1 distance. -/
theorem coordinateDistance_eq_sum (x y : MetricOrderComplex P) (s : Finset P)
    (hx : x.weights.support ⊆ s) (hy : y.weights.support ⊆ s) :
    coordinateDistance x y = ∑ v ∈ s, dist (x.weights v) (y.weights v) := by
  classical
  unfold coordinateDistance
  apply Finset.sum_subset (Finset.union_subset hx hy)
  intro v _ hv
  have hx' : x.weights v = 0 :=
    Finsupp.notMem_support_iff.mp (fun h ↦ hv (Finset.mem_union_left _ h))
  have hy' : y.weights v = 0 :=
    Finsupp.notMem_support_iff.mp (fun h ↦ hv (Finset.mem_union_right _ h))
  simp [hx', hy']

theorem coordinate_dist_le_coordinateDistance (x y : MetricOrderComplex P) (v : P) :
    dist (x.weights v) (y.weights v) ≤ coordinateDistance x y := by
  classical
  unfold coordinateDistance
  by_cases hv : v ∈ x.weights.support ∪ y.weights.support
  · exact Finset.single_le_sum (fun _ _ ↦ dist_nonneg) hv
  · have hx : x.weights v = 0 :=
      Finsupp.notMem_support_iff.mp (fun h ↦ hv (Finset.mem_union_left _ h))
    have hy : y.weights v = 0 :=
      Finsupp.notMem_support_iff.mp (fun h ↦ hv (Finset.mem_union_right _ h))
    simpa [hx, hy] using Finset.sum_nonneg (s := x.weights.support ∪ y.weights.support)
      (fun w _ ↦ dist_nonneg (x := x.weights w) (y := y.weights w))

/-- The metric is the actual finite-support L1 metric, not the product topology. -/
instance : MetricSpace (MetricOrderComplex P) where
  dist := coordinateDistance
  dist_self x := by simp [coordinateDistance]
  dist_comm x y := by simp [coordinateDistance, Finset.union_comm, dist_comm]
  dist_triangle x y z := by
    classical
    let s := x.weights.support ∪ y.weights.support ∪ z.weights.support
    have hx : x.weights.support ⊆ s := by intro v hv; simp [s, hv]
    have hy : y.weights.support ⊆ s := by intro v hv; simp [s, hv]
    have hz : z.weights.support ⊆ s := by intro v hv; simp [s, hv]
    rw [coordinateDistance_eq_sum x z s hx hz, coordinateDistance_eq_sum x y s hx hy,
      coordinateDistance_eq_sum y z s hy hz, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v _ ↦ dist_triangle _ _ _
  eq_of_dist_eq_zero h := by
    apply ext
    intro v
    apply dist_le_zero.mp
    exact (coordinate_dist_le_coordinateDistance _ _ v).trans h.le

/-- A vertex is the coordinate vector of mass one at that vertex. -/
def vertex (v : P) : MetricOrderComplex P := by
  classical
  refine ⟨⟨Finsupp.single v 1, ?_, ?_⟩, ?_⟩
  · intro w
    simp only [Finsupp.zero_apply, Finsupp.single_apply]
    split_ifs <;> norm_num
  · simp
  · simp

@[simp]
theorem vertex_weights (v : P) : (vertex v).weights = Finsupp.single v 1 := rfl

/-- The largest barycentric coordinate, attained on the nonempty finite support. -/
def maximum (x : MetricOrderComplex P) : ℝ :=
  x.weights.support.sup' x.support_nonempty x.weights

theorem exists_maximum (x : MetricOrderComplex P) :
    ∃ v ∈ x.weights.support, x.maximum = x.weights v :=
  Finset.exists_mem_eq_sup' x.support_nonempty x.weights

theorem maximum_pos (x : MetricOrderComplex P) : 0 < x.maximum := by
  obtain ⟨v, hv, h⟩ := x.exists_maximum
  rw [h]
  exact lt_of_le_of_ne (x.weights_nonneg v) (Ne.symm (Finsupp.mem_support_iff.mp hv))

theorem weight_le_maximum (x : MetricOrderComplex P) (v : P) :
    x.weights v ≤ x.maximum := by
  classical
  by_cases hv : v ∈ x.weights.support
  · exact Finset.le_sup' x.weights hv
  · rw [Finsupp.notMem_support_iff.mp hv]
    exact x.maximum_pos.le

theorem maximum_le (x : MetricOrderComplex P) (r : ℝ)
    (h : ∀ v, x.weights v ≤ r) : x.maximum ≤ r :=
  (Finset.sup'_le_iff x.support_nonempty x.weights).mpr (fun v _ ↦ h v)

@[simp]
theorem maximum_vertex (v : P) : (vertex v).maximum = 1 := by
  classical
  simp [maximum, vertex_weights]

/-- The L1 metric is the finite sum of coordinate distances over either support. -/
theorem dist_eq_sum (x y : MetricOrderComplex P) :
    dist x y = ∑ v ∈ x.weights.support ∪ y.weights.support,
      dist (x.weights v) (y.weights v) := rfl

/-- Each coordinate changes by at most the L1 distance. -/
theorem coordinate_dist_le (x y : MetricOrderComplex P) (v : P) :
    dist (x.weights v) (y.weights v) ≤ dist x y :=
  coordinate_dist_le_coordinateDistance x y v

theorem coordinate_lipschitz (v : P) :
    LipschitzWith 1 (fun x : MetricOrderComplex P ↦ x.weights v) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  simpa using coordinate_dist_le x y v

@[fun_prop]
theorem continuous_coordinate (v : P) :
    Continuous (fun x : MetricOrderComplex P ↦ x.weights v) :=
  (coordinate_lipschitz v).continuous

theorem maximum_sub_le_dist (x y : MetricOrderComplex P) :
    x.maximum - y.maximum ≤ dist x y := by
  obtain ⟨v, _, hv⟩ := x.exists_maximum
  have h := coordinate_dist_le x y v
  rw [Real.dist_eq] at h
  have h' := le_abs_self (x.weights v - y.weights v)
  have hv' := weight_le_maximum y v
  rw [hv]
  linarith

/-- The maximum coordinate is itself 1-Lipschitz, although supports can change. -/
theorem maximum_lipschitz :
    LipschitzWith 1 (maximum : MetricOrderComplex P → ℝ) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, abs_le]
  constructor
  · have := maximum_sub_le_dist y x
    rw [dist_comm] at this
    linarith
  · exact maximum_sub_le_dist x y

@[fun_prop]
theorem continuous_maximum : Continuous (maximum : MetricOrderComplex P → ℝ) :=
  maximum_lipschitz.continuous

end MetricOrderComplex
end Topology
