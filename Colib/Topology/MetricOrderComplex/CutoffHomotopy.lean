/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.Cutoff
public import Mathlib.Topology.Homotopy.Basic

import Mathlib.Tactic.Ring

/-!
# Vertex-fixed straight-line homotopy for the metric cutoff

The normalized cutoff and the original point lie in the same finite chain
simplex. Their affine interpolation therefore stays in the metric order
complex. Explicit L1 estimates prove continuity even when the support of the
original point changes. This supplies the metric-side homotopy for the future
comparison with weak realization topology; no such comparison is assumed here.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/CutoffHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual finitely supported
coordinate model, L1 topology and universe parameters are retained. -/
@[expose] public section
noncomputable section

open scoped Topology unitInterval

universe u

namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- Classical equality is used only to enumerate finite supports. -/
local instance instDecidableEqCutoffHomotopy : DecidableEq P := Classical.decEq P

/-- Straight-line interpolation from the normalized cutoff to the original point. -/
def cutoffBlend (t : I) (x : MetricOrderComplex P) : MetricOrderComplex P := by
  refine ⟨⟨(1 - (t : ℝ)) • x.cutoff.weights + (t : ℝ) • x.weights, ?_, ?_⟩, ?_⟩
  · intro v
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr t.2.2) (x.cutoff.weights_nonneg v))
      (mul_nonneg t.2.1 (x.weights_nonneg v))
  · rw [Finsupp.sum_add_index (by simp) (by intros; rfl),
      Finsupp.sum_smul_index (fun _ ↦ rfl), Finsupp.sum_smul_index (fun _ ↦ rfl)]
    simp only [Finsupp.sum, ← Finset.mul_sum]
    change (1 - (t : ℝ)) * x.cutoff.weights.sum (fun _ a ↦ a) +
      (t : ℝ) * x.weights.sum (fun _ a ↦ a) = 1
    rw [weights_total, weights_total]
    ring
  · refine IsChain.mono ?_ x.support_chain
    intro v hv
    rcases Finset.mem_union.mp (Finsupp.support_add hv) with hv | hv
    · exact x.cutoff_support_subset (Finsupp.support_smul hv)
    · exact Finsupp.support_smul hv

@[simp]
theorem cutoffBlend_weights (t : I) (x : MetricOrderComplex P) (v : P) :
    (cutoffBlend t x).weights v = (1 - (t : ℝ)) * x.cutoff.weights v +
      (t : ℝ) * x.weights v := rfl

theorem cutoffBlend_support_subset (t : I) (x : MetricOrderComplex P) :
    (cutoffBlend t x).weights.support ⊆ x.weights.support := by
  intro v hv
  rcases Finset.mem_union.mp (Finsupp.support_add hv) with hv | hv
  · exact x.cutoff_support_subset (Finsupp.support_smul hv)
  · exact Finsupp.support_smul hv

@[simp]
theorem cutoffBlend_zero (x : MetricOrderComplex P) : cutoffBlend 0 x = x.cutoff := by
  ext v
  simp

@[simp]
theorem cutoffBlend_one (x : MetricOrderComplex P) : cutoffBlend 1 x = x := by
  ext v
  simp

@[simp]
theorem cutoffBlend_vertex (t : I) (v : P) : cutoffBlend t (vertex v) = vertex v := by
  ext w
  simp only [cutoffBlend_weights, cutoff_vertex]
  ring

/-- The affine interpolation is controlled in the space variable by the two endpoint maps. -/
theorem cutoffBlend_dist_space (t : I) (x y : MetricOrderComplex P) :
    dist (cutoffBlend t x) (cutoffBlend t y) ≤
      (1 - (t : ℝ)) * dist x.cutoff y.cutoff + (t : ℝ) * dist x y := by
  let s := x.weights.support ∪ y.weights.support
  have hx : x.weights.support ⊆ s := Finset.subset_union_left
  have hy : y.weights.support ⊆ s := Finset.subset_union_right
  have hcx := x.cutoff_support_subset.trans hx
  have hcy := y.cutoff_support_subset.trans hy
  change coordinateDistance _ _ ≤ (1 - (t : ℝ)) * coordinateDistance _ _ +
    (t : ℝ) * coordinateDistance _ _
  rw [coordinateDistance_eq_sum _ _ s ((cutoffBlend_support_subset t x).trans hx)
      ((cutoffBlend_support_subset t y).trans hy),
    coordinateDistance_eq_sum _ _ s hcx hcy, coordinateDistance_eq_sum _ _ s hx hy,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  simp only [cutoffBlend_weights, Real.dist_eq]
  rw [show (1 - (t : ℝ)) * x.cutoff.weights v + (t : ℝ) * x.weights v -
      ((1 - (t : ℝ)) * y.cutoff.weights v + (t : ℝ) * y.weights v) =
      (1 - (t : ℝ)) * (x.cutoff.weights v - y.cutoff.weights v) +
      (t : ℝ) * (x.weights v - y.weights v) by ring]
  exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul,
    abs_of_nonneg (sub_nonneg.mpr t.2.2), abs_of_nonneg t.2.1])

/-- Every interpolation path has a uniform time-Lipschitz bound of two. -/
theorem cutoffBlend_dist_time (t s : I) (x : MetricOrderComplex P) :
    dist (cutoffBlend t x) (cutoffBlend s x) ≤ 2 * dist (t : ℝ) (s : ℝ) := by
  change coordinateDistance _ _ ≤ _
  rw [coordinateDistance_eq_sum _ _ x.weights.support
    (cutoffBlend_support_subset t x) (cutoffBlend_support_subset s x)]
  have hsum : ∑ v ∈ x.weights.support, x.cutoff.weights v = 1 := by
    rw [← Finsupp.sum_of_support_subset _ x.cutoff_support_subset (fun _ a ↦ a) (by simp)]
    exact x.cutoff.weights_total
  calc
    _ ≤ ∑ v ∈ x.weights.support,
        dist (t : ℝ) (s : ℝ) * (x.cutoff.weights v + x.weights v) := by
      apply Finset.sum_le_sum
      intro v _
      simp only [cutoffBlend_weights, Real.dist_eq]
      rw [show (1 - (t : ℝ)) * x.cutoff.weights v + (t : ℝ) * x.weights v -
          ((1 - (s : ℝ)) * x.cutoff.weights v + (s : ℝ) * x.weights v) =
          ((s : ℝ) - (t : ℝ)) * x.cutoff.weights v +
          ((t : ℝ) - (s : ℝ)) * x.weights v by ring]
      calc
        _ ≤ |((s : ℝ) - (t : ℝ)) * x.cutoff.weights v| +
            |((t : ℝ) - (s : ℝ)) * x.weights v| := abs_add_le _ _
        _ = _ := by
          rw [abs_mul, abs_mul, abs_of_nonneg (x.cutoff.weights_nonneg v),
            abs_of_nonneg (x.weights_nonneg v), abs_sub_comm (s : ℝ) (t : ℝ)]
          ring
    _ = 2 * dist (t : ℝ) (s : ℝ) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hsum]
      change dist (t : ℝ) (s : ℝ) * (1 + x.weights.sum (fun _ a ↦ a)) = _
      rw [weights_total]
      ring

/-- Joint continuity follows from L1 estimates, rather than coordinatewise continuity alone. -/
@[fun_prop]
theorem continuous_cutoffBlend :
    Continuous (fun z : I × MetricOrderComplex P ↦ cutoffBlend z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hc : Continuous (fun w : I × MetricOrderComplex P ↦
      dist w.2.cutoff z.2.cutoff + dist w.2 z.2 +
        2 * dist (w.1 : ℝ) (z.1 : ℝ)) := by fun_prop
  have he : ∀ᶠ w in 𝓝 z, dist w.2.cutoff z.2.cutoff + dist w.2 z.2 +
      2 * dist (w.1 : ℝ) (z.1 : ℝ) < ε :=
    hc.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
  filter_upwards [he] with w hw
  have ht := cutoffBlend_dist_time w.1 z.1 z.2
  have hs := cutoffBlend_dist_space w.1 w.2 z.2
  have hc' : (1 - (w.1 : ℝ)) * dist w.2.cutoff z.2.cutoff ≤
      dist w.2.cutoff z.2.cutoff := mul_le_of_le_one_left dist_nonneg (by linarith [w.1.2.1])
  have hx' : (w.1 : ℝ) * dist w.2 z.2 ≤ dist w.2 z.2 :=
    mul_le_of_le_one_left dist_nonneg w.1.2.2
  have htri := dist_triangle (cutoffBlend w.1 w.2) (cutoffBlend w.1 z.2)
    (cutoffBlend z.1 z.2)
  linarith

/-- The actual vertex-fixed homotopy from the cutoff map to the identity. -/
def cutoffHomotopy : (cutoffMap (P := P)).Homotopy (ContinuousMap.id (MetricOrderComplex P)) where
  toFun z := cutoffBlend z.1 z.2
  continuous_toFun := continuous_cutoffBlend
  map_zero_left := cutoffBlend_zero
  map_one_left := cutoffBlend_one

@[simp]
theorem cutoffHomotopy_vertex (t : I) (v : P) : cutoffHomotopy (t, vertex v) = vertex v :=
  cutoffBlend_vertex t v

end Topology.MetricOrderComplex
