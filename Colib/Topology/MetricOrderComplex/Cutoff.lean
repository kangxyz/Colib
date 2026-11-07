/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.Coordinates
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.ContinuousMap.Basic

import Mathlib.Tactic.Linarith

/-!
# A locally finitely supported cutoff of metric order complexes

The cutoff removes half the largest coordinate from every coordinate, takes
the positive part, and normalizes the remaining mass. It preserves chain
supports and fixes every vertex. On the L1 ball of radius one quarter of the
largest weight at `x`, every cutoff support lies in the one finite support of
`x`. This is the finite-chart input for a future map to the weak realization.

All positivity and support assertions are proved for the displayed formula;
no local-finiteness hypothesis is placed on the poset.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/Cutoff.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual finitely supported
coordinate model, L1 topology and universe parameters are retained. -/
@[expose] public section
noncomputable section

open scoped Topology

universe u

namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- The unnormalized half-maximum cutoff. -/
def cutoffWeights (x : MetricOrderComplex P) : P →₀ ℝ :=
  x.weights.mapRange (fun a ↦ max 0 (a - x.maximum / 2))
    (by rw [zero_sub, max_eq_left]; linarith [x.maximum_pos])

@[simp]
theorem cutoffWeights_apply (x : MetricOrderComplex P) (v : P) :
    x.cutoffWeights v = max 0 (x.weights v - x.maximum / 2) := rfl

theorem cutoffWeights_nonneg (x : MetricOrderComplex P) (v : P) :
    0 ≤ x.cutoffWeights v := le_max_left _ _

theorem cutoffWeights_support_subset (x : MetricOrderComplex P) :
    x.cutoffWeights.support ⊆ x.weights.support := Finsupp.support_mapRange

/-- The positive mass left by the cutoff. -/
def cutoffMass (x : MetricOrderComplex P) : ℝ :=
  x.cutoffWeights.sum (fun _ a ↦ a)

theorem cutoffMass_pos (x : MetricOrderComplex P) : 0 < x.cutoffMass := by
  obtain ⟨v, _, hv⟩ := x.exists_maximum
  have hv' : 0 < x.cutoffWeights v := by
    rw [cutoffWeights_apply, ← hv]
    exact lt_max_of_lt_right (by linarith [x.maximum_pos])
  apply Finsupp.sum_pos' (fun w _ ↦ x.cutoffWeights_nonneg w)
  exact ⟨v, Finsupp.mem_support_iff.mpr (ne_of_gt hv'), hv'⟩

/-- The normalized cutoff is again a point of the same metric order complex. -/
def cutoff (x : MetricOrderComplex P) : MetricOrderComplex P := by
  refine ⟨⟨x.cutoffMass⁻¹ • x.cutoffWeights, ?_, ?_⟩, ?_⟩
  · intro v
    exact mul_nonneg (inv_nonneg.mpr x.cutoffMass_pos.le) (x.cutoffWeights_nonneg v)
  · rw [Finsupp.sum_smul_index (fun _ ↦ rfl)]
    change (∑ v ∈ x.cutoffWeights.support, x.cutoffMass⁻¹ * x.cutoffWeights v) = 1
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt x.cutoffMass_pos)
  · exact x.support_chain.mono (fun v hv ↦
      x.cutoffWeights_support_subset (Finsupp.support_smul hv))

@[simp]
theorem cutoff_weights_apply (x : MetricOrderComplex P) (v : P) :
    x.cutoff.weights v = max 0 (x.weights v - x.maximum / 2) / x.cutoffMass := by
  change x.cutoffMass⁻¹ * x.cutoffWeights v = _
  simp only [cutoffWeights_apply, div_eq_mul_inv, mul_comm]

theorem cutoff_support_subset (x : MetricOrderComplex P) :
    x.cutoff.weights.support ⊆ x.weights.support :=
  Finset.Subset.trans Finsupp.support_smul x.cutoffWeights_support_subset

/-- A vertex remains a vertex, so this operation retains every possible basepoint. -/
@[simp]
theorem cutoff_vertex (v : P) : (vertex v).cutoff = vertex v := by
  classical
  have hw : (vertex v).cutoffWeights = Finsupp.single v (1 / 2 : ℝ) := by
    ext w
    by_cases h : v = w
    · subst w
      norm_num [cutoffWeights_apply]
    · simp [cutoffWeights_apply, Ne.symm h]
  have hm : (vertex v).cutoffMass = 1 / 2 := by simp [cutoffMass, hw]
  apply ext
  intro w
  change (vertex v).cutoffMass⁻¹ * (vertex v).cutoffWeights w = _
  rw [hm, hw]
  by_cases h : v = w
  · subst w
    norm_num
  · simp [Ne.symm h]

/-- On a quantitative neighborhood of `x`, cutoff weights vanish outside `support x`. -/
theorem cutoffWeights_eq_zero_of_dist_lt (x y : MetricOrderComplex P)
    (hxy : dist y x < x.maximum / 4) {v : P} (hv : v ∉ x.weights.support) :
    y.cutoffWeights v = 0 := by
  have hxv : x.weights v = 0 := Finsupp.notMem_support_iff.mp hv
  have hcoord := coordinate_dist_le y x v
  rw [hxv, Real.dist_eq, sub_zero, abs_of_nonneg (y.weights_nonneg v)] at hcoord
  have hmax := maximum_sub_le_dist x y
  rw [dist_comm x y] at hmax
  rw [cutoffWeights_apply, max_eq_left]
  linarith [x.maximum_pos]

/-- One fixed finite chain contains every cutoff support on this L1 ball. -/
theorem cutoffWeights_support_subset_of_dist_lt (x y : MetricOrderComplex P)
    (hxy : dist y x < x.maximum / 4) :
    y.cutoffWeights.support ⊆ x.weights.support := by
  intro v hv
  by_contra hxv
  exact (Finsupp.mem_support_iff.mp hv) (cutoffWeights_eq_zero_of_dist_lt x y hxy hxv)

theorem cutoff_support_subset_of_dist_lt (x y : MetricOrderComplex P)
    (hxy : dist y x < x.maximum / 4) :
    y.cutoff.weights.support ⊆ x.weights.support :=
  Finset.Subset.trans Finsupp.support_smul
    (cutoffWeights_support_subset_of_dist_lt x y hxy)

/-- In particular, the cutoff has locally finite coordinate support. -/
theorem eventually_cutoff_support_subset (x : MetricOrderComplex P) :
    ∀ᶠ y in 𝓝 x, y.cutoff.weights.support ⊆ x.weights.support := by
  filter_upwards [Metric.ball_mem_nhds x (by linarith [x.maximum_pos] : 0 < x.maximum / 4)]
    with y hy
  exact cutoff_support_subset_of_dist_lt x y hy

@[fun_prop]
theorem continuous_cutoffWeights_coordinate (v : P) :
    Continuous (fun x : MetricOrderComplex P ↦ x.cutoffWeights v) := by
  simp only [cutoffWeights_apply]
  exact continuous_const.max ((continuous_coordinate v).sub (continuous_maximum.div_const 2))

/-- The varying finite sum is continuous because a fixed support suffices locally. -/
@[fun_prop]
theorem continuous_cutoffMass : Continuous (cutoffMass : MetricOrderComplex P → ℝ) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc : Continuous (fun y : MetricOrderComplex P ↦
      ∑ v ∈ x.weights.support, y.cutoffWeights v) :=
    continuous_finsetSum _ (fun v _ ↦ continuous_cutoffWeights_coordinate v)
  apply hc.continuousAt.congr
  filter_upwards [Metric.ball_mem_nhds x (by linarith [x.maximum_pos] : 0 < x.maximum / 4)]
    with y hy
  exact (Finsupp.sum_of_support_subset y.cutoffWeights
    (cutoffWeights_support_subset_of_dist_lt x y hy) (fun _ a ↦ a) (by simp)).symm

@[fun_prop]
theorem continuous_cutoff_coordinate (v : P) :
    Continuous (fun x : MetricOrderComplex P ↦ x.cutoff.weights v) := by
  simp only [cutoff_weights_apply]
  exact (continuous_cutoffWeights_coordinate v).div continuous_cutoffMass
    (fun x ↦ ne_of_gt x.cutoffMass_pos)

/-- Coordinate continuity and the proved local support bound give L1 continuity. -/
@[fun_prop]
theorem continuous_cutoff : Continuous (cutoff : MetricOrderComplex P → MetricOrderComplex P) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hs : Filter.Tendsto
      (fun y : MetricOrderComplex P ↦ ∑ v ∈ x.weights.support,
        dist (y.cutoff.weights v) (x.cutoff.weights v)) (𝓝 x) (𝓝 (0 : ℝ)) := by
    simpa only [dist_self, Finset.sum_const_zero] using
      tendsto_finsetSum x.weights.support (fun v _ ↦
        (continuous_cutoff_coordinate v).continuousAt.dist
          (continuousAt_const : ContinuousAt
            (fun _ : MetricOrderComplex P ↦ x.cutoff.weights v) x))
  filter_upwards [eventually_cutoff_support_subset x,
    (Metric.tendsto_nhds.mp hs) ε hε] with y hy hdist
  change coordinateDistance y.cutoff x.cutoff < ε
  rw [coordinateDistance_eq_sum _ _ x.weights.support hy (cutoff_support_subset x)]
  exact lt_of_le_of_lt (le_abs_self _) (by simpa only [Real.dist_eq, sub_zero] using hdist)

/-- The explicit continuous cutoff self-map, fixing every vertex. -/
def cutoffMap : C(MetricOrderComplex P, MetricOrderComplex P) :=
  ⟨cutoff, continuous_cutoff⟩

end Topology.MetricOrderComplex
