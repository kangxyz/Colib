/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.CommonPointContinuity
public import Mathlib.Topology.Path

import Mathlib.Tactic.Ring

/-!
# Affine segments inside one actual chain simplex

An affine segment is available only when the union of its endpoint supports is
a chain. Continuity uses the proved positive-total-one L1 criterion, including
families whose supporting simplex changes. No affine segment between arbitrary
metric-order points is introduced.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/AffineSegment.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual finitely supported
coordinate model, L1 topology and universe parameters are retained. -/
@[expose] public section
noncomputable section

open scoped Topology unitInterval

universe u v
namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- Classical equality is used only to enumerate finite supports. -/
local instance instDecidableEqAffineSegment : DecidableEq P := Classical.decEq P

/-- Affine interpolation inside the stipulated common chain simplex. -/
def affineCombination (t : I) (x y : MetricOrderComplex P)
    (h : IsChain (· ≤ ·) ((x.weights.support ∪ y.weights.support : Finset P) : Set P)) :
    MetricOrderComplex P := by
  refine ⟨⟨(1 - (t : ℝ)) • x.weights + (t : ℝ) • y.weights, ?_, ?_⟩, ?_⟩
  · intro v
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (x.weights_nonneg v))
      (mul_nonneg t.2.1 (y.weights_nonneg v))
  · rw [Finsupp.sum_add_index (by simp) (by intros; rfl),
      Finsupp.sum_smul_index (fun _ ↦ rfl), Finsupp.sum_smul_index (fun _ ↦ rfl)]
    simp only [Finsupp.sum, ← Finset.mul_sum]
    change (1 - (t : ℝ)) * x.weights.sum (fun _ a ↦ a) +
      (t : ℝ) * y.weights.sum (fun _ a ↦ a) = 1
    rw [weights_total, weights_total]
    ring
  · refine IsChain.mono ?_ h
    intro v hv
    rcases Finset.mem_union.mp (Finsupp.support_add hv) with hx | hy
    · exact Finset.mem_union_left _ (Finsupp.support_smul hx)
    · exact Finset.mem_union_right _ (Finsupp.support_smul hy)

@[simp]
theorem affineCombination_weights (t : I) (x y : MetricOrderComplex P) (h) (v : P) :
    (affineCombination t x y h).weights v =
      (1 - (t : ℝ)) * x.weights v + (t : ℝ) * y.weights v := rfl

@[simp]
theorem affineCombination_zero (x y : MetricOrderComplex P) (h) :
    affineCombination 0 x y h = x := by ext v; simp

@[simp]
theorem affineCombination_one (x y : MetricOrderComplex P) (h) :
    affineCombination 1 x y h = y := by ext v; simp

@[simp]
theorem affineCombination_self (t : I) (x : MetricOrderComplex P) (h) :
    affineCombination t x x h = x := by ext v; simp only [affineCombination_weights]; ring

/-- Positivity of a shared vertex survives the whole affine segment. -/
theorem affineCombination_coordinate_pos (t : I) (x y : MetricOrderComplex P) (h) (v : P)
    (hx : 0 < x.weights v) (hy : 0 < y.weights v) :
    0 < (affineCombination t x y h).weights v := by
  rw [affineCombination_weights]
  by_cases ht : (t : ℝ) = 0
  · simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hx
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr t.2.2) hx.le)
      (mul_pos (lt_of_le_of_ne t.2.1 (Ne.symm ht)) hy)

/-- The actual path along one chain simplex. -/
def affinePath (x y : MetricOrderComplex P)
    (h : IsChain (· ≤ ·) ((x.weights.support ∪ y.weights.support : Finset P) : Set P)) :
    Path x y where
  toFun t := affineCombination t x y h
  continuous_toFun := by
    apply continuous_of_coordinates
    intro v
    simp only [affineCombination_weights]
    fun_prop
  source' := affineCombination_zero x y h
  target' := affineCombination_one x y h

@[simp]
theorem affinePath_self (x : MetricOrderComplex P) (h) : affinePath x x h = Path.refl x := by
  apply Path.ext
  funext t
  exact affineCombination_self t x h

/-- Joint continuity of affine path families is genuine L1 continuity. -/
theorem affinePath_continuous_family {A : Type v} [TopologicalSpace A]
    (f g : C(A, MetricOrderComplex P))
    (h : ∀ a, IsChain (· ≤ ·) (((f a).weights.support ∪
      (g a).weights.support : Finset P) : Set P)) :
    Continuous (fun z : A × I ↦ affinePath (f z.1) (g z.1) (h z.1) z.2) := by
  apply continuous_of_coordinates
  intro v
  change Continuous (fun z : A × I ↦
    (1 - (z.2 : ℝ)) * (f z.1).weights v + (z.2 : ℝ) * (g z.1).weights v)
  fun_prop

end Topology.MetricOrderComplex
