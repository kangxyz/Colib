/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Analysis.Convex.StdSimplex.BarycentricSubdivision
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
Adapted from `Quillen/Topology/LocalCoefficients/BarycentricMesh.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Quantitative mesh estimates for actual barycentric simplex maps

The coordinate L1 distance contracts when the vertices of an affine simplex
share a fixed positive coordinate. These estimates concern the native point
maps; the recursive subdivision terms are certified in `BarycentricTermMesh`.
-/

@[expose] public section

noncomputable section

attribute [local instance] Classical.decEq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped BigOperators Topology

namespace stdSimplex.BarycentricSubdivision

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The coordinate L1 distance on the standard simplex. -/
def l1Dist (x y : _root_.stdSimplex ℝ I) : ℝ := ∑ i, |x i - y i|

theorem l1Dist_nonneg (x y : _root_.stdSimplex ℝ I) : 0 ≤ l1Dist x y :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Every real standard simplex has coordinate L1 diameter at most two. -/
theorem l1Dist_le_two (x y : _root_.stdSimplex ℝ I) : l1Dist x y ≤ 2 := by
  calc
    l1Dist x y ≤ ∑ i, (x i + y i) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_of_nonneg (stdSimplex.zero_le x i), abs_of_nonneg (stdSimplex.zero_le y i)]
        using abs_sub (x i) (y i)
    _ = 2 := by simp [Finset.sum_add_distrib]; norm_num

/-- Removing the same nonnegative mass at one vertex makes an affine simplex
contract L1 distances by the remaining total mass. -/
theorem l1Dist_affineSimplex_le (v : I → _root_.stdSimplex ℝ J) (j₀ : J)
    (c : ℝ) (hc : ∀ i, c ≤ (v i) j₀) (x y : _root_.stdSimplex ℝ I) :
    l1Dist (affineSimplex v x) (affineSimplex v y) ≤ (1 - c) * l1Dist x y := by
  classical
  let r (i : I) (j : J) := (v i) j - if j = j₀ then c else 0
  have hr (i : I) (j : J) : 0 ≤ r i j := by
    dsimp [r]
    split_ifs with h
    · subst j
      exact sub_nonneg.mpr (hc i)
    · simp
  have htotal (i : I) : ∑ j, r i j = 1 - c := by
    simp [r, Finset.sum_sub_distrib]
  have hcoord (j : J) :
      (affineSimplex v x) j - (affineSimplex v y) j =
        ∑ i, (x i - y i) * r i j := by
    rw [affineSimplex_weights, affineSimplex_weights]
    simp only [r, mul_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul]
    simp
  calc
    l1Dist (affineSimplex v x) (affineSimplex v y) =
        ∑ j, |∑ i, (x i - y i) * r i j| := by
      simp only [l1Dist, hcoord]
    _ ≤ ∑ j, ∑ i, |x i - y i| * r i j := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [abs_mul, abs_of_nonneg (hr _ _)] using
        Finset.abs_sum_le_sum_abs (s := Finset.univ)
          (fun i ↦ (x i - y i) * r i j)
    _ = (1 - c) * l1Dist x y := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, htotal, ← Finset.sum_mul, l1Dist]
      exact mul_comm _ _

/-- The standard barycentric contraction factor, equal to `n / (n + 1)`. -/
def contractionFactor (n : ℕ) : ℝ := 1 - ((n + 1 : ℕ) : ℝ)⁻¹

theorem contractionFactor_nonneg (n : ℕ) : 0 ≤ contractionFactor n := by
  rw [contractionFactor, sub_nonneg]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

theorem contractionFactor_lt_one (n : ℕ) : contractionFactor n < 1 := by
  rw [contractionFactor]
  have h : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  linarith

/-- The ordinary coordinate sup metric, with the original simplex topology. -/
abbrev coordinateMetric (I : Type*) [Fintype I] : MetricSpace (_root_.stdSimplex ℝ I) :=
  inferInstance

/-- The coordinate metric is bounded above by the coordinate L1 distance. -/
theorem coordinateDist_le_l1Dist (x y : _root_.stdSimplex ℝ I) :
    let := coordinateMetric I
    dist x y ≤ l1Dist x y := by
  change dist (x : I → ℝ) (y : I → ℝ) ≤ l1Dist x y
  rw [dist_pi_le_iff (l1Dist_nonneg x y)]
  intro i
  rw [Real.dist_eq]
  exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (x j - y j))
    (Finset.mem_univ i)


end stdSimplex.BarycentricSubdivision
