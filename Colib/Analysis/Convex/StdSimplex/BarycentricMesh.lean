/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Analysis.Convex.StdSimplex.BarycentricSubdivision
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.MetricSpace.Basic
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

namespace Convexity.StdSimplex.BarycentricSubdivision

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The coordinate L1 distance on the standard simplex. -/
def l1Dist (x y : StdSimplex ℝ I) : ℝ := ∑ i, |x.weights i - y.weights i|

theorem l1Dist_nonneg (x y : StdSimplex ℝ I) : 0 ≤ l1Dist x y :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Every real standard simplex has coordinate L1 diameter at most two. -/
theorem l1Dist_le_two (x y : StdSimplex ℝ I) : l1Dist x y ≤ 2 := by
  calc
    l1Dist x y ≤ ∑ i, (x.weights i + y.weights i) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_of_nonneg (x.weights_nonneg i), abs_of_nonneg (y.weights_nonneg i)]
        using abs_sub (x.weights i) (y.weights i)
    _ = 2 := by simp [Finset.sum_add_distrib]; norm_num

/-- Removing the same nonnegative mass at one vertex makes an affine simplex
contract L1 distances by the remaining total mass. -/
theorem l1Dist_affineSimplex_le (v : I → StdSimplex ℝ J) (j₀ : J)
    (c : ℝ) (hc : ∀ i, c ≤ (v i).weights j₀) (x y : StdSimplex ℝ I) :
    l1Dist (affineSimplex v x) (affineSimplex v y) ≤ (1 - c) * l1Dist x y := by
  classical
  let r (i : I) (j : J) := (v i).weights j - if j = j₀ then c else 0
  have hr (i : I) (j : J) : 0 ≤ r i j := by
    dsimp [r]
    split_ifs with h
    · subst j
      exact sub_nonneg.mpr (hc i)
    · simp
  have htotal (i : I) : ∑ j, r i j = 1 - c := by
    simp [r, Finset.sum_sub_distrib]
  have hcoord (j : J) :
      (affineSimplex v x).weights j - (affineSimplex v y).weights j =
        ∑ i, (x.weights i - y.weights i) * r i j := by
    rw [affineSimplex_weights, affineSimplex_weights]
    simp only [r, mul_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul]
    simp
  calc
    l1Dist (affineSimplex v x) (affineSimplex v y) =
        ∑ j, |∑ i, (x.weights i - y.weights i) * r i j| := by
      simp only [l1Dist, hcoord]
    _ ≤ ∑ j, ∑ i, |x.weights i - y.weights i| * r i j := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [abs_mul, abs_of_nonneg (hr _ _)] using
        Finset.abs_sum_le_sum_abs (s := Finset.univ)
          (fun i ↦ (x.weights i - y.weights i) * r i j)
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
abbrev coordinateMetric (I : Type*) [Fintype I] : MetricSpace (StdSimplex ℝ I) :=
  Topology.IsEmbedding.comapMetricSpace
    (fun x : StdSimplex ℝ I ↦ (x.weights : I → ℝ))
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ I)

/-- The coordinate metric is bounded above by the coordinate L1 distance. -/
theorem coordinateDist_le_l1Dist (x y : StdSimplex ℝ I) :
    let := coordinateMetric I
    dist x y ≤ l1Dist x y := by
  change dist (x.weights : I → ℝ) (y.weights : I → ℝ) ≤ l1Dist x y
  rw [dist_pi_le_iff (l1Dist_nonneg x y)]
  intro i
  rw [Real.dist_eq]
  exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (x.weights j - y.weights j))
    (Finset.mem_univ i)


end Convexity.StdSimplex.BarycentricSubdivision
