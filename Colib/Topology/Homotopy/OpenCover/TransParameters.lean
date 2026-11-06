/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.JoinParameters
public import Mathlib.Topology.Subpath

/-!
# Trans Parameters

Native constructions and proofs for the canonical completion comparison.
-/

@[expose] public section

noncomputable section
open Set
universe u
namespace FundamentalGroupoid.OpenCover

/-- The midpoint of the unit interval. -/
def halfPoint : unitInterval := ⟨1 / 2, by norm_num⟩
/-- The affine parameterization of the first half of the unit interval. -/
def leftHalf (t : unitInterval) : unitInterval := Icc.convexComb 0 halfPoint t
/-- The affine parameterization of the second half of the unit interval. -/
def rightHalf (t : unitInterval) : unitInterval := Icc.convexComb halfPoint 1 t

@[simp] theorem coe_leftHalf (t : unitInterval) : (leftHalf t : ℝ) = (t : ℝ) / 2 := by
  simp [leftHalf, halfPoint, Icc.coe_convexComb]
  ring
@[simp] theorem coe_rightHalf (t : unitInterval) : (rightHalf t : ℝ) = (1 + (t : ℝ)) / 2 := by
  simp [rightHalf, halfPoint, Icc.coe_convexComb]
  ring

theorem leftHalf_monotone : Monotone leftHalf := by
  intro a b hab
  change (leftHalf a : ℝ) ≤ (leftHalf b : ℝ)
  simp only [coe_leftHalf]
  exact div_le_div_of_nonneg_right hab (by norm_num)
theorem rightHalf_monotone : Monotone rightHalf := by
  intro a b hab
  change (rightHalf a : ℝ) ≤ (rightHalf b : ℝ)
  simp only [coe_rightHalf]
  linarith [show (a : ℝ) ≤ (b : ℝ) from hab]

variable {X : Type u} [TopologicalSpace X]
theorem trans_leftHalf {x y z : X} (p : Path x y) (q : Path y z) (t : unitInterval) :
    (p.trans q) (leftHalf t) = p t := by
  rw [← Path.extend_apply _ (leftHalf t).property,
    Path.extend_trans_of_le_half _ _ (by rw [coe_leftHalf]; linarith [t.property.2])]
  have he : 2 * (leftHalf t : ℝ) = (t : ℝ) := by rw [coe_leftHalf]; ring
  rw [he, Path.extend_apply]

theorem trans_rightHalf {x y z : X} (p : Path x y) (q : Path y z) (t : unitInterval) :
    (p.trans q) (rightHalf t) = q t := by
  rw [← Path.extend_apply _ (rightHalf t).property,
    Path.extend_trans_of_half_le _ _ (by rw [coe_rightHalf]; linarith [t.property.1])]
  have he : 2 * (rightHalf t : ℝ) - 1 = (t : ℝ) := by rw [coe_rightHalf]; ring
  rw [he, Path.extend_apply]

theorem leftHalf_convexComb (a b t : unitInterval) :
    Icc.convexComb (leftHalf a) (leftHalf b) t = leftHalf (Icc.convexComb a b t) := by
  apply Subtype.ext
  simp only [Icc.coe_convexComb, coe_leftHalf]
  ring

theorem rightHalf_convexComb (a b t : unitInterval) :
    Icc.convexComb (rightHalf a) (rightHalf b) t = rightHalf (Icc.convexComb a b t) := by
  apply Subtype.ext
  simp only [Icc.coe_convexComb, coe_rightHalf]
  ring

end FundamentalGroupoid.OpenCover
