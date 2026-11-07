/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The compact square quotient with a three-sided upper boundary

The two vertical sides collapse to the lower corners. The upper edge traverses the left, upper,
and right target edges with quarter, quarter, and half durations, respectively.
-/
/-! Implementation source: `Quillen/Topology/Homotopy/ThreeSideSquare.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, coordinates,
whole boundary traces and universe parameters are retained with native owners.
-/
@[expose] public section
noncomputable section
open scoped unitInterval Topology
namespace Topology.ThreeSideSquare

/-- The vertical coordinate of the three-sided boundary traversal. -/
def height (s : ℝ) : ℝ := min (4 * s) (min 1 (2 - 2 * s))
/-- The horizontal coordinate of the three-sided boundary traversal. -/
def position (s : ℝ) : ℝ := max 0 (min 1 (4 * s - 1))

private lemma height_nonneg (s : unitInterval) : 0 ≤ height s := by
  unfold height
  apply le_min
  · exact mul_nonneg (by norm_num) s.2.1
  · apply le_min zero_le_one
    nlinarith [s.2.2]

private lemma height_le_one (s : unitInterval) : height s ≤ 1 :=
  (min_le_right _ _).trans (min_le_left _ _)

private lemma position_nonneg (s : unitInterval) : 0 ≤ position s := le_max_left _ _
private lemma position_le_one (s : unitInterval) : position s ≤ 1 := by
  exact max_le zero_le_one (min_le_left _ _)

/-- The explicit compact parameter-square collapse. -/
def collapse (z : unitInterval × unitInterval) : unitInterval × unitInterval :=
  (⟨z.1 * height z.2, by
    constructor
    · exact mul_nonneg z.1.2.1 (height_nonneg z.2)
    · calc
        (z.1 : ℝ) * height z.2 ≤ 1 * height z.2 :=
          mul_le_mul_of_nonneg_right z.1.2.2 (height_nonneg z.2)
        _ ≤ 1 := by simpa using height_le_one z.2⟩,
   ⟨(1 - z.1) * z.2 + z.1 * position z.2, by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr z.1.2.2) z.2.2.1)
        (mul_nonneg z.1.2.1 (position_nonneg z.2))
    · calc
        _ ≤ (1 - (z.1 : ℝ)) * 1 + z.1 * 1 := add_le_add
          (mul_le_mul_of_nonneg_left z.2.2.2 (sub_nonneg.mpr z.1.2.2))
          (mul_le_mul_of_nonneg_left (position_le_one z.2) z.1.2.1)
        _ = 1 := by ring⟩)

/-- The collapse is continuous on the whole compact parameter square. -/
lemma continuous_collapse : Continuous collapse := by
  unfold collapse height position
  fun_prop

private lemma height_left {s : ℝ} (hs : s ≤ 1 / 4) : height s = 4 * s := by
  unfold height
  apply min_eq_left
  apply le_min <;> linarith

private lemma position_left {s : ℝ} (hs : s ≤ 1 / 4) : position s = 0 := by
  unfold position
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

private lemma height_middle {s : ℝ} (h₀ : 1 / 4 ≤ s) (h₁ : s ≤ 1 / 2) : height s = 1 := by
  unfold height
  rw [min_eq_left (by linarith : (1 : ℝ) ≤ 2 - 2 * s)]
  exact min_eq_right (by linarith)

private lemma position_middle {s : ℝ} (h₀ : 1 / 4 ≤ s) (h₁ : s ≤ 1 / 2) :
    position s = 4 * s - 1 := by
  unfold position
  rw [min_eq_right (by linarith : 4 * s - 1 ≤ (1 : ℝ))]
  exact max_eq_right (by linarith)

private lemma height_right {s : ℝ} (hs : 1 / 2 ≤ s) : height s = 2 - 2 * s := by
  unfold height
  rw [min_eq_right (by linarith : 2 - 2 * s ≤ (1 : ℝ))]
  exact min_eq_right (by linarith)

private lemma position_right {s : ℝ} (hs : 1 / 2 ≤ s) : position s = 1 := by
  unfold position
  rw [min_eq_left (by linarith : (1 : ℝ) ≤ 4 * s - 1)]
  norm_num

/-- The lower edge is unchanged by the parameter collapse. -/
@[simp] lemma collapse_zero (s : unitInterval) : collapse (0, s) = (0, s) := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [collapse]

/-- The left source edge collapses to the lower left corner. -/
@[simp] lemma collapse_left (r : unitInterval) : collapse (r, 0) = (0, 0) := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [collapse, height, position]

/-- The right source edge collapses to the lower right corner. -/
@[simp] lemma collapse_right (r : unitInterval) : collapse (r, 1) = (0, 1) := by
  apply Prod.ext <;> apply Subtype.ext <;> norm_num [collapse, height, position]

private lemma fiber_second {a b : unitInterval × unitInterval}
    (h : collapse a = collapse b) : a.2 = b.2 := by
  have hx := congrArg (fun z : unitInterval × unitInterval => (z.1 : ℝ)) h
  have hy := congrArg (fun z : unitInterval × unitInterval => (z.2 : ℝ)) h
  change (a.1 : ℝ) * height a.2 = (b.1 : ℝ) * height b.2 at hx
  change (1 - (a.1 : ℝ)) * a.2 + a.1 * position a.2 =
    (1 - (b.1 : ℝ)) * b.2 + b.1 * position b.2 at hy
  apply Subtype.ext
  have ha := a.1.2.1
  have hb := b.1.2.1
  obtain ⟨ha₂, ha₃⟩ := a.2.2
  obtain ⟨hb₂, hb₃⟩ := b.2.2
  rcases le_total (a.2 : ℝ) (1/4) with ha₀ | ha₀
  · simp only [height_left ha₀, position_left ha₀] at hx hy
    rcases le_total (b.2 : ℝ) (1/4) with hb₀ | hb₀
    · simp only [height_left hb₀, position_left hb₀] at hx hy
      nlinarith
    · rcases le_total (b.2 : ℝ) (1/2) with hb₁ | hb₁
      · simp only [height_middle hb₀ hb₁, position_middle hb₀ hb₁] at hx hy
        nlinarith
      · simp only [height_right hb₁, position_right hb₁] at hx hy
        nlinarith
  · rcases le_total (a.2 : ℝ) (1/2) with ha₁ | ha₁
    · simp only [height_middle ha₀ ha₁, position_middle ha₀ ha₁] at hx hy
      rcases le_total (b.2 : ℝ) (1/4) with hb₀ | hb₀
      · simp only [height_left hb₀, position_left hb₀] at hx hy
        nlinarith
      · rcases le_total (b.2 : ℝ) (1/2) with hb₁ | hb₁
        · simp only [height_middle hb₀ hb₁, position_middle hb₀ hb₁] at hx hy
          nlinarith
        · simp only [height_right hb₁, position_right hb₁] at hx hy
          nlinarith
    · simp only [height_right ha₁, position_right ha₁] at hx hy
      rcases le_total (b.2 : ℝ) (1/4) with hb₀ | hb₀
      · simp only [height_left hb₀, position_left hb₀] at hx hy
        nlinarith
      · rcases le_total (b.2 : ℝ) (1/2) with hb₁ | hb₁
        · simp only [height_middle hb₀ hb₁, position_middle hb₀ hb₁] at hx hy
          nlinarith
        · simp only [height_right hb₁, position_right hb₁] at hx hy
          nlinarith

/-- The only nontrivial fibers are precisely the two collapsed endpoint edges. -/
lemma collapse_fiber {a b : unitInterval × unitInterval} (h : collapse a = collapse b) :
    a = b ∨ (a.2 = 0 ∧ b.2 = 0) ∨ (a.2 = 1 ∧ b.2 = 1) := by
  have hs := fiber_second h
  by_cases h₀ : a.2 = 0
  · exact Or.inr (Or.inl ⟨h₀, hs.symm.trans h₀⟩)
  by_cases h₁ : a.2 = 1
  · exact Or.inr (Or.inr ⟨h₁, hs.symm.trans h₁⟩)
  left
  apply Prod.ext _ hs
  apply Subtype.ext
  have hp : 0 < height a.2 := by
    unfold height
    apply lt_min
    · have : (0 : ℝ) < a.2 := lt_of_le_of_ne a.2.2.1
        (by intro h; apply h₀; apply Subtype.ext; exact h.symm)
      positivity
    · apply lt_min zero_lt_one
      have : (a.2 : ℝ) < 1 := lt_of_le_of_ne a.2.2.2
        (by intro h; apply h₁; apply Subtype.ext; exact h)
      linarith
  have hx := congrArg (fun z : unitInterval × unitInterval => (z.1 : ℝ)) h
  change (a.1 : ℝ) * height a.2 = (b.1 : ℝ) * height b.2 at hx
  rw [← hs] at hx
  nlinarith

private lemma collapse_eq_iff (u v r s : unitInterval) :
    collapse (u, v) = (r, s) ↔
      (u : ℝ) * height v = r ∧ (1 - (u : ℝ)) * v + u * position v = s := by
  simp only [collapse, Prod.mk.injEq, Subtype.ext_iff]

/-- Every point of the target square has an actual preimage under the collapse. -/
lemma collapse_surjective : Function.Surjective collapse := by
  rintro ⟨r, s⟩
  by_cases hr : r = 0
  · subst r
    exact ⟨(0, s), collapse_zero s⟩
  have hrp : (0 : ℝ) < r := lt_of_le_of_ne r.2.1
    (by intro h; apply hr; apply Subtype.ext; exact h.symm)
  obtain ⟨hr₀, hr₁⟩ := r.2
  obtain ⟨hs₀, hs₁⟩ := s.2
  by_cases hsL : (s : ℝ) ≤ (1 - r) / 4
  · let v : unitInterval := ⟨s + r / 4, by constructor <;> linarith⟩
    have hv : (v : ℝ) = s + r / 4 := rfl
    have hvL : (v : ℝ) ≤ 1 / 4 := by linarith
    have hp : (0 : ℝ) < 4 * v := by rw [hv]; linarith
    let u : unitInterval := ⟨r / (4 * v), by
      constructor
      · exact div_nonneg hr₀ hp.le
      · apply (div_le_one hp).mpr
        rw [hv]
        linarith⟩
    have hx : (u : ℝ) * (4 * v) = r := div_mul_cancel₀ _ hp.ne'
    refine ⟨(u, v), (collapse_eq_iff u v r s).mpr ?_⟩
    rw [height_left hvL, position_left hvL]
    exact ⟨hx, by nlinarith⟩
  by_cases hsR : (1 + (r : ℝ)) / 2 ≤ s
  · let v : unitInterval := ⟨s - r / 2, by constructor <;> linarith⟩
    have hv : (v : ℝ) = s - r / 2 := rfl
    have hvR : (1 : ℝ) / 2 ≤ v := by linarith
    have hp : (0 : ℝ) < 2 - 2 * v := by rw [hv]; linarith
    let u : unitInterval := ⟨r / (2 - 2 * v), by
      constructor
      · exact div_nonneg hr₀ hp.le
      · apply (div_le_one hp).mpr
        rw [hv]
        linarith⟩
    have hx : (u : ℝ) * (2 - 2 * v) = r := div_mul_cancel₀ _ hp.ne'
    refine ⟨(u, v), (collapse_eq_iff u v r s).mpr ?_⟩
    rw [height_right hvR, position_right hvR]
    exact ⟨hx, by nlinarith⟩
  have hp : (0 : ℝ) < 1 + 3 * r := by linarith
  have hvL : (1 : ℝ) / 4 ≤ (s + r) / (1 + 3 * r) := by
    apply (le_div_iff₀ hp).mpr
    linarith
  have hvR : ((s : ℝ) + r) / (1 + 3 * r) ≤ 1 / 2 := by
    apply (div_le_iff₀ hp).mpr
    linarith
  let v : unitInterval := ⟨(s + r) / (1 + 3 * r), by constructor <;> linarith⟩
  have hv : (v : ℝ) * (1 + 3 * r) = s + r := div_mul_cancel₀ _ hp.ne'
  refine ⟨(r, v), (collapse_eq_iff r v r s).mpr ?_⟩
  rw [height_middle hvL hvR, position_middle hvL hvR]
  constructor
  · simp
  · nlinarith

/-- The collapse remains a quotient map after product with any topological space. -/
lemma isQuotientMap_collapse_prod (X : Type*) [TopologicalSpace X] :
    Topology.IsQuotientMap (Prod.map collapse id : (unitInterval × unitInterval) × X → _) :=
  (continuous_collapse.isProperMap.prodMap isProperMap_id).isClosedMap.isQuotientMap
    (continuous_collapse.prodMap continuous_id)
    (collapse_surjective.prodMap Function.surjective_id)

/-- The original upper-edge time corresponding to the target left boundary. -/
def leftTime (r : unitInterval) : unitInterval :=
  ⟨r / 4, by constructor <;> linarith [r.2.1, r.2.2]⟩

/-- The original upper-edge time corresponding to the target top boundary. -/
def topTime (s : unitInterval) : unitInterval :=
  ⟨(s + 1) / 4, by constructor <;> linarith [s.2.1, s.2.2]⟩

/-- The original upper-edge time corresponding to the target right boundary. -/
def rightTime (r : unitInterval) : unitInterval :=
  ⟨1 - r / 2, by constructor <;> linarith [r.2.1, r.2.2]⟩

/-- The first quarter of the upper edge is exactly the target left edge. -/
lemma collapse_leftTime (r : unitInterval) : collapse (1, leftTime r) = (r, 0) := by
  apply (collapse_eq_iff _ _ _ _).mpr
  have h : (leftTime r : ℝ) ≤ 1 / 4 := by dsimp [leftTime]; linarith [r.2.2]
  rw [height_left h, position_left h]
  constructor <;> dsimp [leftTime] <;> ring

/-- The next quarter of the upper edge is exactly the target top edge. -/
lemma collapse_topTime (s : unitInterval) : collapse (1, topTime s) = (1, s) := by
  apply (collapse_eq_iff _ _ _ _).mpr
  have h₀ : (1 : ℝ) / 4 ≤ topTime s := by dsimp [topTime]; linarith [s.2.1]
  have h₁ : (topTime s : ℝ) ≤ 1 / 2 := by dsimp [topTime]; linarith [s.2.2]
  rw [height_middle h₀ h₁, position_middle h₀ h₁]
  constructor <;> dsimp [topTime] <;> ring

/-- The final half of the upper edge is exactly the reversed target right edge. -/
lemma collapse_rightTime (r : unitInterval) : collapse (1, rightTime r) = (r, 1) := by
  apply (collapse_eq_iff _ _ _ _).mpr
  have h : (1 : ℝ) / 2 ≤ rightTime r := by dsimp [rightTime]; linarith [r.2.2]
  rw [height_right h, position_right h]
  constructor <;> dsimp [rightTime] <;> ring

end Topology.ThreeSideSquare
