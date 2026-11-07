/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Boundary-fixed off-center radial expansion of finite cubes

A continuous gauge measures distance from an arbitrary interior diagonal center to the original
cube boundary. Capping its denominator below by a positive parameter gives a continuous radial
expansion, including at the center. It fixes the entire boundary pointwise, and sends the
complement of the smaller homothetic cube to that boundary. Dimension zero is included by a
zero term in the finite maximum. This is the single-cell geometric normalization used in
Puppe's cubical proof of homotopy excision, before any connectivity argument.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/Cube/RadialExpansion.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology

open scoped Topology unitInterval

namespace Cube

variable {d : ℕ}

/-- The directional gauge of one original coordinate around the chosen interior center. -/
def coordinateGauge (c x : unitInterval) : ℝ :=
  max (((c : ℝ) - x) / c) (((x : ℝ) - c) / (1 - c))

/-- The original cube's gauge includes zero, so empty coordinate sets need no special convention. -/
def radialGauge (c : unitInterval) (x : Fin d → unitInterval) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (Fin.cases 0 (fun i ↦ coordinateGauge c (x i)))

theorem radialGauge_nonneg (c : unitInterval) (x : Fin d → unitInterval) :
    0 ≤ radialGauge c x :=
  Finset.le_sup' (Fin.cases 0 (fun i ↦ coordinateGauge c (x i)))
    (Finset.mem_univ (0 : Fin (d + 1)))

theorem coordinateGauge_le_radialGauge (c : unitInterval) (x : Fin d → unitInterval)
    (i : Fin d) : coordinateGauge c (x i) ≤ radialGauge c x :=
  Finset.le_sup' (Fin.cases 0 (fun i ↦ coordinateGauge c (x i))) (Finset.mem_univ i.succ)

theorem coordinateGauge_le_one (c x : unitInterval) (hc₀ : 0 < (c : ℝ))
    (hc₁ : (c : ℝ) < 1) : coordinateGauge c x ≤ 1 := by
  apply max_le
  · apply (div_le_iff₀ hc₀).mpr
    linarith [x.property.1]
  · apply (div_le_iff₀ (sub_pos.mpr hc₁)).mpr
    linarith [x.property.2]

theorem radialGauge_le_one (c : unitInterval) (hc₀ : 0 < (c : ℝ))
    (hc₁ : (c : ℝ) < 1) (x : Fin d → unitInterval) : radialGauge c x ≤ 1 := by
  apply Finset.sup'_le
  intro i _
  cases i using Fin.cases
  · norm_num
  · exact coordinateGauge_le_one c _ hc₀ hc₁

@[fun_prop] theorem continuous_radialGauge (c : unitInterval) :
    Continuous (radialGauge (d := d) c) := by
  apply Continuous.finset_sup'_apply
  intro i _
  cases i using Fin.cases
  · exact continuous_const
  · simp only [Fin.cases_succ]
    unfold coordinateGauge
    fun_prop

/-- The capped reciprocal expansion factor is positive even at the original center. -/
def radialScale (c ε : unitInterval) (x : Fin d → unitInterval) : ℝ :=
  max (ε : ℝ) (radialGauge c x)

theorem radialScale_pos (c ε : unitInterval) (hε : 0 < (ε : ℝ))
    (x : Fin d → unitInterval) : 0 < radialScale c ε x :=
  lt_of_lt_of_le hε (le_max_left _ _)

theorem radialScale_le_one (c ε : unitInterval) (hc₀ : 0 < (c : ℝ))
    (hc₁ : (c : ℝ) < 1) (x : Fin d → unitInterval) : radialScale c ε x ≤ 1 :=
  max_le ε.property.2 (radialGauge_le_one c hc₀ hc₁ x)

/-- The expanded original coordinate, before checking that it stays in the unit interval. -/
def radialCoordinate (c ε : unitInterval) (x : Fin d → unitInterval) (i : Fin d) : ℝ :=
  (c : ℝ) + ((x i : ℝ) - c) / radialScale c ε x

theorem radialCoordinate_mem (c ε : unitInterval) (hc₀ : 0 < (c : ℝ))
    (hc₁ : (c : ℝ) < 1) (hε : 0 < (ε : ℝ)) (x : Fin d → unitInterval) (i : Fin d) :
    radialCoordinate c ε x i ∈ Set.Icc (0 : ℝ) 1 := by
  have hr := radialScale_pos c ε hε x
  have hg := (coordinateGauge_le_radialGauge c x i).trans
    (le_max_right (ε : ℝ) (radialGauge c x))
  have hl : ((c : ℝ) - x i) / c ≤ radialScale c ε x := (le_max_left _ _).trans hg
  have hu : ((x i : ℝ) - c) / (1 - c) ≤ radialScale c ε x := (le_max_right _ _).trans hg
  have hl' := (div_le_iff₀ hc₀).mp hl
  have hu' := (div_le_iff₀ (sub_pos.mpr hc₁)).mp hu
  constructor
  · have h : -(c : ℝ) ≤ ((x i : ℝ) - c) / radialScale c ε x := by
      apply (le_div_iff₀ hr).mpr
      nlinarith
    unfold radialCoordinate
    linarith
  · have h : ((x i : ℝ) - c) / radialScale c ε x ≤ 1 - c := by
      apply (div_le_iff₀ hr).mpr
      nlinarith
    unfold radialCoordinate
    linarith

/-- The actual continuous boundary-fixed radial cube expansion. -/
def radialExpansion (c ε : unitInterval) (hc₀ : 0 < (c : ℝ)) (hc₁ : (c : ℝ) < 1)
    (hε : 0 < (ε : ℝ)) : C((Fin d → unitInterval), Fin d → unitInterval) where
  toFun x i := ⟨radialCoordinate c ε x i, radialCoordinate_mem c ε hc₀ hc₁ hε x i⟩
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    unfold radialCoordinate
    apply continuous_const.add
    apply Continuous.div
    · fun_prop
    · unfold radialScale
      exact continuous_const.max (continuous_radialGauge c)
    · intro x
      exact ne_of_gt (radialScale_pos c ε hε x)

theorem radialGauge_eq_one_of_boundary (c : unitInterval) (hc₀ : 0 < (c : ℝ))
    (hc₁ : (c : ℝ) < 1) (x : Fin d → unitInterval) (hx : x ∈ _root_.Cube.boundary (Fin d)) :
    radialGauge c x = 1 := by
  apply le_antisymm (radialGauge_le_one c hc₀ hc₁ x)
  obtain ⟨i, hi | hi⟩ := hx
  · have h := (le_max_left (((c : ℝ) - x i) / c)
      (((x i : ℝ) - c) / (1 - c))).trans (coordinateGauge_le_radialGauge c x i)
    simpa [hi, ne_of_gt hc₀] using h
  · have h := (le_max_right (((c : ℝ) - x i) / c)
      (((x i : ℝ) - c) / (1 - c))).trans (coordinateGauge_le_radialGauge c x i)
    simpa [hi, ne_of_gt (sub_pos.mpr hc₁)] using h

/-- Every original boundary point is fixed pointwise. -/
theorem radialExpansion_boundary (c ε : unitInterval) (hc₀ : 0 < (c : ℝ))
    (hc₁ : (c : ℝ) < 1) (hε : 0 < (ε : ℝ))
    (x : Fin d → unitInterval) (hx : x ∈ _root_.Cube.boundary (Fin d)) :
    radialExpansion c ε hc₀ hc₁ hε x = x := by
  have hs : radialScale c ε x = 1 := by
    unfold radialScale
    rw [radialGauge_eq_one_of_boundary c hc₀ hc₁ x hx, max_eq_right ε.property.2]
  funext i
  apply Subtype.ext
  change (c : ℝ) + ((x i : ℝ) - c) / radialScale c ε x = x i
  rw [hs]
  ring

/-- Beyond the smaller homothetic cube, the expansion reaches an actual coordinate face. -/
theorem radialExpansion_mem_boundary (c ε : unitInterval) (hc₀ : 0 < (c : ℝ))
    (hc₁ : (c : ℝ) < 1) (hε : 0 < (ε : ℝ)) (x : Fin d → unitInterval)
    (hx : (ε : ℝ) ≤ radialGauge c x) :
    radialExpansion c ε hc₀ hc₁ hε x ∈ _root_.Cube.boundary (Fin d) := by
  have hs : radialScale c ε x = radialGauge c x := max_eq_right hx
  have hr := radialScale_pos c ε hε x
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (Fin.cases 0 (fun i : Fin d ↦ coordinateGauge c (x i)))
  change radialGauge c x = Fin.cases 0 (fun i ↦ coordinateGauge c (x i)) j at hj
  cases j using Fin.cases with
  | zero => simp only [Fin.cases_zero] at hj; linarith
  | succ i =>
    change radialGauge c x = coordinateGauge c (x i) at hj
    rcases le_total (((c : ℝ) - x i) / c) (((x i : ℝ) - c) / (1 - c)) with h | h
    · have he : radialScale c ε x = ((x i : ℝ) - c) / (1 - c) :=
        hs.trans (hj.trans (max_eq_right h))
      have he' := (eq_div_iff (ne_of_gt (sub_pos.mpr hc₁))).mp he
      refine ⟨i, Or.inr (Subtype.ext ?_)⟩
      change radialCoordinate c ε x i = 1
      have hdiv : ((x i : ℝ) - c) / radialScale c ε x = 1 - c := by
        apply (div_eq_iff (ne_of_gt hr)).mpr
        nlinarith
      unfold radialCoordinate
      rw [hdiv]
      ring
    · have he : radialScale c ε x = ((c : ℝ) - x i) / c :=
        hs.trans (hj.trans (max_eq_left h))
      have he' := (eq_div_iff (ne_of_gt hc₀)).mp he
      refine ⟨i, Or.inl (Subtype.ext ?_)⟩
      change radialCoordinate c ε x i = 0
      have hdiv : ((x i : ℝ) - c) / radialScale c ε x = -(c : ℝ) := by
        apply (div_eq_iff (ne_of_gt hr)).mpr
        nlinarith
      unfold radialCoordinate
      rw [hdiv]
      ring

/-- Straight interpolation gives a genuine homotopy fixed on every original boundary point. -/
def radialExpansionHomotopy (c ε : unitInterval) (hc₀ : 0 < (c : ℝ))
    (hc₁ : (c : ℝ) < 1) (hε : 0 < (ε : ℝ)) :
    (ContinuousMap.id (Fin d → unitInterval)).HomotopyRel
      (radialExpansion c ε hc₀ hc₁ hε) (_root_.Cube.boundary (Fin d)) where
  toFun z i := Set.Icc.convexComb (z.2 i) (radialExpansion c ε hc₀ hc₁ hε z.2 i) z.1
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact Set.Icc.continuous_convexComb_prod.comp
      ((continuous_apply i |>.comp continuous_snd).prodMk
        (((continuous_apply i).comp
          ((radialExpansion c ε hc₀ hc₁ hε).continuous.comp continuous_snd)).prodMk continuous_fst))
  map_zero_left x := by funext i; exact Set.Icc.convexComb_zero _ _
  map_one_left x := by funext i; exact Set.Icc.convexComb_one _ _
  prop' t x hx := by
    funext i
    change Set.Icc.convexComb (x i) (radialExpansion c ε hc₀ hc₁ hε x i) t = x i
    rw [radialExpansion_boundary c ε hc₀ hc₁ hε x hx]
    exact Set.Icc.convexComb_eq (x i) t

/-- A radial expansion cannot introduce a new coordinate in an interval containing its center. -/
theorem radialExpansion_mem_band_imp (a b c ε : unitInterval)
    (hac : (a : ℝ) < c) (hcb : (c : ℝ) < b)
    (hc₀ : 0 < (c : ℝ)) (hc₁ : (c : ℝ) < 1) (hε : 0 < (ε : ℝ))
    (x : Fin d → unitInterval) (i : Fin d)
    (hi : (a : ℝ) < radialExpansion c ε hc₀ hc₁ hε x i ∧
      (radialExpansion c ε hc₀ hc₁ hε x i : ℝ) < b) :
    (a : ℝ) < x i ∧ (x i : ℝ) < b := by
  have hr := radialScale_pos c ε hε x
  have hr₁ := radialScale_le_one c ε hc₀ hc₁ x
  have he : (radialCoordinate c ε x i - c) * radialScale c ε x = (x i : ℝ) - c := by
    unfold radialCoordinate
    rw [add_sub_cancel_left, div_mul_cancel₀ _ (ne_of_gt hr)]
  change (a : ℝ) < radialCoordinate c ε x i ∧ radialCoordinate c ε x i < b at hi
  have hl := mul_pos hr (sub_pos.mpr hi.1)
  have hu := mul_pos hr (sub_pos.mpr hi.2)
  have hl' := mul_nonneg (sub_nonneg.mpr hr₁) (le_of_lt (sub_pos.mpr hac))
  have hu' := mul_nonneg (sub_nonneg.mpr hr₁) (le_of_lt (sub_pos.mpr hcb))
  constructor <;> nlinarith

end Cube
