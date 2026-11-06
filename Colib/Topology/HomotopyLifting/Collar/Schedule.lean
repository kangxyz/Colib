/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.TimeChange
public import Colib.Topology.HomotopyLifting.PausedHomotopy

/-!
# Scalar schedules for two-collar lifting

Explicit overlapping cutoffs select short steps in the two collar domains.
A continuously varying path scale controls each step. Stage activations
are initially one and eventually zero, so the eventual lifted maps can be
assembled by local stationarity rather than a discontinuous subdivision
count.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyLifting/Collar/Schedule.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

namespace Topology

/-- Clamp a real number to the unit interval. -/
def clampInterval (x : ℝ) : I := ⟨max 0 (min 1 x),
  le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

@[fun_prop]
theorem continuous_clampInterval : Continuous clampInterval := by unfold clampInterval; fun_prop

theorem clampInterval_eq_zero {x : ℝ} (hx : x ≤ 0) : clampInterval x = 0 := by
  apply Subtype.ext
  exact max_eq_left ((min_le_right _ _).trans hx)

theorem clampInterval_eq_one {x : ℝ} (hx : 1 ≤ x) : clampInterval x = 1 := by
  apply Subtype.ext
  simp [clampInterval, min_eq_left hx]

/-- Upper collar cutoff: full below `13/24`, zero above `5/8`. -/
def upperCollarCutoff (h : I) : I := clampInterval (12 * (5 / 8 - (h : ℝ)))

/-- Lower collar cutoff: full above `11/24`, zero below `3/8`. -/
def lowerCollarCutoff (h : I) : I := clampInterval (12 * ((h : ℝ) - 3 / 8))

@[fun_prop]
theorem continuous_upperCollarCutoff : Continuous upperCollarCutoff := by
  unfold upperCollarCutoff; fun_prop
@[fun_prop]
theorem continuous_lowerCollarCutoff : Continuous lowerCollarCutoff := by
  unfold lowerCollarCutoff; fun_prop

theorem upperCollarCutoff_zero {h : I} (hh : 5 / 8 ≤ (h : ℝ)) : upperCollarCutoff h = 0 :=
  clampInterval_eq_zero (by linarith)

theorem upperCollarCutoff_one {h : I} (hh : (h : ℝ) ≤ 13 / 24) : upperCollarCutoff h = 1 :=
  clampInterval_eq_one (by linarith)

theorem lowerCollarCutoff_zero {h : I} (hh : (h : ℝ) ≤ 3 / 8) : lowerCollarCutoff h = 0 :=
  clampInterval_eq_zero (by linarith)

theorem lowerCollarCutoff_one {h : I} (hh : 11 / 24 ≤ (h : ℝ)) : lowerCollarCutoff h = 1 :=
  clampInterval_eq_one (by linarith)

/-- Stages are fully active through time `2/δ`, and vanish by `3/δ`. -/
def collarStageActivation (δ : I) (n : ℕ) : I := clampInterval (3 - (n : ℝ) * δ)

@[fun_prop]
theorem continuous_collarStageActivation (n : ℕ) : Continuous (fun δ ↦ collarStageActivation δ
    n) := by
  unfold collarStageActivation
  fun_prop

theorem collarStageActivation_one {δ : I} {n : ℕ} (hn : (n : ℝ) * δ ≤ 2) :
    collarStageActivation δ n = 1 := clampInterval_eq_one (by linarith)

theorem collarStageActivation_zero {δ : I} {n : ℕ} (hn : 3 ≤ (n : ℝ) * δ) :
    collarStageActivation δ n = 0 := clampInterval_eq_zero (by linarith)

/-- Advance at most one scale toward the target, after the initial pause. -/
def collarAdvance (target current δ r : I) : I :=
  ⟨min (target : ℝ) ((current : ℝ) + (δ : ℝ) * (pausedTime r : ℝ)),
    le_min target.2.1 (add_nonneg current.2.1 (mul_nonneg δ.2.1 (pausedTime r).2.1)),
    (min_le_left _ _).trans target.2.2⟩

@[fun_prop]
theorem continuous_collarAdvance : Continuous (fun z : I × I × I × I ↦
    collarAdvance z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold collarAdvance
  fun_prop

theorem collarAdvance_le_target (target current δ r : I) : collarAdvance target current δ r ≤
    target := by
  change min (target : ℝ) ((current : ℝ) + (δ : ℝ) * (pausedTime r : ℝ)) ≤ (target : ℝ)
  exact min_le_left _ _

theorem collarAdvance_le_add (target current δ r : I) :
    (collarAdvance target current δ r : ℝ) ≤ (current : ℝ) + δ := by
  have hm : (δ : ℝ) * (pausedTime r : ℝ) ≤ (δ : ℝ) := by
    nlinarith [δ.2.1, (pausedTime r).2.2]
  have hmin := min_le_right (target : ℝ) ((current : ℝ) + (δ : ℝ) * (pausedTime r : ℝ))
  change min (target : ℝ) ((current : ℝ) + (δ : ℝ) * (pausedTime r : ℝ)) ≤ _
  linarith

theorem le_collarAdvance {target current : I} (hc : current ≤ target) (δ r : I) :
    current ≤ collarAdvance target current δ r := by
  change (current : ℝ) ≤ min (target : ℝ) ((current : ℝ) + (δ : ℝ) * (pausedTime r : ℝ))
  exact le_min hc (le_add_of_nonneg_right (mul_nonneg δ.2.1 (pausedTime r).2.1))

theorem collarAdvance_zero {target current : I} (hc : current ≤ target) (δ : I) :
    collarAdvance target current δ 0 = current := by
  apply Subtype.ext
  norm_num [collarAdvance, pausedTime]
  exact hc

theorem collarAdvance_of_paused {target current : I} (hc : current ≤ target) (δ : I)
    {r : I} (hr : (r : ℝ) ≤ 1 / 2) : collarAdvance target current δ r = current := by
  apply Subtype.ext
  dsimp [collarAdvance]
  rw [pausedTime_eq_zero hr]
  simpa using (min_eq_right hc : min (target : ℝ) (current : ℝ) = (current : ℝ))

theorem collarAdvance_one (target current δ : I) :
    (collarAdvance target current δ 1 : ℝ) = min (target : ℝ) ((current : ℝ) + δ) := by
  norm_num [collarAdvance, pausedTime]

@[simp]
theorem collarAdvance_target (target δ r : I) : collarAdvance target target δ r = target := by
  apply le_antisymm
  · exact collarAdvance_le_target _ _ _ _
  · exact le_collarAdvance le_rfl _ _

theorem collarAdvance_abs_sub {target current : I} (hc : current ≤ target) (δ r : I) :
    |(current : ℝ) - (collarAdvance target current δ r : ℝ)| ≤ δ := by
  have h1 : (current : ℝ) ≤ (collarAdvance target current δ r : ℝ) := le_collarAdvance hc δ r
  have h2 := collarAdvance_le_add target current δ r
  rw [abs_of_nonpos (by linarith : (current : ℝ) - (collarAdvance target current δ r : ℝ) ≤ 0)]
  linarith

/-- The upper-collar half of one alternating stage. -/
def collarUpperTime (γ : C(I, I)) (target current : I) (n : ℕ) : I :=
  collarAdvance target current (pathSubdivisionScaleMap γ)
    (collarStageActivation (pathSubdivisionScaleMap γ) n * upperCollarCutoff (γ current))

/-- One upper-collar step followed by one lower-collar step. -/
def collarPairTime (γ : C(I, I)) (target current : I) (n : ℕ) : I :=
  let upper := collarUpperTime γ target current n
  collarAdvance target upper (pathSubdivisionScaleMap γ)
    (collarStageActivation (pathSubdivisionScaleMap γ) n * lowerCollarCutoff (γ upper))

@[fun_prop]
theorem continuous_collarUpperTime (n : ℕ) :
    Continuous (fun z : C(I, I) × I × I ↦ collarUpperTime z.1 z.2.1 z.2.2 n) := by
  unfold collarUpperTime
  fun_prop

@[fun_prop]
theorem continuous_collarPairTime (n : ℕ) :
    Continuous (fun z : C(I, I) × I × I ↦ collarPairTime z.1 z.2.1 z.2.2 n) := by
  unfold collarPairTime
  fun_prop

theorem collarUpperTime_le_target (γ : C(I, I)) (target current : I) (n : ℕ) :
    collarUpperTime γ target current n ≤ target := collarAdvance_le_target _ _ _ _

theorem le_collarUpperTime (γ : C(I, I)) {target current : I} (hc : current ≤ target)
    (n : ℕ) : current ≤ collarUpperTime γ target current n := le_collarAdvance hc _ _

theorem collarPairTime_le_target (γ : C(I, I)) (target current : I) (n : ℕ) :
    collarPairTime γ target current n ≤ target := collarAdvance_le_target _ _ _ _

theorem collarUpperTime_le_pair (γ : C(I, I)) (target current : I) (n : ℕ) :
    collarUpperTime γ target current n ≤ collarPairTime γ target current n :=
  le_collarAdvance (collarUpperTime_le_target _ _ _ _) _ _

theorem le_collarPairTime (γ : C(I, I)) {target current : I} (hc : current ≤ target)
    (n : ℕ) : current ≤ collarPairTime γ target current n :=
  (le_collarUpperTime γ hc n).trans (collarUpperTime_le_pair γ target current n)

@[simp]
theorem collarUpperTime_target (γ : C(I, I)) (target : I) (n : ℕ) :
    collarUpperTime γ target target n = target := collarAdvance_target _ _ _

@[simp]
theorem collarPairTime_target (γ : C(I, I)) (target : I) (n : ℕ) :
    collarPairTime γ target target n = target := by
  simp [collarPairTime]

theorem collarUpperTime_of_inactive (γ : C(I, I)) {target current : I}
    (hc : current ≤ target) {n : ℕ} (hn : 3 ≤ (n : ℝ) * pathSubdivisionScale γ) :
    collarUpperTime γ target current n = current := by
  unfold collarUpperTime
  rw [collarStageActivation_zero hn, zero_mul, collarAdvance_zero hc]

theorem collarPairTime_of_inactive (γ : C(I, I)) {target current : I}
    (hc : current ≤ target) {n : ℕ} (hn : 3 ≤ (n : ℝ) * pathSubdivisionScale γ) :
    collarPairTime γ target current n = current := by
  simp only [collarPairTime, collarUpperTime_of_inactive γ hc hn,
    collarStageActivation_zero (δ := pathSubdivisionScaleMap γ) hn, zero_mul,
    collarAdvance_zero hc]

/-- A fully active alternating stage advances by a whole subdivision scale,
unless it first reaches the target. -/
theorem collarPairTime_progress (γ : C(I, I)) {target current : I}
    (hc : current ≤ target) {n : ℕ} (hn : (n : ℝ) * pathSubdivisionScale γ ≤ 2) :
    min (target : ℝ) ((current : ℝ) + pathSubdivisionScale γ) ≤
      (collarPairTime γ target current n : ℝ) := by
  have ha : collarStageActivation (pathSubdivisionScaleMap γ) n = 1 :=
    collarStageActivation_one hn
  by_cases hh : (γ current : ℝ) ≤ 13 / 24
  · have hupper : (collarUpperTime γ target current n : ℝ) =
        min (target : ℝ) ((current : ℝ) + pathSubdivisionScale γ) := by
      simp only [collarUpperTime, ha, upperCollarCutoff_one hh, one_mul]
      exact collarAdvance_one _ _ _
    rw [← hupper]
    exact collarUpperTime_le_pair γ target current n
  · have hdist := pathSubdivisionScale_controls_abs γ current
        (collarUpperTime γ target current n) (collarAdvance_abs_sub hc _ _)
    have hheight : 11 / 24 ≤ (γ (collarUpperTime γ target current n) : ℝ) := by
      have hlt := (abs_lt.mp hdist).2
      have hh := lt_of_not_ge hh
      linarith
    have hlower : (collarPairTime γ target current n : ℝ) =
        min (target : ℝ) ((collarUpperTime γ target current n : ℝ) +
          pathSubdivisionScale γ) := by
      simp only [collarPairTime, ha, lowerCollarCutoff_one hheight, one_mul]
      exact collarAdvance_one _ _ _
    rw [hlower]
    have hle : (current : ℝ) ≤ (collarUpperTime γ target current n : ℝ) :=
      le_collarUpperTime γ hc n
    exact min_le_min le_rfl (by linarith)

/-- The alternating schedule starts at zero and uses stage `n` to pass
from its `n`th value to its `(n+1)`st value. -/
def collarScheduleTime (γ : C(I, I)) (target : I) : ℕ → I
  | 0 => 0
  | n + 1 => collarPairTime γ target (collarScheduleTime γ target n) n

@[simp]
theorem collarScheduleTime_zero (γ : C(I, I)) (target : I) :
    collarScheduleTime γ target 0 = 0 := rfl

@[simp]
theorem collarScheduleTime_succ (γ : C(I, I)) (target : I) (n : ℕ) :
    collarScheduleTime γ target (n + 1) =
      collarPairTime γ target (collarScheduleTime γ target n) n := rfl

@[fun_prop]
theorem continuous_collarScheduleTime (n : ℕ) :
    Continuous (fun z : C(I, I) × I ↦ collarScheduleTime z.1 z.2 n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    simp only [collarScheduleTime_succ]
    exact (continuous_collarPairTime n).comp
      (continuous_fst.prodMk (continuous_snd.prodMk ih))

theorem collarScheduleTime_le_target (γ : C(I, I)) (target : I) (n : ℕ) :
    collarScheduleTime γ target n ≤ target := by
  cases n with
  | zero => exact target.2.1
  | succ n => exact collarPairTime_le_target _ _ _ _

theorem collarScheduleTime_le_succ (γ : C(I, I)) (target : I) (n : ℕ) :
    collarScheduleTime γ target n ≤ collarScheduleTime γ target (n + 1) :=
  le_collarPairTime γ (collarScheduleTime_le_target γ target n) n

theorem monotone_collarScheduleTime (γ : C(I, I)) (target : I) :
    Monotone (collarScheduleTime γ target) :=
  monotone_nat_of_le_succ (collarScheduleTime_le_succ γ target)

theorem collarScheduleTime_stationary (γ : C(I, I)) (target : I) {n m : ℕ}
    (hn : collarScheduleTime γ target n = target) (hnm : n ≤ m) :
    collarScheduleTime γ target m = target := by
  apply le_antisymm (collarScheduleTime_le_target γ target m)
  have h := monotone_collarScheduleTime γ target hnm
  simpa only [hn] using h

/-- Each pair contributes a full scale until the schedule has arrived. -/
theorem collarScheduleTime_progress (γ : C(I, I)) (target : I) (n : ℕ) :
    min (target : ℝ) ((n : ℝ) * pathSubdivisionScale γ) ≤
      (collarScheduleTime γ target n : ℝ) := by
  induction n with
  | zero => simp [target.2.1]
  | succ n ih =>
    by_cases harrived : (target : ℝ) ≤ (n : ℝ) * pathSubdivisionScale γ
    · have heq : collarScheduleTime γ target n = target := by
        apply le_antisymm (collarScheduleTime_le_target _ _ _)
        change (target : ℝ) ≤ (collarScheduleTime γ target n : ℝ)
        simpa only [min_eq_left harrived] using ih
      simp only [collarScheduleTime_succ, heq, collarPairTime_target]
      exact min_le_left _ _
    · have hcur : (n : ℝ) * pathSubdivisionScale γ ≤
          (collarScheduleTime γ target n : ℝ) := by
        simpa only [min_eq_right (le_of_not_ge harrived)] using ih
      have hn : (n : ℝ) * pathSubdivisionScale γ ≤ 2 := by
        have ht := target.2.2
        linarith
      refine le_trans ?_ (collarPairTime_progress γ
        (collarScheduleTime_le_target γ target n) hn)
      apply min_le_min le_rfl
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      linarith

/-- Arrival occurs once the accumulated whole-stage scale reaches one. -/
theorem collarScheduleTime_eq_target (γ : C(I, I)) (target : I) {n : ℕ}
    (hn : 1 ≤ (n : ℝ) * pathSubdivisionScale γ) :
    collarScheduleTime γ target n = target := by
  apply le_antisymm (collarScheduleTime_le_target _ _ _)
  change (target : ℝ) ≤ (collarScheduleTime γ target n : ℝ)
  have h := collarScheduleTime_progress γ target n
  simpa only [min_eq_left (target.2.2.trans hn)] using h

/-- Both arrival and deactivation hold uniformly on a neighborhood of every
path. The bound is independent of the target parameter. -/
theorem exists_collarSchedule_stationary_neighborhood (γ : C(I, I)) :
    ∃ N : ℕ, ∃ U : Set C(I, I), IsOpen U ∧ γ ∈ U ∧
      ∀ η ∈ U, ∀ (target : I) (n : ℕ), N ≤ n →
        collarScheduleTime η target n = target ∧
          collarStageActivation (pathSubdivisionScaleMap η) n = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (3 / pathSubdivisionScale γ)
  have hN' : 3 < (N : ℝ) * pathSubdivisionScale γ :=
    (div_lt_iff₀ (pathSubdivisionScale_pos γ)).mp hN
  refine ⟨N, {η | 3 < (N : ℝ) * pathSubdivisionScale η},
    isOpen_lt continuous_const (continuous_const.mul continuous_pathSubdivisionScale), hN', ?_⟩
  intro η hη target n hn
  have hlarge : 3 ≤ (n : ℝ) * pathSubdivisionScale η :=
    le_trans (le_of_lt hη)
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) (pathSubdivisionScale_pos η).le)
  exact ⟨collarScheduleTime_eq_target η target (by linarith),
    collarStageActivation_zero hlarge⟩

/-- For a fixed path, every sufficiently late stage has arrived and is inactive. -/
theorem exists_collarSchedule_stationary (γ : C(I, I)) :
    ∃ N : ℕ, ∀ (target : I) (n : ℕ), N ≤ n →
      collarScheduleTime γ target n = target ∧
        collarStageActivation (pathSubdivisionScaleMap γ) n = 0 := by
  obtain ⟨N, U, _, hγ, hU⟩ := exists_collarSchedule_stationary_neighborhood γ
  exact ⟨N, hU γ hγ⟩

end Topology
