/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Weak

/-!
# Paused and fiberwise formulations of weak lifting

Weak covering-homotopy lifting is equivalent to exact lifting for homotopies
which are stationary during the first half of the interval. This provides
the exact initial-value formulation needed for cutoff-controlled collar
lifting, while preserving the already proved homotopy-pullback comparison.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyLifting/PausedHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology

/-- Compress time into the first half of the interval. -/
def firstHalfTime (t : I) : I := ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

/-- Parametrize the second half of the interval. -/
def secondHalfTime (t : I) : I := ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

/-- Wait for half the interval, then traverse the entire interval. -/
def pausedTime (t : I) : I := ⟨max 0 (2 * (t : ℝ) - 1),
  le_max_left _ _, max_le (by norm_num) (by linarith [t.2.2])⟩

@[fun_prop] theorem continuous_firstHalfTime : Continuous firstHalfTime := by
  unfold firstHalfTime; fun_prop
@[fun_prop] theorem continuous_secondHalfTime : Continuous secondHalfTime := by
  unfold secondHalfTime; fun_prop
@[fun_prop] theorem continuous_pausedTime : Continuous pausedTime := by unfold pausedTime; fun_prop

@[simp]
theorem firstHalfTime_zero : firstHalfTime 0 = 0 := by apply Subtype.ext; norm_num [firstHalfTime]

@[simp]
theorem firstHalfTime_one : firstHalfTime 1 = secondHalfTime 0 := by
  apply Subtype.ext
  norm_num [firstHalfTime, secondHalfTime]

theorem firstHalfTime_le_half (t : I) : (firstHalfTime t : ℝ) ≤ 1 / 2 := by
  dsimp [firstHalfTime]
  linarith [t.2.2]

theorem pausedTime_eq_zero {t : I} (h : (t : ℝ) ≤ 1 / 2) : pausedTime t = 0 := by
  apply Subtype.ext
  exact max_eq_left (by linarith)

@[simp]
theorem pausedTime_firstHalfTime (t : I) : pausedTime (firstHalfTime t) = 0 :=
  pausedTime_eq_zero (firstHalfTime_le_half t)

@[simp]
theorem pausedTime_secondHalfTime (t : I) : pausedTime (secondHalfTime t) = t := by
  apply Subtype.ext
  change max 0 (2 * ((1 + (t : ℝ)) / 2) - 1) = (t : ℝ)
  have ht : 2 * ((1 + (t : ℝ)) / 2) - 1 = (t : ℝ) := by ring
  rw [ht, max_eq_right t.2.1]

/-- Exact lifting when the base homotopy is stationary for half the time. -/
def PausedHomotopyLiftingProperty {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) : Prop :=
  ∀ (A : Type u) [TopologicalSpace A] (a : C(A, E)) (H : C(I × A, B)),
    (∀ (t : I) (x : A), (t : ℝ) ≤ 1 / 2 → H (t, x) = p (a x)) →
      ∃ L : C(I × A, E), (∀ x, L (0, x) = a x) ∧ ∀ t x, p (L (t, x)) = H (t, x)

/-- The weak initial correction uses the stationary first half; the weak
lift traverses the prescribed homotopy during the second half. -/
theorem WeakHomotopyLiftingProperty.paused
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : WeakHomotopyLiftingProperty p) : PausedHomotopyLiftingProperty p := by
  intro A _ a H hpaused
  let H' : C(I × A, B) := ⟨fun z ↦ H (secondHalfTime z.1, z.2), by fun_prop⟩
  have hz : ∀ x, H' (0, x) = p (a x) :=
    fun x ↦ hpaused (secondHalfTime 0) x (by norm_num [secondHalfTime])
  obtain ⟨L, hL, K, hK⟩ := hp A a H' hz
  let J : (homotopyTimeSlice L 0).Homotopy (homotopyTimeSlice L 1) := {
    toContinuousMap := L
    map_zero_left := fun _ ↦ rfl
    map_one_left := fun _ ↦ rfl }
  refine ⟨(K.trans J).toContinuousMap, (K.trans J).map_zero_left, ?_⟩
  intro t x
  change p ((K.trans J) (t, x)) = H (t, x)
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · exact (hK _ x).trans (hpaused t x ht).symm
  · change p (L (_, x)) = H (t, x)
    rw [hL]
    change H (secondHalfTime _, x) = H (t, x)
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      dsimp [secondHalfTime]
      ring
    · rfl

/-- Conversely, exact lifting of a paused homotopy supplies a weak lift
by discarding its stationary first half. -/
theorem PausedHomotopyLiftingProperty.weak
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : PausedHomotopyLiftingProperty p) : WeakHomotopyLiftingProperty p := by
  intro A _ a H hzero
  let H' : C(I × A, B) := ⟨fun z ↦ H (pausedTime z.1, z.2), by fun_prop⟩
  have hpaused : ∀ (t : I) (x : A), (t : ℝ) ≤ 1 / 2 → H' (t, x) = p (a x) := by
    intro t x ht
    change H (pausedTime t, x) = p (a x)
    rw [pausedTime_eq_zero ht]
    exact hzero x
  obtain ⟨Q, hQzero, hQ⟩ := hp A a H' hpaused
  let L : C(I × A, E) := ⟨fun z ↦ Q (secondHalfTime z.1, z.2), by fun_prop⟩
  have hL : ∀ t x, p (L (t, x)) = H (t, x) := by
    intro t x
    change p (Q (secondHalfTime t, x)) = _
    rw [hQ]
    change H (pausedTime (secondHalfTime t), x) = _
    rw [pausedTime_secondHalfTime]
  let K : a.Homotopy (homotopyTimeSlice L 0) := {
    toFun z := Q (firstHalfTime z.1, z.2)
    continuous_toFun := by fun_prop
    map_zero_left := fun x ↦ by simpa using hQzero x
    map_one_left := fun x ↦ by simp only [firstHalfTime_one]; rfl }
  refine ⟨L, hL, ⟨K, ?_⟩⟩
  intro t x
  change p (Q (firstHalfTime t, x)) = _
  rw [hQ]
  change H (pausedTime (firstHalfTime t), x) = _
  rw [pausedTime_firstHalfTime]
  exact hzero x

/-- The two concrete formulations of weak covering-homotopy lifting agree. -/
theorem weakHomotopyLiftingProperty_iff_paused
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    WeakHomotopyLiftingProperty p ↔ PausedHomotopyLiftingProperty p :=
  ⟨WeakHomotopyLiftingProperty.paused, PausedHomotopyLiftingProperty.weak⟩

end Topology
