/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Collar.LiftData
public import Colib.Topology.Homotopy.LocallyStationary

/-!
# Weak lifting from two height collars

The construction alternates the two cutoff-controlled collar lifts. A
continuous path scale supplies finite progress, while stage activations
vanish locally uniformly. Thus the actual eventual lift is continuous and
its initial correction is an actual locally stationary concatenation.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyLifting/Collar/TwoCharts.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology

/-- Postcompose compact-open paths with the height function. -/
def heightPathMap {B : Type u} [TopologicalSpace B] (height : C(B, I)) : C(C(I, B), C(I, I)) where
  toFun γ := height.comp γ
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact height.continuous.comp continuous_eval

namespace CollarLiftData

variable {E B Z : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Z]
  {p : C(E, B)} {height : C(B, I)} (d : CollarLiftData p height Z)
  (hp₀ : WeakHomotopyLiftingProperty (baseRestrictionMap p (upperBaseCollar height)))
  (hp₁ : WeakHomotopyLiftingProperty (baseRestrictionMap p (upperBaseCollar (reflectedHeight
    height))))
  (act : ℕ → C(Z, I))

/-- Successive actual alternating collar lifts. -/
def iterate : ℕ → CollarLiftData p height Z
  | 0 => d
  | n + 1 => (iterate n).pairNext hp₀ hp₁ (act n)

@[simp] theorem iterate_paths (n : ℕ) : (d.iterate hp₀ hp₁ act n).paths = d.paths := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
@[simp] theorem iterate_target (n : ℕ) : (d.iterate hp₀ hp₁ act n).target = d.target := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
@[simp] theorem iterate_scale (n : ℕ) : (d.iterate hp₀ hp₁ act n).scale = d.scale := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- The actual homotopy used by one stage of the iteration. -/
def iterateHomotopy (n : ℕ) :
    (d.iterate hp₀ hp₁ act n).point.Homotopy (d.iterate hp₀ hp₁ act (n + 1)).point :=
  (d.iterate hp₀ hp₁ act n).pairHomotopy hp₀ hp₁ (act n)

/-- Inactivity implies local stationarity of the whole stage homotopies. -/
theorem iterateHomotopy_locallyStationary
    (ha : ∀ z, ∃ U : Set Z, IsOpen U ∧ z ∈ U ∧ ∃ N, ∀ y ∈ U, ∀ n, N ≤ n → act n y = 0) :
    LocallyStationaryHomotopies (fun n ↦ (d.iterate hp₀ hp₁ act n).point)
      (d.iterateHomotopy hp₀ hp₁ act) := by
  intro z
  obtain ⟨U, hU, hz, N, hN⟩ := ha z
  refine ⟨U, hU, hz, N, ?_⟩
  intro y hy n hn t
  have heq : ∀ k, N ≤ k → (d.iterate hp₀ hp₁ act k).point y = (d.iterate hp₀ hp₁ act N).point y
    := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [← (d.iterateHomotopy hp₀ hp₁ act k).map_one_left]
      exact ((d.iterate hp₀ hp₁ act k).pairHomotopy_stationary hp₀ hp₁ (act k) y (hN y hy k hk)
        1).trans ih
  exact ((d.iterate hp₀ hp₁ act n).pairHomotopy_stationary hp₀ hp₁ (act n) y (hN y hy n hn)
    t).trans (heq n hn)

end CollarLiftData

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B)) (height : C(B, I))

/-- Universal initial data: a path with its given starting lift, and an
arbitrary target time at which a lifted value is requested. -/
def twoCollarInitialData : CollarLiftData p height (I × MappingPath p) where
  paths := ⟨fun z ↦ z.2.1.2, by fun_prop⟩
  target := ContinuousMap.fst
  current := ContinuousMap.const _ 0
  scale := pathSubdivisionScaleMap.comp ((heightPathMap height).comp ⟨fun z ↦ z.2.1.2, by fun_prop⟩)
  point := (MappingPath.source p).comp ContinuousMap.snd
  current_le_target z := z.1.2.1
  point_eq z := z.2.2.symm
  oscillation z s t h := pathSubdivisionScale_controls_abs (height.comp z.2.1.2) s t h

/-- Continuous stage activations, depending only on the original height path. -/
def twoCollarActivation (n : ℕ) : C(I × MappingPath p, I) :=
  ⟨fun z ↦ collarStageActivation (pathSubdivisionScaleMap (height.comp z.2.1.2)) n,
    (continuous_collarStageActivation n).comp
      (pathSubdivisionScaleMap.continuous.comp
        ((heightPathMap height).continuous.comp (by fun_prop)))⟩

theorem twoCollarActivation_locallyInactive :
    ∀ z : I × MappingPath p, ∃ U : Set (I × MappingPath p), IsOpen U ∧ z ∈ U ∧
      ∃ N, ∀ y ∈ U, ∀ n, N ≤ n → twoCollarActivation p height n y = 0 := by
  intro z
  obtain ⟨N, U, hU, hz, hN⟩ := exists_collarSchedule_stationary_neighborhood (height.comp z.2.1.2)
  let φ : C(I × MappingPath p, C(I, I)) :=
    (heightPathMap height).comp ⟨fun z ↦ z.2.1.2, by fun_prop⟩
  refine ⟨φ ⁻¹' U, hU.preimage φ.continuous, hz, N, ?_⟩
  intro y hy n hn
  exact (hN (φ y) hy y.1 n hn).2

variable (hp₀ : WeakHomotopyLiftingProperty (baseRestrictionMap p (upperBaseCollar height)))
  (hp₁ : WeakHomotopyLiftingProperty (baseRestrictionMap p (upperBaseCollar (reflectedHeight
    height))))

/-- The actual iterated lifted data. -/
def twoCollarData (n : ℕ) : CollarLiftData p height (I × MappingPath p) :=
  (twoCollarInitialData p height).iterate hp₀ hp₁ (twoCollarActivation p height) n

@[simp] theorem twoCollarData_paths (n : ℕ) :
    (twoCollarData p height hp₀ hp₁ n).paths = (twoCollarInitialData p height).paths :=
  CollarLiftData.iterate_paths _ _ _ _ n
@[simp] theorem twoCollarData_target (n : ℕ) :
    (twoCollarData p height hp₀ hp₁ n).target = (twoCollarInitialData p height).target :=
  CollarLiftData.iterate_target _ _ _ _ n
@[simp] theorem twoCollarData_scale (n : ℕ) :
    (twoCollarData p height hp₀ hp₁ n).scale = (twoCollarInitialData p height).scale :=
  CollarLiftData.iterate_scale _ _ _ _ n

/-- Its current base time is exactly the proved scalar collar schedule. -/
theorem twoCollarData_current (n : ℕ) (z : I × MappingPath p) :
    (twoCollarData p height hp₀ hp₁ n).current z = collarScheduleTime (height.comp z.2.1.2) z.1
      n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((twoCollarData p height hp₀ hp₁ n).pairNext hp₀ hp₁ (twoCollarActivation p height
      n)).current z = _
    rw [CollarLiftData.pairNext_current]
    simp only [twoCollarData_paths, twoCollarData_target, twoCollarData_scale, ih]
    rfl

/-- The complete lifted stage homotopies are locally stationary. -/
theorem twoCollarStationarity :
    LocallyStationaryHomotopies (fun n ↦ (twoCollarData p height hp₀ hp₁ n).point)
      ((twoCollarInitialData p height).iterateHomotopy hp₀ hp₁ (twoCollarActivation p height)) :=
  (twoCollarInitialData p height).iterateHomotopy_locallyStationary hp₀ hp₁
    (twoCollarActivation p height) (twoCollarActivation_locallyInactive p height)

/-- The actual continuous eventual lift of all universal base paths. -/
def twoCollarUniversalLift : C(I × MappingPath p, E) :=
  (twoCollarStationarity p height hp₀ hp₁).limit

/-- Finite scalar progress identifies the terminal projection exactly. -/
theorem twoCollarUniversalLift_projection (t : I) (z : MappingPath p) :
    p (twoCollarUniversalLift p height hp₀ hp₁ (t, z)) = z.1.2 t := by
  apply (twoCollarStationarity p height hp₀ hp₁).limit_comp_of_eventually
    p (fun z : I × MappingPath p ↦ z.2.1.2 z.1)
  intro x
  obtain ⟨N, hN⟩ := exists_collarSchedule_stationary (height.comp x.2.1.2)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [(twoCollarData p height hp₀ hp₁ n).point_eq]
  rw [twoCollarData_paths]
  change x.2.1.2 ((twoCollarData p height hp₀ hp₁ n).current x) = _
  rw [twoCollarData_current, (hN x.1 n hn).1]

/-- The locally stationary stage homotopies supply the weak initial
correction on the original source of each universal path. -/
def twoCollarUniversalCorrection :
    (MappingPath.source p).Homotopy (homotopyTimeSlice (twoCollarUniversalLift p height hp₀ hp₁)
      0) :=
  ((twoCollarStationarity p height hp₀ hp₁).homotopy.compContinuousMap
    (show C(MappingPath p, I × MappingPath p) from
      ⟨fun z ↦ (0, z), by fun_prop⟩)).cast rfl rfl

/-- At target time zero every stage stays over the original base point,
including the complete initial correction. -/
theorem twoCollarUniversalCorrection_projection (t : I) (z : MappingPath p) :
    p (twoCollarUniversalCorrection p height hp₀ hp₁ (t, z)) = p (MappingPath.source p z) := by
  have h := (twoCollarStationarity p height hp₀ hp₁).homotopy_property
    (fun x e ↦ x.1 = 0 → p e = p (MappingPath.source p x.2))
    (by
      intro n r x hx
      have ht : (twoCollarData p height hp₀ hp₁ n).target x = 0 := by
        rw [twoCollarData_target]
        exact hx
      have hc : (twoCollarData p height hp₀ hp₁ n).current x =
          (twoCollarData p height hp₀ hp₁ n).target x := by
        apply le_antisymm ((twoCollarData p height hp₀ hp₁ n).current_le_target x)
        rw [ht]
        exact ((twoCollarData p height hp₀ hp₁ n).current x).2.1
      have hh := (twoCollarData p height hp₀ hp₁ n).pairHomotopy_projection_of_target
        hp₀ hp₁ (twoCollarActivation p height n) r x hc
      apply hh.trans
      rw [twoCollarData_paths, twoCollarData_target]
      change x.2.1.2 x.1 = p (MappingPath.source p x.2)
      rw [hx]
      exact x.2.2) t (0, z)
  exact h rfl

include hp₀ hp₁ in
/-- Concrete two-collar local-to-global weak lifting. The only hypotheses
are the weak covering-homotopy properties on the two explicit open height
collars. The global lift and its fiberwise initial correction are derived
from the locally stationary construction above. -/
theorem weakLifting_of_two_collars : WeakHomotopyLiftingProperty p := by
  intro A _ a H hzero
  let m : C(A, MappingPath p) := {
    toFun x := ⟨(a x, ⟨fun t ↦ H (t, x), by fun_prop⟩), hzero x⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk a.continuous
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact H.continuous.comp continuous_swap }
  let L : C(I × A, E) := (twoCollarUniversalLift p height hp₀ hp₁).comp
    ⟨fun z ↦ (z.1, m z.2), by fun_prop⟩
  let K : a.Homotopy (homotopyTimeSlice L 0) :=
    ((twoCollarUniversalCorrection p height hp₀ hp₁).compContinuousMap m).cast rfl rfl
  refine ⟨L, ?_, ⟨K, ?_⟩⟩
  · intro t x
    exact twoCollarUniversalLift_projection p height hp₀ hp₁ t (m x)
  · intro t x
    exact twoCollarUniversalCorrection_projection p height hp₀ hp₁ t (m x)

end Topology
