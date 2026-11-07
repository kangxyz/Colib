/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Collar.Cutoff
public import Colib.Topology.HomotopyLifting.Collar.Schedule

/-!
# One actual cutoff-controlled collar lift

A local paused lift on the upper height collar extends continuously to all
parameters with a cutoff. The resulting family retains the exact initial
point, advances the base path by the explicit scalar schedule, and is
stationary whenever the stage activation vanishes.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyLifting/Collar/LiftData.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology

/-- Restrict a continuous map to a subset of its base. -/
def baseRestrictionMap {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (S : Set B) : C({e : E // p e ∈ S}, S) where
  toFun e := ⟨p e.1, e.2⟩
  continuous_toFun := by fun_prop

/-- The upper open collar of a height function. -/
def upperBaseCollar {B : Type u} [TopologicalSpace B] (height : C(B, I)) : Set B :=
  {b | (height b : ℝ) < 3 / 4}

/-- Concrete geometric input to a single lifting stage. The path scale
controls only short height oscillations; no global lifting conclusion is
part of this data. -/
structure CollarLiftData {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (height : C(B, I)) (Z : Type u) [TopologicalSpace Z] where
  /-- The continuous family of base paths indexed by `Z`. -/
  paths : C(Z, C(I, B))
  /-- The desired final time on each base path. -/
  target : C(Z, I)
  /-- The time on each base path reached by the chosen point in `E`. -/
  current : C(Z, I)
  /-- The time scale controlling height oscillation along each base path. -/
  scale : C(Z, I)
  /-- The continuous family of current lift points in `E`. -/
  point : C(Z, E)
  /-- The current time does not exceed the target time for any parameter. -/
  current_le_target : ∀ z, current z ≤ target z
  /-- Each chosen point projects to its base path at the current time. -/
  point_eq : ∀ z, p (point z) = paths z (current z)
  /-- Along each base path, times at distance at most the chosen scale have heights differing by
  less than `1 / 12`. -/
  oscillation : ∀ (z : Z) (s t : I), |(s : ℝ) - (t : ℝ)| ≤ (scale z : ℝ) →
    |(height (paths z s) : ℝ) - (height (paths z t) : ℝ)| < 1 / 12

namespace CollarLiftData

variable {E B Z : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Z]
  {p : C(E, B)} {height : C(B, I)} (d : CollarLiftData p height Z)

/-- The height at the current base point. -/
def currentHeight : C(Z, I) := ⟨fun z ↦ height (d.paths z (d.current z)), by fun_prop⟩

/-- A domain with enough room for a full short step in the upper collar. -/
def upperDomain : Set Z := {z | (d.currentHeight z : ℝ) < 2 / 3}

/-- An open set where the upper cutoff has already vanished. -/
def upperZeroDomain : Set Z := {z | 5 / 8 < (d.currentHeight z : ℝ)}

theorem isOpen_upperDomain : IsOpen d.upperDomain :=
  isOpen_lt (continuous_subtype_val.comp d.currentHeight.continuous) continuous_const

theorem isOpen_upperZeroDomain : IsOpen d.upperZeroDomain :=
  isOpen_lt continuous_const (continuous_subtype_val.comp d.currentHeight.continuous)

theorem upperDomain_union_zero : d.upperDomain ∪ d.upperZeroDomain = Set.univ := by
  ext z
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases h : (d.currentHeight z : ℝ) < 2 / 3
  · exact Or.inl h
  · exact Or.inr (by dsimp [upperZeroDomain]; linarith)

/-- The stage activation times the height cutoff. -/
def upperCutoff (activation : C(Z, I)) : C(Z, I) :=
  ⟨fun z ↦ activation z * upperCollarCutoff (d.currentHeight z), by fun_prop⟩

theorem upperCutoff_zero (activation : C(Z, I)) (z : Z) (hz : z ∈ d.upperZeroDomain) :
    d.upperCutoff activation z = 0 := by
  change activation z * upperCollarCutoff (d.currentHeight z) = 0
  rw [upperCollarCutoff_zero (le_of_lt hz), mul_zero]

/-- Current lifted points belong to the upper restricted map on this domain. -/
def upperInitial : C(d.upperDomain, {e : E // p e ∈ upperBaseCollar height}) where
  toFun z := ⟨d.point z.1, by
    change (height (p (d.point z.1)) : ℝ) < 3 / 4
    rw [d.point_eq]
    have hz := z.2
    change (height (d.paths z.1 (d.current z.1)) : ℝ) < 2 / 3 at hz
    linarith⟩
  continuous_toFun := by fun_prop

/-- The whole paused short segment stays inside the upper collar. -/
def upperBaseHomotopy : C(I × d.upperDomain, upperBaseCollar height) where
  toFun z := ⟨d.paths z.2.1
    (collarAdvance (d.target z.2.1) (d.current z.2.1) (d.scale z.2.1) z.1), by
      have ho := d.oscillation z.2.1 (d.current z.2.1)
        (collarAdvance (d.target z.2.1) (d.current z.2.1) (d.scale z.2.1) z.1)
        (collarAdvance_abs_sub (d.current_le_target z.2.1) (d.scale z.2.1) z.1)
      have hz := z.2.2
      change (height (d.paths z.2.1 (d.current z.2.1)) : ℝ) < 2 / 3 at hz
      change (height (d.paths z.2.1 _) : ℝ) < 3 / 4
      linarith [(abs_lt.mp ho).1]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have ht : Continuous (fun z : I × d.upperDomain ↦
        collarAdvance (d.target z.2.1) (d.current z.2.1) (d.scale z.2.1) z.1) :=
      continuous_collarAdvance.comp ((d.target.continuous.comp (by fun_prop)).prodMk
        ((d.current.continuous.comp (by fun_prop)).prodMk
          ((d.scale.continuous.comp (by fun_prop)).prodMk continuous_fst)))
    exact continuous_eval.comp ((d.paths.continuous.comp (by fun_prop)).prodMk ht)

theorem upperBaseHomotopy_paused (t : I) (z : d.upperDomain) (ht : (t : ℝ) ≤ 1 / 2) :
    d.upperBaseHomotopy (t, z) = baseRestrictionMap p (upperBaseCollar height) (d.upperInitial
      z) := by
  apply Subtype.ext
  change d.paths z.1 (collarAdvance (d.target z.1) (d.current z.1) (d.scale z.1) t) = p (d.point
    z.1)
  rw [collarAdvance_of_paused (d.current_le_target z.1) (d.scale z.1) ht]
  exact (d.point_eq z.1).symm

variable (hp : WeakHomotopyLiftingProperty (baseRestrictionMap p (upperBaseCollar height)))

/-- The actual local family supplied by the local weak lifting hypothesis. -/
def upperLocalLift : C(I × d.upperDomain, {e : E // p e ∈ upperBaseCollar height}) :=
  (hp.paused d.upperDomain d.upperInitial d.upperBaseHomotopy d.upperBaseHomotopy_paused).choose

theorem upperLocalLift_zero (z : d.upperDomain) :
    d.upperLocalLift hp (0, z) = d.upperInitial z :=
  (hp.paused d.upperDomain d.upperInitial d.upperBaseHomotopy
    d.upperBaseHomotopy_paused).choose_spec.1 z

theorem upperLocalLift_projection (t : I) (z : d.upperDomain) :
    p (d.upperLocalLift hp (t, z)).1 =
      d.paths z.1 (collarAdvance (d.target z.1) (d.current z.1) (d.scale z.1) t) :=
  congrArg Subtype.val
    ((hp.paused d.upperDomain d.upperInitial d.upperBaseHomotopy
      d.upperBaseHomotopy_paused).choose_spec.2 t z)

/-- Forgetting the local subtype gives a local family in the original total space. -/
def upperLocalFamily : C(I × d.upperDomain, E) :=
  ⟨fun z ↦ (d.upperLocalLift hp z).1, by fun_prop⟩

theorem upperLocalFamily_zero (z : d.upperDomain) : d.upperLocalFamily hp (0, z) = d.point z.1 :=
  congrArg Subtype.val (d.upperLocalLift_zero hp z)

/-- The actual global cutoff-controlled lifting stage. -/
def upperStage (activation : C(Z, I)) : C(I × Z, E) :=
  cutoffLift d.upperDomain d.upperZeroDomain d.isOpen_upperDomain d.isOpen_upperZeroDomain
    d.upperDomain_union_zero (d.upperCutoff activation) (d.upperCutoff_zero activation)
    d.point (d.upperLocalFamily hp) (d.upperLocalFamily_zero hp)

@[simp]
theorem upperStage_zero (activation : C(Z, I)) (z : Z) :
    d.upperStage hp activation (0, z) = d.point z :=
  cutoffLift_zero _ _ _ _ _ _ _ _ _ _ _

/-- Vanishing activation makes the entire lifted stage exactly stationary. -/
theorem upperStage_stationary (activation : C(Z, I)) (z : Z) (hz : activation z = 0) (r : I) :
    d.upperStage hp activation (r, z) = d.point z := by
  apply cutoffLift_apply_of_zero
  change activation z * _ = 0
  rw [hz, zero_mul]

/-- Every intermediate point of the global stage lies over its precise
cutoff-rescaled time on the original base path. -/
theorem upperStage_projection (activation : C(Z, I)) (r : I) (z : Z) :
    p (d.upperStage hp activation (r, z)) =
      d.paths z (collarAdvance (d.target z) (d.current z) (d.scale z) (r * d.upperCutoff
        activation z)) := by
  apply cutoffLift_property (P := fun r z e ↦ p e =
    d.paths z (collarAdvance (d.target z) (d.current z) (d.scale z) (r * d.upperCutoff
      activation z)))
  · intro r z
    exact d.upperLocalLift_projection hp _ z
  · intro r z hz
    rw [d.upperCutoff_zero activation z hz, mul_zero,
      collarAdvance_zero (d.current_le_target z) (d.scale z)]
    exact d.point_eq z

/-- The endpoint of one lifted stage is valid input to the next stage. -/
def upperNext (activation : C(Z, I)) : CollarLiftData p height Z where
  paths := d.paths
  target := d.target
  current := ⟨fun z ↦ collarAdvance (d.target z) (d.current z) (d.scale z) (d.upperCutoff
    activation z),
    continuous_collarAdvance.comp (d.target.continuous.prodMk
      (d.current.continuous.prodMk (d.scale.continuous.prodMk (d.upperCutoff
        activation).continuous)))⟩
  scale := d.scale
  point := homotopyTimeSlice (d.upperStage hp activation) 1
  current_le_target z := collarAdvance_le_target _ _ _ _
  point_eq z := by
    change p (d.upperStage hp activation (1, z)) = d.paths z
      (collarAdvance (d.target z) (d.current z) (d.scale z) (d.upperCutoff activation z))
    simpa only [one_mul] using d.upperStage_projection hp activation 1 z
  oscillation := d.oscillation

/-- One cutoff stage as a homotopy between its actual endpoint maps. -/
def upperHomotopy (activation : C(Z, I)) : d.point.Homotopy (d.upperNext hp activation).point where
  toContinuousMap := d.upperStage hp activation
  map_zero_left := d.upperStage_zero hp activation
  map_one_left _ := rfl

@[simp] theorem upperNext_paths (activation : C(Z, I)) : (d.upperNext hp activation).paths =
    d.paths := rfl
@[simp] theorem upperNext_target (activation : C(Z, I)) : (d.upperNext hp activation).target =
    d.target := rfl
@[simp] theorem upperNext_scale (activation : C(Z, I)) : (d.upperNext hp activation).scale =
    d.scale := rfl

/-- At a reached target, the entire stage homotopy stays in that fixed fiber. -/
theorem upperHomotopy_projection_of_target (activation : C(Z, I)) (r : I) (z : Z)
    (hz : d.current z = d.target z) :
    p (d.upperHomotopy hp activation (r, z)) = d.paths z (d.target z) := by
  change p (d.upperStage hp activation (r, z)) = _
  rw [d.upperStage_projection hp activation, hz, collarAdvance_target]

end CollarLiftData

/-- Reverse the height coordinate, interchanging the two collar domains. -/
def reflectedHeight {B : Type u} [TopologicalSpace B] (height : C(B, I)) : C(B, I) :=
  ⟨fun b ↦ σ (height b), by fun_prop⟩

@[simp]
theorem upperCollarCutoff_symm (h : I) : upperCollarCutoff (σ h) = lowerCollarCutoff h := by
  unfold upperCollarCutoff lowerCollarCutoff
  congr 1
  change 12 * (5 / 8 - (1 - (h : ℝ))) = 12 * ((h : ℝ) - 3 / 8)
  ring

namespace CollarLiftData

variable {E B Z : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Z]
  {p : C(E, B)} {height : C(B, I)} (d : CollarLiftData p height Z)

/-- The same geometric data measured with the opposite height coordinate. -/
def reflect : CollarLiftData p (reflectedHeight height) Z where
  paths := d.paths
  target := d.target
  current := d.current
  scale := d.scale
  point := d.point
  current_le_target := d.current_le_target
  point_eq := d.point_eq
  oscillation z s t h := by
    have hd := d.oscillation z s t h
    change |(1 - (height (d.paths z s) : ℝ)) - (1 - (height (d.paths z t) : ℝ))| < 1 / 12
    have he : (1 - (height (d.paths z s) : ℝ)) - (1 - (height (d.paths z t) : ℝ)) =
        -((height (d.paths z s) : ℝ) - (height (d.paths z t) : ℝ)) := by ring
    rw [he, abs_neg]
    exact hd

variable (hp₀ : WeakHomotopyLiftingProperty (baseRestrictionMap p (upperBaseCollar height)))
  (hp₁ : WeakHomotopyLiftingProperty (baseRestrictionMap p (upperBaseCollar (reflectedHeight
    height))))

/-- A reflected upper stage gives the lower-collar stage in the original data. -/
def lowerNext (activation : C(Z, I)) : CollarLiftData p height Z where
  paths := d.paths
  target := d.target
  current := (d.reflect.upperNext hp₁ activation).current
  scale := d.scale
  point := (d.reflect.upperNext hp₁ activation).point
  current_le_target := (d.reflect.upperNext hp₁ activation).current_le_target
  point_eq := (d.reflect.upperNext hp₁ activation).point_eq
  oscillation := d.oscillation

/-- The lower-collar stage homotopy. -/
def lowerHomotopy (activation : C(Z, I)) : d.point.Homotopy (d.lowerNext hp₁ activation).point :=
  d.reflect.upperHomotopy hp₁ activation

theorem lowerNext_current (activation : C(Z, I)) (z : Z) :
    (d.lowerNext hp₁ activation).current z =
      collarAdvance (d.target z) (d.current z) (d.scale z)
        (activation z * lowerCollarCutoff (d.currentHeight z)) := by
  change collarAdvance _ _ _ (activation z * upperCollarCutoff (σ (d.currentHeight z))) = _
  rw [upperCollarCutoff_symm]
  rfl

/-- One upper stage followed by one lower stage. -/
def pairNext (activation : C(Z, I)) : CollarLiftData p height Z :=
  (d.upperNext hp₀ activation).lowerNext hp₁ activation

/-- The time coordinate of a lifted pair is exactly the scalar upper/lower update. -/
theorem pairNext_current (activation : C(Z, I)) (z : Z) :
    (d.pairNext hp₀ hp₁ activation).current z =
      let upper := collarAdvance (d.target z) (d.current z) (d.scale z)
        (activation z * upperCollarCutoff (height (d.paths z (d.current z))))
      collarAdvance (d.target z) upper (d.scale z)
        (activation z * lowerCollarCutoff (height (d.paths z upper))) := by
  change ((d.upperNext hp₀ activation).lowerNext hp₁ activation).current z = _
  rw [lowerNext_current]
  rfl

/-- Both actual collar stages as a single endpoint-preserving homotopy. -/
def pairHomotopy (activation : C(Z, I)) : d.point.Homotopy (d.pairNext hp₀ hp₁ activation).point :=
  (d.upperHomotopy hp₀ activation).trans ((d.upperNext hp₀ activation).lowerHomotopy hp₁ activation)

@[simp] theorem pairNext_paths (activation : C(Z, I)) : (d.pairNext hp₀ hp₁ activation).paths =
    d.paths := rfl
@[simp] theorem pairNext_target (activation : C(Z, I)) : (d.pairNext hp₀ hp₁ activation).target
    = d.target := rfl
@[simp] theorem pairNext_scale (activation : C(Z, I)) : (d.pairNext hp₀ hp₁ activation).scale =
    d.scale := rfl

/-- An inactive stage is stationary throughout, including both collar corrections. -/
theorem pairHomotopy_stationary (activation : C(Z, I)) (z : Z) (hz : activation z = 0) (r : I) :
    d.pairHomotopy hp₀ hp₁ activation (r, z) = d.point z := by
  change ((d.upperHomotopy hp₀ activation).trans
    ((d.upperNext hp₀ activation).lowerHomotopy hp₁ activation)) (r, z) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact d.upperStage_stationary hp₀ activation z hz _
  · change (d.upperNext hp₀ activation).reflect.upperStage hp₁ activation (_, z) = _
    rw [(d.upperNext hp₀ activation).reflect.upperStage_stationary hp₁ activation z hz]
    exact d.upperStage_stationary hp₀ activation z hz 1

/-- A stage begun at its target stays over that target throughout both halves. -/
theorem pairHomotopy_projection_of_target (activation : C(Z, I)) (r : I) (z : Z)
    (hz : d.current z = d.target z) :
    p (d.pairHomotopy hp₀ hp₁ activation (r, z)) = d.paths z (d.target z) := by
  change p (((d.upperHomotopy hp₀ activation).trans
    ((d.upperNext hp₀ activation).lowerHomotopy hp₁ activation)) (r, z)) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact d.upperHomotopy_projection_of_target hp₀ activation _ z hz
  · apply (d.upperNext hp₀ activation).reflect.upperHomotopy_projection_of_target hp₁ activation
    change collarAdvance _ (d.current z) _ _ = d.target z
    rw [hz, collarAdvance_target]

end CollarLiftData
end Topology
