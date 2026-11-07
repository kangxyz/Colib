/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.PathSubdivision.TimePaths
public import Colib.Topology.HomotopyPullback.Fibration

/-!
# Remaining-tail maps at the current parameter

A partial lift consists of a parameter and an actual source point over an
intermediate time. Appending the original remaining tail gives a point of
the original homotopy pullback. The same construction on a path pool uses
that pool point's current parameter, even when a preceding homotopy moves it.
Explicit time-path interpolation removes both a segment subdivision and a
constant prefix, retaining every constant original boundary track.


Implementation provenance:
`Quillen/Topology/PathSubdivision/TailMaps.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.CubicalSubdivision


noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology.PathSubdivision
open CubicalSubdivision
variable {D E X B : Type u} [TopologicalSpace D] [TopologicalSpace E]
  [TopologicalSpace X] [TopologicalSpace B]

/-- The actual time slice of the original path family. -/
def slice (H : C(unitInterval × D, B)) (s : unitInterval) : C(D, B) :=
  ⟨fun d ↦ H (s,d),by fun_prop⟩

/-- Original parameters paired with source points over the displayed time. -/
abbrev Stage (p : C(E, B)) (H : C(unitInterval × D, B)) (s : unitInterval) :=
  {z : D × E // p z.2 = H (s,z.1)}

/-- An actual segment of the original family at its supplied parameter. -/
def familyPath (H : C(unitInterval × D, B)) (s t : unitInterval) (d : D) :
    Path (H (s,d)) (H (t,d)) :=
  (timePath s t).map (show Continuous (fun r ↦ H (r,d)) from by fun_prop)

@[simp] theorem familyPath_apply (H : C(unitInterval × D, B)) (s t r : unitInterval) (d : D) :
    familyPath H s t d r = H (affineTime s t r,d) := rfl

@[simp] theorem familyPath_self (H : C(unitInterval × D, B)) (s : unitInterval) (d : D) :
    familyPath H s s d = Path.refl (H (s,d)) := by
  ext r
  exact congrArg (fun q ↦ H (q,d)) (affineTime_self s r)

/-- Enter the next slice's genuine homotopy pullback by the actual original segment. -/
def stageSegment (p : C(E, B)) (H : C(unitInterval × D, B)) (s t : unitInterval) :
    C(Stage p H s,HomotopyPullback p (slice H t)) where
  toFun z := ⟨(z.val.1,z.val.2,(familyPath H s t z.val.1).toContinuousMap),
    (Path.source _).trans z.property.symm,Path.target _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : Stage p H s × unitInterval ↦
      H (affineTime s t z.2,z.1.val.1))
    fun_prop

/-- A zero-length segment is literally the original constant-path inclusion. -/
theorem stageSegment_self (p : C(E, B)) (H : C(unitInterval × D, B)) (s : unitInterval) :
    stageSegment p H s s = HomotopyPullback.strictPullbackInclusion p (slice H s) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  refine Prod.ext rfl ?_
  refine Prod.ext rfl ?_
  exact congrArg Path.toContinuousMap (familyPath_self H s z.val.1)

variable (p : C(E, B)) (f : C(X, B)) (H : C(unitInterval × D, B)) (k : C(D, X))
  (hEnd : ∀ d, H (1, d) = f (k d))

/-- Follow the complete remaining original tail at the current stage parameter. -/
def stageToPullback (s : unitInterval) : C(Stage p H s,HomotopyPullback p f) where
  toFun z := ⟨(k z.val.1,z.val.2,(familyPath H s 1 z.val.1).toContinuousMap),
    (Path.source _).trans z.property.symm,(Path.target _).trans (hEnd z.val.1)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : Stage p H s × unitInterval ↦
      H (affineTime s 1 z.2,z.1.val.1))
    fun_prop

/-- Append a remaining tail after an arbitrary source-to-slice path.
The original tail is evaluated at this point's parameter, which may have moved. -/
def appendToPullback (s : unitInterval) : C(HomotopyPullback p (slice H s),HomotopyPullback p f)
    where
  toFun z := ⟨(k z.val.1,z.val.2.1,
    ((⟨z.val.2.2,z.property.1,z.property.2⟩ : Path (p z.val.2.1) (H (s,z.val.1))).trans
      (familyPath H s 1 z.val.1)).toContinuousMap),
    Path.source _,(Path.target _).trans (hEnd z.val.1)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    refine Path.trans_continuous_family
      (fun z : HomotopyPullback p (slice H s) ↦
        (⟨z.val.2.2,z.property.1,z.property.2⟩ : Path (p z.val.2.1) (H (s,z.val.1)))) ?_
      (fun z ↦ familyPath H s 1 z.val.1) ?_
    · change Continuous (fun z : HomotopyPullback p (slice H s) × unitInterval ↦ z.1.val.2.2 z.2)
      fun_prop
    · change Continuous (fun z : HomotopyPullback p (slice H s) × unitInterval ↦
        H (affineTime s 1 z.2,z.1.val.1))
      fun_prop

@[simp] theorem appendToPullback_parameter (s : unitInterval)
    (z : HomotopyPullback p (slice H s)) :
    (appendToPullback p f H k hEnd s z).val.1 = k z.val.1 := rfl

@[simp] theorem appendToPullback_source (s : unitInterval)
    (z : HomotopyPullback p (slice H s)) :
    (appendToPullback p f H k hEnd s z).val.2.1 = z.val.2.1 := rfl

/-- Explicitly remove the subdivision of the original remaining time path.
The homotopy keeps the supplied stage parameter and source point unchanged. -/
def stageJoinHomotopy (s t : unitInterval) :
    ((appendToPullback p f H k hEnd t).comp (stageSegment p H s t)).Homotopy
      (stageToPullback p f H k hEnd s) where
  toFun z := ⟨(k z.2.val.1,z.2.val.2,
    ⟨fun r ↦ H (timeJoinHomotopy s t 1 (z.1,r),z.2.val.1),by fun_prop⟩),
    by
      change H (timeJoinHomotopy s t 1 (z.1,0),z.2.val.1) = p z.2.val.2
      rw [timeJoinHomotopy_source]
      exact z.2.property.symm,
    by
      change H (timeJoinHomotopy s t 1 (z.1,1),z.2.val.1) = f (k z.2.val.1)
      rw [timeJoinHomotopy_target]
      exact hEnd z.2.val.1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × Stage p H s) × unitInterval ↦
      H (timeJoinHomotopy s t 1 (z.1.1,z.2),z.1.2.val.1))
    fun_prop
  map_zero_left z := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    refine Prod.ext rfl ?_
    apply ContinuousMap.ext
    intro r
    change H (timeJoinHomotopy s t 1 (0,r),z.val.1) =
      ((familyPath H s t z.val.1).trans (familyPath H t 1 z.val.1)) r
    rw [(timeJoinHomotopy s t 1).apply_zero]
    change (((timePath s t).trans (timePath t 1)).map
      (show Continuous (fun q ↦ H (q,z.val.1)) from by fun_prop)) r = _
    rw [Path.map_trans]
    rfl
  map_one_left z := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    refine Prod.ext rfl ?_
    apply ContinuousMap.ext
    intro r
    change H (timeJoinHomotopy s t 1 (1,r),z.val.1) = H (affineTime s 1 r,z.val.1)
    rw [(timeJoinHomotopy s t 1).apply_one]
    rfl

/-- The entire reparametrization is fixed on every original constant track. -/
theorem stageJoinHomotopy_fixed (s t : unitInterval) (z : Stage p H s)
    (h : ∀ r, H (r, z.val.1) = H (1, z.val.1)) (r : unitInterval) :
    stageJoinHomotopy p f H k hEnd s t (r,z) = stageToPullback p f H k hEnd s z := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  refine Prod.ext rfl ?_
  apply ContinuousMap.ext
  intro q
  exact (h _).trans (h _).symm

/-- Removing a constant prefix is the same actual time-path homotopy with
its first segment collapsed. -/
def stageUnpadHomotopy (s : unitInterval) :
    ((appendToPullback p f H k hEnd s).comp
      (HomotopyPullback.strictPullbackInclusion p (slice H s))).Homotopy
        (stageToPullback p f H k hEnd s) :=
  (stageJoinHomotopy p f H k hEnd s s).cast
    (by rw [stageSegment_self]) rfl

theorem stageUnpadHomotopy_fixed (s : unitInterval) (z : Stage p H s)
    (h : ∀ r, H (r, z.val.1) = H (1, z.val.1)) (r : unitInterval) :
    stageUnpadHomotopy p f H k hEnd s (r,z) = stageToPullback p f H k hEnd s z :=
  stageJoinHomotopy_fixed p f H k hEnd s s z h r

/-- The final stage is an actual point of the original strict pullback. -/
def stageFinalMap : C(Stage p H 1,{z : X × E // p z.2 = f z.1}) where
  toFun z := ⟨(k z.val.1,z.val.2),z.property.trans (hEnd z.val.1)⟩
  continuous_toFun := by fun_prop

/-- The last remaining tail is literally constant in the original target. -/
theorem stageToPullback_one : stageToPullback p f H k hEnd 1 =
    (HomotopyPullback.strictPullbackInclusion p f).comp (stageFinalMap p f H k hEnd) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  refine Prod.ext rfl ?_
  refine Prod.ext rfl ?_
  apply ContinuousMap.ext
  intro r
  change H (affineTime 1 1 r,z.val.1) = f (k z.val.1)
  rw [affineTime_self]
  exact hEnd z.val.1

end Topology.PathSubdivision
