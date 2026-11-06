/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.PathSubdivision.SlabCover
public import Mathlib.Topology.Homotopy.Path

/-!
# Literal affine time paths and their concatenation homotopy

Concatenating two original time segments and then removing that subdivision
is an explicit homotopy through time paths with both endpoints fixed. Every
subsequent application to a family evaluates the original family at the
current parameter, rather than attempting a vertical correction.


Implementation provenance:
`Quillen/Topology/PathSubdivision/TimePaths.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.CubicalSubdivision


noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.PathSubdivision
open CubicalSubdivision

/-- Actual affine interpolation between two points of the unit interval. -/
def affineTime (a b t : unitInterval) : unitInterval :=
  ⟨(1-(t : ℝ))*(a : ℝ)+(t : ℝ)*(b : ℝ),by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
        (mul_nonneg t.property.1 b.property.1)
    · have h₀ := mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr t.property.2)
      have h₁ := mul_le_mul_of_nonneg_left b.property.2 t.property.1
      nlinarith⟩

@[fun_prop] theorem continuous_affineTime :
    Continuous (fun z : unitInterval × (unitInterval × unitInterval) ↦
      affineTime z.1 z.2.1 z.2.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun z : unitInterval × (unitInterval × unitInterval) ↦
    (1-(z.2.2 : ℝ))*(z.1 : ℝ)+(z.2.2 : ℝ)*(z.2.1 : ℝ))
  fun_prop

@[simp] theorem affineTime_zero (a b : unitInterval) : affineTime a b 0 = a := by
  apply Subtype.ext
  simp [affineTime]
@[simp] theorem affineTime_one (a b : unitInterval) : affineTime a b 1 = b := by
  apply Subtype.ext
  simp [affineTime]
@[simp] theorem affineTime_self (a t : unitInterval) : affineTime a a t = a := by
  apply Subtype.ext
  change (1-(t : ℝ))*(a : ℝ)+(t : ℝ)*(a : ℝ) = a
  ring
@[simp] theorem affineTime_zero_one (t : unitInterval) : affineTime 0 1 t = t := by
  apply Subtype.ext
  simp [affineTime]

/-- The actual time segment, with exact source and target. -/
def timePath (a b : unitInterval) : Path a b where
  toFun t := affineTime a b t
  continuous_toFun := by fun_prop
  source' := affineTime_zero a b
  target' := affineTime_one a b

@[simp] theorem timePath_apply (a b t : unitInterval) : timePath a b t = affineTime a b t := rfl

@[simp] theorem timePath_self (a : unitInterval) : timePath a a = Path.refl a := by
  ext t
  exact congrArg Subtype.val (affineTime_self a t)

/-- Each mesh slab is exactly the affine path between its original endpoints. -/
theorem timePath_intervalCell (m : ℕ) (i : Fin (m + 1)) (t : unitInterval) :
    timePath (intervalCell m i 0) (intervalCell m i 1) t = intervalCell m i t := by
  apply Subtype.ext
  change (1-(t : ℝ))*(((i : ℝ)+0)/(m+1))+
    (t : ℝ)*(((i : ℝ)+1)/(m+1)) = ((i : ℝ)+t)/(m+1)
  ring

/-- Removing a concatenation of time segments by explicit interpolation.
No ordering or strict interior assumption on the three times is needed. -/
def timeJoinHomotopy (a b c : unitInterval) :
    ((timePath a b).trans (timePath b c)).Homotopy (timePath a c) where
  toFun z := affineTime (((timePath a b).trans (timePath b c)) z.2) (timePath a c z.2) z.1
  continuous_toFun := by fun_prop
  map_zero_left t := affineTime_zero _ _
  map_one_left t := affineTime_one _ _
  prop' r t ht := by
    rcases ht with ht | ht
    · rw [ht]
      simp
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      simp

/-- The entire concatenation homotopy starts at the original first time. -/
theorem timeJoinHomotopy_source (a b c r : unitInterval) :
    timeJoinHomotopy a b c (r,0) = a := by simp [timeJoinHomotopy]

/-- The entire concatenation homotopy ends at the original final time. -/
theorem timeJoinHomotopy_target (a b c r : unitInterval) :
    timeJoinHomotopy a b c (r,1) = c := by simp [timeJoinHomotopy]

end Topology.PathSubdivision
