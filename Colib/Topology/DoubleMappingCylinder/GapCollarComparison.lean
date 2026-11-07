/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.Gap
public import Colib.Topology.DoubleMappingCylinder.BandContraction
public import Colib.Topology.HomotopyPullback.OverlapPaths
public import Colib.Topology.HomotopyPullback.Symmetry

/-!
# The original full cylinder gap and its actual collar comparison

The midpoint section of the literal overlap band is a genuine homotopy equivalence. On targets,
the original endpoint collar inclusions induce the actual path-preserving homotopy equivalence
of homotopy pullbacks. The resulting square commutes by an explicit homotopy shrinking the full
cylinder time to the selected band time. Both moving endpoints stay in their actual collars,
and the source point, deformation time and original stored path time are all retained.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/GapCollarComparison.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat.DoubleCylinder

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (lo hi : unitInterval)

/-- The original open band, with its exact product coordinates and actual overlap codomain. -/
def gapOverlapHomeomorph : A × Band lo hi ≃ₜ
    ↥(leftCollarSet f g sq hi ∩ rightCollarSet f g sq lo) :=
  (bandHomeomorph f g sq lo hi).trans {
    toFun z := ⟨z.val, z.property.2, z.property.1⟩
    invFun z := ⟨z.val, z.property.2, z.property.1⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-- The original source maps to its selected actual cylinder height, with an explicit inverse. -/
def gapOverlapEquiv (c : Band lo hi) : ContinuousMap.HomotopyEquiv A
    ↥(leftCollarSet f g sq hi ∩ rightCollarSet f g sq lo) :=
  (bandProjectionHomotopyEquiv lo hi A c).symm.trans
    (gapOverlapHomeomorph f g sq lo hi).toHomotopyEquiv

/-- The source equivalence uses exactly the original cylinder at the supplied band time. -/
@[simp] theorem gapOverlapEquiv_apply (c : Band lo hi) (a : A) :
    ((gapOverlapEquiv f g sq lo hi c).toFun a).val = l (a, ULift.up c.val) := rfl

/-- The original endpoint inclusions induce the path-preserving target equivalence. -/
def gapTargetCollarEquiv (hhi : 0 < hi) (hlo : lo < 1) :
    ContinuousMap.HomotopyEquiv
      (HomotopyPullback (gapLeftEndpoint e) (gapRightEndpoint e))
      (HomotopyPullback (ContinuousMap.subtypeVal (leftCollarSet f g sq hi))
        (ContinuousMap.subtypeVal (rightCollarSet f g sq lo))) :=
  (HomotopyPullback.sourceEquiv (gapRightEndpoint e)
    (ContinuousMap.subtypeVal (leftCollarSet f g sq hi))
    (leftCollarStrongDeformationRetract f g sq hi hhi).toHomotopyEquiv).trans
      (HomotopyPullback.parameterEquiv (ContinuousMap.subtypeVal (leftCollarSet f g sq hi))
        (ContinuousMap.subtypeVal (rightCollarSet f g sq lo))
        (rightCollarStrongDeformationRetract f g sq lo hlo).toHomotopyEquiv)

/-- The target comparison keeps the actual original stored path unchanged. -/
@[simp] theorem gapTargetCollarEquiv_path (hhi : 0 < hi) (hlo : lo < 1)
    (z : HomotopyPullback (gapLeftEndpoint e) (gapRightEndpoint e)) (t : unitInterval) :
    ((gapTargetCollarEquiv f g sq lo hi hhi hlo).toFun z).val.2.2 t = z.val.2.2 t := rfl

/-- The actual simultaneous deformation of every original cylinder path. -/
def gapCollarTrack (c : Band lo hi) : C(unitInterval × (unitInterval × A), D) :=
  ⟨fun z ↦ (gap f g sq z.2.2).val.2.2 (Set.Icc.convexComb z.2.1 c.val z.1), by
    change Continuous (fun z : unitInterval × (unitInterval × A) ↦
      l (z.2.2, ULift.up (Set.Icc.convexComb z.2.1 c.val z.1)))
    exact l.hom.continuous.comp (by fun_prop)⟩

/-- The left moving endpoint remains below the original upper collar cut. -/
theorem gapCollarTrack_zero_mem (c : Band lo hi) (r : unitInterval) (a : A) :
    gapCollarTrack f g sq lo hi c (r, 0, a) ∈ leftCollarSet f g sq hi := by
  change height f g sq (l (a, ULift.up (Set.Icc.convexComb 0 c.val r))) < hi
  rw [height_cylinder]
  exact lt_of_le_of_lt (Set.Icc.convexComb_le bot_le r) c.property.2

/-- The right moving endpoint remains above the original lower collar cut. -/
theorem gapCollarTrack_one_mem (c : Band lo hi) (r : unitInterval) (a : A) :
    gapCollarTrack f g sq lo hi c (r, 1, a) ∈ rightCollarSet f g sq lo := by
  change lo < height f g sq (l (a, ULift.up (Set.Icc.convexComb 1 c.val r)))
  rw [height_cylinder]
  apply lt_of_lt_of_le c.property.1
  change (c.val : ℝ) ≤ (1 - (r : ℝ)) * 1 + (r : ℝ) * (c.val : ℝ)
  nlinarith [c.val.property.2, r.property.2]

/-- The explicit original homotopy square, with no strictification or replacement gap map. -/
def gapCollarHomotopy (c : Band lo hi) (hhi : 0 < hi) (hlo : lo < 1) :
    ((gapTargetCollarEquiv f g sq lo hi hhi hlo).toFun.comp (gap f g sq)).Homotopy
      ((HomotopyPullback.overlapComparison (leftCollarSet f g sq hi)
        (rightCollarSet f g sq lo)).comp (gapOverlapEquiv f g sq lo hi c).toFun) where
  toFun z := ⟨(⟨gapCollarTrack f g sq lo hi c (z.1, 1, z.2),
      gapCollarTrack_one_mem f g sq lo hi c z.1 z.2⟩,
    ⟨gapCollarTrack f g sq lo hi c (z.1, 0, z.2),
      gapCollarTrack_zero_mem f g sq lo hi c z.1 z.2⟩,
    ⟨fun t ↦ gapCollarTrack f g sq lo hi c (z.1, t, z.2), by fun_prop⟩), rfl, rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × A) × unitInterval ↦
      gapCollarTrack f g sq lo hi c (z.1.1, z.2, z.1.2))
    fun_prop
  map_zero_left a := by
    apply HomotopyPullback.overlap_path_ext
    apply ContinuousMap.ext
    intro t
    change l (a, ULift.up (Set.Icc.convexComb t c.val 0)) = l (a, ULift.up t)
    rw [Set.Icc.convexComb_zero]
  map_one_left a := by
    apply HomotopyPullback.overlap_path_ext
    apply ContinuousMap.ext
    intro t
    change l (a, ULift.up (Set.Icc.convexComb t c.val 1)) = l (a, ULift.up c.val)
    rw [Set.Icc.convexComb_one]

/-- The homotopy retains all three original parameters in its stored path. -/
@[simp] theorem gapCollarHomotopy_path (c : Band lo hi) (hhi : 0 < hi) (hlo : lo < 1)
    (r t : unitInterval) (a : A) :
    (gapCollarHomotopy f g sq lo hi c hhi hlo (r, a)).val.2.2 t =
      l (a, ULift.up (Set.Icc.convexComb t c.val r)) := rfl

end TopCat.DoubleCylinder
