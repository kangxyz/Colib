/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.Band

/-!
# The original band projection as an explicit homotopy equivalence

The open interval factor is contracted to a supplied actual point of that same band, by
straight interpolation. The product projection retains its literal first-coordinate map.
No separation condition on the other factor or quotient base-change assumption is needed.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/BandContraction.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

open scoped Topology unitInterval

universe u

namespace TopCat.DoubleCylinder

variable (lo hi : unitInterval)

/-- The explicit midpoint supplies a point in every nonempty ordered height band. -/
def bandMidpoint (h : lo < hi) : Band lo hi :=
  ⟨⟨((lo : ℝ) + hi) / 2, by
    constructor <;> linarith [lo.property.1, lo.property.2, hi.property.1, hi.property.2]⟩, by
    change (lo : ℝ) < hi at h
    constructor
    · change (lo : ℝ) < ((lo : ℝ) + hi) / 2
      linarith
    · change ((lo : ℝ) + hi) / 2 < (hi : ℝ)
      linarith⟩

/-- The chosen band point is the actual arithmetic midpoint of the two supplied cutoffs. -/
@[simp] theorem bandMidpoint_val (h : lo < hi) :
    ((bandMidpoint lo hi h).val : ℝ) = ((lo : ℝ) + hi) / 2 := rfl

/-- Straight interpolation stays in the original open band, including at both times. -/
def bandInterpolation (c : Band lo hi) : C(unitInterval × Band lo hi, Band lo hi) where
  toFun z := ⟨Set.Icc.convexComb c.val z.2.val z.1, by
    rcases le_total c.val z.2.val with h | h
    · exact ⟨c.property.1.trans_le (Set.Icc.le_convexComb h z.1),
        (Set.Icc.convexComb_le h z.1).trans_lt z.2.property.2⟩
    · rw [← Set.Icc.convexComb_symm]
      exact ⟨z.2.property.1.trans_le (Set.Icc.le_convexComb h (unitInterval.symm z.1)),
        (Set.Icc.convexComb_le h (unitInterval.symm z.1)).trans_lt c.property.2⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Set.Icc.continuous_convexComb_prod.comp
      (continuous_const.prodMk (continuous_snd.subtype_val.prodMk continuous_fst))

@[simp] theorem bandInterpolation_zero (c z : Band lo hi) :
    bandInterpolation lo hi c (0, z) = c :=
  Subtype.ext (Set.Icc.convexComb_zero c.val z.val)

@[simp] theorem bandInterpolation_one (c z : Band lo hi) :
    bandInterpolation lo hi c (1, z) = z :=
  Subtype.ext (Set.Icc.convexComb_one c.val z.val)

@[simp] theorem bandInterpolation_fixed (c : Band lo hi) (t : unitInterval) :
    bandInterpolation lo hi c (t, c) = c :=
  Subtype.ext (Set.Icc.convexComb_eq c.val t)

/-- The original projection away from the open band has the displayed constant-band inverse. -/
def bandProjectionHomotopyEquiv (X : Type u) [TopologicalSpace X] (c : Band lo hi) :
    ContinuousMap.HomotopyEquiv (X × Band lo hi) X where
  toFun := ContinuousMap.fst
  invFun := (ContinuousMap.id X).prodMk (ContinuousMap.const X c)
  left_inv := ⟨{
    toFun z := (z.2.1, bandInterpolation lo hi c (z.1, z.2.2))
    continuous_toFun := by fun_prop
    map_zero_left x := Prod.ext rfl (bandInterpolation_zero lo hi c x.2)
    map_one_left x := Prod.ext rfl (bandInterpolation_one lo hi c x.2) }⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id X)⟩

@[simp] theorem bandProjectionHomotopyEquiv_toFun (X : Type u) [TopologicalSpace X]
    (c : Band lo hi) : (bandProjectionHomotopyEquiv lo hi X c).toFun = ContinuousMap.fst := rfl

end TopCat.DoubleCylinder
