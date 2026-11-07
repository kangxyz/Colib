/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.ProjectionFibration
public import Colib.Topology.HomotopyFiber.GroupDetection

/-! # The original common-base homotopy-fiber square

The actual fiber of a composite is literally the strict pullback of the
actual fiber projection. That projection already has a proved covering-
homotopy lifting property, so the original constant-outer-path comparison
is a genuine homotopy equivalence. No lifting property of either original
map, nor any global realization theorem, is assumed.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/CommonBaseSquare.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.HomotopyFiber
variable {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (p : C(X, B)) (q : C(Y, B)) (j : C(X, Y)) (sq : q.comp j = p) (b : B)

/-- Retain the displayed source point and the whole original target path;
the new fiber source coordinate is the original map j applied to that point. -/
def commonBaseStrictPullbackHomeomorph : HomotopyFiber p b ≃ₜ
    {z : X × HomotopyFiber q b // projection q b z.2 = j z.1} where
  toFun z := ⟨(z.1.1, mapOver p q j sq b z), rfl⟩
  invFun z := ⟨(z.1.1, z.1.2.1.2),
    z.1.2.2.1.trans ((congrArg q z.2).trans (ContinuousMap.congr_fun sq z.1.1)), z.1.2.2.2⟩
  left_inv z := rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · exact z.2.symm
      · rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.fst.prodMk (mapOver p q j sq b).continuous
  continuous_invFun := by fun_prop

@[simp] theorem commonBaseStrictPullbackHomeomorph_source (z : HomotopyFiber p b) :
    (commonBaseStrictPullbackHomeomorph p q j sq b z).1.1 = z.1.1 := rfl

@[simp] theorem commonBaseStrictPullbackHomeomorph_fiber (z : HomotopyFiber p b) :
    (commonBaseStrictPullbackHomeomorph p q j sq b z).1.2 = mapOver p q j sq b z := rfl

/-- A map over the common base preserves every point of the stored path. -/
@[simp] theorem mapOver_path_apply (z : HomotopyFiber p b) (t : unitInterval) :
    (mapOver p q j sq b z).1.2 t = z.1.2 t := rfl

/-- The literal original fiber square, with its constant outer comparison path. -/
def commonBaseComparison : C(HomotopyFiber p b, HomotopyPullback (projection q b) j) :=
  HomotopyPullback.comparison (projection q b) j (projection p b) (mapOver p q j sq b) rfl

/-- Its homotopy equivalence follows from the proved lifting property of the
actual homotopy-fiber projection, with no lifting hypothesis on p or q. -/
def commonBaseComparisonEquiv :
    ContinuousMap.HomotopyEquiv (HomotopyFiber p b) (HomotopyPullback (projection q b) j) :=
  (commonBaseStrictPullbackHomeomorph p q j sq b).toHomotopyEquiv.trans
    (HomotopyPullback.strictPullbackHomotopyEquivOfLifting (projection q b) j
      (projection_homotopyLiftingProperty q b))

/-- The forward map is exactly the original common-base square comparison. -/
@[simp] theorem commonBaseComparisonEquiv_toFun :
    (commonBaseComparisonEquiv p q j sq b).toFun = commonBaseComparison p q j sq b := rfl

/-- The parameter is the original source coordinate. -/
@[simp] theorem commonBaseComparison_parameter (z : HomotopyFiber p b) :
    (commonBaseComparison p q j sq b z).1.1 = z.1.1 := rfl

/-- The fiber coordinate is precisely the original map over the common base. -/
@[simp] theorem commonBaseComparison_fiber (z : HomotopyFiber p b) :
    (commonBaseComparison p q j sq b z).1.2.1 = mapOver p q j sq b z := rfl

/-- The outer path is literally constant, with no extra concatenated segment. -/
@[simp] theorem commonBaseComparison_outerPath (z : HomotopyFiber p b) :
    (commonBaseComparison p q j sq b z).1.2.2 = ContinuousMap.const unitInterval (j z.1.1) := rfl

/-- The original square comparison is bijective on every finite based
homotopy degree, at every actual fiber point, including degree zero. -/
theorem commonBaseComparison_bijective (z : HomotopyFiber p b) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (commonBaseComparison p q j sq b)
      (x := z) rfl) :=
  homotopyGroupMap_bijective_of_homotopyEquiv (commonBaseComparisonEquiv p q j sq b) rfl n

end Topology.HomotopyFiber
