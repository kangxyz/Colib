/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DeformationRetract.Basic
public import Colib.Topology.FiberwiseMappingPath.BaseChange

/-! # Actual base change of a fiberwise strong deformation retract

Every new parameter is retained literally. The supplied entire deformation
preserves the displayed base, so its retraction and homotopy restrict to every
matched pullback without a quotient or pushout preservation assumption.


Implementation provenance:
`Quillen/Topology/DeformationRetract/FiberwiseBaseChange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.FiberwiseMappingPath


noncomputable section
open Topology TopCat
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.CylinderStrongDeformationRetract
open FiberwiseMappingPath
variable {A C B : TopCat.{u}} {i : A ⟶ C}
  (R : TopCat.CylinderStrongDeformationRetract i) (q : C ⟶ B)
  (hR : R.H ≫ q = fst C TopCat.I ≫ q)
  {D : Type u} [TopologicalSpace D] (g : C(D, B))

/-- The genuine fiberwise deformation gives an actual homotopy equivalence
on the original strict pullback, with its canonical inclusion forward. -/
def baseChangeHomotopyEquiv : ContinuousMap.HomotopyEquiv
    (BaseChangedSource q.hom i.hom g) (BaseChangedTarget q.hom g) := by
  have hr (c : C) : q (i (R.r c)) = q c := by
    have hh := ConcreteCategory.congr_hom hR (c,ULift.up 0)
    have hzero := ConcreteCategory.congr_hom R.H₀ c
    change q (R.H (c,ULift.up 0)) = q c at hh
    change R.H (c,ULift.up 0) = i (R.r c) at hzero
    rw [hzero] at hh
    exact hh
  let j := baseChangedMap q.hom i.hom g
  let r : C(BaseChangedTarget q.hom g,BaseChangedSource q.hom i.hom g) := {
    toFun x := ⟨(x.val.1,R.r x.val.2),(hr _).trans x.property⟩
    continuous_toFun := by fun_prop }
  refine { toFun := j,invFun := r,left_inv := ?_,right_inv := ?_ }
  · have heq : r.comp j = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      exact Prod.ext rfl (ConcreteCategory.congr_hom R.retract x.val.2)
    rw [heq]
  · refine ⟨{
      toFun z := ⟨(z.2.val.1,R.H (z.2.val.2,ULift.up z.1)),
        (ConcreteCategory.congr_hom hR (z.2.val.2,ULift.up z.1)).trans z.2.property⟩
      continuous_toFun := by fun_prop
      map_zero_left x := ?_
      map_one_left x := ?_ }⟩
    · apply Subtype.ext
      exact Prod.ext rfl (ConcreteCategory.congr_hom R.H₀ x.val.2)
    · apply Subtype.ext
      exact Prod.ext rfl (ConcreteCategory.congr_hom R.H₁ x.val.2)

@[simp] theorem baseChangeHomotopyEquiv_toFun :
    (R.baseChangeHomotopyEquiv q hR g).toFun = baseChangedMap q.hom i.hom g := rfl

end TopCat.CylinderStrongDeformationRetract
