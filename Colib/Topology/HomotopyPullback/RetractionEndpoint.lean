/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.RetractionBaseChange

/-! The actual end square of a genuine pullback over a collar is homotopy
cartesian, with its canonical endpoint comparison. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyPullback/RetractionEndpoint.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology
namespace TopCat.RetractionPullback
variable {B X E : TopCat.{u}} {i : B ⟶ X}
  (R : TopCat.CylinderStrongDeformationRetract i) (p : E ⟶ B)

/-- The projection from the strict pullback of `p` along the collar retraction to its collar
coordinate in `X`. -/
abbrev projection : C(Space R p, X) := HomotopyPullback.strictBaseProjection p.hom R.r.hom

theorem endpoint_square : (projection R p).comp (inclusion R p) = i.hom.comp p.hom := rfl

/-- Pulling the actual collar pullback back to its end recovers the
original total space homeomorphically. -/
def endpointPullbackHomeomorph :
    E ≃ₜ {z : B × Space R p // projection R p z.2 = i z.1} where
  toFun e := ⟨(p e, inclusion R p e), rfl⟩
  invFun z := z.1.2.1.2
  left_inv _ := rfl
  right_inv z := by
    have hx : z.1.2.1.1 = i z.1.1 := z.2
    have he : p z.1.2.1.2 = z.1.1 := by
      exact z.1.2.2.trans ((congrArg R.r hx).trans (ConcreteCategory.congr_hom R.retract z.1.1))
    apply Subtype.ext
    apply Prod.ext
    · exact he
    · apply Subtype.ext
      exact Prod.ext ((congrArg i he).trans hx.symm) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The canonical square over the base-collar end is homotopy cartesian
as soon as the original vertical map is a genuine fibration. -/
def endpointHomotopyEquiv (hp : HomotopyLiftingProperty p.hom) :
    ContinuousMap.HomotopyEquiv E (HomotopyPullback (projection R p) i.hom) :=
  (endpointPullbackHomeomorph R p).toHomotopyEquiv.trans
    (HomotopyPullback.strictPullbackHomotopyEquivOfLifting (projection R p) i.hom
      (HomotopyLiftingProperty.baseChange _ _ hp))

@[simp] theorem endpointHomotopyEquiv_toFun (hp : HomotopyLiftingProperty p.hom) :
    (endpointHomotopyEquiv R p hp).toFun =
      HomotopyPullback.comparison (projection R p) i.hom p.hom (inclusion R p)
        (endpoint_square R p) := rfl

end TopCat.RetractionPullback
