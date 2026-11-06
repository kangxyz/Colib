/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.ProjectionFibration

/-! # The original fiber projection over an explicitly contracted base

A specified base contraction makes its actual one-point inclusion a
homotopy equivalence. The existing parameter equivalence of homotopy
pullbacks then proves that the original homotopy-fiber projection is a
genuine homotopy equivalence, without any fibration hypothesis on the map.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/ContractibleBase.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology.HomotopyFiber
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]

/-- The actual point inclusion is an equivalence when the displayed base
contracts to that point; its inverse is the unique map to a point. -/
def pointInclusionEquiv (b : B)
    (H : (ContinuousMap.id B).Homotopy (ContinuousMap.const B b)) :
    ContinuousMap.HomotopyEquiv (ULift.{u} Unit) B where
  toFun := ContinuousMap.const _ b
  invFun := ContinuousMap.const _ ⟨()⟩
  left_inv := by
    have h : (ContinuousMap.const (ULift.{u} Unit) (⟨()⟩ : ULift.{u} Unit)) =
        ContinuousMap.id (ULift.{u} Unit) := by
      ext x
    change (ContinuousMap.const (ULift.{u} Unit) (⟨()⟩ : ULift.{u} Unit)).Homotopic _
    rw [h]
  right_inv := ⟨H.symm⟩

/-- The genuine homotopy-fiber projection is an actual equivalence over the
specified contracted base, with its original source coordinate unchanged. -/
def projectionEquivOfContraction (p : C(E, B)) (b : B)
    (H : (ContinuousMap.id B).Homotopy (ContinuousMap.const B b)) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber p b) E :=
  (constantParameterHomeomorph p b).toHomotopyEquiv.trans
    (HomotopyPullback.sourceProjectionEquivOfParameterEquiv p
      (ContinuousMap.const (ULift.{u} Unit) b) (pointInclusionEquiv b H) rfl)

@[simp] theorem projectionEquivOfContraction_toFun (p : C(E, B)) (b : B)
    (H : (ContinuousMap.id B).Homotopy (ContinuousMap.const B b)) :
    (projectionEquivOfContraction p b H).toFun = projection p b := rfl

/-- The original inclusion of an actual strict fiber in its total space. -/
def strictFiberToSource (p : C(E, B)) (b : B) : C({x : E // p x = b}, E) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- For a genuine fibration, the original strict-fiber inclusion is likewise
an actual homotopy equivalence over the contracted base. -/
def strictFiberEquivOfContraction (p : C(E, B)) (hp : HomotopyLiftingProperty p)
    (b : B) (H : (ContinuousMap.id B).Homotopy (ContinuousMap.const B b)) :
    ContinuousMap.HomotopyEquiv {x : E // p x = b} E :=
  (strictFiberHomotopyEquivOfLifting p hp b).trans (projectionEquivOfContraction p b H)

@[simp] theorem strictFiberEquivOfContraction_toFun
    (p : C(E, B)) (hp : HomotopyLiftingProperty p)
    (b : B) (H : (ContinuousMap.id B).Homotopy (ContinuousMap.const B b)) :
    (strictFiberEquivOfContraction p hp b H).toFun = strictFiberToSource p b := rfl

end Topology.HomotopyFiber
