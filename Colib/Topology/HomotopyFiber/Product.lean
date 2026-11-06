/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.Equivalence

/-! # The actual homotopy fiber of a topological product projection

Implementation provenance:
`Quillen/Topology/HomotopyFiber/Product.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open scoped Topology
universe u v

namespace Topology.HomotopyFiber
variable (X : Type u) [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

/-- Reassociate the actual point/path pairs, without changing their topology. -/
def sndCoordinates (y : Y) : HomotopyFiber (ContinuousMap.snd : C(X × Y, Y)) y ≃ₜ
    X × HomotopyFiber (ContinuousMap.id Y) y where
  toFun z := (z.1.1.1, ⟨(z.1.1.2, z.1.2), z.2⟩)
  invFun z := ⟨((z.1, z.2.1.1), z.2.1.2), z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Projection away from the explicitly contracted identity fiber. -/
def identityFiberProductEquiv (y : Y) :
    ContinuousMap.HomotopyEquiv (X × HomotopyFiber (ContinuousMap.id Y) y) X where
  toFun := ContinuousMap.fst
  invFun := (ContinuousMap.id X).prodMk
    (ContinuousMap.const X (basepoint (ContinuousMap.id Y) y y rfl))
  left_inv := ⟨(ContinuousMap.Homotopy.refl ContinuousMap.fst).prodMk
    ((idContraction y).symm.comp (ContinuousMap.Homotopy.refl ContinuousMap.snd))⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id X)⟩

/-- The original first projection on the actual fiber is a homotopy equivalence. -/
def sndEquiv (y : Y) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber (ContinuousMap.snd : C(X × Y, Y)) y) X :=
  (sndCoordinates X y).toHomotopyEquiv.trans (identityFiberProductEquiv X y)

@[simp] theorem sndEquiv_toFun (y : Y) :
    (sndEquiv X y).toFun = ContinuousMap.fst.comp (projection ContinuousMap.snd y) := rfl

/-- Its inverse is exactly the constant-path inclusion of the original strict fiber. -/
@[simp] theorem sndEquiv_invFun_apply (y : Y) (x : X) :
    (sndEquiv X y).invFun x = basepoint ContinuousMap.snd y (x, y) rfl := rfl

end Topology.HomotopyFiber
