/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.ProjectionFibration
public import Colib.Topology.HomotopyFiber.GroupDetection

/-! # Genuine transport between the original fibers along a base path

A single displayed path induces an actual homotopy equivalence. Its forward
map keeps the original source coordinate and changes only the target path.
Naturality over a fixed base is strict. No continuously chosen family of
paths or global fiberwise inverse is used.

Implementation provenance:
`Quillen/Topology/HomotopyFiber/BasepointTransport.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original source coordinate,
base path and entire path parametrization are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology.HomotopyFiber
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- The displayed path as a homotopy between the actual point maps. -/
def pointMapHomotopy {b c : B} (γ : Path b c) :
    (ContinuousMap.const (ULift.{u} Unit) b).Homotopy (ContinuousMap.const _ c) where
  toFun z := γ z.1
  continuous_toFun := γ.continuous.comp continuous_fst
  map_zero_left _ := γ.source
  map_one_left _ := γ.target

/-- Reversing into the actual constant-map pullback and back transports the
original fiber along the displayed base path. -/
def basepointTransportEquiv (p : C(E, B)) {b c : B} (γ : Path b c) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber p b) (HomotopyFiber p c) :=
  (projectionPullbackHomeomorph p b).toHomotopyEquiv.trans
    ((HomotopyPullback.homotopyEquiv p (pointMapHomotopy γ)).trans
      (projectionPullbackHomeomorph p c).symm.toHomotopyEquiv)

/-- The original source point is unchanged by genuine transport. -/
@[simp] theorem basepointTransportEquiv_source (p : C(E, B)) {b c : B} (γ : Path b c)
    (z : HomotopyFiber p b) : (basepointTransportEquiv p γ z).val.1 = z.val.1 := rfl

/-- The new path is exactly the original path followed by the displayed
base path, with the standard concatenation parametrization. -/
@[simp] theorem basepointTransportEquiv_path (p : C(E, B)) {b c : B} (γ : Path b c)
    (z : HomotopyFiber p b) :
    (basepointTransportEquiv p γ z).val.2 = ((toPath p b z).trans γ).toContinuousMap := by
  change ((γ.symm.trans (toPath p b z).symm).symm).toContinuousMap = _
  rw [Path.trans_symm, Path.symm_symm, Path.symm_symm]

/-- Exact source-coordinate identity of the original continuous maps. -/
@[simp] theorem projection_basepointTransportEquiv (p : C(E, B)) {b c : B} (γ : Path b c) :
    (projection p c).comp (basepointTransportEquiv p γ).toFun = projection p b := rfl

/-- Transport commutes strictly with the original source-change fiber map. -/
theorem basepointTransportEquiv_mapOver (p : C(E, B)) (q : C(F, B)) (f : C(E, F))
    (sq : q.comp f = p) {b c : B} (γ : Path b c) :
    (basepointTransportEquiv q γ).toFun.comp (mapOver p q f sq b) =
      (mapOver p q f sq c).comp (basepointTransportEquiv p γ).toFun := by
  ext z
  rfl

/-- Strict naturality for an arbitrary original commuting square. The whole
original fiber path is postcomposed with the actual base map. -/
theorem basepointTransportEquiv_map {B' : Type u} [TopologicalSpace B']
    (p : C(E, B)) (q : C(F, B')) (f : C(E, F)) (v : C(B, B'))
    (sq : v.comp p = q.comp f) {b c : B} (γ : Path b c) :
    (basepointTransportEquiv q (γ.map v.continuous)).toFun.comp (map f v sq b) =
      (map f v sq c).comp (basepointTransportEquiv p γ).toFun := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    change (((pointMapHomotopy (γ.map v.continuous)).evalAt (⟨()⟩ : ULift.{u} Unit)).symm.trans
        ((toPath p b z).symm.map v.continuous)) (unitInterval.symm t) =
      v ((((pointMapHomotopy γ).evalAt (⟨()⟩ : ULift.{u} Unit)).symm.trans
        (toPath p b z).symm) (unitInterval.symm t))
    simp only [Path.trans_apply, Path.symm_apply, Path.map_coe, Function.comp_apply]
    split_ifs <;> rfl

end Topology.HomotopyFiber
