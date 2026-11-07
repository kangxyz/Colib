/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Fibration
public import Colib.Topology.HomotopyPullback.Symmetry

/-! # The genuine homotopy-fiber projection is a fibration

The projection is a pullback of the endpoint fibration for paths starting
at the fixed target point, with path reversal expressed by the existing
actual homotopy-pullback symmetry homeomorphism.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/ProjectionFibration.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- Transport the actual covering-homotopy lifting property along a source
homeomorphism, preserving the prescribed initial lift literally. -/
theorem HomotopyLiftingProperty.comp_homeomorph (p : C(E, B))
    (hp : HomotopyLiftingProperty p) (e : F ≃ₜ E) :
    HomotopyLiftingProperty (p.comp (e : C(F, E))) := by
  intro A _ a H hzero
  obtain ⟨L, hL₀, hL⟩ := hp A ((e : C(F, E)).comp a) H hzero
  refine ⟨(e.symm : C(E, F)).comp L, ?_, ?_⟩
  · intro a'
    change e.symm (L (0, a')) = a a'
    rw [hL₀]
    exact e.symm_apply_apply _
  · intro t a'
    change p (e (e.symm (L (t, a')))) = H (t, a')
    rw [e.apply_symm_apply]
    exact hL t a'

namespace HomotopyFiber
variable (f : C(E, B)) (b : B)

/-- Adding the unique constant parameter identifies the original homotopy
fiber with its literal homotopy-pullback presentation. -/
def constantParameterHomeomorph : HomotopyFiber f b ≃ₜ
    HomotopyPullback f (ContinuousMap.const (ULift.{u} Unit) b) where
  toFun z := ⟨(⟨()⟩, z.1), z.2⟩
  invFun z := ⟨z.1.2, z.2⟩
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Reversing the genuine path turns the fiber projection into the canonical
base projection of a homotopy pullback. -/
def projectionPullbackHomeomorph : HomotopyFiber f b ≃ₜ
    HomotopyPullback (ContinuousMap.const (ULift.{u} Unit) b) f :=
  (constantParameterHomeomorph f b).trans
    (HomotopyPullback.symmetryHomeomorph f (ContinuousMap.const (ULift.{u} Unit) b))

/-- The actual source projection, with its compact-open path topology, has
covering-homotopy lifting for all parameter spaces in the displayed universe. -/
theorem projection_homotopyLiftingProperty : HomotopyLiftingProperty (projection f b) :=
  HomotopyLiftingProperty.comp_homeomorph
    (HomotopyPullback.baseProjection (ContinuousMap.const (ULift.{u} Unit) b) f)
    (HomotopyPullback.baseProjection_homotopyLiftingProperty
      (ContinuousMap.const (ULift.{u} Unit) b) f) (projectionPullbackHomeomorph f b)

end HomotopyFiber
end Topology
