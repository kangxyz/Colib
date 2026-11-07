/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyPullback.Basic

/-!
# Literal point comparisons for actual homotopy fibers

Equality of the target point changes only the endpoint proof of a fiber. A homotopy pullback
along an actual map from a singleton parameter is the same original fiber, with its source
and entire path coordinates unchanged. These homeomorphisms retain those literal coordinates.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyFiber/PointComparison.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original objects, maps,
point hypotheses, whole stored cylinder paths and universe parameters are
retained. Native namespace and lower-import ownership are used. -/
@[expose] public section
noncomputable section
open scoped Topology
universe u
namespace Topology.HomotopyFiber
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))

/-- A target-point equality changes only the endpoint proof, preserving the full original path. -/
def basepointEqHomeomorph {y y' : Y} (h : y = y') :
    HomotopyFiber f y ≃ₜ HomotopyFiber f y' where
  toFun z := ⟨z.1, z.2.1, z.2.2.trans h⟩
  invFun z := ⟨z.1, z.2.1, z.2.2.trans h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The equality comparison retains the original source and whole path, literally. -/
@[simp] theorem basepointEqHomeomorph_val {y y' : Y} (h : y = y') (z : HomotopyFiber f y) :
    (basepointEqHomeomorph f h z).1 = z.1 := rfl

/-- A singleton parameter gives the original path-space fiber at its displayed value. -/
def singletonParameterHomeomorph (A : Type u) [TopologicalSpace A] [Subsingleton A]
    (g : C(A, Y)) (a : A) : HomotopyPullback f g ≃ₜ HomotopyFiber f (g a) where
  toFun z := ⟨z.1.2, z.2.1, z.2.2.trans (congrArg g (Subsingleton.elim _ _))⟩
  invFun z := ⟨(a, z.1), z.2⟩
  left_inv z := by apply Subtype.ext; exact Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- Removing the singleton parameter preserves the complete original path coordinates. -/
@[simp] theorem singletonParameterHomeomorph_val (A : Type u) [TopologicalSpace A]
    [Subsingleton A] (g : C(A, Y)) (a : A) (z : HomotopyPullback f g) :
    (singletonParameterHomeomorph f A g a z).1 = z.1.2 := rfl

end Topology.HomotopyFiber
