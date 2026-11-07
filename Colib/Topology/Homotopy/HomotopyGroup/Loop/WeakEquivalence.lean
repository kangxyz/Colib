/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift
public import Colib.Topology.HomotopyFiber.WeakSquareTransport

/-!
# Complete weak equivalences of actual based loop spaces

The literal based loop space is homeomorphic to the homotopy fiber of the
chosen point. Weak invariance of that fiber proves that the unchanged
`basedLoopMap` is a complete weak equivalence, including all components and
all homotopy degrees at every loop. No separation or connectivity hypothesis
is imposed on the spaces or their loop spaces.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/Loop/WeakEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, basepoints,
coefficients and signs are retained with native Colib dependencies. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
universe u
namespace Topology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The literal based loop space is the actual homotopy fiber of its chosen point. -/
def loopHomotopyFiberHomeomorph (x : X) :
    Path x x ≃ₜ HomotopyFiber (ContinuousMap.const PUnit.{u + 1} x) x where
  toFun := HomotopyFiber.loopInclusion (ContinuousMap.const PUnit.{u + 1} x) x PUnit.unit rfl
  invFun z := { toContinuousMap := z.1.2, source' := z.2.1, target' := z.2.2 }
  left_inv γ := by apply Path.ext; funext t; rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  continuous_toFun :=
    (HomotopyFiber.loopInclusion (ContinuousMap.const PUnit.{u + 1} x) x PUnit.unit rfl).continuous
  continuous_invFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : HomotopyFiber (ContinuousMap.const PUnit.{u + 1} x) x ×
      unitInterval ↦ z.1.1.2 z.2)
    fun_prop

/-- The comparison retains the whole original loop, with no reparametrization. -/
@[simp] theorem loopHomotopyFiberHomeomorph_path (x : X) (γ : Path x x) :
    (loopHomotopyFiberHomeomorph x γ).1.2 = γ.toContinuousMap := rfl

/-- A complete weak equivalence induces a complete weak equivalence of the
actual based loop spaces, including every loop-space component. -/
theorem basedLoopMap_isWeakHomotopyEquivalence (f : C(X, Y)) {x : X} {y : Y}
    (h : f x = y) (hf : IsWeakHomotopyEquivalence f) :
    IsWeakHomotopyEquivalence (basedLoopMap f h) := by
  subst y
  let e₁ := loopHomotopyFiberHomeomorph x
  let e₂ := (loopHomotopyFiberHomeomorph (f x)).symm
  have hw := HomotopyFiber.map_isWeakHomotopyEquivalence
    (p := ContinuousMap.const PUnit.{u + 1} x)
    (q := ContinuousMap.const PUnit.{u + 1} (f x))
    (ContinuousMap.id PUnit.{u + 1}) f rfl
    (isWeakHomotopyEquivalence_of_homotopyEquiv
      (Homeomorph.refl PUnit.{u + 1}).toHomotopyEquiv) hf x
  have hh := (isWeakHomotopyEquivalence_of_homotopyEquiv e₂.toHomotopyEquiv).comp
    (hw.comp (isWeakHomotopyEquivalence_of_homotopyEquiv e₁.toHomotopyEquiv))
  exact hh

end Topology
