/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.Path

/-! # Transposition of the two actual based-loop parameters

The double-loop coordinate interchange fixes all four edges and is an involutive homeomorphism.
-/
/-! Implementation provenance: the existing native operation is extracted from
`Colib/Topology/HomotopyFiber/ConnectingLoopPathClass.lean`, itself adapted from
`Quillen/Topology/HomotopyFiber/ConnectingLoopPathClass.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The application no longer owns this generic map.
The application formula and homeomorphism are from
`Quillen/Topology/Prespectrum/ParameterLooping.lean` at that same revision. -/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u
namespace Path
variable {X : Type u} [TopologicalSpace X]

/-- The two original loop parameters are interchanged, with all boundary values retained. -/
def doubleLoopTranspose (x : X) :
    C(Path (Path.refl x) (Path.refl x), Path (Path.refl x) (Path.refl x)) where
  toFun β := {
    toFun s := {
      toFun t := β t s
      continuous_toFun := by fun_prop
      source' := by rw [β.source]; rfl
      target' := by rw [β.target]; rfl }
    continuous_toFun := by
      apply Path.continuous_uncurry_iff.mp
      change Continuous (fun a : unitInterval × unitInterval ↦ β a.2 a.1)
      fun_prop
    source' := by ext t; exact (β t).source
    target' := by ext t; exact (β t).target }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun a : ((Path (Path.refl x) (Path.refl x) × unitInterval) ×
      unitInterval) ↦ a.1.1 a.2 a.1.2)
    fun_prop

/-- The original transpose preserves the specified constant double loop. -/
theorem doubleLoopTranspose_refl (x : X) :
    doubleLoopTranspose x (Path.refl (Path.refl x)) = Path.refl (Path.refl x) := by
  ext s t
  rfl

/-- Transposition interchanges the two original evaluation coordinates. -/
@[simp] theorem doubleLoopTranspose_apply (x : X)
    (γ : Path (Path.refl x) (Path.refl x)) (s t : unitInterval) :
    doubleLoopTranspose x γ s t = γ t s := rfl

/-- The parameter transpose is an actual involutive homeomorphism. -/
def doubleLoopTransposeHomeomorph {X : Type u} [TopologicalSpace X] (x : X) :
    Path (Path.refl x) (Path.refl x) ≃ₜ Path (Path.refl x) (Path.refl x) where
  toFun := doubleLoopTranspose x
  invFun := doubleLoopTranspose x
  left_inv γ := by apply Path.ext; funext s; apply Path.ext; funext t; rfl
  right_inv γ := by apply Path.ext; funext s; apply Path.ext; funext t; rfl
  continuous_toFun := (doubleLoopTranspose x).continuous
  continuous_invFun := (doubleLoopTranspose x).continuous

end Path
