/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.Homotopy.Equiv

/-! # Actual homotopy equivalence from adjacent composite equivalences

Extracted from Quillen/Topology/HomotopyFiber/SourceEquivalence.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. No homotopy fiber is used by this
standalone construction. The forward map remains exactly the specified map.
-/
@[expose] public noncomputable section
namespace ContinuousMap.HomotopyEquiv

/-- Two adjacent composites being equivalences forces the outer forward map
to be an equivalence. This is an explicit homotopy-level two-out-of-six argument. -/
def ofAdjacentComposites {A B C D : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (a : C(A, B)) (b : C(C, A)) (c : C(D, C))
    (e₁ : ContinuousMap.HomotopyEquiv C B) (e₂ : ContinuousMap.HomotopyEquiv D A)
    (h₁ : e₁.toFun = a.comp b) (h₂ : e₂.toFun = b.comp c) :
    ContinuousMap.HomotopyEquiv A B where
  toFun := a
  invFun := b.comp e₁.invFun
  left_inv := by
    have hleft := e₁.left_inv
    have hright := e₂.right_inv
    rw [h₁] at hleft
    rw [h₂] at hright
    exact ((ContinuousMap.Homotopic.refl ((b.comp e₁.invFun).comp a)).comp hright.symm).trans
      (((((ContinuousMap.Homotopic.refl b).comp hleft).comp
        (ContinuousMap.Homotopic.refl c)).comp
          (ContinuousMap.Homotopic.refl e₂.invFun)).trans hright)
  right_inv := by
    have h := e₁.right_inv
    rw [h₁] at h
    exact h


end ContinuousMap.HomotopyEquiv
