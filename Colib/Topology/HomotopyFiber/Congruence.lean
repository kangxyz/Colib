/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.Basic

/-! Equal maps and endpoints give an identity-coordinate fiber homeomorphism.

Implementation source: `Quillen/CategoryTheory/TheoremB/VertexWeakAssembly.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Only dependency ownership changes. -/
@[expose] public noncomputable section
open scoped Topology
universe u

namespace Topology.HomotopyFiber
/-- Changing equal maps and endpoints retains the entire source/path pair. -/
def congrHomeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f = g) {a b : Y} (h' : a = b) :
    HomotopyFiber f a ≃ₜ HomotopyFiber g b where
  toFun z := ⟨z.1, by simpa only [← h, ← h'] using z.2⟩
  invFun z := ⟨z.1, by simpa only [h, h'] using z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
end Topology.HomotopyFiber
