/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.Map

/-! Actual homotopy fibers are naturally homeomorphic under a strict square
whose source and target maps are homeomorphisms. -/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/Homeomorph.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, paths and identity
basepoints are retained under native namespace and dependency ownership. -/
@[expose] public section

noncomputable section
open scoped Topology
universe u v w z
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

/-- Homeomorphisms of a strict arrow square induce an actual path-space fiber
homeomorphism, including postcomposition of the complete target path. -/
def homeomorphOfSquare (f : C(X, Y)) (g : C(X', Y'))
    (u : X ≃ₜ X') (v : Y ≃ₜ Y')
    (sq : (v : C(Y, Y')).comp f = g.comp u) (y : Y) :
    HomotopyFiber f y ≃ₜ HomotopyFiber g (v y) where
  toFun := map (f₁ := f) (f₂ := g) (u : C(X, X')) (v : C(Y, Y')) sq y
  invFun a := ⟨(u.symm a.1.1, (v.symm : C(Y', Y)).comp a.1.2), by
    change v.symm (a.1.2 0) = f (u.symm a.1.1)
    rw [a.2.1]
    apply v.injective
    rw [Homeomorph.apply_symm_apply]
    have h := ContinuousMap.congr_fun sq (u.symm a.1.1)
    simpa using h.symm,
    by change v.symm (a.1.2 1) = y; rw [a.2.2, Homeomorph.symm_apply_apply]⟩
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · exact u.symm_apply_apply _
    · apply ContinuousMap.ext
      intro t
      exact v.symm_apply_apply _
  right_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · exact u.apply_symm_apply _
    · apply ContinuousMap.ext
      intro t
      exact v.apply_symm_apply _
  continuous_toFun := (map (f₁ := f) (f₂ := g) (u : C(X, X')) (v : C(Y, Y')) sq y).continuous
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact u.symm.continuous.comp (projection g (v y)).continuous
    · exact (ContinuousMap.continuous_postcomp (v.symm : C(Y', Y))).comp (by fun_prop)

@[simp] theorem homeomorphOfSquare_apply (f : C(X, Y)) (g : C(X', Y'))
    (u : X ≃ₜ X') (v : Y ≃ₜ Y') (sq : (v : C(Y, Y')).comp f = g.comp u) (y : Y)
    (a : HomotopyFiber f y) :
    homeomorphOfSquare f g u v sq y a = map (f₁ := f) (f₂ := g) (u : C(X, X')) (v : C(Y, Y')) sq
      y a := rfl

end Topology.HomotopyFiber
