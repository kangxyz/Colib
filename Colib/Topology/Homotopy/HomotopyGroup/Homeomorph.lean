/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Map

/-! # The actual forward homotopy-group map of a based homeomorphism

This direct inverse construction avoids importing the stronger unbased homotopy-equivalence
criterion when the comparison is already a homeomorphism. No inverse homotopy is assumed.
-/
@[expose] public noncomputable section
universe u v
namespace HomotopyGroup
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}

/-- The actual postcomposition map of a homeomorphism is a group isomorphism. -/
def homeomorphPiEquiv (e : X ≃ₜ Y) (h : e x = y) (n : ℕ) :
    Pi (n + 1) X x ≃* Pi (n + 1) Y y := by
  have hi : e.symm y = x := by rw [← h]; exact e.symm_apply_apply x
  let f := piMap n (e : C(X, Y)) h
  let g := piMap n (e.symm : C(Y, X)) hi
  have hgf : g.comp f = MonoidHom.id _ := by
    rw [← mapHom_comp]
    have he : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
      ext z
      exact e.symm_apply_apply z
    simp only [he]
    exact mapHom_id (N := Fin (n + 1))
  have hfg : f.comp g = MonoidHom.id _ := by
    rw [← mapHom_comp]
    have he : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y := by
      ext z
      exact e.apply_symm_apply z
    simp only [he]
    exact mapHom_id (N := Fin (n + 1))
  exact { f with
    invFun := g
    left_inv := fun a ↦ DFunLike.congr_fun hgf a
    right_inv := fun a ↦ DFunLike.congr_fun hfg a }

/-- No comparison is inserted into the forward homomorphism. -/
@[simp]
theorem homeomorphPiEquiv_coe (e : X ≃ₜ Y) (h : e x = y) (n : ℕ) :
    ↑(homeomorphPiEquiv e h n) = piMap n (e : C(X, Y)) h := rfl

end HomotopyGroup
