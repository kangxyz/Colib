/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.MixedNerve
public import Colib.Topology.Realization.HomotopyBridge
public import Mathlib.Topology.Homotopy.Equiv

/-! # Realized categorical equivalences with independent hom universes

Adapted from `Quillen/Waldhausen/QuillenComparison/MixedNerve.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Both nerves are the existing native
category nerves; only the unnecessary equality of hom universes is removed.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial
universe u v w

namespace CategoryTheory.MixedNerve

variable {C D : Type (max u v w)} [Category.{v} C] [Category.{w} D]

/-- Categorical equivalences induce realization homotopy equivalences with
the exact postcomposition nerve map, even when the hom universes differ. -/
def realizationEquivalence (e : C ≌ D) :
    ContinuousMap.HomotopyEquiv |nerve C| |nerve D| where
  toFun := (SSet.toTop.map (nerveMap.{u, v, w} e.functor)).hom
  invFun := (SSet.toTop.map (nerveMap.{u, w, v} e.inverse)).hom
  left_inv := by
    have h := SSet.realizationSimplicialHomotopy (homotopy.{max u w, v, v} e.unitIso.hom)
    have h₀ : nerveMap.{max u w, v, v} (𝟭 C) = 𝟙 (nerve C) := rfl
    have h₁ : nerveMap.{max u w, v, v} (e.functor ⋙ e.inverse) =
        nerveMap.{u, v, w} e.functor ≫ nerveMap.{u, w, v} e.inverse := rfl
    rw [h₀, h₁, SSet.toTop.map_id, SSet.toTop.map_comp] at h
    exact ⟨h.symm⟩
  right_inv := by
    have h := SSet.realizationSimplicialHomotopy (homotopy.{max u v, w, w} e.counitIso.hom)
    have h₀ : nerveMap.{max u v, w, w} (𝟭 D) = 𝟙 (nerve D) := rfl
    have h₁ : nerveMap.{max u v, w, w} (e.inverse ⋙ e.functor) =
        nerveMap.{u, w, v} e.inverse ≫ nerveMap.{u, v, w} e.functor := rfl
    rw [h₀, h₁, SSet.toTop.map_id, SSet.toTop.map_comp] at h
    exact ⟨h⟩

@[simp]
theorem realizationEquivalence_toFun (e : C ≌ D) :
    (realizationEquivalence.{u, v, w} e).toFun = (SSet.toTop.map (nerveMap.{u, v, w} e.functor)).hom
      := rfl

end CategoryTheory.MixedNerve
