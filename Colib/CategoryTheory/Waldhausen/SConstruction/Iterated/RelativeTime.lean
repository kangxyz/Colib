/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.SplitFiber

/-!
# The original ordinal time extension

Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/RelativeCylinder.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, ordinal parameters, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Simplicial
namespace CategoryTheory.Waldhausen.IteratedS

open Fibration.RelativeRows

/-- Extend the actual time parameter by the new initial zero vertex. -/
def relativeTime {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) : addInitial.obj n ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk {
    toFun := Fin.cases 0 τ.toOrderHom
    monotone' := by
      intro i j h
      cases i using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ i =>
        cases j using Fin.cases with
        | zero => have h' : i.val + 1 ≤ 0 := h; omega
        | succ j => exact τ.toOrderHom.monotone (Nat.le_of_succ_le_succ h) }

lemma relativeTime_reindex {m n : SimplexCategory} (α : m ⟶ n) (τ : n ⟶ ⦋1⦌) :
    addInitial.map α ≫ relativeTime τ = relativeTime (α ≫ τ) := by
  ext i : 3
  cases i using Fin.cases <;> rfl

lemma relativeTime_tail {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    tail.app n ≫ relativeTime τ = τ := by ext i : 3; rfl

lemma relativeTime_zero (n : SimplexCategory) :
    relativeTime (n.const ⦋1⦌ 0) = (addInitial.obj n).const ⦋1⦌ 0 := by
  ext i : 3
  cases i using Fin.cases <;> rfl

lemma relativeTime_one (n : SimplexCategory) :
    relativeTime (n.const ⦋1⦌ 1) = fiberOrdinal n := rfl

end CategoryTheory.Waldhausen.IteratedS
