/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Reindex
public import Colib.CategoryTheory.Waldhausen.Rows.ReindexExact

/-! # The actual added-initial-vertex indexing of relative quotient rows

The new ordinal is literally `[n+1]`. Every map fixes the added vertex and
sends the original vertex `i+1` to `α(i)+1`, so tail restriction commutes
strictly with every original ordinal map.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/Index.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows

/-- Extend an ordinal map by fixing a new initial vertex. -/
def addInitialMap {m n : SimplexCategory} (α : m ⟶ n) : ⦋m.len + 1⦌ ⟶ ⦋n.len + 1⦌ :=
  SimplexCategory.Hom.mk {
    toFun := Fin.cases 0 (fun i ↦ (α.toOrderHom i).succ)
    monotone' := by
      intro i j h
      cases i using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ i =>
        cases j using Fin.cases with
        | zero => have h' : i.val + 1 ≤ 0 := h; omega
        | succ j =>
          change (α.toOrderHom i).val + 1 ≤ (α.toOrderHom j).val + 1
          exact Nat.add_le_add_right (α.toOrderHom.monotone (Nat.le_of_succ_le_succ h)) 1 }

/-- The actual relative-row ordinal functor. -/
def addInitial : SimplexCategory ⥤ SimplexCategory where
  obj n := ⦋n.len + 1⦌
  map := addInitialMap
  map_id _ := by ext i : 3; cases i using Fin.cases <;> rfl
  map_comp _ _ := by ext i : 3; cases i using Fin.cases <;> rfl

/-- The original tail vertices are the literal successor vertices. -/
def tail : 𝟭 SimplexCategory ⟶ addInitial where
  app n := SimplexCategory.Hom.mk ⟨Fin.succ, fun _ _ h ↦ Nat.succ_le_succ h⟩
  naturality _ _ _ := by ext i : 3; rfl

@[simp] theorem addInitialMap_zero {m n : SimplexCategory} (α : m ⟶ n) :
    (addInitialMap α).toOrderHom 0 = 0 := rfl
@[simp] theorem addInitialMap_succ {m n : SimplexCategory} (α : m ⟶ n) (i : Fin (m.len + 1)) :
    (addInitialMap α).toOrderHom i.succ = (α.toOrderHom i).succ := rfl
@[simp] theorem tail_apply (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (tail.app n).toOrderHom i = i.succ := rfl

/-- The first relative object is the actual interval from the added vertex to the first tail
vertex. -/
def firstInterval (n : SimplexCategory) : Interval (addInitial.obj n) :=
  interval 0 (0 : Fin (n.len + 1)).succ (Fin.zero_le _)

/-- Tail restriction commutes strictly with every actual relative ordinal restriction. -/
theorem tail_reindex {C : Type u} [Category.{v} C] (W : Structure C)
    {m n : SimplexCategory} (α : m ⟶ n) :
    QuotientRows.reindex W (addInitial.map α) ⋙ QuotientRows.reindex W (tail.app m) =
      QuotientRows.reindex W (tail.app n) ⋙ QuotientRows.reindex W α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
