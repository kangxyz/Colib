/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Reindex
public import Colib.CategoryTheory.Waldhausen.SConstruction.Bisimplicial

/-! # Exact agreement with the existing independent S-construction grids

The new full quotient-row objects have precisely the old zero/cofibration/
quotient predicates. The original nerve-direction weak condition remains
separate and unchanged.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/Rows/GridBridge.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd.
   Isolated strict compilation is recorded in the accompanying release report. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Include one original quotient row in a two-degree S-grid. -/
def gridRestriction {n m : SimplexCategory} (t : Fin (m.len + 1)) : Interval n ⥤ Grid₂ n m :=
  (show Monotone (fun p : Interval n ↦ ((t, p) : Grid₂ n m)) from
    fun _ _ h ↦ ⟨le_rfl, h⟩).functor

/-- Every original S-grid row is an actual object of the constructed full row category. -/
theorem isRow_of_isSimplex₂ {n m : SimplexCategory} {F : Grid₂ n m ⥤ C}
    (hF : IsSimplex₂ W.cof W.weq F) (t : Fin (m.len + 1)) :
    IsRow W (gridRestriction t ⋙ F) where
  zero i := hF.zero t i
  cofibration i j k hij hjk := hF.cofibration t i j k hij hjk
  quotient i j k hij hjk := hF.quotient t i j k hij hjk

/-- The existing independent-grid predicates are exactly the new row predicates
plus the original pointwise weak-equivalence nerve condition. -/
theorem isSimplex₂_iff {n m : SimplexCategory} (F : Grid₂ n m ⥤ C) :
    IsSimplex₂ W.cof W.weq F ↔
      (∀ t : Fin (m.len + 1), IsRow W (gridRestriction t ⋙ F)) ∧
      (∀ (s t : Fin (m.len + 1)) (i j : Fin (n.len + 1)) (hst : s ≤ t) (hij : i ≤ j),
        W.weq (F.map (homOfLE (show grid₂ s i j hij ≤ grid₂ t i j hij from
          ⟨hst, le_rfl, le_rfl⟩)))) := by
  constructor
  · intro h
    exact ⟨isRow_of_isSimplex₂ W h, h.weak⟩
  · rintro ⟨hr, hw⟩
    exact {
      zero := fun t i ↦ (hr t).zero i
      cofibration := fun t i j k hij hjk ↦ (hr t).cofibration i j k hij hjk
      quotient := fun t i j k hij hjk ↦ (hr t).quotient i j k hij hjk
      weak := hw }

/-- Reindexing the row inclusion is exactly the existing independent grid restriction. -/
theorem gridRestriction_reindex {n' n m' m : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m) (t : Fin (m'.len + 1)) :
    gridRestriction t ⋙ gridMap₂ α β = indexMap α ⋙ gridRestriction (β.toOrderHom t) := rfl

end CategoryTheory.Waldhausen.QuotientRows
