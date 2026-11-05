/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic


/-! Ordered joins of nonempty finite ordinals and their actual monotone maps. -/
/-! Implementation provenance: extracted from `Quillen/Topology/Realization/Edgewise.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, proofs,
assumptions, and universes are retained; only namespaces/imports are migrated.
-/
@[expose] public section


noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.OrdinalJoin

/-- Ordered join of two nonempty finite ordinals. -/
def joinObj (p q : SimplexCategory) : SimplexCategory := ⦋p.len + q.len + 1⦌

/-- Inclusion of the first summand in the ordered join. -/
def left (p q : SimplexCategory) : p ⟶ joinObj p q :=
  SimplexCategory.Hom.mk ⟨fun i ↦ ⟨i.val, by dsimp [joinObj]; omega⟩,
    fun _ _ h ↦ h⟩

/-- Inclusion of the second summand in the ordered join. -/
def right (p q : SimplexCategory) : q ⟶ joinObj p q :=
  SimplexCategory.Hom.mk ⟨fun i ↦ ⟨p.len + 1 + i.val, by dsimp [joinObj]; omega⟩,
    fun _ _ h ↦ Nat.add_le_add_left h _⟩

@[simp] theorem left_val (p q : SimplexCategory) (i : Fin (p.len + 1)) :
    ((left p q).toOrderHom i).val = i.val := rfl

@[simp] theorem right_val (p q : SimplexCategory) (i : Fin (q.len + 1)) :
    ((right p q).toOrderHom i).val = p.len + 1 + i.val := rfl

/-- A pair of increasing maps acts on the ordered join, separately in each half. -/
def joinMap {p q p' q' : SimplexCategory} (f : p ⟶ p') (g : q ⟶ q') :
    joinObj p q ⟶ joinObj p' q' :=
  SimplexCategory.Hom.mk {
    toFun i := if h : i.val < p.len + 1 then
      (left p' q').toOrderHom (f.toOrderHom ⟨i.val, h⟩)
      else (right p' q').toOrderHom (g.toOrderHom ⟨i.val - (p.len + 1), by
        have := i.isLt; dsimp [joinObj] at this; omega⟩)
    monotone' := by
      intro i j hij
      dsimp only
      split_ifs with hi hj hj
      · exact f.toOrderHom.monotone hij
      · have := (f.toOrderHom ⟨i.val, hi⟩).isLt
        change _ ≤ _
        change (f.toOrderHom ⟨i.val, hi⟩).val ≤ p'.len + 1 + _
        omega
      · have : i.val ≤ j.val := hij
        omega
      · change p'.len + 1 + _ ≤ p'.len + 1 + _
        apply Nat.add_le_add_left
        exact g.toOrderHom.monotone (Nat.sub_le_sub_right hij _) }

@[simp] theorem joinMap_left {p q p' q' : SimplexCategory} (f : p ⟶ p') (g : q ⟶ q')
    (i : Fin (p.len + 1)) :
    (joinMap f g).toOrderHom ((left p q).toOrderHom i) =
      (left p' q').toOrderHom (f.toOrderHom i) := by
  change (if h : i.val < p.len + 1 then _ else _) = _
  rw [dite_eq_left i.isLt]
  rfl


@[simp] theorem joinMap_right {p q p' q' : SimplexCategory} (f : p ⟶ p') (g : q ⟶ q')
    (i : Fin (q.len + 1)) :
    (joinMap f g).toOrderHom ((right p q).toOrderHom i) =
      (right p' q').toOrderHom (g.toOrderHom i) := by
  change (if h : p.len + 1 + i.val < p.len + 1 then _ else _) = _
  rw [dite_eq_right (by omega)]
  congr 2
  apply Fin.ext
  change p.len + 1 + i.val - (p.len + 1) = i.val
  omega


/-- Every join vertex belongs to one of its two summands. -/
theorem join_cases {p q : SimplexCategory} (i : Fin ((joinObj p q).len + 1)) :
    (∃ j, i = (left p q).toOrderHom j) ∨
      (∃ j, i = (right p q).toOrderHom j) := by
  by_cases h : i.val < p.len + 1
  · exact .inl ⟨⟨i.val, h⟩, rfl⟩
  · refine .inr ⟨⟨i.val - (p.len + 1), by
        have := i.isLt; dsimp [joinObj] at this; omega⟩, ?_⟩
    apply Fin.ext
    change i.val = p.len + 1 + (i.val - (p.len + 1))
    omega

@[simp] theorem joinMap_id (p q : SimplexCategory) :
    joinMap (𝟙 p) (𝟙 q) = 𝟙 (joinObj p q) := by
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> simp

@[simp] theorem joinMap_comp {p q p' q' p'' q'' : SimplexCategory}
    (f : p ⟶ p') (g : q ⟶ q') (f' : p' ⟶ p'') (g' : q' ⟶ q'') :
    joinMap (f ≫ f') (g ≫ g') = joinMap f g ≫ joinMap f' g' := by
  ext i : 3
  rcases join_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> simp [SimplexCategory.comp_toOrderHom]

end SSet.OrdinalJoin
