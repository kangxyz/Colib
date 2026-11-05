/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.OrdinalJoin

/-! # Maps out of the genuine ordinal join

Extracted from `Quillen/Topology/Realization/EdgewiseSimplex.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. These declarations use neither
reversal nor subdivision. Both ordinary and reversed subdivision can reuse them.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace SSet.OrdinalJoin

/-- Increasing maps from the two halves glue if all first-half values precede
all second-half values. -/
def joinDesc {p q r : SimplexCategory} (a : p ⟶ r) (b : q ⟶ r)
    (h : ∀ i j, a.toOrderHom i ≤ b.toOrderHom j) : joinObj p q ⟶ r :=
  SimplexCategory.Hom.mk {
    toFun i := if hi : i.val < p.len + 1 then a.toOrderHom ⟨i.val, hi⟩
      else b.toOrderHom ⟨i.val - (p.len + 1), by
        have := i.isLt; dsimp [joinObj] at this; omega⟩
    monotone' := by
      intro i j hij
      dsimp only
      split_ifs with hi hj hj
      · exact a.toOrderHom.monotone hij
      · exact h _ _
      · have : i.val ≤ j.val := hij; omega
      · exact b.toOrderHom.monotone (Nat.sub_le_sub_right hij _) }

@[simp] theorem joinDesc_left {p q r : SimplexCategory} (a : p ⟶ r) (b : q ⟶ r)
    (h : ∀ i j, a.toOrderHom i ≤ b.toOrderHom j) (i : Fin (p.len + 1)) :
    (joinDesc a b h).toOrderHom ((left p q).toOrderHom i) = a.toOrderHom i := by
  change (if hi : i.val < p.len + 1 then _ else _) = _
  rw [dite_eq_left i.isLt]
  rfl

@[simp] theorem joinDesc_right {p q r : SimplexCategory} (a : p ⟶ r) (b : q ⟶ r)
    (h : ∀ i j, a.toOrderHom i ≤ b.toOrderHom j) (i : Fin (q.len + 1)) :
    (joinDesc a b h).toOrderHom ((right p q).toOrderHom i) = b.toOrderHom i := by
  change (if hi : p.len + 1 + i.val < p.len + 1 then _ else _) = _
  rw [dite_eq_right (by omega)]
  congr 1
  apply Fin.ext
  change p.len + 1 + i.val - (p.len + 1) = i.val
  omega

end SSet.OrdinalJoin
