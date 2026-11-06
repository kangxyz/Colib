/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.PathValue

/-!
# Join Parameters

Join two finite parameter lists, identifying their shared endpoint.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory
namespace FundamentalGroupoid.OpenCover

/-- Join two finite parameter lists, identifying their shared endpoint. -/
def joinParameters {α : Type*} {m n : ℕ}
    (a : Fin (m + 1) → α) (b : Fin (n + 1) → α) (i : Fin (m + n + 1)) : α :=
  if h : i.val < m then a ⟨i.val, by omega⟩ else b ⟨i.val - m, by omega⟩

theorem joinParameters_left {α : Type*} {m n : ℕ}
    (a : Fin (m + 1) → α) (b : Fin (n + 1) → α) (hab : a (Fin.last m) = b 0)
    (i : Fin (m + 1)) :
    joinParameters a b ⟨i.val, by omega⟩ = a i := by
  simp only [joinParameters]
  split
  · rfl
  · rename_i h
    have hi : i = Fin.last m := by apply Fin.ext; simp; omega
    subst i
    simpa using hab.symm

theorem joinParameters_right {α : Type*} {m n : ℕ}
    (a : Fin (m + 1) → α) (b : Fin (n + 1) → α) (i : Fin (n + 1)) :
    joinParameters a b ⟨m + i.val, by omega⟩ = b i := by
  simp only [joinParameters]
  rw [dite_eq_right (by omega)]
  congr 1
  apply Fin.ext
  simp

theorem joinParameters_monotone {α : Type*} [Preorder α] {m n : ℕ}
    (a : Fin (m + 1) → α) (b : Fin (n + 1) → α) (hab : a (Fin.last m) = b 0)
    (ha : Monotone a) (hb : Monotone b) : Monotone (joinParameters a b) := by
  intro i j hij
  simp only [joinParameters]
  split <;> split
  · exact ha (by simpa using hij)
  · exact (ha (Fin.le_last _)).trans (hab ▸ hb (Fin.zero_le _))
  · omega
  · exact hb (by simp only [Fin.le_iff_val_le_val]; omega)

end FundamentalGroupoid.OpenCover
