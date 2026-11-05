/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Symbols.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.SymbolReorder

/-!
# Adjacent relations for homogeneous tuple symbols

The adjacent Steinberg relation from `Aglib.KTheory.MilnorK.Basic` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f` is proved on Stacks' homogeneous subgroup, using
its actual relation `milnorKSymbol_mul_steinberg`. The adjacent skew identities adapt
`Aglib.KTheory.MilnorK.Symbols` at the same revision, using the native list theorem
`Stacks.Chow.milnorKSymbolProd_swap_cons`. No relation is added to the object.

Stacks Project, Tag 0EAY, first paragraph supplies the tensor-algebra Steinberg quotient.
The identities here are derived consequences of that presentation, not verbatim statements
of the remark. In particular this is not an alternating quotient: repeated entries need
not vanish.
-/

@[expose] public noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- An adjacent pair whose entries add to `1` kills a homogeneous tuple symbol. -/
theorem milnorKTupleSymbol_steinberg (a : Fin n → kˣ) (i j : Fin n)
    (hij : i.val + 1 = j.val) (h : (a i : k) + (a j : k) = 1) :
    milnorKTupleSymbol a = 0 := by
  apply Subtype.ext
  change milnorKSymbolProd k (List.ofFn a) = 0
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases n with
      | zero => have := i.isLt; have := j.isLt; omega
      | succ n =>
          cases i using Fin.cases with
          | zero =>
              have hj : j = (0 : Fin (n + 1)).succ := Fin.ext (by simpa using hij.symm)
              subst j
              rw [List.ofFn_succ, milnorKSymbolProd_cons, List.ofFn_succ,
                milnorKSymbolProd_cons, ← mul_assoc, milnorKSymbol_mul_steinberg h, zero_mul]
          | succ i =>
              cases j using Fin.cases with
              | zero => simp only [Fin.val_zero, Fin.val_succ] at hij; omega
              | succ j =>
                  rw [List.ofFn_succ, milnorKSymbolProd_cons,
                    ih (fun l => a l.succ) i j (by simpa using hij) h, mul_zero]

/-- Swapping substituted entries at adjacent positions negates the homogeneous symbol. -/
theorem milnorKTupleSymbol_update_adjacent_skew (a : Fin n → kˣ) (i j : Fin n)
    (hij : i.val + 1 = j.val) (b c : kˣ) :
    milnorKTupleSymbol (Function.update (Function.update a i b) j c) =
      -milnorKTupleSymbol (Function.update (Function.update a i c) j b) := by
  apply Subtype.ext
  change milnorKSymbolProd k (List.ofFn (Function.update (Function.update a i b) j c)) =
    -milnorKSymbolProd k (List.ofFn (Function.update (Function.update a i c) j b))
  induction a using Fin.consInduction with
  | elim0 => exact Fin.elim0 i
  | @cons n x a ih =>
      cases i using Fin.cases with
      | zero =>
          cases n with
          | zero => have := j.isLt; simp only [Fin.val_zero] at hij; omega
          | succ n =>
              have hj : j = (0 : Fin (n + 1)).succ := Fin.ext (by simpa using hij.symm)
              subst j
              cases a using Fin.consCases with
              | cons y a =>
                  simpa only [Fin.update_cons_zero, ← Fin.cons_update, List.ofFn_cons] using
                    Stacks.Chow.milnorKSymbolProd_swap_cons b c (List.ofFn a)
      | succ i =>
          cases j using Fin.cases with
          | zero => simp only [Fin.val_zero, Fin.val_succ] at hij; omega
          | succ j =>
              simp only [← Fin.cons_update, List.ofFn_cons, milnorKSymbolProd_cons]
              rw [ih i j (by simpa using hij), mul_neg]

/-- Interchanging two adjacent entries negates the original homogeneous tuple symbol. -/
theorem milnorKTupleSymbol_adjacent_skew (a : Fin n → kˣ) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    milnorKTupleSymbol a =
      -milnorKTupleSymbol (Function.update (Function.update a i (a j)) j (a i)) := by
  simpa only [Function.update_eq_self] using
    milnorKTupleSymbol_update_adjacent_skew a i j hij (a i) (a j)

attribute [colib_tag "COL-0014"] milnorKTupleSymbol_update_mul
  milnorKTupleSymbol_update_one milnorKTupleSymbol_eq_zero_of_eq_one
  milnorKTupleSymbol_update_inv milnorKTupleSymbol_steinberg
  milnorKTupleSymbol_update_adjacent_skew milnorKTupleSymbol_adjacent_skew

add_to_stacks 0EAY
  "Consequence of the defining Steinberg ideal: an adjacent pair summing to one vanishes"
  milnorKTupleSymbol_steinberg
