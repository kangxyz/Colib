/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.Data.List.OfFn
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKSymbolProd

/-!
# Homogeneous tuple symbols in the native Milnor K-groups

`milnorKTupleSymbol` is the native Stacks list symbol, with its degree recorded in
`MilnorKTheory`. It introduces no new quotient or presentation. Coordinate multiplicativity
and identity/inverse formulas adapt `Aglib.KTheory.MilnorK.Basic` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f` directly to this homogeneous subgroup.

The underlying tensor-algebra quotient and list symbols are those of Stacks Project,
Tag 0EAY, first paragraph. The tuple notation and coordinate formulas are consequences
of that tensor-algebra presentation. All statements allow arbitrary characteristic.
-/

@[expose] public noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- The ordered tuple symbol in the native degree-`n` Milnor K-group. -/
@[colib_tag "COL-0013", stacks 0EAY
  "Ordered products in the homogeneous component of the tensor-algebra Steinberg quotient"]
def milnorKTupleSymbol (a : Fin n → kˣ) : MilnorKTheory k n :=
  ⟨milnorKSymbolProd k (List.ofFn a), by
    simpa only [List.length_ofFn] using milnorKSymbolProd_mem_milnorKGrading (List.ofFn a)⟩

/-- Forgetting the degree gives precisely the native Stacks list symbol. -/
@[simp] theorem coe_milnorKTupleSymbol (a : Fin n → kˣ) :
    (milnorKTupleSymbol a : MilnorKRing k) = milnorKSymbolProd k (List.ofFn a) := rfl

/-- Multiplication in one coordinate adds the corresponding homogeneous symbols. -/
theorem milnorKTupleSymbol_update_mul (a : Fin n → kˣ) (i : Fin n) (b c : kˣ) :
    milnorKTupleSymbol (Function.update a i (b * c)) =
      milnorKTupleSymbol (Function.update a i b) +
        milnorKTupleSymbol (Function.update a i c) := by
  apply Subtype.ext
  change milnorKSymbolProd k (List.ofFn (Function.update a i (b * c))) =
    milnorKSymbolProd k (List.ofFn (Function.update a i b)) +
      milnorKSymbolProd k (List.ofFn (Function.update a i c))
  induction a using Fin.consInduction with
  | elim0 => exact Fin.elim0 i
  | cons x a ih =>
      cases i using Fin.cases with
      | zero =>
          simp only [Fin.update_cons_zero, List.ofFn_cons, milnorKSymbolProd_cons,
            milnorKSymbol_mul, add_mul]
      | succ i =>
          simp only [← Fin.cons_update, List.ofFn_cons, milnorKSymbolProd_cons]
          rw [ih i, mul_add]

/-- A coordinate equal to `1` contributes the zero symbol. -/
@[simp] theorem milnorKTupleSymbol_update_one (a : Fin n → kˣ) (i : Fin n) :
    milnorKTupleSymbol (Function.update a i 1) = 0 := by
  have h := milnorKTupleSymbol_update_mul a i 1 1
  rw [one_mul] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

/-- Identity-axis vanishing without changing the tuple. -/
theorem milnorKTupleSymbol_eq_zero_of_eq_one (a : Fin n → kˣ) (i : Fin n)
    (h : a i = 1) : milnorKTupleSymbol a = 0 := by
  simpa only [← h, Function.update_eq_self] using milnorKTupleSymbol_update_one a i

/-- Inverting a coordinate negates the homogeneous symbol. -/
@[simp] theorem milnorKTupleSymbol_update_inv (a : Fin n → kˣ) (i : Fin n) (b : kˣ) :
    milnorKTupleSymbol (Function.update a i b⁻¹) =
      -milnorKTupleSymbol (Function.update a i b) := by
  have h := milnorKTupleSymbol_update_mul a i b b⁻¹
  rw [mul_inv_cancel, milnorKTupleSymbol_update_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm
