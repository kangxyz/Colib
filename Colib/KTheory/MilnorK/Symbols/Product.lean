/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Symbols.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeZero

/-!
# Native graded products of Milnor symbols

The multiplication is Mathlib's existing `GradedMonoid.GMul.mul`, supplied by the Stacks
Milnor grading. No second product operation or quotient model is introduced. The tuple formula
and degree-zero scalar formulas adapt `Aglib.KTheory.MilnorK.Product.product_symbol`,
`product_zero_left`, and `product_zero_right` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`.

Degree transport uses ordinary equality transport. The canonical degree-zero identification
is Stacks' `milnorKTheoryZeroAddEquiv`. These formulas concern the tensor-algebra Steinberg
quotient of Stacks Project, Tag 0EAY, first paragraph, over fields of arbitrary characteristic.
-/

@[expose] public noncomputable section

universe u

variable {k : Type u} [Field k] {m n : ℕ}

/-- The native graded product of two tuple symbols is their ordered concatenation. -/
@[simp] theorem milnorKTupleSymbol_gmul (a : Fin m → kˣ) (b : Fin n → kˣ) :
    GradedMonoid.GMul.mul (milnorKTupleSymbol a) (milnorKTupleSymbol b) =
      milnorKTupleSymbol (Fin.append a b) := by
  apply Subtype.ext
  simp only [SetLike.coe_gMul, coe_milnorKTupleSymbol, List.ofFn_fin_append,
    milnorKSymbolProd_append]

private theorem coe_milnorKTheory_cast {m n : ℕ} (h : m = n) (x : MilnorKTheory k m) :
    ((cast (congrArg (MilnorKTheory k) h) x : MilnorKTheory k n) : MilnorKRing k) = x := by
  subst n
  rfl

private theorem coe_milnorKTheory_zero (z : MilnorKTheory k 0) :
    (z : MilnorKRing k) = milnorKTheoryZeroAddEquiv k z • (1 : MilnorKRing k) := by
  obtain ⟨r, rfl⟩ := milnorKZeroMap_surjective k z
  rw [milnorKTheoryZeroAddEquiv_milnorKZeroMap]
  change (milnorKSteinbergIdeal k).ringCon.mk'
    (algebraMap ℤ (MilnorKTensorAlgebra k) r) = r • (1 : MilnorKRing k)
  rw [Algebra.algebraMap_eq_smul_one, map_zsmul, map_one]

/-- Multiplication on the left by a degree-zero class is its canonical integer scalar. -/
theorem milnorKTheory_gmul_zero_left (z : MilnorKTheory k 0) (x : MilnorKTheory k n) :
    cast (congrArg (MilnorKTheory k) (Nat.zero_add n)) (GradedMonoid.GMul.mul z x) =
      milnorKTheoryZeroAddEquiv k z • x := by
  apply Subtype.ext
  rw [coe_milnorKTheory_cast (Nat.zero_add n), SetLike.coe_gMul, coe_milnorKTheory_zero z]
  change (milnorKTheoryZeroAddEquiv k z • (1 : MilnorKRing k)) * (x : MilnorKRing k) =
    milnorKTheoryZeroAddEquiv k z • (x : MilnorKRing k)
  rw [smul_mul_assoc, one_mul]

/-- Multiplication on the right by a degree-zero class is its canonical integer scalar. -/
theorem milnorKTheory_gmul_zero_right (x : MilnorKTheory k n) (z : MilnorKTheory k 0) :
    cast (congrArg (MilnorKTheory k) (Nat.add_zero n)) (GradedMonoid.GMul.mul x z) =
      milnorKTheoryZeroAddEquiv k z • x := by
  apply Subtype.ext
  rw [coe_milnorKTheory_cast (Nat.add_zero n), SetLike.coe_gMul, coe_milnorKTheory_zero z]
  change (x : MilnorKRing k) * (milnorKTheoryZeroAddEquiv k z • (1 : MilnorKRing k)) =
    milnorKTheoryZeroAddEquiv k z • (x : MilnorKRing k)
  rw [mul_smul_comm, mul_one]

attribute [colib_tag "COL-0022"] milnorKTupleSymbol_gmul
  milnorKTheory_gmul_zero_left milnorKTheory_gmul_zero_right

add_to_stacks 0EAY
  "Consequence of the tensor-algebra quotient: ordered symbol products concatenate"
  milnorKTupleSymbol_gmul
add_to_stacks 0EAY
  "Consequence of the canonical degree-zero identification with integers: scalar multiplication"
  milnorKTheory_gmul_zero_left
add_to_stacks 0EAY
  "Consequence of the canonical degree-zero identification with integers: scalar multiplication"
  milnorKTheory_gmul_zero_right
