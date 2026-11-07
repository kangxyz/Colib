/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKInvolution
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKSymbolProd

/-!
# The native grading involution on ordered symbols

This is a direct consequence of the existing Stacks involution on degree-one symbols, not a
second involution or an independently reconstructed grading. The integer sign remains valid
in arbitrary characteristic.
-/

@[expose] public section

namespace Stacks.Chow

universe u

variable {k : Type u} [Field k]

/-- The native involution multiplies a list symbol by the parity sign of its length. -/
theorem milnorKInvolution_symbolProd (l : List kˣ) :
    milnorKInvolution k (milnorKSymbolProd k l) =
      (-1 : ℤ) ^ l.length • milnorKSymbolProd k l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [milnorKSymbolProd_cons, map_mul, milnorKInvolution_milnorKSymbol, ih,
      List.length_cons, pow_succ, mul_smul, neg_one_smul, smul_neg, neg_mul, mul_smul_comm]

end Stacks.Chow
