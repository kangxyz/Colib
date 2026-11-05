/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Symbols.Product

universe u

variable {k : Type u} [Field k] {n : ℕ}

-- Two nonempty blocks retain their order and the native graded product.
example (a b : kˣ) :
    GradedMonoid.GMul.mul (milnorKTupleSymbol ![a]) (milnorKTupleSymbol ![b]) =
      milnorKTupleSymbol (Fin.append ![a] ![b]) := by simp

private theorem empty_symbol_eq_zeroMap_one :
    milnorKTupleSymbol (Fin.elim0 : Fin 0 → kˣ) = milnorKZeroMap k 1 := by
  apply Subtype.ext
  simp [milnorKTupleSymbol, milnorKZeroMap]

-- Empty symbols act as units, with each actual degree transport displayed.
example (x : MilnorKTheory k n) :
    cast (congrArg (MilnorKTheory k) (Nat.zero_add n))
      (GradedMonoid.GMul.mul (milnorKTupleSymbol (Fin.elim0 : Fin 0 → kˣ)) x) = x := by
  rw [milnorKTheory_gmul_zero_left, empty_symbol_eq_zeroMap_one,
    milnorKTheoryZeroAddEquiv_milnorKZeroMap, one_smul]

example (x : MilnorKTheory k n) :
    cast (congrArg (MilnorKTheory k) (Nat.add_zero n))
      (GradedMonoid.GMul.mul x (milnorKTupleSymbol (Fin.elim0 : Fin 0 → kˣ))) = x := by
  rw [milnorKTheory_gmul_zero_right, empty_symbol_eq_zeroMap_one,
    milnorKTheoryZeroAddEquiv_milnorKZeroMap, one_smul]

-- Negative degree-zero values test integer, rather than natural, scalar action.
example (x : MilnorKTheory k n) :
    cast (congrArg (MilnorKTheory k) (Nat.zero_add n))
      (GradedMonoid.GMul.mul (milnorKZeroMap k (-1)) x) = -x := by
  rw [milnorKTheory_gmul_zero_left, milnorKTheoryZeroAddEquiv_milnorKZeroMap, neg_one_zsmul]

example (x : MilnorKTheory k n) :
    cast (congrArg (MilnorKTheory k) (Nat.add_zero n))
      (GradedMonoid.GMul.mul x (milnorKZeroMap k (-1))) = -x := by
  rw [milnorKTheory_gmul_zero_right, milnorKTheoryZeroAddEquiv_milnorKZeroMap, neg_one_zsmul]
