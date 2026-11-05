/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Symbols.Relations

universe u

variable {k : Type u} [Field k]

example (a : Fin 0 → kˣ) : (milnorKTupleSymbol a : MilnorKRing k) = 1 := by
  simp [milnorKTupleSymbol]

example (a : kˣ) :
    (milnorKTupleSymbol (fun _ : Fin 1 => a) : MilnorKRing k) = milnorKSymbol k a := by
  simp [milnorKTupleSymbol, List.ofFn_succ]

example (a b : kˣ) (h : (a : k) + (b : k) = 1) :
    milnorKTupleSymbol ![a, b] = 0 :=
  milnorKTupleSymbol_steinberg ![a, b] 0 1 rfl h

example (a b : kˣ) : milnorKTupleSymbol ![a, b] = -milnorKTupleSymbol ![b, a] := by
  have h : Function.update (Function.update ![a, b] 0 b) 1 a = ![b, a] := by
    ext i
    fin_cases i <;> simp
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, h] using
    milnorKTupleSymbol_adjacent_skew ![a, b] 0 1 rfl

example {n : ℕ} (a : Fin n → kˣ) (i : Fin n) (b c : kˣ) :
    milnorKTupleSymbol (Function.update a i (b * c)) =
      milnorKTupleSymbol (Function.update a i b) +
        milnorKTupleSymbol (Function.update a i c) :=
  milnorKTupleSymbol_update_mul a i b c

example {n : ℕ} (a : Fin n → kˣ) (i : Fin n) :
    milnorKTupleSymbol (Function.update a i 1) = 0 := by simp

example {n : ℕ} (a : Fin n → kˣ) (i : Fin n) (b : kˣ) :
    milnorKTupleSymbol (Function.update a i b⁻¹) =
      -milnorKTupleSymbol (Function.update a i b) := by simp
