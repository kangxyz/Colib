/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Symbols.Descent

universe u v

variable {k : Type u} [Field k] {A : Type v} [AddCommGroup A] {n : ℕ}

-- The target universe is independent, and no positive-degree hypothesis is required.
example (s : (Fin n → kˣ) → A) (hs : IsMilnorKSymbolMap s) :
    ∃! f : MilnorKTheory k n →ₗ[ℤ] A, ∀ a, f (milnorKTupleSymbol a) = s a :=
  hs.existsUnique_lift

example (s : (Fin n → kˣ) → A) (hs : IsMilnorKSymbolMap s) (a : Fin n → kˣ) :
    hs.lift (milnorKTupleSymbol a) = s a := hs.lift_symbol a

-- In degree zero every function on the unique empty tuple satisfies both relations vacuously.
example (s : (Fin 0 → kˣ) → A) :
    ∃! f : MilnorKTheory k 0 →ₗ[ℤ] A, ∀ a, f (milnorKTupleSymbol a) = s a := by
  have hs : IsMilnorKSymbolMap s :=
    ⟨fun _ i => Fin.elim0 i, fun _ i => Fin.elim0 i⟩
  exact hs.existsUnique_lift

-- Extending the native symbol function recovers the identity on the native homogeneous group.
example :
    (milnorKTupleSymbol_isSymbolMap (k := k) (n := n)).lift =
      LinearMap.id (R := ℤ) (M := MilnorKTheory k n) := by
  apply milnorKTheory_linearMap_ext
  intro a
  exact (milnorKTupleSymbol_isSymbolMap (k := k) (n := n)).lift_symbol a
