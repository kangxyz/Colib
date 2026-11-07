/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Symbols.Ext

universe u v

variable {k : Type u} [Field k] {A : Type v} [AddCommGroup A] {n : ℕ}

-- Codomain size is independent of the field, in both native map categories.
example (f g : MilnorKTheory k n →+ A)
    (h : ∀ a : Fin n → kˣ, f (milnorKTupleSymbol a) = g (milnorKTupleSymbol a)) :
    f = g := milnorKTheory_addHom_ext f g h

example (f g : MilnorKTheory k n →ₗ[ℤ] A)
    (h : ∀ a : Fin n → kˣ, f (milnorKTupleSymbol a) = g (milnorKTupleSymbol a)) :
    f = g := milnorKTheory_linearMap_ext f g h

-- Degree zero is determined by its one empty tuple, without a positive-degree assumption.
example (f g : MilnorKTheory k 0 →+ A)
    (h : f (milnorKTupleSymbol (Fin.elim0 : Fin 0 → kˣ)) =
      g (milnorKTupleSymbol (Fin.elim0 : Fin 0 → kˣ))) : f = g := by
  apply milnorKTheory_addHom_ext
  intro a
  have ha : a = (Fin.elim0 : Fin 0 → kˣ) := funext fun i => Fin.elim0 i
  simpa only [ha] using h

example (f g : MilnorKTheory k 0 →ₗ[ℤ] A)
    (h : f (milnorKTupleSymbol (Fin.elim0 : Fin 0 → kˣ)) =
      g (milnorKTupleSymbol (Fin.elim0 : Fin 0 → kˣ))) : f = g := by
  apply milnorKTheory_linearMap_ext
  intro a
  have ha : a = (Fin.elim0 : Fin 0 → kˣ) := funext fun i => Fin.elim0 i
  simpa only [ha] using h
