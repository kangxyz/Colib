/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Residue.Specialization

universe u v

open Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

-- Independent universes and arbitrary degree; the uniformizer remains an explicit parameter.
example (hπ : Irreducible π) (n : ℕ) (a : Fin n → Fˣ) :
    dvrMilnorSpecialization hπ n (milnorKTupleSymbol a) =
      milnorKTupleSymbol (dvrFracUnitPart hπ ∘ a) :=
  dvrMilnorSpecialization_tupleSymbol hπ n a

example (hπ : Irreducible π) (n : ℕ) (a : Fin n → Rˣ) :
    dvrMilnorSpecialization hπ n
      (milnorKTupleSymbol (Units.map (algebraMap R F).toMonoidHom ∘ a)) =
        milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) :=
  dvrMilnorSpecialization_ringUnits hπ n a

-- Degree zero retains the empty symbol.
example (hπ : Irreducible π) :
    dvrMilnorSpecialization (F := F) hπ 0
      (milnorKTupleSymbol (Fin.elim0 : Fin 0 → Fˣ)) =
        milnorKTupleSymbol (Fin.elim0 : Fin 0 → (IsLocalRing.ResidueField R)ˣ) := by
  rw [dvrMilnorSpecialization_tupleSymbol]
  congr 1
  exact funext fun i => Fin.elim0 i

-- An arbitrary tuple slot may contain the uniformizer.
example (hπ : Irreducible π) (n : ℕ) (a : Fin n → Fˣ) (i : Fin n)
    (hi : a i = dvrFracUniformizer F hπ) :
    dvrMilnorSpecialization hπ n (milnorKTupleSymbol a) = 0 :=
  dvrMilnorSpecialization_tuple_uniformizer hπ n a i hi
