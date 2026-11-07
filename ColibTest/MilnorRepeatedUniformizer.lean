/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Residue.RepeatedUniformizer

universe u v

open Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

-- Every target degree and independent ring/fraction-field universes are retained.
example (hπ : Irreducible π) (n : ℕ) :
    dvrMilnorTameSymbol hπ n
      (milnorKTupleSymbol (fun _ : Fin (n + 1) => dvrFracUniformizer F hπ)) =
        milnorKTupleSymbol (fun _ : Fin n => (-1 : (IsLocalRing.ResidueField R)ˣ)) :=
  dvrMilnorTameSymbol_tuple_uniformizers hπ n

-- One uniformizer has residue the empty symbol in degree zero.
example (hπ : Irreducible π) :
    dvrMilnorTameSymbol hπ 0
      (milnorKTupleSymbol (fun _ : Fin 1 => dvrFracUniformizer F hπ)) =
        milnorKTupleSymbol (Fin.elim0 : Fin 0 → (IsLocalRing.ResidueField R)ˣ) := by
  rw [dvrMilnorTameSymbol_tuple_uniformizers]
  congr 1
  exact funext fun i => Fin.elim0 i

-- In degree two the formula retains the {-1} symbol, without asserting it is nonzero.
example (hπ : Irreducible π) :
    dvrMilnorTameSymbol hπ 1
      (milnorKTupleSymbol (fun _ : Fin 2 => dvrFracUniformizer F hπ)) =
        milnorKTupleSymbol (fun _ : Fin 1 => (-1 : (IsLocalRing.ResidueField R)ˣ)) :=
  dvrMilnorTameSymbol_tuple_uniformizers hπ 1
