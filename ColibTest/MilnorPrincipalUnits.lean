/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Residue.PrincipalUnits

universe u v

open Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]

-- Independent universes, arbitrary slot, and no conditions on the remaining field units.
example (n : ℕ) (a : Fin (n + 1) → Fˣ) (i : Fin (n + 1)) (u : Rˣ)
    (hi : a i = Units.map (algebraMap R F).toMonoidHom u)
    (hu : Units.map (IsLocalRing.residue R).toMonoidHom u = 1) :
    dvrMilnorTameSymbol' R F n (milnorKTupleSymbol a) = 0 :=
  dvrMilnorTameSymbol'_tuple_principal_unit n a i u hi hu

-- Degree one is included; the residue lands in the native degree-zero component.
example (u : Rˣ) (hu : Units.map (IsLocalRing.residue R).toMonoidHom u = 1) :
    dvrMilnorTameSymbol' R F 0
      (milnorKTupleSymbol (fun _ : Fin 1 => Units.map (algebraMap R F).toMonoidHom u)) = 0 :=
  dvrMilnorTameSymbol'_tuple_principal_unit 0 _ 0 u rfl hu

-- The stronger result kills the whole shift image, not just its residue coefficient.
example {π : R} (hπ : Irreducible π) (l : List Fˣ) (u : Rˣ)
    (hu : Units.map (IsLocalRing.residue R).toMonoidHom u = 1)
    (hmem : Units.map (algebraMap R F).toMonoidHom u ∈ l) :
    dvrMilnorShiftMap (F := F) hπ (milnorKSymbolProd F l) = 0 :=
  dvrMilnorShiftMap_symbolProd_principal_unit hπ l u hu hmem
