/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Residue.CanonicalRamifiedMap
public import Colib.RingTheory.KTheory.MilnorK.Residue.RepeatedUniformizer

/-!
# Canonical residue normalization at any uniformizer

These specialize the native uniformizer formula to ordered tuples and discharge the previously
pending canonical version of the repeated-uniformizer formula. They adapt
`MilnorK.DVR.residue_ring_units_uniformizer` and `MilnorK.DVR.residue_uniformizers` in
`Aglib.KTheory.MilnorK.Residue.DVR`, revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`,
lines 74–86 and 105–110. The repeated `{-1}` symbol is retained, including characteristic two;
no nonvanishing claim is made.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

/-- Appending any uniformizer to ring units gives literal reduction under the canonical residue. -/
theorem dvrMilnorTameSymbol'_tuple_snoc_uniformizer (hπ : Irreducible π)
    (n : ℕ) (a : Fin n → Rˣ) :
    dvrMilnorTameSymbol' R F n
        (milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap R F).toMonoidHom ∘ a)
          (dvrFracUniformizer F hπ))) =
      milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) := by
  rw [dvrMilnorTameSymbol'_eq_of_ramified_identity hπ]
  apply Subtype.ext
  have h := dvrMilnorTameSymbol_uniformizer (F := F) hπ n (List.ofFn a)
    (y := milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap R F).toMonoidHom ∘ a)
      (dvrFracUniformizer F hπ))) (by
        rw [coe_milnorKTupleSymbol, List.ofFn_succ']
        simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
          milnorKSymbolProd_append, milnorKSymbolProd_singleton, unitSymbolProd,
          List.map_ofFn, Function.comp_def]
        rfl)
  simpa only [coe_milnorKTupleSymbol, residueSymbolProd, List.map_ofFn, Function.comp_def] using h

/-- The canonical residue of repeated copies of any uniformizer retains the full sign symbol. -/
theorem dvrMilnorTameSymbol'_tuple_uniformizers (hπ : Irreducible π) (n : ℕ) :
    dvrMilnorTameSymbol' R F n
      (milnorKTupleSymbol (fun _ : Fin (n + 1) => dvrFracUniformizer F hπ)) =
        milnorKTupleSymbol (fun _ : Fin n => (-1 : (IsLocalRing.ResidueField R)ˣ)) := by
  rw [dvrMilnorTameSymbol'_eq_of_ramified_identity hπ]
  exact dvrMilnorTameSymbol_tuple_uniformizers hπ n

end Stacks.Chow

attribute [colib_tag "COL-0152"]
  Stacks.Chow.dvrMilnorTameSymbol'_tuple_snoc_uniformizer
  Stacks.Chow.dvrMilnorTameSymbol'_tuple_uniformizers
attribute [stacks 0EAY "DVR tame-symbol background; canonical tuple normalizations proved here"]
  Stacks.Chow.dvrMilnorTameSymbol'_tuple_snoc_uniformizer
  Stacks.Chow.dvrMilnorTameSymbol'_tuple_uniformizers
