/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Symbols.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.MilnorTameSymbol

/-!
# Repeated uniformizers in the native tame residue

The relation `ξ² = {-1} ξ` in the existing Milnor shift ring retains every repeated-uniformizer
sign. This proves the specified-uniformizer specialization of
`MilnorK.residue_symbol_uniformizers` in `Aglib.KTheory.MilnorK.Residue.Basic` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. It does not assert the canonical arbitrary-uniformizer
version, which additionally uses uniformizer independence.
-/

@[expose] public noncomputable section

universe u v

namespace MilnorKShift

variable {k : Type u} [Field k]

/-- Every positive power of the native shift generator retains its full `{-1}` coefficient. -/
theorem mk_zero_one_pow_succ (n : ℕ) :
    (mk 0 1 : MilnorKShift k) ^ (n + 1) = mk 0 (milnorKNegOne k ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    apply ext <;> simp [pow_succ]

end MilnorKShift

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

/-- The specified uniformizer maps to the native shift generator. -/
theorem dvrMilnorShiftMap_symbol_uniformizer (hπ : Irreducible π) :
    dvrMilnorShiftMap (F := F) hπ (milnorKSymbol F (dvrFracUniformizer F hπ)) =
      MilnorKShift.mk 0 1 := by
  have hord : dvrFracOrd (F := F) hπ (dvrFracUniformizer F hπ) = 1 :=
    dvrFracOrd_eq_of_eq (u := 1) (n := 1) hπ (by simp)
  have hpart : dvrFracUnitPart (F := F) hπ (dvrFracUniformizer F hπ) = 1 :=
    (dvrFracUnitPart_eq_of_eq (u := 1) (n := 1) hπ (by simp)).trans (Units.ext (by simp))
  rw [dvrMilnorShiftMap_milnorKSymbol]
  apply MilnorKShift.ext <;> simp [hpart, hord]

/-- The residue of `n+1` copies of the specified uniformizer is `n` copies of `-1`. -/
theorem dvrMilnorTameSymbol_tuple_uniformizers (hπ : Irreducible π) (n : ℕ) :
    dvrMilnorTameSymbol hπ n
      (milnorKTupleSymbol (fun _ : Fin (n + 1) => dvrFracUniformizer F hπ)) =
        milnorKTupleSymbol (fun _ : Fin n => (-1 : (IsLocalRing.ResidueField R)ˣ)) := by
  apply Subtype.ext
  simp only [dvrMilnorTameSymbol_coe, coe_milnorKTupleSymbol, milnorKSymbolProd,
    List.ofFn_const, List.map_replicate, List.prod_replicate, map_pow]
  rw [dvrMilnorShiftMap_symbol_uniformizer, MilnorKShift.mk_zero_one_pow_succ,
    MilnorKShift.shift_mk]
  rw [milnorKNegOne_eq]

end Stacks.Chow

attribute [colib_tag "COL-0125"] Stacks.Chow.dvrMilnorTameSymbol_tuple_uniformizers

add_to_stacks 0EAY
  "Construction consequence: repeated specified uniformizers give the exact tuple of minus ones"
  Stacks.Chow.dvrMilnorTameSymbol_tuple_uniformizers
