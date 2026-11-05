/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Symbols.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.MilnorTameSymbol
public import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Principal-unit vanishing for native DVR residues

A symbol containing a principal unit in any slot has zero tame residue, even when all other
entries are arbitrary fraction-field units. The stronger intermediate statement is that the
whole native shift-ring image vanishes. We use the Stacks map, unit-part and valuation formulas;
no new valuation data, residue construction, or Milnor model is introduced.

This adapts `MilnorK.DVR.residue_principal_ring_unit` from
`Aglib.KTheory.MilnorK.Residue.DVR` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. Both ring and fraction-field universes are independent.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

/-- A principal ring unit has zero image in the entire native Milnor shift ring. -/
theorem dvrMilnorShiftMap_symbol_principal_unit (hπ : Irreducible π) (u : Rˣ)
    (hu : Units.map (IsLocalRing.residue R).toMonoidHom u = 1) :
    dvrMilnorShiftMap (F := F) hπ
      (milnorKSymbol F (Units.map (algebraMap R F).toMonoidHom u)) = 0 := by
  rw [dvrMilnorShiftMap_milnorKSymbol]
  apply MilnorKShift.ext
  · change milnorKSymbol (IsLocalRing.ResidueField R) _ = 0
    have hp := dvrFracUnitPart_unitsMap (F := F) hπ u
    exact (congrArg (milnorKSymbol (IsLocalRing.ResidueField R)) (hp.trans hu)).trans
      milnorKSymbol_one
  · simp [dvrFracOrd_unitsMap]

/-- A principal unit anywhere in an ordered symbol kills the entire shift-ring image. -/
theorem dvrMilnorShiftMap_symbolProd_principal_unit (hπ : Irreducible π)
    (l : List Fˣ) (u : Rˣ)
    (hu : Units.map (IsLocalRing.residue R).toMonoidHom u = 1)
    (hmem : Units.map (algebraMap R F).toMonoidHom u ∈ l) :
    dvrMilnorShiftMap (F := F) hπ (milnorKSymbolProd F l) = 0 := by
  rw [milnorKSymbolProd, map_list_prod, List.map_map]
  apply List.prod_eq_zero
  exact List.mem_map.mpr ⟨_, hmem, dvrMilnorShiftMap_symbol_principal_unit hπ u hu⟩

/-- Tame residue at any uniformizer vanishes if any tuple entry is a principal ring unit. -/
theorem dvrMilnorTameSymbol_tuple_principal_unit (hπ : Irreducible π) (n : ℕ)
    (a : Fin (n + 1) → Fˣ) (i : Fin (n + 1)) (u : Rˣ)
    (hi : a i = Units.map (algebraMap R F).toMonoidHom u)
    (hu : Units.map (IsLocalRing.residue R).toMonoidHom u = 1) :
    dvrMilnorTameSymbol hπ n (milnorKTupleSymbol a) = 0 := by
  apply Subtype.ext
  rw [dvrMilnorTameSymbol_coe, coe_milnorKTupleSymbol,
    dvrMilnorShiftMap_symbolProd_principal_unit hπ _ u hu]
  · rfl
  · exact List.mem_ofFn.mpr ⟨i, hi⟩

/-- The canonical native DVR residue kills a tuple with a principal ring unit in any slot. -/
theorem dvrMilnorTameSymbol'_tuple_principal_unit (n : ℕ)
    (a : Fin (n + 1) → Fˣ) (i : Fin (n + 1)) (u : Rˣ)
    (hi : a i = Units.map (algebraMap R F).toMonoidHom u)
    (hu : Units.map (IsLocalRing.residue R).toMonoidHom u = 1) :
    dvrMilnorTameSymbol' R F n (milnorKTupleSymbol a) = 0 :=
  dvrMilnorTameSymbol_tuple_principal_unit
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec n a i u hi hu

end Stacks.Chow

attribute [colib_tag "COL-0122"] Stacks.Chow.dvrMilnorShiftMap_symbol_principal_unit
  Stacks.Chow.dvrMilnorShiftMap_symbolProd_principal_unit
  Stacks.Chow.dvrMilnorTameSymbol_tuple_principal_unit
  Stacks.Chow.dvrMilnorTameSymbol'_tuple_principal_unit

add_to_stacks 0EAY
  "Construction consequence: a principal unit kills the native DVR tame residue in any tuple slot"
  Stacks.Chow.dvrMilnorTameSymbol'_tuple_principal_unit
