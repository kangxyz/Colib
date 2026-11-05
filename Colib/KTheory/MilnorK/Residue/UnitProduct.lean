/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Symbols.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.MilnorTameSymbol

/-!
# Left ring-unit products and the native DVR residue

The tame residue commutes with left multiplication by a tuple of actual ring units, reduced
by the literal residue map. Its right factor is an arbitrary homogeneous Milnor class. Both
multiplication and residue are the existing native operations.

This adapts `MilnorK.DVR.residue_product_ring_units_left` in
`Aglib.KTheory.MilnorK.Residue.Product` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. No positive-degree or characteristic restriction is
introduced. The source's associativity cast is definitional for the native natural-number grading.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

/-- The residue at a specified uniformizer commutes with a left tuple of ring units. -/
theorem dvrMilnorTameSymbol_unitTuple_mul (hπ : Irreducible π) (m n : ℕ)
    (a : Fin m → Rˣ) (z : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol hπ (m + n)
      (GradedMonoid.GMul.mul (i := m) (j := n + 1)
        (milnorKTupleSymbol (Units.map (algebraMap R F).toMonoidHom ∘ a)) z) =
      GradedMonoid.GMul.mul (i := m) (j := n)
        (milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a))
        (dvrMilnorTameSymbol hπ n z) := by
  apply Subtype.ext
  simp only [dvrMilnorTameSymbol_coe, SetLike.coe_gMul, coe_milnorKTupleSymbol]
  have hunit : milnorKSymbolProd F
      (List.ofFn (Units.map (algebraMap R F).toMonoidHom ∘ a)) =
        unitSymbolProd F (List.ofFn a) := by
    simp only [unitSymbolProd, List.map_ofFn, Function.comp_def]
    rfl
  rw [hunit, map_mul, dvrMilnorShiftMap_unitSymbolProd]
  simp [residueSymbolProd, List.map_ofFn, Function.comp_def]

/-- The canonical native DVR residue commutes with a left tuple of actual ring units. -/
theorem dvrMilnorTameSymbol'_unitTuple_mul (m n : ℕ)
    (a : Fin m → Rˣ) (z : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol' R F (m + n)
      (GradedMonoid.GMul.mul (i := m) (j := n + 1)
        (milnorKTupleSymbol (Units.map (algebraMap R F).toMonoidHom ∘ a)) z) =
      GradedMonoid.GMul.mul (i := m) (j := n)
        (milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a))
        (dvrMilnorTameSymbol' R F n z) :=
  dvrMilnorTameSymbol_unitTuple_mul
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec m n a z

end Stacks.Chow

attribute [colib_tag "COL-0127"] Stacks.Chow.dvrMilnorTameSymbol_unitTuple_mul
  Stacks.Chow.dvrMilnorTameSymbol'_unitTuple_mul

add_to_stacks 0EAY
  "Construction consequence: a left ring-unit tuple reduces and multiplies the residue of any class"
  Stacks.Chow.dvrMilnorTameSymbol'_unitTuple_mul
