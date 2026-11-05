/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Symbols.Surjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.MilnorTameSymbol

/-!
# Surjectivity of the native DVR residue

Every residue-field unit lifts to a unit in the local ring. Appending the chosen uniformizer
to a tuple of such lifts produces a preimage under the native tame symbol. Existing homogeneous
symbol extensionality then gives surjectivity in all degrees, including degree zero.

This is a direct consequence of the native normalization in Stacks Project Tag 0EAY, not an
asserted same-name Aglib source theorem. It needs neither uniformizer independence nor the
high-level norm imports, and reconstructs no residue or Milnor model.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

/-- The native residue for any specified uniformizer is surjective in every degree. -/
theorem dvrMilnorTameSymbol_surjective (hπ : Irreducible π) (n : ℕ) :
    Function.Surjective (dvrMilnorTameSymbol (F := F) hπ n) := by
  apply milnorKTheory_surjective_of_tupleSymbol
  intro a
  have hsurj := IsLocalRing.surjective_units_map_of_local_ringHom (IsLocalRing.residue R)
    IsLocalRing.residue_surjective inferInstance
  choose b hb using fun i => hsurj (a i)
  let z : MilnorKTheory F (n + 1) := GradedMonoid.GMul.mul (i := n) (j := 1)
    (milnorKTupleSymbol (Units.map (algebraMap R F).toMonoidHom ∘ b))
    (milnorKTupleSymbol ![dvrFracUniformizer F hπ])
  refine ⟨z, ?_⟩
  apply Subtype.ext
  have hz : (z : MilnorKRing F) =
      unitSymbolProd F (List.ofFn b) * milnorKSymbol F (dvrFracUniformizer F hπ) := by
    simp [z, coe_milnorKTupleSymbol, unitSymbolProd, List.map_ofFn, List.ofFn_succ,
      Function.comp_def]
  rw [dvrMilnorTameSymbol_uniformizer hπ n (List.ofFn b) hz]
  have hbfun : Units.map (IsLocalRing.residue R).toMonoidHom ∘ b = a := funext hb
  simp only [residueSymbolProd, List.map_ofFn, hbfun, coe_milnorKTupleSymbol]

/-- The canonical native DVR residue is surjective in every nonnegative target degree. -/
theorem dvrMilnorTameSymbol'_surjective (n : ℕ) :
    Function.Surjective (dvrMilnorTameSymbol' R F n) :=
  dvrMilnorTameSymbol_surjective (IsDiscreteValuationRing.exists_irreducible R).choose_spec n

end Stacks.Chow

attribute [colib_tag "COL-0133"] Stacks.Chow.dvrMilnorTameSymbol_surjective
  Stacks.Chow.dvrMilnorTameSymbol'_surjective

add_to_stacks 0EAY "Consequence of unit-plus-uniformizer normalization and residue-unit lifting"
  Stacks.Chow.dvrMilnorTameSymbol_surjective
