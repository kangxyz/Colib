/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Symbols.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.MilnorTameSymbol

/-!
# Specialization from the main component of the native DVR shift map

Specialization at a specified uniformizer is the main component of the existing Stacks shift
map, restricted to the existing homogeneous groups. No residue data or quotient is reconstructed.
This adapts the actual-DVR part of `Aglib.KTheory.MilnorK.Residue.Specialization` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. It does not migrate arbitrary twisted abstract residue
data or claim that specialization is independent of the uniformizer.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

/-- The main component of the native shift map preserves homogeneous degree. -/
theorem dvrMilnorShiftMap_main_mem (hπ : Irreducible π) (n : ℕ) {x : MilnorKRing F}
    (hx : x ∈ milnorKGrading F n) :
    MilnorKShift.main (dvrMilnorShiftMap (F := F) hπ x) ∈
      milnorKGrading (IsLocalRing.ResidueField R) n := by
  obtain ⟨t, ht, rfl⟩ := hx
  simp only [SetLike.mem_coe, Submodule.mem_toAddSubgroup] at ht
  exact (mem_milnorKShiftGrading.mp (dvrMilnorTensorMap_mem_milnorKShiftGrading hπ n ht)).1

/-- Specialization at a specified uniformizer is the existing shift map's main component. -/
def dvrMilnorSpecialization (hπ : Irreducible π) (n : ℕ) :
    MilnorKTheory F n →ₗ[ℤ] MilnorKTheory (IsLocalRing.ResidueField R) n :=
  AddMonoidHom.toIntLinearMap
    { toFun x := ⟨MilnorKShift.main (dvrMilnorShiftMap (F := F) hπ x),
        dvrMilnorShiftMap_main_mem hπ n x.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' x y := Subtype.ext (by simp) }

/-- Coercion identifies specialization with the main component, not a separately defined map. -/
@[simp] theorem dvrMilnorSpecialization_coe (hπ : Irreducible π) (n : ℕ)
    (x : MilnorKTheory F n) :
    (dvrMilnorSpecialization hπ n x : MilnorKRing (IsLocalRing.ResidueField R)) =
      MilnorKShift.main (dvrMilnorShiftMap (F := F) hπ x) := rfl

/-- On an ordered list symbol the main component takes the unit part of each entry. -/
theorem main_dvrMilnorShiftMap_symbolProd (hπ : Irreducible π) (l : List Fˣ) :
    MilnorKShift.main (dvrMilnorShiftMap (F := F) hπ (milnorKSymbolProd F l)) =
      milnorKSymbolProd (IsLocalRing.ResidueField R) (l.map (dvrFracUnitPart hπ)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [milnorKSymbolProd_cons, map_mul, ih, dvrMilnorShiftMap_milnorKSymbol]

/-- Specialization has exactly the coordinatewise unit-part formula in every degree. -/
@[simp] theorem dvrMilnorSpecialization_tupleSymbol (hπ : Irreducible π) (n : ℕ)
    (a : Fin n → Fˣ) :
    dvrMilnorSpecialization hπ n (milnorKTupleSymbol a) =
      milnorKTupleSymbol (dvrFracUnitPart hπ ∘ a) := by
  apply Subtype.ext
  simp [main_dvrMilnorShiftMap_symbolProd, List.map_ofFn, Function.comp_def]

/-- On actual ring units, specialization is literal residue reduction. -/
theorem dvrMilnorSpecialization_ringUnits (hπ : Irreducible π) (n : ℕ) (a : Fin n → Rˣ) :
    dvrMilnorSpecialization hπ n
      (milnorKTupleSymbol (Units.map (algebraMap R F).toMonoidHom ∘ a)) =
        milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a) := by
  rw [dvrMilnorSpecialization_tupleSymbol]
  congr 1
  funext i
  exact dvrFracUnitPart_unitsMap hπ (a i)

/-- Any slot occupied by the specified uniformizer makes specialization zero. -/
theorem dvrMilnorSpecialization_tuple_uniformizer (hπ : Irreducible π) (n : ℕ)
    (a : Fin n → Fˣ) (i : Fin n) (hi : a i = dvrFracUniformizer F hπ) :
    dvrMilnorSpecialization hπ n (milnorKTupleSymbol a) = 0 := by
  rw [dvrMilnorSpecialization_tupleSymbol]
  apply milnorKTupleSymbol_eq_zero_of_eq_one _ i
  change dvrFracUnitPart hπ (a i) = 1
  rw [hi]
  exact (dvrFracUnitPart_eq_of_eq (u := 1) (n := 1) hπ (by simp)).trans (Units.ext (by simp))

end Stacks.Chow

attribute [colib_tag "COL-0132"] Stacks.Chow.dvrMilnorSpecialization
  Stacks.Chow.dvrMilnorSpecialization_tupleSymbol Stacks.Chow.dvrMilnorSpecialization_ringUnits
  Stacks.Chow.dvrMilnorSpecialization_tuple_uniformizer

add_to_stacks 0EAY
  "Construction consequence: specified-uniformizer specialization is the shift map main component"
  Stacks.Chow.dvrMilnorSpecialization
