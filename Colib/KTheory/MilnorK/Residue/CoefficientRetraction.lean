/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Residue.Specialization
public import Colib.KTheory.MilnorK.Symbols.Transport
public import Colib.Util.References

/-!
# Coefficient fields and native DVR specialization

For an actual field map `c : k → R` into a DVR, specialization of its fraction-field image is
transport along `residue ∘ c`. If this residue-field embedding has a specified field retraction,
its image in the fraction field induces a split injection in every Milnor degree.

This is a low-level consequence of the native DVR unit formula. It isolates the coefficient-field
mechanism underlying the higher Stacks `MilnorNorm.ConstantRetraction` construction, without
redefining that rational-function model or claiming a new proof of its existing concrete theorem.
The residue-field retraction is explicit data with a checked composition equation; no particular
DVR is asserted to admit one. All three universes are independent.
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]
  {k : Type w} [Field k] {π : R}

/-- Specialization of any coefficient-field class is literal residue-field transport. -/
theorem dvrMilnorSpecialization_baseField (hπ : Irreducible π) (c : k →+* R) (n : ℕ) :
    (dvrMilnorSpecialization (F := F) hπ n).comp
        (milnorKTheoryMap ((algebraMap R F).comp c) n) =
      milnorKTheoryMap ((IsLocalRing.residue R).comp c) n := by
  apply milnorKTheory_linearMap_ext
  intro a
  simp only [LinearMap.comp_apply, milnorKTheoryMap_tupleSymbol]
  have hfield : Units.map ((algebraMap R F).comp c).toMonoidHom ∘ a =
      Units.map (algebraMap R F).toMonoidHom ∘ (Units.map c.toMonoidHom ∘ a) := by
    funext i
    apply Units.ext
    rfl
  rw [hfield, dvrMilnorSpecialization_ringUnits]
  congr 1

/-- An actual residue-field retraction gives a retraction of the native Milnor field map. -/
theorem dvrMilnorSpecialization_baseField_retraction (hπ : Irreducible π)
    (c : k →+* R) (g : IsLocalRing.ResidueField R →+* k)
    (hc : g.comp ((IsLocalRing.residue R).comp c) = RingHom.id k) (n : ℕ) :
    ((milnorKTheoryMap g n).comp (dvrMilnorSpecialization (F := F) hπ n)).comp
        (milnorKTheoryMap ((algebraMap R F).comp c) n) = LinearMap.id := by
  rw [LinearMap.comp_assoc, dvrMilnorSpecialization_baseField, ← milnorKTheoryMap_comp,
    hc, milnorKTheoryMap_id]

/-- A split residue-field embedding yields an injective Milnor map to the fraction field. -/
theorem milnorKTheoryMap_injective_of_dvr_coefficient_retraction
    (c : k →+* R) (g : IsLocalRing.ResidueField R →+* k)
    (hc : g.comp ((IsLocalRing.residue R).comp c) = RingHom.id k) (n : ℕ) :
    Function.Injective (milnorKTheoryMap ((algebraMap R F).comp c) n) := by
  have h := dvrMilnorSpecialization_baseField_retraction (F := F)
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec c g hc n
  have hleft : Function.LeftInverse
      ((milnorKTheoryMap g n).comp (dvrMilnorSpecialization (F := F)
        (IsDiscreteValuationRing.exists_irreducible R).choose_spec n))
      (milnorKTheoryMap ((algebraMap R F).comp c) n) := fun x => LinearMap.congr_fun h x
  exact hleft.injective

end Stacks.Chow

attribute [colib_tag "COL-0135"] Stacks.Chow.dvrMilnorSpecialization_baseField
  Stacks.Chow.dvrMilnorSpecialization_baseField_retraction
  Stacks.Chow.milnorKTheoryMap_injective_of_dvr_coefficient_retraction

add_to_stacks 0EAY
  "DVR tame-symbol background only; coefficient splitting follows from native specialization"
  Stacks.Chow.dvrMilnorSpecialization_baseField_retraction
