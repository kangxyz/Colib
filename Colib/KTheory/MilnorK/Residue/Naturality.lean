/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Residue.Specialization
public import Colib.KTheory.MilnorK.Symbols.Transport

/-!
# Specialization under an unramified local map of discrete valuation rings

The native fraction-unit decomposition proves unit-part compatibility for an actual local ring
map and a compatible fraction-field map taking a specified uniformizer to a uniformizer. Thus
naturality does not assume an abstract unit-part compatibility interface. This specializes
`MilnorK.specialize_restrict` in `Aglib.KTheory.MilnorK.Residue.Restriction` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f` to actual DVRs, using the hypotheses of its DVR section.
Specialization still depends on the specified uniformizer; no canonical independence is claimed.
-/

@[expose] public noncomputable section

universe u v w z

namespace Stacks.Chow

variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type w} {E : Type z} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) [IsLocalHom j] (f : F →+* E)
  (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
  {π : R}
include hf

/-- Mapping the native DVR decomposition proves compatibility of the actual unit parts. -/
theorem dvrFracUnitPart_map (hπ : Irreducible π) (hjπ : Irreducible (j π)) (x : Fˣ) :
    dvrFracUnitPart hjπ (Units.map f.toMonoidHom x) =
      Units.map (IsLocalRing.ResidueField.map j).toMonoidHom (dvrFracUnitPart hπ x) := by
  obtain ⟨u, hu, hpart⟩ := exists_eq_unit_mul_zpow hπ x
  have hmap : ((Units.map f.toMonoidHom x : Eˣ) : E) =
      algebraMap S E ((Units.map j.toMonoidHom u : Sˣ) : S) *
        (algebraMap S E (j π)) ^ dvrFracOrd hπ x := by
    change f (x : F) = _
    rw [hu, map_mul, map_zpow₀, hf, hf]
    rfl
  rw [dvrFracUnitPart_eq_of_eq hjπ hmap, hpart]
  apply Units.ext
  exact (IsLocalRing.ResidueField.map_residue j (u : R)).symm

/-- The specialization square for actual DVR maps, in every degree and independent universes. -/
theorem dvrMilnorSpecialization_map (hπ : Irreducible π) (hjπ : Irreducible (j π)) (n : ℕ) :
    (milnorKTheoryMap (IsLocalRing.ResidueField.map j) n).comp
        (dvrMilnorSpecialization (F := F) hπ n) =
      (dvrMilnorSpecialization (F := E) hjπ n).comp (milnorKTheoryMap f n) := by
  apply milnorKTheory_linearMap_ext
  intro a
  simp only [LinearMap.comp_apply, dvrMilnorSpecialization_tupleSymbol,
    milnorKTheoryMap_tupleSymbol]
  congr 1
  funext i
  exact (dvrFracUnitPart_map j f hf hπ hjπ (a i)).symm

end Stacks.Chow

attribute [colib_tag "COL-0130"] Stacks.Chow.dvrFracUnitPart_map
  Stacks.Chow.dvrMilnorSpecialization_map

add_to_stacks 0EAY "Construction consequence: specialization for uniformizer-preserving local maps"
  Stacks.Chow.dvrMilnorSpecialization_map
