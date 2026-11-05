/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Residue.RamifiedMap
public import Colib.Util.References

/-!
# Canonical ramified DVR residues

The general ramified square, specialized to the identity field map and exponent one, proves
uniformizer independence directly. This gives a low-dependency route to the already existing
native uniformizer-independence statement; it does not duplicate the upstream twist proof or
define another residue. The bridge names are distinct from the statements in the high-import
`DvrTameSymbol.Invariance` module and can coexist with that module.

The final canonical square adapts `MilnorK.DVR.residue_ramified_restrict` in
`Aglib.KTheory.MilnorK.Residue.RamifiedRestriction`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, lines 161–172, now including its canonical
uniformizer identification. All four universes remain independent.
-/

@[expose] public noncomputable section

universe u v w z

namespace Stacks.Chow

section Independence

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]

/-- Native uniformizer independence as the exponent-one identity case of ramified restriction.
This has the same conclusion as upstream `dvrMilnorTameSymbol_irreducible_congr`, with a
low-dependency proof through the general ramified theorem. -/
theorem dvrMilnorTameSymbol_eq_of_ramified_identity {π ρ : R}
    (hπ : Irreducible π) (hρ : Irreducible ρ) (n : ℕ) :
    dvrMilnorTameSymbol (F := F) hρ n = dvrMilnorTameSymbol (F := F) hπ n := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible R hρ hπ
  have hπmap : (RingHom.id R) π = (u : R) * ρ ^ 1 := by
    simpa only [RingHom.id_apply, pow_one, mul_comm] using hu.symm
  have h := dvrMilnorTameSymbol_map_ramified (RingHom.id R) (RingHom.id F)
    (fun _ => rfl) hπ hρ u 1 hπmap n
  simp only [IsLocalRing.ResidueField.map_id, milnorKTheoryMap_id,
    Nat.cast_one, one_smul] at h
  exact h


/-- The native canonical residue agrees with any specified uniformizer, via ramified restriction.
This is a low-dependency bridge to upstream `dvrMilnorTameSymbol'_eq`. -/
theorem dvrMilnorTameSymbol'_eq_of_ramified_identity {π : R}
    (hπ : Irreducible π) (n : ℕ) :
    dvrMilnorTameSymbol' R F n = dvrMilnorTameSymbol (F := F) hπ n :=
  dvrMilnorTameSymbol_eq_of_ramified_identity hπ
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec n

end Independence

variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type w} {E : Type z} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) [IsLocalHom j] (f : F →+* E)
  (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
  {π : R} {ρ : S}

include hf

/-- The canonical native residue square for a ramified local DVR map, in every degree. -/
theorem dvrMilnorTameSymbol'_map_ramified (hπ : Irreducible π) (hρ : Irreducible ρ)
    (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e) (n : ℕ) :
    (dvrMilnorTameSymbol' S E n).comp (milnorKTheoryMap f (n + 1)).toAddMonoidHom =
      (e : ℤ) • ((milnorKTheoryMap (IsLocalRing.ResidueField.map j) n).toAddMonoidHom.comp
        (dvrMilnorTameSymbol' R F n)) := by
  rw [dvrMilnorTameSymbol'_eq_of_ramified_identity hρ,
    dvrMilnorTameSymbol'_eq_of_ramified_identity hπ]
  exact dvrMilnorTameSymbol_map_ramified j f hf hπ hρ u e hπmap n

end Stacks.Chow

attribute [colib_tag "COL-0150"] Stacks.Chow.dvrMilnorTameSymbol'_map_ramified
attribute [stacks 0EAY "DVR tame-symbol background; canonical ramified comparison proved here"]
  Stacks.Chow.dvrMilnorTameSymbol'_map_ramified
