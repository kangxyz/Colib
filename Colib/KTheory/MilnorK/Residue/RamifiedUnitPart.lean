/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.FractionUnits

/-!
# Angular components under ramified DVR maps

This is the actual unit-part transformation needed by higher-degree ramified residues.
It adapts `MilnorK.K2.DVR.ramified_unitResidue_map` in
`Aglib.KTheory.MilnorK.K2.DVR.RamifiedRestriction`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, lines 175–184. Both DVRs and their fraction
fields have independent universes. The ramification unit is retained literally, including
its possibly negative power. This is not yet the all-degree residue identity.
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
  {π : R} {ρ : S}

include hf

/-- The angular component acquires the residue of the ramification unit to the source order. -/
theorem dvrFracUnitPart_map_ramified (hπ : Irreducible π) (hρ : Irreducible ρ)
    (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e) (x : Fˣ) :
    dvrFracUnitPart hρ (Units.map f.toMonoidHom x) =
      Units.map (IsLocalRing.ResidueField.map j).toMonoidHom (dvrFracUnitPart hπ x) *
        Units.map (IsLocalRing.residue S).toMonoidHom u ^ dvrFracOrd hπ x := by
  obtain ⟨a, ha, hpart⟩ := exists_eq_unit_mul_zpow hπ x
  have hp : Units.map f.toMonoidHom (dvrFracUniformizer F hπ) =
      Units.map (algebraMap S E).toMonoidHom u * (dvrFracUniformizer E hρ) ^ e := by
    apply Units.ext
    change f (algebraMap R F π) = algebraMap S E (u : S) * (algebraMap S E ρ) ^ e
    rw [hf, hπmap, map_mul, map_pow]
  have ha' : x = Units.map (algebraMap R F).toMonoidHom a *
      (dvrFracUniformizer F hπ) ^ dvrFracOrd hπ x := by
    apply Units.ext
    simpa using ha
  have hau : Units.map f.toMonoidHom (Units.map (algebraMap R F).toMonoidHom a) =
      Units.map (algebraMap S E).toMonoidHom (Units.map j.toMonoidHom a) := by
    apply Units.ext
    exact hf (a : R)
  have hx : Units.map f.toMonoidHom x =
      Units.map (algebraMap S E).toMonoidHom
        (Units.map j.toMonoidHom a * u ^ dvrFracOrd hπ x) *
      (dvrFracUniformizer E hρ) ^ ((e : ℤ) * dvrFracOrd hπ x) := by
    conv_lhs => rw [ha']
    rw [map_mul, map_zpow, hau, hp, mul_zpow, ← zpow_natCast, ← zpow_mul]
    simp only [map_mul, map_zpow, mul_assoc]
  have hval (b : Sˣ) (m : ℤ) :
      ((Units.map (algebraMap S E).toMonoidHom b *
        (dvrFracUniformizer E hρ) ^ m : Eˣ) : E) =
      algebraMap S E (b : S) * (algebraMap S E ρ) ^ m := by simp
  rw [dvrFracUnitPart_eq_of_eq hρ ((congrArg Units.val hx).trans (hval _ _)), hpart,
    map_mul, map_zpow]
  congr 1

end Stacks.Chow
