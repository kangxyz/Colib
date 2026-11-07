/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.FractionUnits
public import Colib.Util.References

/-!
# The native DVR order under a ramified field map

An actual compatible ring/field square and an equality `j π = u ρ^e` imply that integer orders
are multiplied by `e`. This adapts `MilnorK.K2.DVR.ramified_value_map` in
`Aglib.KTheory.MilnorK.K2.DVR.RamifiedRestriction`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, lines 149–155. The proof uses native fraction-unit
decomposition and uniqueness. It creates no normalized-lift or valuation model. No local-map
hypothesis is needed for this order equality once the actual ramification equality is supplied.
-/

@[expose] public noncomputable section

universe u v w z

namespace Stacks.Chow

variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type w} {E : Type z} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) (f : F →+* E)
  (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
  {π : R} {ρ : S}

include hf

/-- Actual ramification of the uniformizer multiplies native integer orders by its exponent. -/
theorem dvrFracOrd_map_ramified (hπ : Irreducible π) (hρ : Irreducible ρ)
    (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e) (x : Fˣ) :
    dvrFracOrd hρ (Units.map f.toMonoidHom x) =
      (e : ℤ) * dvrFracOrd hπ x := by
  obtain ⟨a, ha, -⟩ := exists_eq_unit_mul_zpow hπ x
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
  apply dvrFracOrd_eq_of_eq (u := Units.map j.toMonoidHom a * u ^ dvrFracOrd hπ x) hρ
  have hval (b : Sˣ) (m : ℤ) :
      ((Units.map (algebraMap S E).toMonoidHom b *
        (dvrFracUniformizer E hρ) ^ m : Eˣ) : E) =
      algebraMap S E (b : S) * (algebraMap S E ρ) ^ m := by simp
  exact (congrArg Units.val hx).trans (hval _ _)

end Stacks.Chow

attribute [colib_tag "COL-0140"] Stacks.Chow.dvrFracOrd_map_ramified
