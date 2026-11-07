/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Norm.DVROrder
public import Colib.RingTheory.Norm.DVRPrimeUniformizer

/-!
# Native angular components of ordinary DVR norms

An actual normalized integral coefficient determines the angular component of the norm of
an arbitrary fraction-field unit, including negative order. The general formula keeps the
ramification exponent. The exponent-one corollary is unconditional under the finite local DVR
hypotheses; the prime-degree corollary retains Henselianity and exponent invertibility.
No Milnor norm or all-degree norm–residue square is claimed in this arithmetic leaf.

-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Chow

section UnitPartPowers

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

/-- Integer powers of the existing native angular component. -/
theorem dvrFracUnitPart_zpow (hπ : Irreducible π) (x : Fˣ) (n : ℤ) :
    dvrFracUnitPart hπ (x ^ n) = dvrFracUnitPart hπ x ^ n := by
  unfold dvrFracUnitPart
  rw [map_zpow]
  change Units.map (residue R).toMonoidHom
      (((dvrFracUnitsEquiv F hπ).symm x).1 ^ n) =
    (Units.map (residue R).toMonoidHom ((dvrFracUnitsEquiv F hπ).symm x).1) ^ n
  exact map_zpow (Units.map (residue R).toMonoidHom) _ _

end UnitPartPowers

variable (R S : Type u) (F E : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E] {π : R} {ϖ : S}

/-- The angular component of the ordinary norm of a genuine ring unit. -/
theorem dvrFracUnitPart_norm_unitsMap
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (a : Sˣ) :
    dvrFracUnitPart hπ
        (Units.map (Algebra.norm F) (Units.map (algebraMap S E).toMonoidHom a)) =
      Units.map (Algebra.norm (ResidueField R))
        (Units.map (residue S).toMonoidHom a) ^ e := by
  rw [Algebra.norm_unitsMap_eq_intNorm R S F E]
  rw [dvrFracUnitPart_eq_of_eq
    (u := Units.map (Algebra.intNorm R S) a) (n := 0) hπ (by simp)]
  exact Algebra.residueUnits_intNorm_eq_norm_pow R S hπ hϖ u e he a

/-- An exact integral coefficient identifies the actual angular component of the ordinary
field norm of the extension uniformizer. -/
theorem dvrFracUnitPart_norm_uniformizer_of_coefficient
    (hπ : Irreducible π) (hϖ : Irreducible ϖ) (b₀ : Rˣ)
    (hb₀ : Algebra.intNorm R S ϖ =
      π ^ Module.finrank (ResidueField R) (ResidueField S) * (b₀ : R)) :
    dvrFracUnitPart hπ (Units.map (Algebra.norm F) (dvrFracUniformizer E hϖ)) =
      Units.map (residue R).toMonoidHom b₀ := by
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  apply dvrFracUnitPart_eq_of_eq
    (u := b₀) (n := (Module.finrank (ResidueField R) (ResidueField S) : ℤ)) hπ
  change Algebra.norm F (algebraMap S E ϖ) =
    algebraMap R F (b₀ : R) * (algebraMap R F π) ^
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ)
  have hnorm : algebraMap R F (Algebra.intNorm R S ϖ) =
      Algebra.norm F (algebraMap S E ϖ) :=
    Algebra.algebraMap_intNorm (A := R) (B := S) (K := F) (L := E) ϖ
  rw [← hnorm, hb₀, map_mul, map_pow, zpow_natCast, mul_comm]

/-- The ordinary norm angular component for arbitrary fraction-field units, including poles.
The ramification exponent remains in the formula. -/
theorem dvrFracUnitPart_norm_of_coefficient
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (b₀ : Rˣ) (hb₀ : Algebra.intNorm R S ϖ =
      π ^ Module.finrank (ResidueField R) (ResidueField S) * (b₀ : R)) (b : Eˣ) :
    dvrFracUnitPart hπ (Units.map (Algebra.norm F) b) =
      Units.map (Algebra.norm (ResidueField R)) (dvrFracUnitPart hϖ b) ^ e *
        (Units.map (residue R).toMonoidHom b₀) ^ dvrFracOrd hϖ b := by
  obtain ⟨a, ha, hpart⟩ := exists_eq_unit_mul_zpow hϖ b
  have hb : b = Units.map (algebraMap S E).toMonoidHom a *
      dvrFracUniformizer E hϖ ^ dvrFracOrd hϖ b := by
    apply Units.ext
    simpa using ha
  conv_lhs => rw [hb]
  rw [map_mul, map_zpow, dvrFracUnitPart_mul,
    dvrFracUnitPart_norm_unitsMap R S F E hπ hϖ u e he a, dvrFracUnitPart_zpow,
    dvrFracUnitPart_norm_uniformizer_of_coefficient R S F E hπ hϖ b₀ hb₀, hpart]

/-- Substitution of the supplied exact signed residue coefficient. -/
theorem dvrFracUnitPart_norm_of_exact_coefficient
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (b₀ : Rˣ) (hb₀ : Algebra.intNorm R S ϖ =
      π ^ Module.finrank (ResidueField R) (ResidueField S) * (b₀ : R))
    (hres : residue R (b₀ : R) =
      (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹) (b : Eˣ) :
    dvrFracUnitPart hπ (Units.map (Algebra.norm F) b) =
      Units.map (Algebra.norm (ResidueField R)) (dvrFracUnitPart hϖ b) ^ e *
        (((-1 : (ResidueField R)ˣ) ^
            (Module.finrank (ResidueField R) (ResidueField S) * (e - 1))) *
          (Units.map (Algebra.norm (ResidueField R))
            (Units.map (residue S).toMonoidHom u))⁻¹) ^ dvrFracOrd hϖ b := by
  have hresUnits : Units.map (residue R).toMonoidHom b₀ =
      ((-1 : (ResidueField R)ˣ) ^
        (Module.finrank (ResidueField R) (ResidueField S) * (e - 1))) *
        (Units.map (Algebra.norm (ResidueField R))
          (Units.map (residue S).toMonoidHom u))⁻¹ := by
    apply Units.ext
    simpa using hres
  rw [dvrFracUnitPart_norm_of_coefficient R S F E hπ hϖ u e he b₀ hb₀ b, hresUnits]

/-- Exponent one requires neither Henselianity nor prime field degree. -/
theorem dvrFracUnitPart_norm_of_exponent_one
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (he : algebraMap R S π = (u : S) * ϖ) (b : Eˣ) :
    dvrFracUnitPart hπ (Units.map (Algebra.norm F) b) =
      Units.map (Algebra.norm (ResidueField R)) (dvrFracUnitPart hϖ b) *
        (Units.map (Algebra.norm (ResidueField R))
          (Units.map (residue S).toMonoidHom u))⁻¹ ^ dvrFracOrd hϖ b := by
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  obtain ⟨b₀, hb₀, hres⟩ :=
    IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_exponent_one
      R S F E hπ hϖ u he
  have he1 : algebraMap R S π = (u : S) * ϖ ^ 1 := by simpa only [pow_one] using he
  have hresUnits : Units.map (residue R).toMonoidHom b₀ =
      (Units.map (Algebra.norm (ResidueField R))
        (Units.map (residue S).toMonoidHom u))⁻¹ := by
    apply Units.ext
    simpa using hres
  simpa only [pow_one, hresUnits] using
    dvrFracUnitPart_norm_of_coefficient R S F E hπ hϖ u 1 he1 b₀ hb₀ b

/-- The existing prime-degree coefficient supplies the angular formula, retaining its actual
Henselianity and exponent-invertibility hypotheses. -/
theorem dvrFracUnitPart_norm_of_prime_degree [HenselianLocalRing S]
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (heunit : IsUnit (e : S)) (hp : Nat.Prime (Module.finrank F E)) (b : Eˣ) :
    dvrFracUnitPart hπ (Units.map (Algebra.norm F) b) =
      Units.map (Algebra.norm (ResidueField R)) (dvrFracUnitPart hϖ b) ^ e *
        (((-1 : (ResidueField R)ˣ) ^
            (Module.finrank (ResidueField R) (ResidueField S) * (e - 1))) *
          (Units.map (Algebra.norm (ResidueField R))
            (Units.map (residue S).toMonoidHom u))⁻¹) ^ dvrFracOrd hϖ b := by
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  obtain ⟨b₀, hb₀, hres⟩ :=
    IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_prime_degree
      R S F E hπ hϖ u e he heunit hp
  exact dvrFracUnitPart_norm_of_exact_coefficient R S F E hπ hϖ u e he b₀ hb₀ hres b

end Stacks.Chow
