/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Norm.DVRUniformizer

/-!
# Exact uniformizer norm coefficients in prime field degree

The exponent-one case follows directly from the norm of the mapped base
uniformizer and unit-norm reduction. The actual prime-degree dichotomy then
combines it with the henselian residue-degree-one calculation. Both branches
produce the same exact normalized coefficient and its determinant sign.

## Source provenance

Adapted from `Aglib/RingTheory/DVRPrimeUniformizerNorm.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`2c9e1e98145e9ca28d2b9726eeb13e1af312ad0f1271e32c36c7604731b8e898`.
The original module is `Motivic.Aglib.RingTheory.DVRPrimeUniformizerNorm`, with source SHA-256
`8a5fe1563cd9fc32767cd8dce5b2815043cd8edc59cb9a16324caaac88b19d98`.
The actual norms, uniformizers, residue maps, coefficients and signs are
preserved. Perfectness of the base fraction field is no longer needed because
the degree formula comes from the pinned Stacks local fundamental identity.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v w z

namespace IsDiscreteValuationRing

variable (R : Type u) (S : Type v) (F : Type w) (E : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]

include F E

/-- The exponent-one coefficient is the inverse integral norm of the actual
ramification unit. Neither Hensel lifting nor prime field degree is required. -/
@[colib_tag "COL-0199"]
theorem exists_uniformizer_norm_coefficient_of_exponent_one
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (he : algebraMap R S π = (u : S) * ϖ) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ =
        π ^ Module.finrank (ResidueField R) (ResidueField S) * (b : R) ∧
      residue R (b : R) =
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  have he1 : algebraMap R S π = (u : S) * ϖ ^ 1 := by simpa only [pow_one] using he
  have hdegree : Module.finrank F E = Module.finrank (ResidueField R) (ResidueField S) := by
    simpa only [one_mul] using
      finrank_eq_ramification_mul_residue_finrank R S F E hπ hϖ u 1 he1
  have hnorm : Algebra.intNorm R S (algebraMap R S π) =
      π ^ Module.finrank (ResidueField R) (ResidueField S) := by
    apply IsFractionRing.injective R F
    rw [Algebra.algebraMap_intNorm (K := F) (L := E),
      ← IsScalarTower.algebraMap_apply R S E, IsScalarTower.algebraMap_apply R F E,
      Algebra.norm_algebraMap, map_pow, hdegree]
  let t : Rˣ := Units.map (Algebra.intNorm R S) u
  have hprod : (t : R) * Algebra.intNorm R S ϖ =
      π ^ Module.finrank (ResidueField R) (ResidueField S) := by
    simpa only [he, map_mul, Units.coe_map, t] using hnorm
  refine ⟨t⁻¹, ?_, ?_⟩
  · calc
      Algebra.intNorm R S ϖ = ((t⁻¹ : Rˣ) : R) *
          ((t : R) * Algebra.intNorm R S ϖ) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      _ = _ := by rw [hprod, mul_comm]
  · have htres : Units.map (residue R).toMonoidHom t =
        Units.map (Algebra.norm (ResidueField R)) (Units.map (residue S).toMonoidHom u) := by
      simpa only [pow_one, t] using
        Algebra.residueUnits_intNorm_eq_norm_pow R S hπ hϖ u 1 he1 u
    change ((Units.map (residue R).toMonoidHom t⁻¹ : (ResidueField R)ˣ) : ResidueField R) = _
    rw [map_inv, htres]
    simp

/-- Prime actual field degree yields the exact normalized uniformizer norm.
The hypotheses on Hensel lifting and exponent invertibility are retained. -/
@[colib_tag "COL-0199",
  colib_ref "aglib_principal_euler_pin" "RingTheory/DVRPrimeUniformizerNorm.lean"
    "adaptation" "Actual prime-degree dichotomy and exact normalized integral-norm coefficient"]
theorem exists_uniformizer_norm_coefficient_of_prime_degree [HenselianLocalRing S]
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (heunit : IsUnit (e : S)) (hp : Nat.Prime (Module.finrank F E)) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ =
        π ^ Module.finrank (ResidueField R) (ResidueField S) * (b : R) ∧
      residue R (b : R) =
        (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
          (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  rcases ramification_eq_one_or_residue_finrank_eq_one R S F E hπ hϖ u e he hp with he1 | hf1
  · subst e
    simpa only [Nat.sub_self, mul_zero, pow_zero, one_mul] using
      exists_uniformizer_norm_coefficient_of_exponent_one R S F E hπ hϖ u
        (by simpa only [pow_one] using he)
  · simpa only [hf1, pow_one, one_mul] using
      exists_uniformizer_norm_coefficient_of_residue_finrank_one R S F E hπ hϖ u e he heunit hf1

end IsDiscreteValuationRing
