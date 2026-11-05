/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Norm.DVRPrimeUniformizer

/-! Direct consumers of the combined exact prime-degree coefficient. The
exponent-one consumer has no henselianity or primality assumption.

Adapted from `AglibTest/DVRPrimeUniformizerNorm.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`11757ebadf7bd966a73fff33ae1a2d8bc06fdccd2d69c1442e77b040dcaf9a56`.
-/

noncomputable section

open IsLocalRing

universe u v w z

namespace ColibTest.DVRPrimeUniformizerNorm

variable (R : Type u) (S : Type v) (F : Type w) (E : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)

include F E hπ hϖ

/-- Exponent one does not require Hensel lifting or a prime-degree extension. -/
theorem exponent_one (u : Sˣ) (he : algebraMap R S π = (u : S) * ϖ) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ =
        π ^ Module.finrank (ResidueField R) (ResidueField S) * (b : R) ∧
      residue R (b : R) =
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ :=
  IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_exponent_one
    R S F E hπ hϖ u he

variable [HenselianLocalRing S]
  (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
  (hp : Nat.Prime (Module.finrank F E))

include he hp

/-- Both actual prime-degree branches have one common coefficient formula. -/
theorem prime_coefficient (heunit : IsUnit (e : S)) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ =
        π ^ Module.finrank (ResidueField R) (ResidueField S) * (b : R) ∧
      residue R (b : R) =
        (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
          (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ :=
  IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_prime_degree
    R S F E hπ hϖ u e he heunit hp

/-- The exact integral identity transports to the original ordinary field norm. -/
theorem ordinary_field_norm_coefficient (heunit : IsUnit (e : S)) :
    ∃ b : Rˣ, Algebra.norm F (algebraMap S E ϖ) =
        algebraMap R F π ^ Module.finrank (ResidueField R) (ResidueField S) *
          algebraMap R F (b : R) ∧
      residue R (b : R) =
        (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
          (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  obtain ⟨b, hb, hbres⟩ := prime_coefficient R S F E hπ hϖ u e he hp heunit
  refine ⟨b, ?_, hbres⟩
  rw [← Algebra.algebraMap_intNorm (A := R) (K := F) (L := E), hb, map_mul, map_pow]

/-- Residue characteristic zero gives the invertible exponent from actual e>0. -/
theorem residue_characteristic_zero [CharZero (ResidueField S)] :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ =
        π ^ Module.finrank (ResidueField R) (ResidueField S) * (b : R) ∧
      residue R (b : R) =
        (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
          (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  have hd := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    R S F E hπ hϖ u e he
  have hepos : 0 < e := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, zero_mul] at hd
    exact hp.ne_zero hd
  exact prime_coefficient R S F E hπ hϖ u e he hp
    (HenselianLocalRing.PrincipalRoots.isUnit_natCast_of_residue_charZero e hepos)

end ColibTest.DVRPrimeUniformizerNorm
