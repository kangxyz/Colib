/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Norm.DVRUniformizer

/-! Direct coefficient consumers retain the actual ring norm, genuine
residue degree one, exponent invertibility and the exact determinant sign.
No perfectness assumption is made on the fraction field.

Adapted from `AglibTest/DVRUniformizerNorm.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`1f2bc9aeae6d74d1222347d275beb1dc6a1bdbfda18a4815b6971d429ac7257e`.
-/

noncomputable section

open IsLocalRing

universe u v w z

namespace ColibTest.DVRUniformizerNorm

section ActualExtension

variable (R : Type u) (S : Type v) (F : Type w) (E : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [HenselianLocalRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
  (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
  (hf : Module.finrank (ResidueField R) (ResidueField S) = 1)

include F E hπ hϖ he hf

/-- An actual unit is returned as the normalized coefficient. -/
theorem exact_coefficient (heunit : IsUnit (e : S)) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ = π * (b : R) ∧
      residue R (b : R) = (-1 : ResidueField R) ^ (e - 1) *
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ :=
  IsDiscreteValuationRing.exists_uniformizer_norm_coefficient_of_residue_finrank_one
    R S F E hπ hϖ u e he heunit hf

omit he in
/-- The quadratic case keeps the negative sign. -/
theorem quadratic_sign (he2 : algebraMap R S π = (u : S) * ϖ ^ 2)
    (h2 : IsUnit (2 : S)) :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ = π * (b : R) ∧
      residue R (b : R) = -(Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  simpa using exact_coefficient R S F E hπ hϖ u 2 he2 hf h2

/-- Residue characteristic zero explicitly supplies invertibility. -/
theorem residue_characteristic_zero [CharZero (ResidueField S)] :
    ∃ b : Rˣ, Algebra.intNorm R S ϖ = π * (b : R) ∧
      residue R (b : R) = (-1 : ResidueField R) ^ (e - 1) *
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹ := by
  have hd := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
    R S F E hπ hϖ u e he
  have hp : 0 < e := by
    have hpos := Module.finrank_pos (R := F) (M := E)
    rw [hd, hf, mul_one] at hpos
    exact hpos
  exact exact_coefficient R S F E hπ hϖ u e he hf
    (HenselianLocalRing.PrincipalRoots.isUnit_natCast_of_residue_charZero e hp)

end ActualExtension

end ColibTest.DVRUniformizerNorm
