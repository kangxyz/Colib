/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Charpoly.DVRResidue
import Mathlib.Algebra.CharZero.Infinite

/-! Actual integral and field multiplication characteristic-polynomial reduction. -/

noncomputable section

open IsLocalRing

namespace ColibTest.DVRCharpolyResidue

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [IsLocalHom (algebraMap R S)]
  [Infinite (ResidueField R)]

/-- The operator-level reduction requires only an infinite residue base field. -/
theorem actual_residue_operator_power
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S) :
    (Algebra.lmul R S b).charpoly.map (residue R) =
      (Algebra.lmul (ResidueField R) (ResidueField S) (residue S b)).charpoly ^ e :=
  Algebra.residue_charpoly_lmul_eq_pow R S hπ hϖ u e he b

/-- The exponent includes the actual residual relative degree, not a supplied weight. -/
theorem actual_minimal_polynomial_power
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S) :
    (Algebra.lmul R S b).charpoly.map (residue R) =
      (minpoly (ResidueField R) (residue S b)) ^
        (e * Module.finrank
          (IntermediateField.adjoin (ResidueField R) {residue S b}) (ResidueField S)) :=
  Algebra.residue_charpoly_lmul_eq_minpoly_pow R S hπ hϖ u e he b

/-- A literal primitive residue generator removes only the relative-degree factor. -/
theorem actual_primitive_residue_power
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S)
    (B : PowerBasis (ResidueField R) (ResidueField S)) (hB : B.gen = residue S b) :
    (Algebra.lmul R S b).charpoly.map (residue R) =
      (minpoly (ResidueField R) (residue S b)) ^ e :=
  Algebra.residue_charpoly_lmul_eq_minpoly_pow_of_powerBasis R S hπ hϖ u e he b B hB

/-- The same integral polynomial gives both the original fraction-field
characteristic polynomial and its residue reduction. There is no field-to-residue map. -/
theorem original_field_and_residue
    (F E : Type*) [Field F] [Field E] [Algebra R F] [IsFractionRing R F]
    [Algebra F E] [Algebra R E] [Algebra S E]
    [IsScalarTower R F E] [IsScalarTower R S E] [IsIntegralClosure S R E]
    [FiniteDimensional F E]
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S) :
    (Algebra.lmul R S b).charpoly.map (algebraMap R F) =
        (Algebra.lmul F E (algebraMap S E b)).charpoly ∧
      (Algebra.lmul R S b).charpoly.map (residue R) =
        (minpoly (ResidueField R) (residue S b)) ^
          (e * Module.finrank
            (IntermediateField.adjoin (ResidueField R) {residue S b}) (ResidueField S)) :=
  ⟨Algebra.map_charpoly_lmul_integralClosure R F S E b,
    Algebra.residue_charpoly_lmul_eq_minpoly_pow R S hπ hϖ u e he b⟩

end ColibTest.DVRCharpolyResidue
