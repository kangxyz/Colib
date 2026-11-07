/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRMixed

/-!
# Mixed norm-residue compatibility with residue characteristic zero

In fraction-field degree one or prime, the actual local DVR hypotheses construct the
uniformizer equation. Residue characteristic zero makes its positive ramification exponent
a unit. The existing exponent-one and Henselian prime-degree mixed theorems then apply.
No chosen uniformizer, coefficient, or tame-exponent hypothesis is supplied by the caller.

This is compatibility on the existing relative mixed span, not on all original classes.
Henselianity is retained for prime-degree ramification; actual completed branches supply it.
The ring universe and fraction-field universe are independent, as in the lower mixed theorem.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Chow

variable (R S : Type u) (F E : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E]

/-- Fraction-field degree one forces exponent one, so the mixed norm-residue square needs
neither Henselianity nor a residue-characteristic condition. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_finrank_eq_one
    (hdegree : Module.finrank F E = 1) (m : ℕ)
    (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hπ.ne_zero) hϖ
  have heq : e * Module.finrank (ResidueField R) (ResidueField S) = 1 :=
    (IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
      R S F E hπ hϖ u e he).symm.trans hdegree
  have heone : e = 1 := Nat.eq_one_of_mul_eq_one_right heq
  subst e
  apply dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_exponent_one
    R S F E hπ hϖ u _ m x hx
  simpa only [pow_one] using he

/-- Henselian prime-degree mixed compatibility in residue characteristic zero. Positivity
and invertibility of the actual ramification exponent are derived, not assumed. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_prime_degree_of_charZero
    [HenselianLocalRing S] [CharZero (ResidueField R)]
    (hprime : Nat.Prime (Module.finrank F E)) (m : ℕ)
    (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) := by
  let : CharZero (ResidueField S) := charZero_of_injective_algebraMap
    (algebraMap (ResidueField R) (ResidueField S)).injective
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hπ.ne_zero) hϖ
  have hene : e ≠ 0 := by
    intro hz
    have hu : IsUnit (algebraMap R S π) := by
      rw [he, hz, pow_zero, mul_one]
      exact u.isUnit
    exact hπ.not_isUnit (isUnit_of_map_unit (algebraMap R S) π hu)
  have heunit : IsUnit (e : S) := (residue_ne_zero_iff_isUnit _).mp (by
    rw [map_natCast]
    exact Nat.cast_ne_zero.mpr hene)
  exact dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_prime_degree
    R S F E hπ hϖ u e he heunit hprime m x hx

/-- Both possible actual degrees of a normal prime tensor factor satisfy the same mixed
norm-residue square. The degree alternative must come from the actual tensor coordinates. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_one_or_prime_of_charZero
    [HenselianLocalRing S] [CharZero (ResidueField R)]
    (hdegree : Module.finrank F E = 1 ∨ Nat.Prime (Module.finrank F E)) (m : ℕ)
    (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) := by
  rcases hdegree with hone | hprime
  · exact dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_finrank_eq_one
      R S F E hone m x hx
  · exact dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_prime_degree_of_charZero
      R S F E hprime m x hx

end Stacks.Chow

end
