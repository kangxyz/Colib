/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRResidueDegreeOne
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRResidueRamificationOne
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRResidueTrace
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# The lower residue square for actual prime Galois tensor branches

The actual local fundamental identity splits the original prime degree into residue degree
one or ramification one. The former case uses native degree projection. The latter constructs
the native residue power basis and an integral lift, then applies the literal branch-count
and quotient-coordinate proof. Original residue normality follows from the existing actual
integral Galois action. All uniformizers and their equations are constructed internally.

No residue power basis, uniformizer equation, residue normality, factor bijection, branch
norm formula, Henselianity or tame-exponent premise is added to the actual tensor-square data.
The original residue field has characteristic zero; this restriction is not dropped.
The result is the lower branch norm square, not the entire norm-residue theorem.
-/

@[expose] public noncomputable section

open IsLocalRing Module
open scoped TensorProduct BigOperators

universe u v w

namespace Stacks.Chow

open DiscreteValuationRing.Ramification

variable (R S T : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Algebra R T] [FaithfulSMul R T] [IsLocalHom (algebraMap R T)]
  (F E K : Type v)
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E] [IsScalarTower R S E]
  [FiniteDimensional F E] [IsGalois F E]
  [Field K] [Algebra T K] [IsFractionRing T K] [Algebra F K]
  [Algebra R K] [IsScalarTower R T K] [IsScalarTower R F K]
  {ι : Type w} [Fintype ι] (U : ι → Type u) (D : ι → Type v)
  [∀ i, CommRing (U i)] [∀ i, IsDomain (U i)] [∀ i, IsDiscreteValuationRing (U i)]
  [∀ i, Algebra R (U i)] [∀ i, Algebra S (U i)] [∀ i, Algebra T (U i)]
  [∀ i, IsScalarTower R S (U i)] [∀ i, IsScalarTower R T (U i)]
  [∀ i, FaithfulSMul S (U i)] [∀ i, Module.IsTorsionFree T (U i)]
  [∀ i, Module.Finite T (U i)]
  [∀ i, IsLocalHom (algebraMap S (U i))] [∀ i, IsLocalHom (algebraMap T (U i))]
  [∀ i, Field (D i)] [∀ i, Algebra (U i) (D i)] [∀ i, IsFractionRing (U i) (D i)]
  [∀ i, Algebra T (D i)] [∀ i, Algebra K (D i)]
  [∀ i, IsScalarTower T (U i) (D i)] [∀ i, IsScalarTower T K (D i)]
  [∀ i, FiniteDimensional K (D i)]
  [CharZero (ResidueField R)]

/-- All actual upper residue branches satisfy the lower weighted chosen-norm identity.
The full integral-coordinate equation is required, not just the abstract tensor equivalence. -/
theorem sum_ramification_smul_residue_norm_map_of_prime_galois
    (ε : K ⊗[F] E ≃ₐ[K] ∀ i, D i)
    (hcoordinate : ∀ (s : S) (i : ι),
      algebraMap (U i) (D i) (algebraMap S (U i) s) =
        ε (1 ⊗ₜ[F] algebraMap S E s) i)
    (hp : Nat.Prime (finrank F E)) (y : MilnorKRing (ResidueField S)) :
    (∑ i, (ramificationIdx S (U i) : ℤ) •
      milnorKNormRing (ResidueField T) (ResidueField (U i))
        (milnorKRingMap (algebraMap (ResidueField S) (ResidueField (U i))) y)) =
      (ramificationIdx R T : ℤ) •
        milnorKRingMap (algebraMap (ResidueField R) (ResidueField T))
          (milnorKNormRing (ResidueField R) (ResidueField S) y) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hπ.ne_zero) hϖ
  rcases IsDiscreteValuationRing.ramification_eq_one_or_residue_finrank_eq_one
      R S F E hπ hϖ u e he hp with heone | hfone
  · subst e
    let : Normal (ResidueField R) (ResidueField S) :=
      (dvr_residueField_normal_and_galRestrict_surjective R S F E).1
    let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
    let : ∀ i, IsIntegralClosure (U i) T (D i) := fun i =>
      IsIntegralClosure.of_isIntegrallyClosed (U i) T (D i)
    let B := Field.powerBasisOfFiniteOfSeparable (ResidueField R) (ResidueField S)
    obtain ⟨b, hb⟩ := residue_surjective B.gen
    obtain ⟨τ, hτ⟩ := IsDiscreteValuationRing.exists_irreducible T
    choose ω hω using fun i => IsDiscreteValuationRing.exists_irreducible (U i)
    have hfactor (i : ι) : ∃ (d : ℕ) (v : (U i)ˣ),
        algebraMap T (U i) τ = (v : U i) * ω i ^ d :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective T (U i))).mpr hτ.ne_zero)
        (hω i)
    choose d v hd using hfactor
    have hresprime : Nat.Prime (finrank (ResidueField R) (ResidueField S)) := by
      have h := IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank
        R S F E hπ hϖ u 1 he
      rw [one_mul] at h
      rwa [h] at hp
    exact sum_ramification_smul_residue_norm_map_of_ramification_eq_one
      R S T F E K D U ε b (hcoordinate b) hπ hϖ u he B hb.symm
        hτ ω hω v d hd hresprime y
  · exact sum_ramification_smul_residue_norm_map_of_residue_finrank_eq_one
      R S T F E K U D ε hfone y

/-- Homogeneous lower branch compatibility in every degree, including degree zero. -/
theorem sum_ramification_smul_residue_norm_map_of_prime_galois_homogeneous
    (ε : K ⊗[F] E ≃ₐ[K] ∀ i, D i)
    (hcoordinate : ∀ (s : S) (i : ι),
      algebraMap (U i) (D i) (algebraMap S (U i) s) =
        ε (1 ⊗ₜ[F] algebraMap S E s) i)
    (hp : Nat.Prime (finrank F E)) (n : ℕ) (y : MilnorKTheory (ResidueField S) n) :
    (∑ i, (ramificationIdx S (U i) : ℤ) •
      milnorKNorm (ResidueField T) (ResidueField (U i)) n
        (milnorKTheoryMap (algebraMap (ResidueField S) (ResidueField (U i))) n y)) =
      (ramificationIdx R T : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n y) := by
  classical
  apply Subtype.ext
  change (milnorKGrading (ResidueField T) n).subtype
      (∑ i, (ramificationIdx S (U i) : ℤ) •
        milnorKNorm (ResidueField T) (ResidueField (U i)) n
          (milnorKTheoryMap (algebraMap (ResidueField S) (ResidueField (U i))) n y)) =
    (milnorKGrading (ResidueField T) n).subtype
      ((ramificationIdx R T : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n y))
  rw [map_sum]
  simp_rw [map_zsmul, milnorKTheoryMap_eq_transport]
  exact sum_ramification_smul_residue_norm_map_of_prime_galois
    R S T F E K U D ε hcoordinate hp (y : MilnorKRing (ResidueField S))

end Stacks.Chow

end
