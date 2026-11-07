/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport
public import Colib.RingTheory.AdicCompletion.BranchOriginalDegreeSum
public import Mathlib.Data.Int.GCD
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm

/-!
# Degree annihilation from all actual completed normalization branches

For every actual completed branch, apply the native residue-field norm to the ramification-
weighted restriction. The native projection formula supplies the actual residue degree.
Summing over every branch then gives the original fraction-field degree. In the normalization
specialization all finiteness and fraction-field witnesses are derived from finite separability.

Residue finiteness is proved through the finite completed-base algebra and the bijective actual
completion residue map. No original branch localization is asserted finite over the original
base. All fields use one universe, matching the native chosen norm. No adapter object, norm
independence, separability of residue extensions, or torsion-free Milnor group is used.

For the final coprime cancellation, the imported native `intGCD_nsmul_eq_zero` already proves
that two integer annihilators annihilate by their gcd; no second general Bezout API is added.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped BigOperators

universe u

namespace AdicCompletion

variable (R S : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]

local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "D" => fun q : IdealBranch J => BranchCompletion J q

/-- The actual original-base residue extension of each completed branch is finite.
Finiteness comes from completion, not from finiteness of the original localization. -/
theorem branchCompletion_residue_finite (q : IdealBranch J) :
    letI := branchCompletionBase_isLocalHom R S q
    Module.Finite (ResidueField R) (ResidueField (D q)) := by
  let := localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := localCompletionBaseIsScalarTower (S := S) (maximalIdeal R) q
  let := localCompletionBase_isLocalHom R S q
  let := branchCompletionBase_isLocalHom R S q
  let := localCompletionBaseFinite (S := S) (maximalIdeal R)
    (map_maximalIdeal_ne_zero R S) q
  have hmap : algebraMap (ResidueField R) (ResidueField Rhat) =
      ResidueField.map (algebraMap R Rhat) := by
    ext x
    obtain ⟨r, rfl⟩ := residue_surjective x
    rfl
  have hsurj : Function.Surjective
      (algebraMap (ResidueField R) (ResidueField Rhat)) := by
    rw [hmap]
    exact (residueField_map_bijective R).surjective
  let : Module.Finite (ResidueField R) (ResidueField Rhat) :=
    Module.Finite.of_surjective
      (Algebra.linearMap (ResidueField R) (ResidueField Rhat)) hsurj
  let : Module.Finite (ResidueField Rhat) (ResidueField (D q)) := inferInstance
  exact Module.Finite.trans (ResidueField Rhat) (ResidueField (D q))

end AdicCompletion

namespace Stacks.Chow

section FiniteDedekindAlgebra

variable (R S F E : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E]

local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "D" => fun q : AdicCompletion.IdealBranch J =>
  AdicCompletion.BranchCompletion J q

/-- If every actual completed branch kills its ramification-weighted restriction, then
summing the actual residue norm retractions kills the original class by the generic degree. -/
theorem finrank_smul_eq_zero_of_branchCompletion_ramification_smul_restrict_eq_zero
    (n : ℕ) (x : MilnorKTheory (ResidueField R) n)
    (hbranch :
      letI := fun q => AdicCompletion.branchCompletionBase_isLocalHom R S q
      ∀ q : AdicCompletion.IdealBranch J,
        (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R (D q) : ℤ) •
          milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField (D q))) n x = 0) :
    (Module.finrank F E : ℤ) • x = 0 := by
  let := fun q => AdicCompletion.branchCompletionBase_isLocalHom R S q
  have hweight (q : AdicCompletion.IdealBranch J) :
      ((Stacks.DiscreteValuationRing.Ramification.ramificationIdx R (D q) *
        Module.finrank (ResidueField R) (ResidueField (D q)) : ℕ) : ℤ) • x = 0 := by
    let := AdicCompletion.branchCompletion_residue_finite R S q
    have hring : (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R (D q) : ℤ) •
        milnorKRingMap (algebraMap (ResidueField R) (ResidueField (D q)))
          (x : MilnorKRing (ResidueField R)) = 0 := by
      have h := congrArg ((milnorKGrading (ResidueField (D q)) n).subtype) (hbranch q)
      simpa only [map_zsmul, map_zero, milnorKTheoryMap_eq_transport,
        AddMonoidHom.coe_toIntLinearMap, AddSubgroup.subtype_apply,
        milnorKTransport_coe] using h
    have hnorm := congrArg (milnorKNormRing (ResidueField R) (ResidueField (D q))) hring
    rw [map_zsmul, milnorKNormRing_milnorKRingMap, map_zero, smul_smul,
      ← Nat.cast_mul] at hnorm
    apply Subtype.ext
    exact hnorm
  have hsum :
      ((∑ q : AdicCompletion.IdealBranch J,
        Stacks.DiscreteValuationRing.Ramification.ramificationIdx R (D q) *
          Module.finrank (ResidueField R) (ResidueField (D q)) : ℕ) : ℤ) • x = 0 := by
    rw [Nat.cast_sum, Finset.sum_smul]
    exact Finset.sum_eq_zero fun q _ => hweight q
  rw [AdicCompletion.sum_branchCompletion_original_ramification_mul_residue_finrank
    R S F E] at hsum
  exact hsum

end FiniteDedekindAlgebra

section IntegralClosure

variable (R F K : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field K] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [FiniteDimensional F K] [Algebra.IsSeparable F K]
  [DecidableEq (Ideal (integralClosure R K))]

/-- Finite separable normalization supplies every actual branch and all needed finite-module
witnesses. Vanishing of each ramification-weighted residue restriction implies annihilation by
`[K : F]`, with no assumed branch degree sum or finite original localization. -/
theorem finrank_smul_eq_zero_of_integralClosure_branch_ramification_smul_restrict_eq_zero
    (n : ℕ) (x : MilnorKTheory (ResidueField R) n)
    (hbranch :
      letI := integralClosure.isDedekindDomain R F K
      letI := fun q =>
        AdicCompletion.branchCompletionBase_isLocalHom R (integralClosure R K) q
      ∀ q : AdicCompletion.IdealBranch
          ((maximalIdeal R).map (algebraMap R (integralClosure R K))),
        (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R
          (AdicCompletion.BranchCompletion
            ((maximalIdeal R).map (algebraMap R (integralClosure R K))) q) : ℤ) •
          milnorKTheoryMap (algebraMap (ResidueField R)
            (ResidueField (AdicCompletion.BranchCompletion
              ((maximalIdeal R).map (algebraMap R (integralClosure R K))) q))) n x = 0) :
    (Module.finrank F K : ℤ) • x = 0 := by
  let := integralClosure.isDedekindDomain R F K
  let := IsIntegralClosure.finite R F K (integralClosure R K)
  let : Module.IsTorsionFree R K :=
    Module.IsTorsionFree.trans_faithfulSMul R F K
  let : Module.IsTorsionFree R (integralClosure R K) :=
    IsIntegralClosure.isTorsionFree R K
  let : IsFractionRing (integralClosure R K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension R F K (integralClosure R K)
  exact finrank_smul_eq_zero_of_branchCompletion_ramification_smul_restrict_eq_zero
    R (integralClosure R K) F K n x hbranch

end IntegralClosure

end Stacks.Chow
