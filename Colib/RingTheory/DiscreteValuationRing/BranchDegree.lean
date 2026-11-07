/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.DiscreteValuationRing.RamificationDegree
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual DVR branch weights in residue degree one

The complete generic tensor rank and native local fundamental identities determine the sum
of all original-side ramification indices times relative residue degrees. The original
residue degree is one. Ramification cancellation occurs only in the natural numbers.
No Milnor K-theory, characteristic, separability or Henselian hypothesis is used.

The tensor equivalence supplies only the total degree; individual coordinate compatibility
with the integral maps belongs to the separate actual branch construction.
-/

@[expose] public noncomputable section

open IsLocalRing Module
open scoped BigOperators TensorProduct

universe u v w

namespace Stacks.DiscreteValuationRing.Ramification

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
  [FiniteDimensional F E]
  [Field K] [Algebra T K] [IsFractionRing T K] [Algebra F K]
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

/-- The true branch weights have total equal to the base-change ramification when the
original residue extension has degree one. The full tensor product supplies the degree sum. -/
theorem sum_ramification_mul_residue_finrank_of_residue_finrank_eq_one
    (ε : K ⊗[F] E ≃ₐ[K] ∀ i, D i)
    (hf : finrank (ResidueField R) (ResidueField S) = 1) :
    (∑ i, ramificationIdx S (U i) *
      finrank (ResidueField T) (ResidueField (U i))) =
        ramificationIdx R T := by
  classical
  let : FaithfulSMul R S := inferInstance
  let : Module.Flat R S := inferInstance
  let : ∀ i, FaithfulSMul T (U i) := fun _ => inferInstance
  let : ∀ i, FaithfulSMul R (U i) := fun i => FaithfulSMul.trans R S (U i)
  let : ∀ i, IsLocalHom (algebraMap R (U i)) := fun i => by
    rw [IsScalarTower.algebraMap_eq R S (U i)]
    infer_instance
  have hdegree : ramificationIdx R S = finrank F E := by
    have h := ramificationIdx_mul_inertiaDeg_eq_finrank
      R S F E
    rw [Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal R)] at h
    have h' : ramificationIdx R S *
        finrank (ResidueField R) (ResidueField S) = finrank F E := h
    simpa only [hf, mul_one] using h'
  have hsum : (∑ i, ramificationIdx T (U i) *
      finrank (ResidueField T) (ResidueField (U i))) = finrank F E := by
    calc
      _ = ∑ i, finrank K (D i) := by
        apply Finset.sum_congr rfl
        intro i _
        let : Module.Flat T (U i) := inferInstance
        have h := ramificationIdx_mul_inertiaDeg_eq_finrank
          T (U i) K (D i)
        rw [Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal T)] at h
        exact h
      _ = finrank K (∀ i, D i) := (Module.finrank_pi_fintype K).symm
      _ = finrank K (K ⊗[F] E) := ε.toLinearEquiv.finrank_eq.symm
      _ = finrank F E := Module.finrank_baseChange
  have htower (i : ι) :
      ramificationIdx R T *
          ramificationIdx T (U i) =
        ramificationIdx R S *
          ramificationIdx S (U i) := by
    have hT := (IsDiscreteValuationRing.ramificationIdx_and_inertiaDeg_tower R T (U i)).1
    have hS := (IsDiscreteValuationRing.ramificationIdx_and_inertiaDeg_tower R S (U i)).1
    simpa only [ramificationIdx_def,
      Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal T)
        (IsDiscreteValuationRing.not_a_field R),
      Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal T) (maximalIdeal (U i))
        (IsDiscreteValuationRing.not_a_field T),
      Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal S)
        (IsDiscreteValuationRing.not_a_field R),
      Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal S) (maximalIdeal (U i))
        (IsDiscreteValuationRing.not_a_field S)] using hT.symm.trans hS
  have he := one_le_ramificationIdx R S
  apply Nat.eq_of_mul_eq_mul_left he
  calc
    ramificationIdx R S *
        (∑ i, ramificationIdx S (U i) *
          finrank (ResidueField T) (ResidueField (U i))) =
        ∑ i, ramificationIdx R T *
          (ramificationIdx T (U i) *
            finrank (ResidueField T) (ResidueField (U i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, ← htower, mul_assoc]
    _ = ramificationIdx R T * finrank F E := by
      rw [← Finset.mul_sum, hsum]
    _ = ramificationIdx R S *
        ramificationIdx R T := by
      rw [← hdegree, mul_comm]

end Stacks.DiscreteValuationRing.Ramification

end
