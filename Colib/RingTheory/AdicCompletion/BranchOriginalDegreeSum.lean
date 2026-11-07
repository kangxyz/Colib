/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.BranchDegreeSum
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Original-base weights of actual completed branches

All algebra structures are the existing native ones. Only proposition witnesses and numerical
comparisons are added. In particular no original localization is assumed finite over the base.
The completion residue map is compared with the native residue algebra map on every residue.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing
open scoped BigOperators

universe u v w z

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [DecidableEq (Ideal S)]

local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "D" => fun q : IdealBranch J => BranchCompletion J q

/-- The existing original-base algebra map into an actual completed branch is local. -/
theorem branchCompletionBase_isLocalHom (q : IdealBranch J) :
    IsLocalHom (algebraMap R (D q)) := by
  let := localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := localCompletionBaseIsScalarTower (S := S) (maximalIdeal R) q
  let := localCompletionBase_isLocalHom R S q
  rw [IsScalarTower.algebraMap_eq R Rhat (D q)]
  exact RingHom.isLocalHom_comp (algebraMap Rhat (D q)) (algebraMap R Rhat)

/-- Completion of the base leaves each actual branch ramification index unchanged. -/
theorem branchCompletion_ramificationIdx_eq [Module.IsTorsionFree R S]
    (q : IdealBranch J) :
    let := localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    Stacks.DiscreteValuationRing.Ramification.ramificationIdx R (D q) =
      Stacks.DiscreteValuationRing.Ramification.ramificationIdx Rhat (D q) := by
  let := localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := localCompletionBaseIsScalarTower (S := S) (maximalIdeal R) q
  let := localCompletionBaseFaithfulSMul R S q
  let : Module.IsTorsionFree Rhat (D q) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective Rhat (D q))
  let : FaithfulSMul R Rhat :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (of_injective (maximalIdeal R) R)
  let : FaithfulSMul R (D q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      rw [IsScalarTower.algebraMap_eq R Rhat (D q)]
      exact (localCompletionBase_injective R S q).comp
        (of_injective (maximalIdeal R) R))
  let := localCompletionBase_isLocalHom R S q
  let := branchCompletionBase_isLocalHom R S q
  have hcompletion : (maximalIdeal R).ramificationIdx' (maximalIdeal Rhat) = 1 := by
    rw [maximalIdeal_eq_map]
    apply Ideal.ramificationIdx'_map_self_eq_one
    · rw [← maximalIdeal_eq_map]
      exact Ideal.IsMaximal.ne_top inferInstance
    · rw [← maximalIdeal_eq_map]
      exact IsDiscreteValuationRing.not_a_field Rhat
  have htower :=
    (IsDiscreteValuationRing.ramificationIdx_and_inertiaDeg_tower R Rhat (D q)).1
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal (D q))
      (IsDiscreteValuationRing.not_a_field R),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal Rhat)
      (IsDiscreteValuationRing.not_a_field R),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal Rhat) (maximalIdeal (D q))
      (IsDiscreteValuationRing.not_a_field Rhat), hcompletion, one_mul] at htower
  exact htower

/-- The actual branch residue degree is unchanged by completion of the base. -/
theorem branchCompletion_residue_finrank_eq (q : IdealBranch J) :
    let := localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    let := localCompletionBase_isLocalHom R S q
    let := branchCompletionBase_isLocalHom R S q
    Module.finrank (ResidueField R) (ResidueField (D q)) =
      Module.finrank (ResidueField Rhat) (ResidueField (D q)) := by
  let := localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := localCompletionBaseIsScalarTower (S := S) (maximalIdeal R) q
  let := localCompletionBase_isLocalHom R S q
  let := branchCompletionBase_isLocalHom R S q
  have hmap : algebraMap (ResidueField R) (ResidueField Rhat) =
      ResidueField.map (algebraMap R Rhat) := by
    ext x
    obtain ⟨r, rfl⟩ := residue_surjective x
    rfl
  have hdegree : Module.finrank (ResidueField R) (ResidueField Rhat) = 1 :=
    Module.finrank_of_bijective_algebraMap (by
      rw [hmap]
      exact residueField_map_bijective R)
  simpa only [hdegree, one_mul] using
    (Module.finrank_mul_finrank (ResidueField R) (ResidueField Rhat)
      (ResidueField (D q))).symm

variable (F : Type w) (E : Type z)
  [Module.Finite R S] [Module.IsTorsionFree R S]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E]

/-- The ramification indices and residue degrees over the original base, summed over every
actual completed branch, have total weight equal to the original fraction-field degree. -/
theorem sum_branchCompletion_original_ramification_mul_residue_finrank :
    let := fun q => branchCompletionBase_isLocalHom R S q
    (∑ q : IdealBranch J,
      Stacks.DiscreteValuationRing.Ramification.ramificationIdx R (D q) *
        Module.finrank (ResidueField R) (ResidueField (D q))) = Module.finrank F E := by
  let := fun q => branchCompletionBase_isLocalHom R S q
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionBase_isLocalHom R S q
  calc
    (∑ q : IdealBranch J,
      Stacks.DiscreteValuationRing.Ramification.ramificationIdx R (D q) *
        Module.finrank (ResidueField R) (ResidueField (D q))) =
        ∑ q : IdealBranch J,
          Stacks.DiscreteValuationRing.Ramification.ramificationIdx Rhat (D q) *
            Module.finrank (ResidueField Rhat) (ResidueField (D q)) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [branchCompletion_ramificationIdx_eq R S q,
        branchCompletion_residue_finrank_eq R S q]
    _ = Module.finrank F E :=
      sum_localCompletion_ramification_mul_residue_finrank R S F E

end AdicCompletion
