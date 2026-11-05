/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.DiscreteValuationRing
public import Colib.RingTheory.AdicCompletion.FiniteDedekindBranches
public import StacksFrontier.RingTheory.DiscreteValuationRing.EqualCharacteristicStructure
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Local and injective maps to actual completed Dedekind branches

The branch completion abbreviates the existing localization and completion. Its DVR structure
comes from native Dedekind localization and Stacks 0AP1. The completed-base action remains the
previously constructed `localCompletionBaseMap`; no inverse equivalence defines an action.

Adapted from `Aglib/RingTheory/AdicCompletion/BranchUniformizer.lean` and
`Aglib/RingTheory/AdicCompletion/BranchBaseLocal.lean`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. Injectivity uses the existing public
`Stacks.EppTheorem.injective_of_map_irreducible_ne_zero`, rather than reproving its DVR argument.
Neither locality nor injectivity requires module finiteness. The base uniformizer may be ramified
in a branch: its image is only asserted nonzero and a nonunit, not irreducible.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing UniqueFactorizationMonoid

universe u v

section Branch

variable {S : Type v} [CommRing S] [IsDedekindDomain S] [DecidableEq (Ideal S)]

/-- The actual completion of the original localization, not a new ring model. -/
abbrev BranchCompletion (I : Ideal S) (q : IdealBranch I) :=
  AdicCompletion (maximalIdeal (Localization.AtPrime q.val)) (Localization.AtPrime q.val)

/-- Every original localization indexed by an actual ideal factor is a DVR. -/
instance idealBranchLocalizationIsDiscreteValuationRing (I : Ideal S) (q : IdealBranch I) :
    IsDiscreteValuationRing (Localization.AtPrime q.val) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S
    (prime_of_normalized_factor q.val (Multiset.mem_toFinset.mp q.property)).ne_zero _

/-- The original domain embeds in each actual completed branch. -/
theorem branchCompletion_algebraMap_injective (I : Ideal S) (q : IdealBranch I) :
    Function.Injective (algebraMap S (BranchCompletion I q)) := by
  rw [IsScalarTower.algebraMap_eq S (Localization.AtPrime q.val) (BranchCompletion I q)]
  exact (of_injective (maximalIdeal (Localization.AtPrime q.val))
    (Localization.AtPrime q.val)).comp
      (IsLocalization.injective (Localization.AtPrime q.val) q.val.primeCompl_le_nonZeroDivisors)

end Branch

variable (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [DecidableEq (Ideal S)]

omit [DecidableEq (Ideal S)] in
/-- The extended base maximal ideal is nonzero for a torsion-free domain algebra. -/
theorem map_maximalIdeal_ne_zero [Module.IsTorsionFree R S] :
    (maximalIdeal R).map (algebraMap R S) ≠ 0 := by
  apply Ideal.map_ne_bot_of_ne_bot
  exact IsDiscreteValuationRing.not_a_field R

/-- Torsion-freeness keeps the original uniformizer nonzero in every completed branch. -/
theorem branchCompletion_uniformizer_ne_zero [Module.IsTorsionFree R S]
    {π : R} (hπ : Irreducible π)
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    algebraMap S (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)
      (algebraMap R S π) ≠ 0 :=
  (map_ne_zero_iff _ (branchCompletion_algebraMap_injective _ q)).mpr
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hπ.ne_zero)

/-- The base uniformizer remains a nonunit, including in ramified branches. -/
theorem branchCompletion_uniformizer_not_isUnit
    {π : R} (hπ : Irreducible π)
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    ¬ IsUnit (algebraMap S (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)
      (algebraMap R S π)) := by
  have hmem : algebraMap R S π ∈ q.val :=
    idealBranch_le _ q (Ideal.mem_map_of_mem (algebraMap R S)
      (show π ∈ maximalIdeal R from mem_nonunits_iff.mpr hπ.not_isUnit))
  have hlocal : ¬ IsUnit (algebraMap S (Localization.AtPrime q.val) (algebraMap R S π)) :=
    mem_nonunits_iff.mp ((IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime q.val) q.val _).mpr hmem)
  rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime q.val)
    (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)]
  exact fun h => hlocal (IsUnit.of_map _ _ h)

/-- The actual canonical completed-base action is faithful, without a finiteness premise. -/
@[colib_tag "COL-0191",
  colib_ref "aglib_principal_euler_pin" "RingTheory/AdicCompletion/BranchBaseLocal.lean"
    "adaptation" "Faithful canonical completed-base action without module finiteness"]
theorem localCompletionBase_injective [Module.IsTorsionFree R S]
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    Function.Injective (algebraMap (AdicCompletion (maximalIdeal R) R)
      (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) q
  let := localCompletionBaseIsScalarTower (maximalIdeal R) q
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  apply Stacks.EppTheorem.injective_of_map_irreducible_ne_zero _
    (irreducible_algebraMap R hπ)
  rw [← IsScalarTower.algebraMap_apply R (AdicCompletion (maximalIdeal R) R),
    IsScalarTower.algebraMap_apply R S]
  exact branchCompletion_uniformizer_ne_zero R S hπ q

/-- The completed-base action is local, without finite or torsion-free assumptions. -/
@[colib_tag "COL-0191"]
theorem localCompletionBase_isLocalHom
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    IsLocalHom (algebraMap (AdicCompletion (maximalIdeal R) R)
      (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) q
  let := localCompletionBaseIsScalarTower (maximalIdeal R) q
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  apply ((local_hom_TFAE (algebraMap (AdicCompletion (maximalIdeal R) R)
    (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q))).out 1 4).mpr
  rw [(irreducible_algebraMap R hπ).maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
  apply mem_nonunits_iff.mpr
  rw [← IsScalarTower.algebraMap_apply R (AdicCompletion (maximalIdeal R) R),
    IsScalarTower.algebraMap_apply R S]
  exact branchCompletion_uniformizer_not_isUnit R S hπ q

/-- A proposition witness for the same canonical action, not an alternative algebra structure. -/
theorem localCompletionBaseFaithfulSMul [Module.IsTorsionFree R S]
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    FaithfulSMul (AdicCompletion (maximalIdeal R) R)
      (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) q
  exact (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (localCompletionBase_injective R S q)

end AdicCompletion
