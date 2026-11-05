/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.SemilocalBranches
public import Colib.Util.References
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Actual completed local branches of a Dedekind ideal

The index is the subtype of the native normalized ideal factors, with their actual positive
multiplicities. The equivalence uses Mathlib's completions and localizations, and its coordinates
are the native maps on completions, including at quotient level zero.

Adapted from `Aglib/RingTheory/AdicCompletion/DedekindBranches.lean`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The coordinate and evaluation formulas below identify
the original maps explicitly. A nonzero ideal may be the unit ideal; its product is then empty.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open Function IsLocalRing UniqueFactorizationMonoid
open scoped BigOperators

universe u

variable {R : Type u} [CommRing R] [IsDedekindDomain R] [DecidableEq (Ideal R)]

/-- The actual distinct normalized prime-ideal factors, not a new branch carrier. -/
abbrev IdealBranch (I : Ideal R) := ↥(normalizedFactors I).toFinset

instance idealBranchIsMaximal (I : Ideal R) (q : IdealBranch I) : q.val.IsMaximal := by
  have hp := prime_of_normalized_factor q.val (Multiset.mem_toFinset.mp q.property)
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

/-- Every actual ideal factor contains the original ideal. -/
theorem idealBranch_le (I : Ideal R) (q : IdealBranch I) : I ≤ q.val :=
  Ideal.le_of_dvd (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp q.property))

/-- The actual ideal-factor multiplicity is positive. -/
theorem idealBranch_count_pos (I : Ideal R) (q : IdealBranch I) :
    0 < (normalizedFactors I).count q.val :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp q.property)

/-- Unique ideal factorization supplies every branch and its multiplicity. -/
theorem idealBranch_factorization (I : Ideal R) (hI : I ≠ 0) :
    I = ∏ q : IdealBranch I, q.val ^ (normalizedFactors I).count q.val := by
  rw [Finset.prod_coe_sort (normalizedFactors I).toFinset
    (fun J => J ^ (normalizedFactors I).count J)]
  rw [← Finset.prod_multiset_count]
  exact (associated_iff_eq.mp (prod_normalizedFactors hI)).symm

/-- The original ideal maps into the maximal ideal of each actual local branch. -/
theorem idealBranch_map_le_maximalIdeal (I : Ideal R) (q : IdealBranch I) :
    I.map (algebraMap R (Localization.AtPrime q.val)) ≤
      maximalIdeal (Localization.AtPrime q.val) :=
  (Ideal.map_mono (idealBranch_le I q)).trans_eq
    (IsLocalization.AtPrime.map_eq_maximalIdeal q.val (Localization.AtPrime q.val))

/-- Completion at a nonzero Dedekind ideal is the product of the actual local completions. -/
@[colib_tag "COL-0188",
  colib_ref "aglib_principal_euler_pin" "RingTheory/AdicCompletion/DedekindBranches.lean"
    "adaptation" "Canonical maps and actual completions; native lower interfaces"]
def dedekindBranchesAlgEquiv (I : Ideal R) (hI : I ≠ 0) :
    AdicCompletion I R ≃ₐ[R]
      ∀ q : IdealBranch I,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
          (Localization.AtPrime q.val) :=
  semilocalBranchesAlgEquiv (fun q : IdealBranch I => q.val)
    (fun _ _ h => Ideal.isCoprime_of_isMaximal (fun heq => h (Subtype.ext heq)))
    (fun q => (normalizedFactors I).count q.val) (idealBranch_count_pos I)
    (fun q => Localization.AtPrime q.val) I (idealBranch_factorization I hI)

/-- Each coordinate is the original canonical map on completions. -/
theorem dedekindBranchesAlgEquiv_apply (I : Ideal R) (hI : I ≠ 0)
    (x : AdicCompletion I R) (q : IdealBranch I) :
    dedekindBranchesAlgEquiv I hI x q =
      adicCompletionMap (algebraMap R (Localization.AtPrime q.val)) I
        (maximalIdeal (Localization.AtPrime q.val)) (idealBranch_map_le_maximalIdeal I q) x := by
  apply semilocalBranchesAlgEquiv_apply

/-- The original ring enters every completed branch by its native ring maps. -/
@[simp]
theorem dedekindBranchesAlgEquiv_algebraMap (I : Ideal R) (hI : I ≠ 0)
    (r : R) (q : IdealBranch I) :
    dedekindBranchesAlgEquiv I hI (algebraMap R (AdicCompletion I R) r) q =
      algebraMap (Localization.AtPrime q.val)
        (AdicCompletion (maximalIdeal (Localization.AtPrime q.val)) (Localization.AtPrime q.val))
        (algebraMap R (Localization.AtPrime q.val) r) :=
  congrFun ((dedekindBranchesAlgEquiv I hI).commutes r) q

/-- The branch decomposition respects the actual quotient map at every precision. -/
@[colib_tag "COL-0188"]
theorem eval_dedekindBranchesAlgEquiv (I : Ideal R) (hI : I ≠ 0)
    (n : ℕ) (x : AdicCompletion I R) (q : IdealBranch I) :
    evalₐ (maximalIdeal (Localization.AtPrime q.val)) n
        (dedekindBranchesAlgEquiv I hI x q) =
      Ideal.quotientMap ((maximalIdeal (Localization.AtPrime q.val)) ^ n)
        (algebraMap R (Localization.AtPrime q.val))
        (Ideal.map_le_iff_le_comap.mp (by
          rw [Ideal.map_pow]
          exact Ideal.pow_right_mono (idealBranch_map_le_maximalIdeal I q) n))
        (evalₐ I n x) := by
  rw [dedekindBranchesAlgEquiv_apply, adicCompletionMap_evalₐ]

end AdicCompletion
