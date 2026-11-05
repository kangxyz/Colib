/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.DedekindBranches
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Original localized branch residue fields and specified fraction fields

The index is the existing subtype of actual normalized ideal factors. Original local maps and
residue finiteness follow from the ideal inclusion, not from a false assertion that the original
localized ring is finite over the base. A specified original fraction field receives the native
localization algebra for nested denominator submonoids.

Adapted from `Aglib/RingTheory/AdicCompletion/OriginalBranchResidues.lean` and
`Aglib/RingTheory/AdicCompletion/OriginalBranchFractions.lean`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The ring and field universes are independent.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing

universe u v w

section Residue

variable (R : Type u) (S : Type v) [CommRing R] [IsLocalRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [DecidableEq (Ideal S)]

/-- The original base-to-branch localization map reflects units. -/
instance originalBranchIsLocalHom
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    IsLocalHom (algebraMap R (Localization.AtPrime q.val)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have hmem : algebraMap R S a ∈ q.val :=
    idealBranch_le _ q (Ideal.mem_map_of_mem _ (show a ∈ maximalIdeal R from h))
  have hh := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime q.val) q.val (algebraMap R S a)).mpr hmem
  exact hh (by simpa only [← IsScalarTower.algebraMap_apply] using ha)

/-- The original domain surjects onto the residue field of each original branch. -/
theorem originalBranchResidue_surjective
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    Function.Surjective (algebraMap S (ResidueField (Localization.AtPrime q.val))) := by
  intro a
  obtain ⟨b, hb⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal q.val
    (Localization.AtPrime q.val)).surjective a
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨s, hb⟩

/-- Only the original residue extension is claimed finite, not the localization over R. -/
@[colib_tag "COL-0191"]
instance originalBranchResidueFinite [Module.Finite R S]
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    Module.Finite (ResidueField R) (ResidueField (Localization.AtPrime q.val)) := by
  let : Module.Finite S (ResidueField (Localization.AtPrime q.val)) :=
    Module.Finite.of_surjective (Algebra.ofId S
      (ResidueField (Localization.AtPrime q.val))).toLinearMap
        (originalBranchResidue_surjective R S q)
  let : Module.Finite R (ResidueField (Localization.AtPrime q.val)) :=
    Module.Finite.trans S _
  exact Module.Finite.of_restrictScalars_finite R (ResidueField R) _

end Residue

section Fraction

variable (S : Type v) (E : Type w) [CommRing S] [IsDedekindDomain S]
  [Field E] [Algebra S E] [IsFractionRing S E] [DecidableEq (Ideal S)]
  {I : Ideal S} (q : IdealBranch I)

/-- The specified fraction field receives the native localization algebra. -/
abbrev originalBranchFractionAlgebra : Algebra (Localization.AtPrime q.val) E :=
  IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime q.val) E
    q.val.primeCompl (nonZeroDivisors S) q.val.primeCompl_le_nonZeroDivisors

/-- The native localization action extends the specified original domain action. -/
theorem originalBranchFractionTower :
    letI := originalBranchFractionAlgebra S E q
    IsScalarTower S (Localization.AtPrime q.val) E :=
  IsLocalization.localization_isScalarTower_of_submonoid_le
    (Localization.AtPrime q.val) E q.val.primeCompl (nonZeroDivisors S)
    q.val.primeCompl_le_nonZeroDivisors

/-- The same specified original field is a fraction field of every original branch. -/
@[colib_tag "COL-0191"]
theorem originalBranchIsFractionRing :
    letI := originalBranchFractionAlgebra S E q
    IsFractionRing (Localization.AtPrime q.val) E := by
  let := originalBranchFractionAlgebra S E q
  let := originalBranchFractionTower S E q
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.val.primeCompl
    (Localization.AtPrime q.val) E

/-- The original branch fraction map has the actual original domain triangle. -/
theorem originalBranchFractionAlgebra_algebraMap (s : S) :
    letI := originalBranchFractionAlgebra S E q
    algebraMap (Localization.AtPrime q.val) E (algebraMap S (Localization.AtPrime q.val) s) =
      algebraMap S E s := by
  let := originalBranchFractionAlgebra S E q
  let := originalBranchFractionTower S E q
  exact (IsScalarTower.algebraMap_apply S (Localization.AtPrime q.val) E s).symm

end Fraction

end AdicCompletion
