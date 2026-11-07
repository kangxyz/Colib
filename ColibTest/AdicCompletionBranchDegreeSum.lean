/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.AdicCompletion.BranchDegreeSum
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Consumers for the all-completed-branch degree sum

The first two consumers retain independent ring and fraction-field universes and assume
neither separability nor characteristic restrictions. The third constructs the actual
normalization in a finite separable auxiliary extension and derives all needed finiteness,
Dedekind, torsion-free and fraction-field witnesses from native theorems. No original
localized ring is assumed module-finite over the base.
-/

noncomputable section

namespace AdicCompletion

open IsLocalRing
open scoped BigOperators

universe u v w z

section FiniteDedekind

variable (R : Type u) (S : Type v) (F : Type w) (E : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E]

local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "D" => fun q : IdealBranch J => BranchCompletion J q

example :
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    (∑ q : IdealBranch J, Module.finrank (FractionRing Rhat) (FractionRing (D q))) =
      Module.finrank F E :=
  sum_localCompletionFraction_finrank R S F E

example :
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionBase_isLocalHom R S q
    (∑ q : IdealBranch J,
      Stacks.DiscreteValuationRing.Ramification.ramificationIdx Rhat (D q) *
        Module.finrank (ResidueField Rhat) (ResidueField (D q))) = Module.finrank F E :=
  sum_localCompletion_ramification_mul_residue_finrank R S F E

end FiniteDedekind

section AuxiliaryNormalization

variable (R : Type u) (F : Type w) (K : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field K] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [FiniteDimensional F K] [Algebra.IsSeparable F K]
  [DecidableEq (Ideal (integralClosure R K))]

local notation "A" => integralClosure R K
local notation "J" => Ideal.map (algebraMap R A) (maximalIdeal R)
local notation "Rhat" => AdicCompletion (maximalIdeal R) R

example :
    letI : IsDedekindDomain A := integralClosure.isDedekindDomain R F K
    letI := fun q => localCompletionBaseAlgebra (S := A) (maximalIdeal R) q
    letI := fun q => localCompletionBase_isLocalHom R A q
    (∑ q : IdealBranch J,
      Stacks.DiscreteValuationRing.Ramification.ramificationIdx Rhat (BranchCompletion J q) *
        Module.finrank (ResidueField Rhat) (ResidueField (BranchCompletion J q))) =
      Module.finrank F K := by
  let : Module.IsTorsionFree R K := Module.IsTorsionFree.trans_faithfulSMul R F K
  let : Module.IsTorsionFree R A := IsIntegralClosure.isTorsionFree R K
  let : IsDedekindDomain A := integralClosure.isDedekindDomain R F K
  let : Module.Finite R A := IsIntegralClosure.finite R F K A
  let : IsFractionRing A K := integralClosure.isFractionRing_of_finite_extension F K
  exact sum_localCompletion_ramification_mul_residue_finrank R A F K

end AuxiliaryNormalization

end AdicCompletion
