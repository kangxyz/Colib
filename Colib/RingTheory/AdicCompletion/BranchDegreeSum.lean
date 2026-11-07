/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.FractionBranches
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import StacksFrontier.RingTheory.DiscreteValuationRing.FundamentalIdentity

/-!
# The degree sum over all actual completed Dedekind branches

For a finite torsion-free Dedekind algebra over a DVR, the existing actual fraction tensor
decomposition gives the sum of the degrees of every completed branch. The native local
fundamental identity then identifies each summand with its actual ramification index times
its actual residue-field degree. No branch is selected or discarded.

The only actions used are `localCompletionBaseAlgebra`, `localCompletionFractionAlgebra`, and
the native residue-field actions. Finiteness belongs to each completed branch over the
completed base; it is not asserted for an original localization over the original base.
The four original ring and field universes remain independent. No separability, normality,
characteristic, Henselian, residue power-basis, or norm hypothesis is used.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing
open scoped BigOperators TensorProduct

universe u v w z

variable (R : Type u) (S : Type v) (F : Type w) (E : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E]

local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "Fhat" => FractionRing Rhat
local notation "D" => fun q : IdealBranch J => BranchCompletion J q
local notation "C" => fun q : IdealBranch J => FractionRing (D q)

/-- The degrees of all actual completed branch fraction fields sum to the degree of the
specified original fraction extension, using the existing full tensor decomposition. -/
theorem sum_localCompletionFraction_finrank :
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    (∑ q : IdealBranch J, Module.finrank Fhat (C q)) = Module.finrank F E := by
  let := fractionCompletionAlgebra R F
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionFractionAlgebra R S q
  let := fun q => localCompletionFractionFinite R S q
  let : ∀ q : IdealBranch J, Module.Free Fhat (C q) :=
    fun q => Module.Free.of_divisionRing Fhat (C q)
  calc
    (∑ q : IdealBranch J, Module.finrank Fhat (C q)) =
        Module.finrank Fhat (∀ q : IdealBranch J, C q) :=
      (Module.finrank_pi_fintype Fhat).symm
    _ = Module.finrank Fhat (Fhat ⊗[F] E) :=
      (fractionTensorEquivLocalFractionFields R S F E).toLinearEquiv.finrank_eq.symm
    _ = Module.finrank F E := Module.finrank_baseChange

/-- The literal completed-branch ramification indices and residue degrees have total
weight equal to the original field degree. The local fundamental identity supplies every
weight; neither a degree identity nor a tensor equivalence is assumed as an input. -/
theorem sum_localCompletion_ramification_mul_residue_finrank :
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionBase_isLocalHom R S q
    (∑ q : IdealBranch J,
      Stacks.DiscreteValuationRing.Ramification.ramificationIdx Rhat (D q) *
        Module.finrank (ResidueField Rhat) (ResidueField (D q))) = Module.finrank F E := by
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionBase_isLocalHom R S q
  let := fun q => localCompletionBaseFaithfulSMul R S q
  let := fun q => localCompletionBaseFinite (S := S) (maximalIdeal R)
    (map_maximalIdeal_ne_zero R S) q
  let := fun q => localCompletionFractionAlgebra R S q
  let := fun q => localCompletionFractionIsScalarTower R S q
  calc
    (∑ q : IdealBranch J,
      Stacks.DiscreteValuationRing.Ramification.ramificationIdx Rhat (D q) *
        Module.finrank (ResidueField Rhat) (ResidueField (D q))) =
        ∑ q : IdealBranch J, Module.finrank Fhat (C q) := by
      apply Finset.sum_congr rfl
      intro q _
      let : Module.Flat Rhat (D q) := inferInstance
      have h :=
        Stacks.DiscreteValuationRing.Ramification.ramificationIdx_mul_inertiaDeg_eq_finrank
          Rhat (D q) Fhat (C q)
      rw [Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal Rhat)] at h
      exact h
    _ = Module.finrank F E := sum_localCompletionFraction_finrank R S F E

end AdicCompletion
