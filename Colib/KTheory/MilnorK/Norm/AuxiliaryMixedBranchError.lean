/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.AuxiliaryBranchMaps
public import Colib.KTheory.MilnorK.Norm.DVRBranchWeightedError
public import Colib.KTheory.MilnorK.Symbols.MixedMap

/-!
# One actual auxiliary mixed witness controls every completed base branch

The native normalization is `integralClosure R K`, and every normalized ideal factor over
`maximalIdeal R` remains in the conclusion. For each one, the existing auxiliary construction
supplies all upper normalization/completion branches and their literal tensor coordinates.
A single mixed class over `K → M` is transported to every actual upper branch by its full
commuting field square. The already assembled weighted-error theorem then applies.

Neither upper nor lower norm compatibility, actual branch mixedness, branch Henselianity,
branch finiteness, nor branch locality is an input. They are proved by the cited constructions
and the literal map equations. The restriction map in the conclusion is exactly the native
`algebraMap (ResidueField R) (ResidueField T_i)` of the original local map `R → T_i`.

All rings and fields share one universe in this first endpoint. No replacement carrier,
ULift, norm, map definition, or package is introduced. No original localization over R is
claimed finite. The conclusion retains its ramification factor; it is not cancelled.

SOURCE ONLY. This scratch module has not been elaborated, compiled, or linted. Its two
source-stage imports must first be staged at their already assigned mathematical owners.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace Stacks.Chow

open DiscreteValuationRing.Ramification AdicCompletion

/-- One actual finite auxiliary mixed witness makes the ramification weight kill the
restricted original norm-residue error at every actual completed base branch. The full
upper branch family and every mixed membership are constructed inside the proof. -/
theorem ramification_smul_restrict_norm_residue_difference_eq_zero_of_auxiliary_mixed
    (R S F E K M : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [IsLocalHom (algebraMap R S)]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra R E] [Algebra S E] [IsFractionRing S E]
    [Algebra F E] [IsScalarTower R F E] [IsScalarTower R S E]
    [FiniteDimensional F E] [IsGalois F E]
    [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
    [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [Field M] [Algebra R M] [Algebra K M] [IsScalarTower R K M]
    [Algebra S M] [Algebra E M] [IsScalarTower S E M] [IsScalarTower R S M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [CharZero (ResidueField R)]
    (eta : K ⊗[F] E ≃ₐ[K] M)
    (heta : ∀ e : E, eta (1 ⊗ₜ[F] e) = algebraMap E M e)
    (hp : Nat.Prime (Module.finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap K M) n) :
    let A := integralClosure R K
    letI : IsDedekindDomain A := integralClosure.isDedekindDomain R F K
    letI : DecidableEq (Ideal A) := Classical.decEq _
    ∀ i : IdealBranch ((maximalIdeal R).map (algebraMap R A)),
    let T := BranchCompletion ((maximalIdeal R).map (algebraMap R A)) i
    letI : IsLocalHom (algebraMap R T) := by
      rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime i.val) T]
      infer_instance
    (ramificationIdx R T : ℤ) •
      milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
        (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
          milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) = 0 := by
  classical
  letI : IsDiscreteValuationRing.IsExtension R S := ⟨⟩
  have hbranches := exists_auxiliaryBranchTensorEquiv R S F E K M eta heta
  let A := integralClosure R K
  letI : IsDedekindDomain A := integralClosure.isDedekindDomain R F K
  letI : IsFractionRing A K := integralClosure.isFractionRing_of_finite_extension F K
  letI : DecidableEq (Ideal A) := Classical.decEq _
  haveI : Module.IsTorsionFree R K := Module.IsTorsionFree.trans_faithfulSMul R F K
  haveI : Module.IsTorsionFree R A := IsIntegralClosure.isTorsionFree R K
  change ∀ i : IdealBranch ((maximalIdeal R).map (algebraMap R A)), _
  intro i
  let B := Localization.AtPrime i.val
  let T := BranchCompletion ((maximalIdeal R).map (algebraMap R A)) i
  let L := FractionRing T
  letI : IsLocalHom (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R B T]
    infer_instance
  haveI : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).mpr (by
    rw [IsScalarTower.algebraMap_eq R A T]
    exact (branchCompletion_algebraMap_injective _ i).comp
      (FaithfulSMul.algebraMap_injective R A))
  letI := originalBranchFractionAlgebra A K i
  haveI := originalBranchFractionTower A K i
  letI := originalBranchIsFractionRing A K i
  haveI : IsScalarTower R B K := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A K,
      IsScalarTower.algebraMap_apply R A B,
      ← IsScalarTower.algebraMap_apply A B K]
  letI : Algebra B M := ((algebraMap K M).comp (algebraMap B K)).toAlgebra
  haveI : IsScalarTower B K M := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R B M := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K M,
      IsScalarTower.algebraMap_apply R B K,
      ← IsScalarTower.algebraMap_apply B K M]
  let C := integralClosure B M
  letI : IsDedekindDomain C := integralClosure.isDedekindDomain B K M
  haveI : Module.Finite B C := IsIntegralClosure.finite B K M C
  haveI : Module.IsTorsionFree B M := Module.IsTorsionFree.trans_faithfulSMul B K M
  haveI : Module.IsTorsionFree B C := IsIntegralClosure.isTorsionFree B M
  letI : IsFractionRing C M := integralClosure.isFractionRing_of_finite_extension K M
  letI : DecidableEq (Ideal C) := Classical.decEq _
  let J := (maximalIdeal B).map (algebraMap B C)
  let U := fun j : IdealBranch J => BranchCompletion J j
  let D := fun j : IdealBranch J => FractionRing (U j)
  letI := fractionCompletionAlgebra B K
  haveI := fractionCompletionIsScalarTower B K
  letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
  letI := fun j : IdealBranch J => localCompletionBaseAlgebra (S := C) (maximalIdeal B) j
  letI := fun j : IdealBranch J => localCompletionFractionAlgebra B C j
  letI : Algebra R C := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra S C := Stacks.EppTheorem.algebraIntegralClosureBase R B S M
  obtain ⟨epsilon, hRFL, hright, hauxiliary, _, htowers,
    hcomplete, _, hinj, hfraction⟩ := hbranches i
  letI : IsScalarTower R F L := hRFL
  letI : ∀ j : IdealBranch J, IsScalarTower R S (U j) := fun j => (htowers j).1
  letI : ∀ j : IdealBranch J, IsScalarTower R T (U j) := fun j => (htowers j).2.1
  letI : ∀ j : IdealBranch J, IsLocalHom (algebraMap S (U j)) :=
    fun j => (htowers j).2.2
  letI : ∀ j : IdealBranch J, Module.Finite T (U j) := fun j => (hcomplete.2 j).1
  letI : ∀ j : IdealBranch J, HenselianLocalRing (U j) := fun j => (hcomplete.2 j).2
  letI : ∀ j : IdealBranch J, IsLocalHom (algebraMap T (U j)) :=
    fun j => localCompletionBase_isLocalHom B C j
  letI : ∀ j : IdealBranch J, FaithfulSMul T (U j) :=
    fun j => localCompletionBaseFaithfulSMul B C j
  letI : ∀ j : IdealBranch J, Module.IsTorsionFree T (U j) := fun j =>
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective T (U j))
  letI : ∀ j : IdealBranch J, IsScalarTower T L (D j) :=
    fun j => localCompletionFractionIsScalarTower B C j
  letI : ∀ j : IdealBranch J, FiniteDimensional L (D j) :=
    fun j => localCompletionFractionFinite B C j
  letI : ∀ j : IdealBranch J, Algebra E (D j) :=
    fun j => (IsFractionRing.lift (K := E) (hinj j)).toAlgebra
  letI : ∀ j : IdealBranch J, IsScalarTower S E (D j) := fun j => (hfraction j).2
  have hinjSU (j : IdealBranch J) : Function.Injective (algebraMap S (U j)) := by
    intro s t h
    apply hinj j
    simpa only [← IsScalarTower.algebraMap_apply S (U j) (D j)] using
      congrArg (algebraMap (U j) (D j)) h
  letI : ∀ j : IdealBranch J, FaithfulSMul S (U j) := fun j =>
    (faithfulSMul_iff_algebraMap_injective S (U j)).mpr (hinjSU j)
  have hcoordinate (e : E) (j : IdealBranch J) :
      epsilon (1 ⊗ₜ[F] e) j = algebraMap E (D j) e :=
    RingHom.congr_fun (hfraction j).1 e
  let delta : L ⊗[K] M ≃ₐ[L] ∀ j : IdealBranch J, D j :=
    fractionTensorEquivLocalFractionFields B C K M
  let rho (j : IdealBranch J) : M →+* D j := (Pi.evalRingHom D j).comp
    (delta.toRingHom.comp
      (Algebra.TensorProduct.includeRight : M →ₐ[K] L ⊗[K] M).toRingHom)
  have hsquare (j : IdealBranch J) : (rho j).comp (algebraMap K M) =
      (algebraMap L (D j)).comp (algebraMap K L) := by
    ext k
    exact hauxiliary k j
  have hsource (j : IdealBranch J) : (rho j).comp (algebraMap E M) =
      algebraMap E (D j) := by
    ext e
    exact (hright e j).symm.trans (hcoordinate e j)
  have hbranchMixed (j : IdealBranch J) :
      milnorKTheoryMap (algebraMap E (D j)) (n + 1) x ∈
        milnorKMixedSpan (algebraMap L (D j)) n := by
    have h := milnorKTheoryMap_mem_mixedSpan_of_comm (algebraMap K M)
      (algebraMap K L) (rho j) (algebraMap L (D j)) (hsquare j) n
      (milnorKTheoryMap (algebraMap E M) (n + 1) x) hmixed
    have hcomp : milnorKTheoryMap ((rho j).comp (algebraMap E M)) (n + 1) x =
        milnorKTheoryMap (rho j) (n + 1)
          (milnorKTheoryMap (algebraMap E M) (n + 1) x) := by
      rw [milnorKTheoryMap_comp, LinearMap.comp_apply]
    rw [← hcomp, hsource j] at h
    exact h
  exact ramification_smul_restrict_norm_residue_difference_eq_zero_of_mixed_branches
    R S T F E L U D epsilon hcoordinate hp n x hbranchMixed

end Stacks.Chow

end
