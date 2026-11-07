/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.AuxiliaryBranchMaps
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRBranchWeightedError
public import Colib.RingTheory.KTheory.MilnorK.Symbols.MixedMap

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

-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace Stacks.Chow

open DiscreteValuationRing.Ramification _root_.AdicCompletion

/-- The two literal tensor coordinates transport one mixed witness to every factor.
This proof uses only the existing field square and the native tensor-product maps. -/
private theorem mem_mixedSpan_of_tensor_coordinates
    (K M L E : Type u) [Field K] [Field M] [Field L] [Field E]
    [Algebra K M] [Algebra K L] [Algebra E M]
    {ι : Type u} (D : ι → Type u) [∀ j, Field (D j)]
    [∀ j, Algebra L (D j)] [∀ j, Algebra E (D j)]
    (delta : L ⊗[K] M ≃ₐ[L] ∀ j, D j)
    (hsource : ∀ (e : E) (j : ι),
      delta.toFun ((1 : L) ⊗ₜ[K] algebraMap E M e) j = algebraMap E (D j) e)
    (n : ℕ) (x : MilnorKTheory E (n + 1))
    (hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap K M) n) :
    ∀ j, milnorKTheoryMap (algebraMap E (D j)) (n + 1) x ∈
      milnorKMixedSpan (algebraMap L (D j)) n := by
  have hbase (k : K) (j : ι) :
      delta.toFun ((1 : L) ⊗ₜ[K] algebraMap K M k) j =
        algebraMap L (D j) (algebraMap K L k) := by
    have h : (1 : L) ⊗ₜ[K] algebraMap K M k =
        algebraMap L (L ⊗[K] M) (algebraMap K L k) := by
      rw [← Algebra.TensorProduct.algebraMap_apply',
        IsScalarTower.algebraMap_apply K L (L ⊗[K] M)]
    rw [h]
    exact congrFun (delta.commutes (algebraMap K L k)) j
  intro j
  let rho : M →+* D j := (Pi.evalAlgHom L D j).toRingHom.comp
    (delta.toRingHom.comp
      (Algebra.TensorProduct.includeRight : M →ₐ[K] L ⊗[K] M).toRingHom)
  have hsquare : rho.comp (algebraMap K M) =
      (algebraMap L (D j)).comp (algebraMap K L) := by
    ext k
    exact hbase k j
  have hmap : rho.comp (algebraMap E M) = algebraMap E (D j) := by
    ext e
    exact hsource e j
  have h := milnorKTheoryMap_mem_mixedSpan_of_comm (algebraMap K M)
    (algebraMap K L) rho (algebraMap L (D j)) hsquare n
    (milnorKTheoryMap (algebraMap E M) (n + 1) x) hmixed
  have hcomp : milnorKTheoryMap (rho.comp (algebraMap E M)) (n + 1) x =
      milnorKTheoryMap rho (n + 1)
        (milnorKTheoryMap (algebraMap E M) (n + 1) x) := by
    rw [milnorKTheoryMap_comp, LinearMap.comp_apply]
  rw [← hcomp, hmap] at h
  exact h

-- Keep the native branch-index factorization opaque during instance synthesis.
attribute [local irreducible] UniqueFactorizationMonoid.normalizedFactors
  UniqueFactorizationMonoid.factors

set_option maxHeartbeats 400000 in
-- Specializing the full native iterated branch construction checks a large dependent proof.
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
    let A : Type u := integralClosure R K
    let _ : CommRing A := inferInstance
    let _ : CommSemiring A := CommRing.toCommSemiring
    let _ : IsDedekindDomain A := integralClosure.isDedekindDomain R F K
    let _ : DecidableEq (Ideal A) := Classical.decEq _
    ∀ i : IdealBranch ((maximalIdeal R).map (algebraMap R A)),
    let T := BranchCompletion ((maximalIdeal R).map (algebraMap R A)) i
    let _ : IsLocalHom (algebraMap R T) := by
      rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime i.val) T]
      infer_instance
    (ramificationIdx R T : ℤ) •
      milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
        (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
          milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) = 0 := by
  classical
  intro A _ _ _ _ i T _
  let : IsDiscreteValuationRing.IsExtension R S := ⟨⟩
  have hbranches := exists_auxiliaryBranchTensorEquiv R S F E K M eta heta
  let : IsFractionRing A K := integralClosure.isFractionRing_of_finite_extension F K
  have : Module.IsTorsionFree R K := Module.IsTorsionFree.trans_faithfulSMul R F K
  have : Module.IsTorsionFree R A := IsIntegralClosure.isTorsionFree R K
  let B := Localization.AtPrime i.val
  let _ : CommRing B := inferInstance
  let _ : CommSemiring B := CommRing.toCommSemiring
  let L := FractionRing T
  have : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).mpr (by
    rw [IsScalarTower.algebraMap_eq R A T]
    exact (branchCompletion_algebraMap_injective _ i).comp
      (FaithfulSMul.algebraMap_injective R A))
  let := originalBranchFractionAlgebra A K i
  have := originalBranchFractionTower A K i
  let := originalBranchIsFractionRing A K i
  have : FaithfulSMul B K :=
    (faithfulSMul_iff_algebraMap_injective B K).mpr (IsFractionRing.injective B K)
  have : IsScalarTower R B K := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A K,
      IsScalarTower.algebraMap_apply R A B,
      ← IsScalarTower.algebraMap_apply A B K]
  let : Algebra B M := ((algebraMap K M).comp (algebraMap B K)).toAlgebra
  have : IsScalarTower B K M := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R B M := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K M,
      IsScalarTower.algebraMap_apply R B K,
      ← IsScalarTower.algebraMap_apply B K M]
  let C : Type u := integralClosure B M
  let _ : CommRing C := inferInstance
  let _ : CommSemiring C := CommRing.toCommSemiring
  let : IsDedekindDomain C := integralClosure.isDedekindDomain B K M
  have : Module.Finite B C := IsIntegralClosure.finite B K M C
  have : Module.IsTorsionFree B M := Module.IsTorsionFree.trans_faithfulSMul B K M
  have : Module.IsTorsionFree B C := IsIntegralClosure.isTorsionFree B M
  let : IsFractionRing C M := integralClosure.isFractionRing_of_finite_extension K M
  let : DecidableEq (Ideal C) := Classical.decEq _
  let J := (maximalIdeal B).map (algebraMap B C)
  let U := fun j : IdealBranch J => BranchCompletion J j
  let D := fun j : IdealBranch J => FractionRing (U j)
  let delta := fractionTensorEquivLocalFractionFields B C K M
  let _ : Algebra K L := fractionCompletionAlgebra B K
  let _ : SMul K L := Algebra.toSMul
  let _ : Module K L := Algebra.toModule
  have := fractionCompletionIsScalarTower B K
  let : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  let _ : SMul F L := Algebra.toSMul
  let _ : Module F L := Algebra.toModule
  have : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
  let aTU : (j : IdealBranch J) → Algebra T (U j) := fun j =>
    localCompletionBaseAlgebra (S := C) (maximalIdeal B) j
  let _ : (j : IdealBranch J) → SMul T (U j) := fun j => (aTU j).toSMul
  let _ : (j : IdealBranch J) → Module T (U j) := fun j =>
    @Algebra.toModule T (U j) _ _ (aTU j)
  let aLD : (j : IdealBranch J) → Algebra L (D j) := fun j =>
    localCompletionFractionAlgebra B C j
  let _ : (j : IdealBranch J) → SMul L (D j) := fun j => (aLD j).toSMul
  let _ : (j : IdealBranch J) → Module L (D j) := fun j =>
    @Algebra.toModule L (D j) _ _ (aLD j)
  let : Algebra R C := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra S C := Stacks.EppTheorem.algebraIntegralClosureBase R B S M
  refine (hbranches i).elim ?_
  intro epsilon hbranchesData
  have hRFL := hbranchesData.1
  have hright := hbranchesData.2.1
  have htowers := hbranchesData.2.2.2.2.1
  have hcomplete := hbranchesData.2.2.2.2.2.1
  refine hbranchesData.2.2.2.2.2.2.2.elim ?_
  intro hinj hfraction
  let : IsScalarTower R F L := hRFL
  let : ∀ j : IdealBranch J, IsScalarTower R S (U j) := fun j => (htowers j).1
  have := fun j : IdealBranch J => (htowers j).2.1
  have := fun j : IdealBranch J => (htowers j).2.2
  have := fun j : IdealBranch J => (hcomplete.2 j).1
  let : ∀ j : IdealBranch J, HenselianLocalRing (U j) := fun j => (hcomplete.2 j).2
  let : ∀ j : IdealBranch J, IsLocalHom (algebraMap T (U j)) :=
    fun j => localCompletionBase_isLocalHom B C j
  let : ∀ j : IdealBranch J, FaithfulSMul T (U j) :=
    fun j => localCompletionBaseFaithfulSMul B C j
  let : ∀ j : IdealBranch J, Module.IsTorsionFree T (U j) := fun j =>
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective T (U j))
  let : ∀ j : IdealBranch J, IsScalarTower T L (D j) :=
    fun j => localCompletionFractionIsScalarTower B C j
  let : ∀ j : IdealBranch J, FiniteDimensional L (D j) :=
    fun j => localCompletionFractionFinite B C j
  let aED : ∀ j : IdealBranch J, Algebra E (D j) :=
    fun j => (IsFractionRing.lift (K := E) (hinj j)).toAlgebra
  let _ : (j : IdealBranch J) → SMul E (D j) := fun j => (aED j).toSMul
  have := fun j : IdealBranch J => (hfraction j).2
  let : ∀ j : IdealBranch J, IsScalarTower S (U j) (D j) := fun j => inferInstance
  have hinjSU (j : IdealBranch J) : Function.Injective (algebraMap S (U j)) := by
    intro s t h
    apply hinj j
    simpa only [← IsScalarTower.algebraMap_apply S (U j) (D j)] using
      congrArg (algebraMap (U j) (D j)) h
  let : ∀ j : IdealBranch J, FaithfulSMul S (U j) := fun j =>
    (faithfulSMul_iff_algebraMap_injective S (U j)).mpr (hinjSU j)
  have hcoordinate (e : E) (j : IdealBranch J) :
      epsilon.toFun ((1 : L) ⊗ₜ[F] e) j = algebraMap E (D j) e := by
    exact RingHom.congr_fun (hfraction j).1 e
  have hsource (e : E) (j : IdealBranch J) :=
    (hright e j).symm.trans (hcoordinate e j)
  let htransportSource := mem_mixedSpan_of_tensor_coordinates K M L E D _ hsource
  have hbranchMixed := htransportSource n x hmixed
  have hweighted :=
    ramification_smul_restrict_norm_residue_difference_eq_zero_of_mixed_branches
      R S T F E L U D
  have hweightedEpsilon := hweighted epsilon
  have hweightedCoordinate := hweightedEpsilon hcoordinate
  have hweightedClass := hweightedCoordinate hp n x
  have hweightedMixed := hweightedClass hbranchMixed
  exact hweightedMixed

end Stacks.Chow

end
