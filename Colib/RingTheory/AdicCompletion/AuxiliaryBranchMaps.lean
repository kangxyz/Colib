/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.FractionBranches
public import Colib.RingTheory.Henselian.PrincipalRoots
public import StacksFrontier.RingTheory.BaseChangeTransport
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppFactorPackage
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionInput
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The actual iterated auxiliary normalization branches

SOURCE ONLY: this scratch source has not been elaborated, compiled, or linted.

The normalization carriers are literally `integralClosure R K` and
`integralClosure (Localization.AtPrime i.val) M`. Both completions are the existing
`AdicCompletion.BranchCompletion`; both fraction fields are `FractionRing` of those
completions. Every actual normalized ideal factor is retained at both stages.

The input `eta` is the equivalence for the actual mapped-root extension `M`. For the
native quotient presentation it is obtained by tensoring the original presentation
and composing with `AdjoinRoot.baseChangeAlgEquiv`. Its right-coordinate equation is
retained explicitly: an abstract field equivalence is not sufficient here.

The proof constructs only local proof data and an existential algebra equivalence.
It introduces no new branch carrier, factor package, horizontal integral-closure map,
or fraction-field map. The horizontal map is Stacks' `integralClosureBaseMap`, through
`algebraIntegralClosureBase`. Localness uses Stacks' existing tower theorem.

No finiteness of the first localization over `R` is asserted. The only normalization
finiteness statements used are derived from the given finite separable field extensions.
The six original ring and field universes are independent.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe uR uS uF uE uK uM

namespace AdjoinRoot

/-- Composing the actual presentation with native root base change gives the literal
coefficient-map image on every original element. No quotient equivalence or field
embedding is selected independently of the given presentation. -/
theorem baseChangeAlgEquiv_presentation_one_tmul
    (F : Type uF) (K : Type uK) (E : Type uE)
    [CommRing F] [CommRing K] [CommRing E] [Algebra F K] [Algebra F E]
    (p : Polynomial F) (g : AdjoinRoot p ≃ₐ[F] E) (e : E) :
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) g.symm).trans
        (baseChangeAlgEquiv F K p)) (1 ⊗ₜ[F] e) =
      AdjoinRoot.map (algebraMap F K) p (p.map (algebraMap F K)) dvd_rfl (g.symm e) := by
  have hmap : (baseChangeAlgEquiv F K p).toRingHom.comp
      (Algebra.TensorProduct.includeRight : AdjoinRoot p →ₐ[F]
        K ⊗[F] AdjoinRoot p).toRingHom =
        AdjoinRoot.map (algebraMap F K) p (p.map (algebraMap F K)) dvd_rfl := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro c
      exact (baseChangeAlgEquiv_tmul_of F K p c).trans
        (AdjoinRoot.map_of (algebraMap F K) p (p.map (algebraMap F K)) dvd_rfl c).symm
    · exact (baseChangeAlgEquiv_tmul_root F K p).trans
        (AdjoinRoot.map_root (algebraMap F K) p (p.map (algebraMap F K)) dvd_rfl).symm
  simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq]
  exact RingHom.congr_fun hmap (g.symm e)

end AdjoinRoot

namespace AdicCompletion

open IsLocalRing

/-- The actual auxiliary branches have the full tensor decomposition with the native
horizontal integral maps, both field-coordinate squares, localness, and the whole
original-fraction triangle. The final equality identifies the right coordinate with
Mathlib's fraction lift of the actual `S`-to-branch map.

`M` is the specified mapped-root field, not a field selected from an abstract product.
`heta` records its actual original-field map. The hypothesis `Algebra.IsIntegral R S`
is enough for the horizontal map; no finiteness of `S` is used by this construction.
-/
theorem exists_auxiliaryBranchTensorEquiv
    (R : Type uR) (S : Type uS) (F : Type uF) (E : Type uE)
    (K : Type uK) (M : Type uM)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field F] [Field E] [Field K] [Field M]
    [Algebra R S] [Algebra.IsIntegral R S] [IsDiscreteValuationRing.IsExtension R S]
    [Algebra R F] [IsFractionRing R F]
    [Algebra S E] [IsFractionRing S E] [Algebra F E]
    [Algebra R K] [Algebra F K] [IsScalarTower R F K]
    [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [Algebra R M] [Algebra K M] [IsScalarTower R K M]
    [Algebra S M] [Algebra E M] [IsScalarTower S E M] [IsScalarTower R S M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (eta : K ⊗[F] E ≃ₐ[K] M)
    (heta : ∀ e : E, eta (1 ⊗ₜ[F] e) = algebraMap E M e) :
    let A := integralClosure R K
    letI : IsDedekindDomain A := integralClosure.isDedekindDomain R F K
    letI : IsFractionRing A K := integralClosure.isFractionRing_of_finite_extension F K
    letI : DecidableEq (Ideal A) := Classical.decEq _
    ∀ i : IdealBranch ((maximalIdeal R).map (algebraMap R A)),
    let B := Localization.AtPrime i.val
    letI := originalBranchFractionAlgebra A K i
    letI := originalBranchFractionTower A K i
    letI := originalBranchIsFractionRing A K i
    letI : IsScalarTower R B K := IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R A K,
        IsScalarTower.algebraMap_apply R A B,
        ← IsScalarTower.algebraMap_apply A B K]
    letI : Algebra B M := ((algebraMap K M).comp (algebraMap B K)).toAlgebra
    letI : IsScalarTower B K M := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower R B M := IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R K M,
        IsScalarTower.algebraMap_apply R B K,
        ← IsScalarTower.algebraMap_apply B K M]
    let C := integralClosure B M
    letI : IsDedekindDomain C := integralClosure.isDedekindDomain B K M
    letI : Module.Finite B C := IsIntegralClosure.finite B K M C
    letI : Module.IsTorsionFree B M := Module.IsTorsionFree.trans_faithfulSMul B K M
    letI : Module.IsTorsionFree B C := IsIntegralClosure.isTorsionFree B M
    letI : IsFractionRing C M := integralClosure.isFractionRing_of_finite_extension K M
    letI : DecidableEq (Ideal C) := Classical.decEq _
    let J := (maximalIdeal B).map (algebraMap B C)
    let T := BranchCompletion ((maximalIdeal R).map (algebraMap R A)) i
    let L := FractionRing T
    let U := fun j : IdealBranch J => BranchCompletion J j
    let D := fun j : IdealBranch J => FractionRing (U j)
    letI := fractionCompletionAlgebra B K
    letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
    letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
    letI := fun j : IdealBranch J => localCompletionBaseAlgebra (S := C) (maximalIdeal B) j
    letI := fun j : IdealBranch J => localCompletionFractionAlgebra B C j
    letI : Algebra R C := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
    letI : Algebra S C := Stacks.EppTheorem.algebraIntegralClosureBase R B S M
    ∃ epsilon : L ⊗[F] E ≃ₐ[L] ∀ j : IdealBranch J, D j,
      IsScalarTower R F L ∧
      (∀ (e : E) (j : IdealBranch J), epsilon (1 ⊗ₜ[F] e) j =
        fractionTensorEquivLocalFractionFields B C K M
          (1 ⊗ₜ[K] algebraMap E M e) j) ∧
      (∀ (k : K) (j : IdealBranch J),
        fractionTensorEquivLocalFractionFields B C K M
            (1 ⊗ₜ[K] algebraMap K M k) j =
          algebraMap L (D j) (algebraMap K L k)) ∧
      (∀ (s : S) (j : IdealBranch J),
        epsilon (1 ⊗ₜ[F] algebraMap S E s) j =
          algebraMap (U j) (D j) (algebraMap S (U j) s)) ∧
      (∀ j : IdealBranch J, IsScalarTower R S (U j) ∧
        IsScalarTower R T (U j) ∧ IsLocalHom (algebraMap S (U j))) ∧
      (HenselianLocalRing T ∧ ∀ j : IdealBranch J,
        Module.Finite T (U j) ∧ HenselianLocalRing (U j)) ∧
      (CharZero (ResidueField R) → CharZero (ResidueField T) ∧
        ∀ j : IdealBranch J, CharZero (ResidueField (U j)) ∧
          ∀ n : ℕ, 0 < n → IsUnit (n : U j)) ∧
      ∃ hinj : ∀ j : IdealBranch J, Function.Injective (algebraMap S (D j)),
        ∀ j : IdealBranch J,
          ((Pi.evalRingHom D j).comp
              (epsilon.toRingHom.comp
                (Algebra.TensorProduct.includeRight : E →ₐ[F] L ⊗[F] E).toRingHom) =
            IsFractionRing.lift (K := E) (hinj j)) ∧
          (letI : Algebra E (D j) := (IsFractionRing.lift (K := E) (hinj j)).toAlgebra
           IsScalarTower S E (D j)) := by
  classical
  let A := integralClosure R K
  letI : IsDedekindDomain A := integralClosure.isDedekindDomain R F K
  letI : IsFractionRing A K := integralClosure.isFractionRing_of_finite_extension F K
  letI : DecidableEq (Ideal A) := Classical.decEq _
  change ∀ i : IdealBranch ((maximalIdeal R).map (algebraMap R A)), _
  intro i
  let B := Localization.AtPrime i.val
  letI := originalBranchFractionAlgebra A K i
  letI := originalBranchFractionTower A K i
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
  let T := BranchCompletion ((maximalIdeal R).map (algebraMap R A)) i
  let L := FractionRing T
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
  haveI : IsScalarTower S C M :=
    Stacks.EppTheorem.isScalarTower_base_integralClosure_factor R B S M
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B L,
      IsScalarTower.algebraMap_apply B K L,
      ← IsScalarTower.algebraMap_apply R B K]
  have hRFL : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K L,
      IsScalarTower.algebraMap_apply R F K,
      ← IsScalarTower.algebraMap_apply F K L]
  let delta : L ⊗[K] M ≃ₐ[L] ∀ j : IdealBranch J, D j :=
    fractionTensorEquivLocalFractionFields B C K M
  let epsilon : L ⊗[F] E ≃ₐ[L] ∀ j : IdealBranch J, D j :=
    (Algebra.TensorProduct.cancelBaseChange F K L L E).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) eta).trans delta)
  have hepsilon (e : E) (j : IdealBranch J) :
      epsilon (1 ⊗ₜ[F] e) j = delta (1 ⊗ₜ[K] algebraMap E M e) j := by
    simp only [epsilon, AlgEquiv.trans_apply,
      Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq, heta]
  have hauxiliary (k : K) (j : IdealBranch J) :
      delta (1 ⊗ₜ[K] algebraMap K M k) j =
        algebraMap L (D j) (algebraMap K L k) := by
    have h : (1 : L) ⊗ₜ[K] algebraMap K M k =
        algebraMap L (L ⊗[K] M) (algebraMap K L k) := by
      rw [← Algebra.TensorProduct.algebraMap_apply',
        IsScalarTower.algebraMap_apply K L (L ⊗[K] M)]
    rw [h, delta.commutes]
    rfl
  have hintegral (s : S) (j : IdealBranch J) :
      epsilon (1 ⊗ₜ[F] algebraMap S E s) j =
        algebraMap (U j) (D j) (algebraMap S (U j) s) := by
    rw [hepsilon, ← IsScalarTower.algebraMap_apply S E M,
      IsScalarTower.algebraMap_apply S C M]
    change fractionTensorEquivLocalFractionFields B C K M
      (1 ⊗ₜ[K] algebraMap C M (algebraMap S C s)) j = _
    rw [fractionTensorEquivLocalFractionFields_one_tmul]
    rw [← IsScalarTower.algebraMap_apply C (Localization.AtPrime j.val) (U j),
      ← IsScalarTower.algebraMap_apply S C (U j)]
  have hsourceTower (j : IdealBranch J) : IsScalarTower R S (U j) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R B (U j),
        IsScalarTower.algebraMap_apply B C (U j),
        Stacks.EppTheorem.algebraMap_integralClosureBase_eq R B S M r,
        ← IsScalarTower.algebraMap_apply S C (U j)]
  have hcompletedTower (j : IdealBranch J) : IsScalarTower R T (U j) := by
    haveI := localCompletionBaseIsScalarTower (S := C) (maximalIdeal B) j
    exact IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R B (U j),
        IsScalarTower.algebraMap_apply B T (U j),
        ← IsScalarTower.algebraMap_apply R B T]
  have hlocal (j : IdealBranch J) : IsLocalHom (algebraMap S (U j)) := by
    haveI : IsLocalHom (algebraMap B (U j)) := by
      rw [IsScalarTower.algebraMap_eq B (Localization.AtPrime j.val) (U j)]
      infer_instance
    haveI : IsLocalHom (algebraMap R (U j)) := by
      rw [IsScalarTower.algebraMap_eq R B (U j)]
      infer_instance
    haveI := hsourceTower j
    exact Stacks.EppTheorem.isLocalHom_algebraMap_of_tower R S (U j)
  have hcomplete : HenselianLocalRing T ∧ ∀ j : IdealBranch J,
      Module.Finite T (U j) ∧ HenselianLocalRing (U j) := by
    refine ⟨IsDiscreteValuationRing.henselianLocalRing_adicCompletion B, fun j => ?_⟩
    exact ⟨localCompletionBaseFinite (S := C) (maximalIdeal B)
      (map_maximalIdeal_ne_zero B C) j,
      IsDiscreteValuationRing.henselianLocalRing_adicCompletion
        (Localization.AtPrime j.val)⟩
  have hchar (hκ : CharZero (ResidueField R)) : CharZero (ResidueField T) ∧
      ∀ j : IdealBranch J, CharZero (ResidueField (U j)) ∧
        ∀ n : ℕ, 0 < n → IsUnit (n : U j) := by
    letI := hκ
    haveI : IsLocalHom (algebraMap R T) := by
      rw [IsScalarTower.algebraMap_eq R B T]
      infer_instance
    have hT : CharZero (ResidueField T) :=
      charZero_of_injective_ringHom (ResidueField.map (algebraMap R T)).injective
    refine ⟨hT, fun j => ?_⟩
    haveI : IsLocalHom (algebraMap B (U j)) := by
      rw [IsScalarTower.algebraMap_eq B (Localization.AtPrime j.val) (U j)]
      infer_instance
    haveI : IsLocalHom (algebraMap R (U j)) := by
      rw [IsScalarTower.algebraMap_eq R B (U j)]
      infer_instance
    letI : CharZero (ResidueField (U j)) :=
      charZero_of_injective_ringHom (ResidueField.map (algebraMap R (U j))).injective
    exact ⟨inferInstance, fun n hn =>
      HenselianLocalRing.PrincipalRoots.isUnit_natCast_of_residue_charZero n hn⟩
  have hinjSM : Function.Injective (algebraMap S M) := by
    rw [IsScalarTower.algebraMap_eq S E M]
    exact (algebraMap E M).injective.comp (IsFractionRing.injective S E)
  have hinjSC : Function.Injective (algebraMap S C) := by
    intro s t h
    apply hinjSM
    simpa only [← IsScalarTower.algebraMap_apply S C M] using
      congrArg (algebraMap C M) h
  have hinjSU (j : IdealBranch J) : Function.Injective (algebraMap S (U j)) := by
    rw [IsScalarTower.algebraMap_eq S C (U j)]
    exact (branchCompletion_algebraMap_injective J j).comp hinjSC
  have hinjSD (j : IdealBranch J) : Function.Injective (algebraMap S (D j)) := by
    rw [IsScalarTower.algebraMap_eq S (U j) (D j)]
    exact (IsFractionRing.injective (U j) (D j)).comp (hinjSU j)
  refine ⟨epsilon, hRFL, hepsilon, hauxiliary, hintegral,
    fun j => ⟨hsourceTower j, hcompletedTower j, hlocal j⟩,
    hcomplete, hchar, hinjSD, ?_⟩
  intro j
  refine ⟨?_, ?_⟩
  · apply IsFractionRing.ringHom_ext (A := S)
    intro s
    change epsilon (1 ⊗ₜ[F] algebraMap S E s) j =
      IsFractionRing.lift (K := E) (hinjSD j) (algebraMap S E s)
    rw [hintegral, IsFractionRing.lift_algebraMap,
      ← IsScalarTower.algebraMap_apply S (U j) (D j)]
  · letI : Algebra E (D j) := (IsFractionRing.lift (K := E) (hinjSD j)).toAlgebra
    exact IsScalarTower.of_algebraMap_eq fun s =>
      (IsFractionRing.lift_algebraMap (hinjSD j) s).symm

end AdicCompletion
