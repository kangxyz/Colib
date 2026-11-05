/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.Algebra.Algebra.Pi
public import StacksFrontier.RingTheory.AdicCompletion.Comparison
public import StacksFrontier.RingTheory.AdicCompletion.IntersectionOfMaximalIdeals

/-
Additional retained implementation credits:
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Copyright (c) 2026 Colib contributors. All rights reserved.
-/

/-!
# Canonical Chinese remainder and localization maps on completions

The finite Chinese remainder map and the map from a maximal-ideal completion to the
completion of its actual localization are bundled as algebra equivalences. Their forward
maps are the native `adicCompletionMap`. Positive powers are removed using the native
cofinal comparison, with an explicit same-level evaluation formula.

Implementation provenance: adapted from `Aglib/RingTheory/AdicCompletion/{Powers,
ChineseRemainder,Localization}.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f` (Apache-2.0, kangxyz). The inverse-limit
constructions in those files are replaced here by the public comparison and bijectivity
theorems in Stacks revision `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open Function IsLocalRing
open scoped BigOperators

universe u v w

section ChineseRemainder

variable {R : Type u} {ι : Type v} [CommRing R] [Fintype ι]
  (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J))

include hJ in
/-- The powers of a finite product of pairwise comaximal ideals are the corresponding
intersections of powers. -/
theorem prod_pow_eq_iInf (n : ℕ) : (∏ i, J i) ^ n = ⨅ i, J i ^ n := by
  classical
  rw [← Finset.prod_pow]
  simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (s := Finset.univ) (J := fun i => J i ^ n)
    (fun i _ j _ hij => (hJ hij).pow)

include hJ in
/-- The product ideal is contained in each branch ideal. -/
theorem prodIdeal_le (i : ι) : (∏ j, J j) ≤ J i := by
  calc
    (∏ j, J j) = ⨅ j, J j := by simpa using prod_pow_eq_iInf J hJ 1
    _ ≤ J i := iInf_le J i

/-- The Chinese remainder equivalence at the actual quotient level. -/
def quotientProdPowEquiv (n : ℕ) :
    (R ⧸ (∏ i, J i) ^ n) ≃+* ∀ i, R ⧸ J i ^ n :=
  (Ideal.quotEquivOfEq (prod_pow_eq_iInf J hJ n)).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i => J i ^ n)
      (fun _ _ hij => (hJ hij).pow))

@[simp]
theorem quotientProdPowEquiv_mk (n : ℕ) (r : R) (i : ι) :
    quotientProdPowEquiv J hJ n (Ideal.Quotient.mk ((∏ i, J i) ^ n) r) i =
      Ideal.Quotient.mk (J i ^ n) r := rfl

/-- The quotient Chinese remainder maps preserve the actual transition maps. -/
theorem quotientProdPowEquiv_factorPow {m n : ℕ} (hmn : m ≤ n)
    (x : R ⧸ (∏ i, J i) ^ n) (i : ι) :
    quotientProdPowEquiv J hJ m (Ideal.Quotient.factorPow (∏ i, J i) hmn x) i =
      Ideal.Quotient.factorPow (J i) hmn (quotientProdPowEquiv J hJ n x i) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The quotient Chinese remainder equivalence preserves the original base algebra. -/
def quotientProdPowAlgEquiv (n : ℕ) :
    (R ⧸ (∏ i, J i) ^ n) ≃ₐ[R] ∀ i, R ⧸ J i ^ n where
  __ := quotientProdPowEquiv J hJ n
  commutes' r := by ext i; rfl

/-- The branch map is the native completion map of the identity of the original ring. -/
def prodCompletionToBranch (i : ι) :
    AdicCompletion (∏ i, J i) R →ₐ[R] AdicCompletion (J i) R := by
  let hmap : (∏ j, J j).map (RingHom.id R) ≤ J i := by
    simpa using prodIdeal_le J hJ i
  let f := adicCompletionMap (RingHom.id R) (∏ j, J j) (J i) hmap
  refine { f with commutes' := ?_ }
  intro r
  change f (algebraMap R (AdicCompletion (∏ i, J i) R) r) = _
  exact DFunLike.congr_fun
    (adicCompletionMap_comp_algebraMap (RingHom.id R) (∏ j, J j) (J i) hmap) r

@[simp]
theorem eval_prodCompletionToBranch (n : ℕ)
    (x : AdicCompletion (∏ i, J i) R) (i : ι) :
    evalₐ (J i) n (prodCompletionToBranch J hJ i x) =
      quotientProdPowEquiv J hJ n (evalₐ (∏ i, J i) n x) i := by
  change evalₐ (J i) n (adicCompletionMap (RingHom.id R) (∏ j, J j) (J i)
    (by simpa using prodIdeal_le J hJ i) x) = _
  rw [adicCompletionMap_evalₐ]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ (∏ i, J i) n x)
  rw [← hr]
  rfl

/-- Finite Chinese remainder on completions, bundled from the native canonical map.
No inverse limit or inverse map is reconstructed here. -/
@[colib_tag "COL-0186",
  colib_ref "aglib_principal_euler_pin" "RingTheory/AdicCompletion/ChineseRemainder.lean"
    "adaptation" "Canonical maps and actual completions; native lower interfaces"]
def prodCompletionAlgEquiv :
    AdicCompletion (∏ i, J i) R ≃ₐ[R] ∀ i, AdicCompletion (J i) R :=
  AlgEquiv.ofBijective (AlgHom.pi (prodCompletionToBranch J hJ)) (by
    have hprod : (∏ i, J i) = ⨅ i, J i := by
      simpa using prod_pow_eq_iInf J hJ 1
    change Function.Bijective (RingHom.pi fun i =>
      adicCompletionMap (RingHom.id R) (∏ j, J j) (J i)
        (by simpa using prodIdeal_le J hJ i))
    have hbij (K : Ideal R) (hK : K = ⨅ i, J i)
        (hle : ∀ i, K.map (RingHom.id R) ≤ J i) :
        Function.Bijective (RingHom.pi fun i =>
          adicCompletionMap (RingHom.id R) K (J i) (hle i)) := by
      subst K
      exact Stacks.AdicCompletion.bijective_adicCompletion_iInf_to_pi J hJ
    exact hbij _ hprod _)

/-- Every coordinate of the bundled equivalence is the specified native completion map. -/
theorem prodCompletionAlgEquiv_apply (x : AdicCompletion (∏ i, J i) R) (i : ι)
    (hmap : (∏ j, J j).map (RingHom.id R) ≤ J i) :
    prodCompletionAlgEquiv J hJ x i =
      adicCompletionMap (RingHom.id R) (∏ j, J j) (J i) hmap x := rfl

@[simp]
theorem eval_prodCompletionAlgEquiv (n : ℕ)
    (x : AdicCompletion (∏ i, J i) R) (i : ι) :
    evalₐ (J i) n (prodCompletionAlgEquiv J hJ x i) =
      quotientProdPowEquiv J hJ n (evalₐ (∏ i, J i) n x) i :=
  eval_prodCompletionToBranch J hJ n x i

@[simp]
theorem prodCompletionAlgEquiv_algebraMap (r : R) (i : ι) :
    prodCompletionAlgEquiv J hJ (algebraMap R (AdicCompletion (∏ i, J i) R) r) i =
      algebraMap R (AdicCompletion (J i) R) r :=
  congrFun ((prodCompletionAlgEquiv J hJ).commutes r) i

end ChineseRemainder

section Powers

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- A positive power defines the same completion, using the public cofinal comparison. -/
@[colib_tag "COL-0186"]
def powAlgEquiv (e : ℕ) (he : 0 < e) :
    AdicCompletion (I ^ e) R ≃ₐ[R] AdicCompletion I R :=
  compareAlgEquiv R (K₁ := I ^ e) (K₂ := I) (a := 1) (b := e)
    (by simpa only [pow_one] using (Ideal.pow_le_self he.ne' : I ^ e ≤ I)) le_rfl

/-- Although the generic comparison chooses a higher source level, its positive-power
specialization is the native quotient map at the same level. -/
@[simp]
theorem eval_powAlgEquiv (e : ℕ) (he : 0 < e) (n : ℕ)
    (x : AdicCompletion (I ^ e) R) :
    evalₐ I n (powAlgEquiv I e he x) =
      Ideal.Quotient.factor
        (Ideal.pow_right_mono (Ideal.pow_le_self he.ne' : I ^ e ≤ I) n)
        (evalₐ (I ^ e) n x) := by
  rw [powAlgEquiv, evalₐ_compareAlgEquiv]
  rw [← factor_evalₐ (I ^ e) (Nat.le_mul_of_pos_left n (by decide : 0 < 1 + 1)) x]
  simp only [Ideal.Quotient.factor_comp_apply]

/-- The positive-power comparison has the exact native forward completion map. -/
theorem powAlgEquiv_apply (e : ℕ) (he : 0 < e) (x : AdicCompletion (I ^ e) R)
    (hmap : (I ^ e).map (RingHom.id R) ≤ I) :
    powAlgEquiv I e he x = adicCompletionMap (RingHom.id R) (I ^ e) I hmap x := by
  apply ext_evalₐ
  intro n
  rw [eval_powAlgEquiv, adicCompletionMap_evalₐ]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ (I ^ e) n x)
  rw [← hr]
  rfl

theorem powAlgEquiv_algebraMap (e : ℕ) (he : 0 < e) (r : R) :
    powAlgEquiv I e he (algebraMap R (AdicCompletion (I ^ e) R) r) =
      algebraMap R (AdicCompletion I R) r :=
  (powAlgEquiv I e he).commutes r

end Powers

section Localization

variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsMaximal]
  (S : Type w) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p] [IsLocalRing S]

/-- Completing at a maximal ideal agrees with completing its actual localization. The
equivalence is bundled from the native completion map of the original localization map. -/
@[colib_tag "COL-0186"]
def localizationAlgEquiv :
    AdicCompletion p R ≃ₐ[R] AdicCompletion (maximalIdeal S) S := by
  let hmap := IsLocalization.AtPrime.map_eq_maximalIdeal p S
  let f := adicCompletionMap (algebraMap R S) p (maximalIdeal S) hmap.le
  have hf : Function.Bijective f :=
    Stacks.AdicCompletion.adicCompletionMap_bijective_of_map_eq _ _ _ hmap
      (Stacks.AdicCompletion.bijective_adicCompletionMap_localization_atPrime p S)
  refine AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective f hf) ?_
  intro r
  change f (algebraMap R (AdicCompletion p R) r) =
    algebraMap R (AdicCompletion (maximalIdeal S) S) r
  rw [IsScalarTower.algebraMap_apply R S (AdicCompletion (maximalIdeal S) S)]
  exact DFunLike.congr_fun
    (adicCompletionMap_comp_algebraMap (algebraMap R S) p (maximalIdeal S) hmap.le) r

/-- The bundled localization equivalence uses the specified native completion map. -/
theorem localizationAlgEquiv_apply (x : AdicCompletion p R)
    (hmap : p.map (algebraMap R S) ≤ maximalIdeal S) :
    localizationAlgEquiv p S x =
      adicCompletionMap (algebraMap R S) p (maximalIdeal S) hmap x := rfl

/-- Localization on completions evaluates through Mathlib's native quotient equivalence. -/
@[simp]
theorem eval_localizationAlgEquiv (n : ℕ) (x : AdicCompletion p R) :
    evalₐ (maximalIdeal S) n (localizationAlgEquiv p S x) =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n (evalₐ p n x) := by
  rw [localizationAlgEquiv_apply p S x
    (IsLocalization.AtPrime.map_eq_maximalIdeal p S).le, adicCompletionMap_evalₐ]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ p n x)
  rw [← hr]
  rfl

theorem localizationAlgEquiv_algebraMap (r : R) :
    localizationAlgEquiv p S (algebraMap R (AdicCompletion p R) r) =
      algebraMap S (AdicCompletion (maximalIdeal S) S) (algebraMap R S r) :=
  (localizationAlgEquiv p S).commutes r

end Localization

end AdicCompletion
