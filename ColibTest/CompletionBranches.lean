/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.AdicCompletion.FiniteDedekindBranches
import Mathlib.RingTheory.Ideal.Prod

/-!
# Regressions for actual completion branches and finite-algebra base change

These tests use the native completions, quotient maps, localizations and tensor products.
The base, index and localization universes are independent. The CRT tests allow zero
divisors, an empty index and precision zero. The singleton branch retains exponent two.
Canonical completed-base actions are tested before imposing Noetherianity, finiteness or
a nonzero extended ideal. The finite tensor tests assume neither flatness nor torsion-freeness.
-/

noncomputable section

namespace AdicCompletion

open Function IsLocalRing UniqueFactorizationMonoid
open scoped BigOperators TensorProduct

universe u v w

section ChineseRemainder

variable {R : Type u} {ι : Type v} [CommRing R] [Fintype ι]
  (J : ι → Ideal R) (hJ : Pairwise (IsCoprime on J))

example (n : ℕ) (r : R) (i : ι) :
    quotientProdPowEquiv J hJ n (Ideal.Quotient.mk ((∏ j, J j) ^ n) r) i =
      Ideal.Quotient.mk (J i ^ n) r :=
  quotientProdPowEquiv_mk J hJ n r i

example {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ (∏ i, J i) ^ n) (i : ι) :
    quotientProdPowEquiv J hJ m (Ideal.Quotient.factorPow (∏ j, J j) hmn x) i =
      Ideal.Quotient.factorPow (J i) hmn (quotientProdPowEquiv J hJ n x i) :=
  quotientProdPowEquiv_factorPow J hJ hmn x i

example (x : AdicCompletion (∏ i, J i) R) (i : ι)
    (hmap : (∏ j, J j).map (RingHom.id R) ≤ J i) :
    prodCompletionAlgEquiv J hJ x i =
      adicCompletionMap (RingHom.id R) (∏ j, J j) (J i) hmap x :=
  prodCompletionAlgEquiv_apply J hJ x i hmap

example (r : R) (i : ι) :
    prodCompletionAlgEquiv J hJ (algebraMap R (AdicCompletion (∏ j, J j) R) r) i =
      algebraMap R (AdicCompletion (J i) R) r :=
  prodCompletionAlgEquiv_algebraMap J hJ r i

example (n : ℕ) (x : AdicCompletion (∏ i, J i) R) (i : ι) :
    evalₐ (J i) n (prodCompletionAlgEquiv J hJ x i) =
      quotientProdPowEquiv J hJ n (evalₐ (∏ j, J j) n x) i :=
  eval_prodCompletionAlgEquiv J hJ n x i

example (x : AdicCompletion (∏ i, J i) R) (i : ι) :
    evalₐ (J i) 0 (prodCompletionAlgEquiv J hJ x i) =
      quotientProdPowEquiv J hJ 0 (evalₐ (∏ j, J j) 0 x) i :=
  eval_prodCompletionAlgEquiv J hJ 0 x i

end ChineseRemainder

-- The empty product is the unit ideal; no nonempty-index premise is available.
example (R : Type u) [CommRing R] :
    AdicCompletion (⊤ : Ideal R) R ≃ₐ[R]
      ∀ _ : Fin 0, AdicCompletion (⊤ : Ideal R) R := by
  have hprod : (∏ _ : Fin 0, (⊤ : Ideal R)) = ⊤ := by
    rw [Fin.prod_univ_zero]
    exact Ideal.one_eq_top
  exact hprod ▸ prodCompletionAlgEquiv (fun _ : Fin 0 => (⊤ : Ideal R))
    (by intro i; exact Fin.elim0 i)

-- The two complementary coordinate ideals in the actual non-domain ℤ × ℤ.
example :
    let J : Bool → Ideal (ℤ × ℤ) := fun b =>
      if b then Ideal.prod ⊥ ⊤ else Ideal.prod ⊤ ⊥
    AdicCompletion (∏ i, J i) (ℤ × ℤ) ≃ₐ[ℤ × ℤ]
      ∀ i, AdicCompletion (J i) (ℤ × ℤ) := by
  dsimp only
  apply prodCompletionAlgEquiv
  intro i j hij
  cases i <;> cases j
  · exact (hij rfl).elim
  · apply Ideal.isCoprime_iff_exists.mpr
    exact ⟨(1, 0), by simp, (0, 1), by simp, by ext <;> simp⟩
  · apply Ideal.isCoprime_iff_exists.mpr
    exact ⟨(0, 1), by simp, (1, 0), by simp, by ext <;> simp⟩
  · exact (hij rfl).elim

section PowersAndLocalization

variable {R : Type u} [CommRing R] (I : Ideal R)

example (e : ℕ) (he : 0 < e) (x : AdicCompletion (I ^ e) R)
    (hmap : (I ^ e).map (RingHom.id R) ≤ I) :
    powAlgEquiv I e he x = adicCompletionMap (RingHom.id R) (I ^ e) I hmap x :=
  powAlgEquiv_apply I e he x hmap

example (e : ℕ) (he : 0 < e) (r : R) :
    powAlgEquiv I e he (algebraMap R (AdicCompletion (I ^ e) R) r) =
      algebraMap R (AdicCompletion I R) r :=
  powAlgEquiv_algebraMap I e he r

example (e : ℕ) (he : 0 < e) (x : AdicCompletion (I ^ e) R) :
    evalₐ I 0 (powAlgEquiv I e he x) =
      Ideal.Quotient.factor
        (Ideal.pow_right_mono (Ideal.pow_le_self he.ne' : I ^ e ≤ I) 0)
        (evalₐ (I ^ e) 0 x) :=
  eval_powAlgEquiv I e he 0 x

variable (p : Ideal R) [p.IsMaximal] (S : Type w) [CommRing S] [Algebra R S]
  [IsLocalization.AtPrime S p] [IsLocalRing S]

example (r : R) :
    localizationAlgEquiv p S (algebraMap R (AdicCompletion p R) r) =
      algebraMap S (AdicCompletion (maximalIdeal S) S) (algebraMap R S r) :=
  localizationAlgEquiv_algebraMap p S r

example (n : ℕ) (x : AdicCompletion p R) :
    evalₐ (maximalIdeal S) n (localizationAlgEquiv p S x) =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n (evalₐ p n x) :=
  eval_localizationAlgEquiv p S n x

end PowersAndLocalization

section Semilocal

variable {R : Type u} {ι : Type v} [CommRing R] [Fintype ι]
  (J : ι → Ideal R) [∀ i, (J i).IsMaximal]
  (hJ : Pairwise (IsCoprime on J)) (e : ι → ℕ) (he : ∀ i, 0 < e i)
  (S : ι → Type w) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
  [∀ i, IsLocalization.AtPrime (S i) (J i)] [∀ i, IsLocalRing (S i)]
  (I : Ideal R) (hI : I = ∏ i, J i ^ e i)

example : AdicCompletion I R ≃ₐ[R]
    ∀ i, AdicCompletion (maximalIdeal (S i)) (S i) :=
  semilocalBranchesAlgEquiv J hJ e he S I hI

example (x : AdicCompletion I R) (i : ι)
    (hmap : I.map (algebraMap R (S i)) ≤ maximalIdeal (S i)) :
    semilocalBranchesAlgEquiv J hJ e he S I hI x i =
      adicCompletionMap (algebraMap R (S i)) I (maximalIdeal (S i)) hmap x :=
  semilocalBranchesAlgEquiv_apply J hJ e he S I hI x i hmap

example (r : R) (i : ι) :
    semilocalBranchesAlgEquiv J hJ e he S I hI
        (algebraMap R (AdicCompletion I R) r) i =
      algebraMap (S i) (AdicCompletion (maximalIdeal (S i)) (S i))
        (algebraMap R (S i) r) :=
  semilocalBranchesAlgEquiv_algebraMap J hJ e he S I hI r i

example (x : AdicCompletion I R) (i : ι)
    (hmap : I.map (algebraMap R (S i)) ≤ maximalIdeal (S i)) :
    evalₐ (maximalIdeal (S i)) 0 (semilocalBranchesAlgEquiv J hJ e he S I hI x i) =
      Ideal.quotientMap ((maximalIdeal (S i)) ^ 0) (algebraMap R (S i))
        (Ideal.map_le_iff_le_comap.mp (by
          rw [Ideal.map_pow]
          exact Ideal.pow_right_mono hmap 0)) (evalₐ I 0 x) :=
  eval_semilocalBranchesAlgEquiv J hJ e he S I hI x i hmap 0

end Semilocal

example {R : Type u} [CommRing R] (p : Ideal R) [p.IsMaximal] :
    AdicCompletion (p ^ 2) R ≃ₐ[R]
      ∀ _ : Unit, AdicCompletion (maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) := by
  exact semilocalBranchesAlgEquiv (fun _ : Unit => p)
    (fun _ _ h => (h (Subsingleton.elim _ _)).elim)
    (fun _ => 2) (fun _ => by decide) (fun _ => Localization.AtPrime p) (p ^ 2) (by simp)

section Dedekind

variable {R : Type u} [CommRing R] [IsDedekindDomain R] [DecidableEq (Ideal R)]
  (I : Ideal R) (hI : I ≠ 0)

example : I = ∏ q : IdealBranch I, q.val ^ (normalizedFactors I).count q.val :=
  idealBranch_factorization I hI

example (x : AdicCompletion I R) (q : IdealBranch I) :
    dedekindBranchesAlgEquiv I hI x q =
      adicCompletionMap (algebraMap R (Localization.AtPrime q.val)) I
        (maximalIdeal (Localization.AtPrime q.val)) (idealBranch_map_le_maximalIdeal I q) x :=
  dedekindBranchesAlgEquiv_apply I hI x q

example (r : R) (q : IdealBranch I) :
    dedekindBranchesAlgEquiv I hI (algebraMap R (AdicCompletion I R) r) q =
      algebraMap (Localization.AtPrime q.val)
        (AdicCompletion (maximalIdeal (Localization.AtPrime q.val)) (Localization.AtPrime q.val))
        (algebraMap R (Localization.AtPrime q.val) r) :=
  dedekindBranchesAlgEquiv_algebraMap I hI r q

example (x : AdicCompletion I R) (q : IdealBranch I) :
    evalₐ (maximalIdeal (Localization.AtPrime q.val)) 0
        (dedekindBranchesAlgEquiv I hI x q) =
      Ideal.quotientMap ((maximalIdeal (Localization.AtPrime q.val)) ^ 0)
        (algebraMap R (Localization.AtPrime q.val))
        (Ideal.map_le_iff_le_comap.mp (by
          rw [Ideal.map_pow]
          exact Ideal.pow_right_mono (idealBranch_map_le_maximalIdeal I q) 0))
        (evalₐ I 0 x) :=
  eval_dedekindBranchesAlgEquiv I hI 0 x q

-- The nonzero hypothesis does not accidentally exclude the unit ideal.
example : AdicCompletion (1 : Ideal R) R ≃ₐ[R]
    ∀ q : IdealBranch (1 : Ideal R),
      AdicCompletion (maximalIdeal (Localization.AtPrime q.val)) (Localization.AtPrime q.val) :=
  dedekindBranchesAlgEquiv (1 : Ideal R) one_ne_zero

end Dedekind

section FiniteAlgebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

-- Neither Noetherianity nor module finiteness is needed for these canonical formulas.
example (x : AdicCompletion I R) (s : S) :
    tensorToExtendedCompletionAlgHom I (x ⊗ₜ[R] s) =
      completionMap (B := S) I x *
        algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s :=
  tensorToExtendedCompletionAlgHom_tmul I x s

example (n : ℕ) (x : AdicCompletion I R) (r : R) (s : S)
    (hr : evalₐ I n x = Ideal.Quotient.mk (I ^ n) r) :
    evalₐ (I.map (algebraMap R S)) n
        (tensorToExtendedCompletionAlgHom I (x ⊗ₜ[R] s)) =
      Ideal.Quotient.mk ((I.map (algebraMap R S)) ^ n) (algebraMap R S r * s) :=
  evalₐ_tensorToExtendedCompletionAlgHom_tmul_eq_mk I n x r s hr

example [IsNoetherianRing R] [Module.Finite R S] :
    letI := extendedCompletionAlgebra (S := S) I
    AdicCompletion I R ⊗[R] S ≃ₐ[AdicCompletion I R]
      AdicCompletion (I.map (algebraMap R S)) S :=
  tensorEquivExtendedCompletionBase I

-- Arbitrary quotient algebras are admitted; no flatness or torsion-free premise is supplied.
example [IsNoetherianRing R] (K : Ideal R) :
    AdicCompletion I R ⊗[R] (R ⧸ K) ≃ₐ[R]
      AdicCompletion (I.map (algebraMap R (R ⧸ K))) (R ⧸ K) :=
  tensorEquivExtendedCompletion I

example (x : AdicCompletion I R) :
    letI := extendedCompletionAlgebra (S := S) I
    algebraMap (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R S)) S) x =
      adicCompletionMap (algebraMap R S) I (I.map (algebraMap R S)) le_rfl x := by
  let := extendedCompletionAlgebra (S := S) I
  rw [extendedCompletionAlgebra_algebraMap]
  exact DFunLike.congr_fun (completionMap_toRingHom (S := S) I) x

end FiniteAlgebra

section FiniteDedekindBranches

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [DecidableEq (Ideal S)] (I : Ideal R)

-- These four tests deliberately have no hI, Noetherian-base or finite-algebra assumption.
example (q : IdealBranch (I.map (algebraMap R S))) (x : AdicCompletion I R) :
    localCompletionBaseMap I q x =
      adicCompletionMap (algebraMap R (Localization.AtPrime q.val)) I
        (maximalIdeal (Localization.AtPrime q.val)) (idealBranch_base_map_le_maximalIdeal I q) x :=
  rfl

example (q : IdealBranch (I.map (algebraMap R S))) (x : AdicCompletion I R) :
    letI := localCompletionBaseAlgebra I q
    algebraMap (AdicCompletion I R)
        (AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
          (Localization.AtPrime q.val)) x =
      adicCompletionMap (algebraMap R (Localization.AtPrime q.val)) I
        (maximalIdeal (Localization.AtPrime q.val)) (idealBranch_base_map_le_maximalIdeal I q) x :=
  rfl

example (q : IdealBranch (I.map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra I q
    IsScalarTower R (AdicCompletion I R)
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
        (Localization.AtPrime q.val)) :=
  localCompletionBaseIsScalarTower I q

example (q : IdealBranch (I.map (algebraMap R S))) (x : AdicCompletion I R) :
    evalₐ (maximalIdeal (Localization.AtPrime q.val)) 0 (localCompletionBaseMap I q x) =
      Ideal.quotientMap ((maximalIdeal (Localization.AtPrime q.val)) ^ 0)
        (algebraMap R (Localization.AtPrime q.val))
        (Ideal.map_le_iff_le_comap.mp (by
          rw [Ideal.map_pow]
          exact Ideal.pow_right_mono (idealBranch_base_map_le_maximalIdeal I q) 0))
        (evalₐ I 0 x) :=
  eval_localCompletionBaseMap I q 0 x

variable [IsNoetherianRing R] [Module.Finite R S] (hI : I.map (algebraMap R S) ≠ 0)

example (x : AdicCompletion I R) (s : S) (q : IdealBranch (I.map (algebraMap R S))) :
    tensorEquivLocalCompletions I hI (x ⊗ₜ[R] s) q =
      localCompletionBaseMap I q x *
        algebraMap (Localization.AtPrime q.val)
          (AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
            (Localization.AtPrime q.val)) (algebraMap S (Localization.AtPrime q.val) s) :=
  tensorEquivLocalCompletions_tmul I hI x s q

example :
    letI := fun q => localCompletionBaseAlgebra (S := S) I q
    AdicCompletion I R ⊗[R] S ≃ₐ[AdicCompletion I R]
      ∀ q : IdealBranch (I.map (algebraMap R S)),
        AdicCompletion (maximalIdeal (Localization.AtPrime q.val)) (Localization.AtPrime q.val) :=
  tensorEquivLocalCompletionsBase I hI

example (q : IdealBranch (I.map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra I q
    Module.Finite (AdicCompletion I R)
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
        (Localization.AtPrime q.val)) :=
  localCompletionBaseFinite I hI q

end FiniteDedekindBranches

end AdicCompletion
