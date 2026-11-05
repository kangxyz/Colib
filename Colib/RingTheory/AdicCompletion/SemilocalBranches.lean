/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.ChineseRemainder
public import Colib.Util.References
public import StacksFrontier.RingTheory.Rig.AdicCompletionMap

/-
Additional retained implementation credits:
Copyright (c) 2026 Colib contributors. All rights reserved.
-/

/-!
# Actual local branches of a factored ideal completion

An ideal factored into positive powers of pairwise comaximal maximal ideals has completion
equal to the product of the completions of its original local rings. Chinese remainder is
applied first to the powered ideals. Each power is then removed by the public cofinal
comparison, followed by the native localization map. The composite agrees with the native
completion map in every branch and at every quotient level.

Implementation provenance: adapted from `Aglib/RingTheory/AdicCompletion/SemilocalBranches.lean`
at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f` (Apache-2.0, kangxyz). Completion maps,
bijectivity and functoriality are supplied by Stacks revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open Function IsLocalRing
open scoped BigOperators

universe u v w

variable {R : Type u} {ι : Type v} [CommRing R] [Fintype ι]
  (J : ι → Ideal R) [∀ i, (J i).IsMaximal]
  (hJ : Pairwise (IsCoprime on J)) (e : ι → ℕ) (he : ∀ i, 0 < e i)
  (S : ι → Type w) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
  [∀ i, IsLocalization.AtPrime (S i) (J i)] [∀ i, IsLocalRing (S i)]

/-- The completion splits over all the actual maximal localizations in the factorization.
Positive exponents are retained until the cofinal comparison on each branch. -/
@[colib_tag "COL-0187",
  colib_ref "aglib_principal_euler_pin" "RingTheory/AdicCompletion/SemilocalBranches.lean"
    "adaptation" "Canonical maps and actual completions; native lower interfaces"]
def semilocalBranchesAlgEquiv (I : Ideal R) (hI : I = ∏ i, J i ^ e i) :
    AdicCompletion I R ≃ₐ[R] ∀ i, AdicCompletion (maximalIdeal (S i)) (S i) := by
  subst I
  exact (prodCompletionAlgEquiv (fun i => J i ^ e i)
    (fun i j hij => (hJ hij).pow)).trans
      (AlgEquiv.piCongrRight fun i =>
        (powAlgEquiv (J i) (e i) (he i)).trans (localizationAlgEquiv (J i) (S i)))

/-- Each branch of the decomposition is the native completion map of the original
localization. The inclusion proof is an argument so downstream users can supply their own
ideal-containment proof without depending on the construction of the equivalence. -/
theorem semilocalBranchesAlgEquiv_apply (I : Ideal R) (hI : I = ∏ i, J i ^ e i)
    (x : AdicCompletion I R) (i : ι)
    (hmap : I.map (algebraMap R (S i)) ≤ maximalIdeal (S i)) :
    semilocalBranchesAlgEquiv J hJ e he S I hI x i =
      adicCompletionMap (algebraMap R (S i)) I (maximalIdeal (S i)) hmap x := by
  subst I
  let K : ι → Ideal R := fun j => J j ^ e j
  have hK : Pairwise (IsCoprime on K) := fun _ _ hij => (hJ hij).pow
  have hprod : (∏ j, K j).map (RingHom.id R) ≤ K i := by
    simpa using prodIdeal_le K hK i
  have hpow : (K i).map (RingHom.id R) ≤ J i := by
    simpa [K] using (Ideal.pow_le_self (he i).ne' : J i ^ e i ≤ J i)
  have hprod' : (∏ j, K j).map (RingHom.id R) ≤ J i := by
    simpa using (prodIdeal_le K hK i).trans
      (Ideal.pow_le_self (he i).ne' : J i ^ e i ≤ J i)
  have hloc : (J i).map (algebraMap R (S i)) ≤ maximalIdeal (S i) :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal (J i) (S i)).le
  change localizationAlgEquiv (J i) (S i)
      (powAlgEquiv (J i) (e i) (he i) (prodCompletionAlgEquiv K hK x i)) = _
  rw [localizationAlgEquiv_apply _ _ _ hloc,
    powAlgEquiv_apply _ _ _ _ hpow, prodCompletionAlgEquiv_apply _ _ _ _ hprod]
  have hp := DFunLike.congr_fun
    (Rig.adicCompletionMap_comp (RingHom.id R) (RingHom.id R)
      (∏ j, K j) (K i) (J i) hprod hpow hprod') x
  have hl := DFunLike.congr_fun
    (Rig.adicCompletionMap_comp (RingHom.id R) (algebraMap R (S i))
      (∏ j, K j) (J i) (maximalIdeal (S i)) hprod' hloc hmap) x
  change adicCompletionMap (algebraMap R (S i)) (J i) (maximalIdeal (S i)) hloc
      (adicCompletionMap (RingHom.id R) (K i) (J i) hpow
        (adicCompletionMap (RingHom.id R) (∏ j, K j) (K i) hprod x)) = _
  calc
    _ = adicCompletionMap (algebraMap R (S i)) (J i) (maximalIdeal (S i)) hloc
        (adicCompletionMap (RingHom.id R) (∏ j, K j) (J i) hprod' x) :=
      congrArg (adicCompletionMap (algebraMap R (S i)) (J i)
        (maximalIdeal (S i)) hloc) hp
    _ = adicCompletionMap (algebraMap R (S i)) (∏ j, K j)
        (maximalIdeal (S i)) hmap x := hl

/-- Every quotient level of every branch is induced by the original localization map. -/
@[colib_tag "COL-0187"]
theorem eval_semilocalBranchesAlgEquiv (I : Ideal R) (hI : I = ∏ i, J i ^ e i)
    (x : AdicCompletion I R) (i : ι)
    (hmap : I.map (algebraMap R (S i)) ≤ maximalIdeal (S i)) (n : ℕ) :
    evalₐ (maximalIdeal (S i)) n (semilocalBranchesAlgEquiv J hJ e he S I hI x i) =
      Ideal.quotientMap ((maximalIdeal (S i)) ^ n) (algebraMap R (S i))
        (Ideal.map_le_iff_le_comap.mp (by
          rw [Ideal.map_pow]
          exact Ideal.pow_right_mono hmap n)) (evalₐ I n x) := by
  rw [semilocalBranchesAlgEquiv_apply J hJ e he S I hI x i hmap]
  exact adicCompletionMap_evalₐ _ _ _ hmap n x

@[simp]
theorem semilocalBranchesAlgEquiv_algebraMap (I : Ideal R)
    (hI : I = ∏ i, J i ^ e i) (r : R) (i : ι) :
    semilocalBranchesAlgEquiv J hJ e he S I hI (algebraMap R (AdicCompletion I R) r) i =
      algebraMap (S i) (AdicCompletion (maximalIdeal (S i)) (S i))
        (algebraMap R (S i) r) :=
  congrFun ((semilocalBranchesAlgEquiv J hJ e he S I hI).commutes r) i

end AdicCompletion
