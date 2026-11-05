/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Colib.Util.References
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Regular
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.Multiplication

/-!
# Principal Euler associativity from Stacks 02QF

The existing Stacks multiplication formula supplies the weighted sum over nonclosed
support points. At those points the scalar avoids the prime, so the order of vanishing
is the principal Euler integer of the prime quotient. Extending this Euler sum to all
minimal support points is valid because the residue field at the closed point has
Euler integer zero.

This last step matters in dimension zero. Minimal support points and nonclosed support
points need not be the same set: the first can contain the closed point and the second
is empty. We do not extend the order-of-vanishing sum to that extra point. For the
residue field and a scalar in the maximal ideal, its Euler integer is zero whereas
the order of its zero image is one.

The final Euler formula assumes a finite module over a Noetherian local ring, a scalar
in the maximal ideal, and finite scalar cokernel length. The pure cokernel-length
formula additionally assumes scalar regularity. No Cohen--Macaulay or equidimensional
assumption is added. The zero module and zero-dimensional modules are included.

## Source provenance

This adapts the endpoint scope of
`Aglib/RingTheory/Multiplicity/PrincipalEuler/Associativity.lean`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`a50cb34591c0466aa7449f0a6c90ef14e2d50feafdd7f575fc93ff1644e30456`.
That file credits `R5Lab.RingTheory.LocalLength.PrincipalEulerAssociativity`, revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`bf1fac16ef81cd1e488dd55b90c1a3ebb8edcd9faa70f6691fe1b5843db48f74`.

The proof directly reuses
`AlgebraicGeometry.periodicLength_mul_eq_finsum_support` (Stacks 02QF) at pinned Stacks
revision `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`. There is no additional filtration
or localization model. The finite sums use intrinsic minimal points of the existing
support, and their weights use the native `LocalizedModule`.

This is a local algebraic associativity theorem, not a motivic comparison theorem.
-/

@[expose] public noncomputable section

open scoped BigOperators

universe u v

namespace Module

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

private theorem supportDim_nonpos_of_finite_length [IsLocalRing A] [Module.Finite A M]
    (hM : Module.length A M ≠ ⊤) : Module.supportDim A M ≤ 0 := by
  cases subsingleton_or_nontrivial M with
  | inl h =>
    let := h
    rw [Module.supportDim_eq_bot_of_subsingleton]
    exact bot_le
  | inr h =>
    let := h
    rw [Module.supportDim, support_of_isFiniteLength (Module.length_ne_top_iff.mp hM)]
    exact Order.krullDim_nonpos_of_subsingleton

/-- A finite scalar cokernel, with the scalar in the local maximal ideal, forces
the support of the original module to have dimension at most one. -/
theorem supportDim_le_one_of_finite_cokernel [IsNoetherianRing A] [IsLocalRing A]
    [Module.Finite A M] (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    Module.supportDim A M ≤ 1 := by
  have hQ : Module.length A (QuotSMulTop t M) ≠ ⊤ := by
    rw [AlgebraicGeometry.range_lsmul_eq_smul_top (M := M) t] at hM
    exact hM
  have hdQ := supportDim_nonpos_of_finite_length hQ
  have h := (Module.supportDim_le_supportDim_quotSMulTop_succ (M := M) ht).trans
    (add_le_add hdQ (le_refl 1))
  simpa only [zero_add] using h

private theorem regular_primeQuotient (t : A) (q : PrimeSpectrum A)
    (ht : t ∉ q.asIdeal) : IsSMulRegular (A ⧸ q.asIdeal) t := by
  intro x y hxy
  have ht0 : Ideal.Quotient.mk q.asIdeal t ≠ 0 :=
    Ideal.Quotient.eq_zero_iff_mem.not.mpr ht
  exact mul_left_cancel₀ ht0 hxy

/-- For a prime not containing the scalar, the principal Euler integer of its
prime quotient is the integer-valued order of vanishing. -/
theorem principalEuler_primeQuotient_eq_ord (t : A) (q : PrimeSpectrum A)
    (ht : t ∉ q.asIdeal) :
    principalEuler (N := A ⧸ q.asIdeal) t =
      ((Ring.ord (A ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal t)).toNat : ℤ) := by
  calc
    _ = ((Module.length A (QuotSMulTop t (A ⧸ q.asIdeal))).toNat : ℤ) :=
      AlgebraicGeometry.periodicLength_mul_eq_length_quotSMulTop t
        (regular_primeQuotient t q ht)
    _ = _ := by
      rw [(AlgebraicGeometry.quotSMulTopQuotientEquiv t q.asIdeal).length_eq,
        ← AlgebraicGeometry.ord_quotient_eq_length t q.asIdeal]

/-- The closed point contributes zero to the Euler-weighted formula, including
when it is itself a minimal point of a zero-dimensional support. -/
theorem principalEuler_quotient_closedPoint_eq_zero [IsLocalRing A] (t : A) :
    principalEuler (N := A ⧸ (IsLocalRing.closedPoint A).asIdeal) t = 0 := by
  let : (IsLocalRing.closedPoint A).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  let : IsSimpleModule A (A ⧸ (IsLocalRing.closedPoint A).asIdeal) :=
    isSimpleModule_iff_quot_maximal.mpr
      ⟨(IsLocalRing.closedPoint A).asIdeal, inferInstance, ⟨LinearEquiv.refl A _⟩⟩
  exact principalEuler_zero_of_finite_length t (by simp)

/-- Stacks 02QF expressed using the canonical principal Euler abbreviation.
The order-of-vanishing sum is over nonclosed support points, not all minimal points. -/
@[stacks 02QF "native principal Euler formulation"]
theorem principalEuler_eq_finsum_nonclosed_support [IsNoetherianRing A] [IsLocalRing A]
    [Module.Finite A M] (t : A) (hd : Module.supportDim A M ≤ 1)
    (hdQ : Module.supportDim A (QuotSMulTop t M) ≤ 0) :
    principalEuler (N := M) t =
      ∑ᶠ q ∈ {q : PrimeSpectrum A |
          q ∈ Module.support A M ∧ q ≠ IsLocalRing.closedPoint A},
        ((Ring.ord (A ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal t)).toNat : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) :=
  AlgebraicGeometry.periodicLength_mul_eq_finsum_support t hd hdQ

/-- Euler associativity over the intrinsic minimal support points. A possible
closed minimal point is included with its zero Euler contribution. The dimension
bound is at most one, not an equality, so this also covers dimension zero. -/
@[colib_tag "COL-0173"]
theorem principalEuler_associativity_of_supportDim [IsNoetherianRing A] [IsLocalRing A]
    [Module.Finite A M] (t : A) (hd : Module.supportDim A M ≤ 1)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    principalEuler (N := M) t =
      ∑ᶠ q ∈ {q : PrimeSpectrum A | Minimal (· ∈ Module.support A M) q},
        ((Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) *
            principalEuler (N := A ⧸ q.asIdeal) t := by
  classical
  have hQ : Module.length A (QuotSMulTop t M) ≠ ⊤ := by
    rw [AlgebraicGeometry.range_lsmul_eq_smul_top (M := M) t] at hM
    exact hM
  have hdQ := supportDim_nonpos_of_finite_length hQ
  have hn := AlgebraicGeometry.finite_nonclosed_support hd
  have hm := AlgebraicGeometry.finite_minimal_support (R := A) (M := M)
  calc
    _ = ∑ᶠ q ∈ {q : PrimeSpectrum A |
          q ∈ Module.support A M ∧ q ≠ IsLocalRing.closedPoint A},
        ((Ring.ord (A ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal t)).toNat : ℤ) *
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) :=
      principalEuler_eq_finsum_nonclosed_support t hd hdQ
    _ = ∑ᶠ q ∈ {q : PrimeSpectrum A |
          q ∈ Module.support A M ∧ q ≠ IsLocalRing.closedPoint A},
        ((Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) *
            principalEuler (N := A ⧸ q.asIdeal) t := by
      apply finsum_mem_congr rfl
      intro q hq
      have htq : t ∉ q.asIdeal := by
        intro htq
        have hqx : q ∈ Module.support A (QuotSMulTop t M) := by
          rw [Module.support_quotSMulTop]
          exact ⟨hq.1, Set.singleton_subset_iff.mpr htq⟩
        exact hq.2 (AlgebraicGeometry.eq_closed_of_mem_supportDim_le_zero hdQ q hqx)
      rw [principalEuler_primeQuotient_eq_ord t q htq, mul_comm]
    _ = _ := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hn,
        finsum_mem_eq_finite_toFinset_sum _ hm]
      apply Finset.sum_subset
      · intro q hq
        obtain ⟨hqs, hqn⟩ := hn.mem_toFinset.mp hq
        exact hm.mem_toFinset.mpr
          (AlgebraicGeometry.minimal_of_mem_support_ne_closed hd q hqs hqn)
      · intro q hq hqn
        have heq : q = IsLocalRing.closedPoint A := by
          by_contra hne
          exact hqn (hn.mem_toFinset.mpr ⟨(hm.mem_toFinset.mp hq).1, hne⟩)
        subst q
        rw [principalEuler_quotient_closedPoint_eq_zero, mul_zero]

/-- Principal Euler associativity with the support-dimension condition derived
from finite scalar cokernel length and membership in the local maximal ideal. -/
@[colib_tag "COL-0173",
  stacks 02QF "Euler-weighted minimal-support formulation, including dimension zero"]
theorem principalEuler_associativity [IsNoetherianRing A] [IsLocalRing A]
    [Module.Finite A M] (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    principalEuler (N := M) t =
      ∑ᶠ q ∈ {q : PrimeSpectrum A | Minimal (· ∈ Module.support A M) q},
        ((Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) *
            principalEuler (N := A ⧸ q.asIdeal) t :=
  principalEuler_associativity_of_supportDim t
    (supportDim_le_one_of_finite_cokernel t ht hM) hM

/-- For a scalar regular on the original module, Euler associativity is the
weighted principal-cokernel length formula. Regularity on every contributing
prime quotient follows from minimality, rather than being assumed separately. -/
@[colib_tag "COL-0173"]
theorem principalCokernel_associativity [IsNoetherianRing A] [IsLocalRing A]
    [Module.Finite A M] (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A)
    (hr : IsSMulRegular M t)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    ((Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t))).toNat : ℤ) =
      ∑ᶠ q ∈ {q : PrimeSpectrum A | Minimal (· ∈ Module.support A M) q},
        ((Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) *
            ((Module.length A ((A ⧸ q.asIdeal) ⧸
              LinearMap.range (LinearMap.lsmul A (A ⧸ q.asIdeal) t))).toNat : ℤ) := by
  rw [← principalEuler_of_regular t hr, principalEuler_associativity t ht hM]
  apply finsum_mem_congr rfl
  intro q hq
  have htq : t ∉ q.asIdeal :=
    hr.notMem_of_mem_minimalPrimes ((AlgebraicGeometry.minimal_support_iff q).mp hq)
  rw [principalEuler_of_regular t (regular_primeQuotient t q htq)]

end Module
