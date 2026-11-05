/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Multiplicity.PrincipalEuler.Filtration
import Colib.RingTheory.Multiplicity.PrincipalEuler.Associativity
import Mathlib.RingTheory.KrullDimension.Field

open scoped BigOperators

universe u v w z

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]

-- The scalar invariant is the existing periodic complex, with independent ring and module
-- universes. No alternate homology or quotient model is introduced at the public boundary.
example (t : A) :
    Module.principalEuler (N := M) t =
      AlgebraicGeometry.periodicLength
        (AlgebraicGeometry.twoPeriodicComplex (0 : Module.End A M)
          (LinearMap.lsmul A M t) (zero_mul _) (mul_zero _)) := rfl

example (t : A) :
    Module.principalEuler (N := M) t =
      ((Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t))).toNat : ℤ) -
        ((Module.length A (LinearMap.ker (LinearMap.lsmul A M t))).toNat : ℤ) :=
  Module.principalEuler_eq_length_quotient_sub_length_ker t

-- Finite-length cancellation does not assume a Noetherian or local ring, or regularity.
example (t : A) (hM : Module.length A M ≠ ⊤) :
    Module.principalEuler (N := M) t = 0 :=
  Module.principalEuler_zero_of_finite_length t hM

example (t : A) : Module.principalEuler (N := (⊥ : Submodule A M)) t = 0 :=
  Module.principalEuler_zero_of_finite_length t (by simp)

-- The regular endpoint does not silently add a finite-cokernel assumption.
example (t : A) (ht : IsSMulRegular M t) :
    Module.principalEuler (N := M) t =
      ((Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t))).toNat : ℤ) :=
  Module.principalEuler_of_regular t ht

example (t : A) :
    Module.FinitePrincipal M t ↔
      IsFiniteLength A (LinearMap.ker (LinearMap.lsmul A M t)) ∧
        IsFiniteLength A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) :=
  Module.finitePrincipal_iff_isFiniteLength t

example (t : A) (ht : IsSMulRegular M t)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    Module.FinitePrincipal M t :=
  Module.finitePrincipal_of_regular M t ht hM

section ExactSequence

variable {P : Type z} [AddCommGroup P] [Module A P]

-- The three carriers occupy v, w, and z, independently of the ring universe u.
-- Only the outer homology modules are assumed finite.
example (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (t : A)
    (hM : Module.FinitePrincipal M t) (hP : Module.FinitePrincipal P t) :
    Module.FinitePrincipal N t ∧
      Module.principalEuler (N := N) t =
        Module.principalEuler (N := M) t + Module.principalEuler (N := P) t :=
  Module.finitePrincipal_and_principalEuler_add_of_exact f g hf hg hex t hM hP

example (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (t : A)
    (hM : Module.FinitePrincipal M t) (hN : Module.FinitePrincipal N t)
    (hP : Module.FinitePrincipal P t) :
    Module.principalEuler (N := N) t =
      Module.principalEuler (N := M) t + Module.principalEuler (N := P) t :=
  Module.principalEuler_add_of_exact f g hf hg hex t hM hN hP

-- Equivalence transport also permits different carrier universes.
example (e : M ≃ₗ[A] N) (t : A) :
    Module.principalEuler (N := M) t = Module.principalEuler (N := N) t ∧
      (Module.FinitePrincipal M t ↔ Module.FinitePrincipal N t) :=
  ⟨Module.principalEuler_congr e t, Module.finitePrincipal_congr e t⟩

end ExactSequence

-- Kernel support needs no finite-generation hypothesis.
example (t : A) :
    Module.support A (LinearMap.ker (LinearMap.lsmul A M t)) ⊆
      Module.support A M ∩ PrimeSpectrum.zeroLocus ({t} : Set A) :=
  Module.support_ker_lsmul_subset t

example [Module.Finite A M] (t : A) :
    Module.support A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) =
      Module.support A M ∩ PrimeSpectrum.zeroLocus ({t} : Set A) :=
  Module.support_quotient_range_lsmul t

-- The support route needs Noetherianity and finite modules, but neither locality nor
-- scalar regularity. The contained-support module may occupy a different universe.
example [IsNoetherianRing A] [Module.Finite A M] [Module.Finite A N] (t : A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤)
    (hs : Module.support A N ⊆ Module.support A M) :
    Module.FinitePrincipal N t :=
  Module.finitePrincipal_of_support_subset t hM hs

-- Actual subquotients work without an additional U ≤ V hypothesis.
example [IsNoetherianRing A] [Module.Finite A M] (t : A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤)
    (U V : Submodule A M) : Module.FinitePrincipal (V ⧸ U.submoduleOf V) t :=
  Module.finitePrincipal_subquotient_of_finite_cokernel t hM U V

example [IsNoetherianRing A] [Module.Finite A M] (t : A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤)
    (U V : Submodule A M) (hUV : U ≤ V) :
    Module.principalEuler (N := V) t = Module.principalEuler (N := U) t +
      Module.principalEuler (N := V ⧸ U.submoduleOf V) t :=
  Module.principalEuler_add_of_submodule_le t U V hUV
    (Module.finitePrincipal_submodule_of_finite_cokernel t hM U)
    (Module.finitePrincipal_submodule_of_finite_cokernel t hM V)
    (Module.finitePrincipal_subquotient_of_finite_cokernel t hM U V)

section PrimeFiltration

variable (s : RelSeries {UV : Submodule A M × Submodule A M |
    UV.1.IsQuotientEquivQuotientPrime UV.2})
variable (p : Fin s.length → PrimeSpectrum A)
variable (hquot : ∀ i : Fin s.length,
    Nonempty (((s i.succ) ⧸ (s i.castSucc).submoduleOf (s i.succ)) ≃ₗ[A]
      A ⧸ (p i).asIdeal))
variable (hhead : s.head = ⊥) (hlast : s.last = ⊤)

include hquot hhead hlast

-- Native RelSeries data and actual subquotients are accepted directly.
example (t : A) (hF : ∀ i, Module.FinitePrincipal (s i) t)
    (hP : ∀ i, Module.FinitePrincipal (A ⧸ (p i).asIdeal) t) :
    Module.principalEuler (N := M) t =
      ∑ i : Fin s.length, Module.principalEuler (N := A ⧸ (p i).asIdeal) t :=
  Module.principalEuler_eq_sum_of_prime_relSeries s p hquot hhead hlast t hF hP

example [IsNoetherianRing A] [Module.Finite A M] (t : A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    Module.principalEuler (N := M) t =
      ∑ i : Fin s.length, Module.principalEuler (N := A ⧸ (p i).asIdeal) t :=
  Module.principalEuler_eq_sum_of_prime_relSeries_of_finite_cokernel
    s p hquot hhead hlast t hM

-- Once the filtration is supplied, the local multiplicity endpoints do not require
-- a Noetherian ring, finite generation, or a chosen scalar.
example :
    {q | Minimal (· ∈ Set.range p) q} = {q | Minimal (· ∈ Module.support A M) q} :=
  Module.minimal_range_eq_minimal_support_of_prime_relSeries s p hquot hhead hlast

example (q : PrimeSpectrum A) (hq : Minimal (· ∈ Module.support A M) q) :
    ({i | p i = q}.ncard : ℕ∞) =
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) :=
  Module.ncard_eq_length_localizedModule_of_prime_relSeries s p hquot hhead hlast q hq

example (q : PrimeSpectrum A) (hq : Minimal (· ∈ Module.support A M) q) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) ≠ ⊤ ∧
      (Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M)).toNat = {i | p i = q}.ncard :=
  ⟨Module.length_localizedModule_ne_top_of_prime_relSeries s p hquot hhead hlast q hq,
    Module.length_localizedModule_toNat_eq_ncard_of_prime_relSeries
      s p hquot hhead hlast q hq⟩

end PrimeFiltration

-- The existence theorem returns one filtration whose labels compute both Euler length
-- and the local multiplicities; this client retains that shared witness.
example [IsNoetherianRing A] [Module.Finite A M] (t : A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    ∃ (s : RelSeries {UV : Submodule A M × Submodule A M |
        UV.1.IsQuotientEquivQuotientPrime UV.2}) (p : Fin s.length → PrimeSpectrum A),
      Module.principalEuler (N := M) t =
        (∑ i : Fin s.length, Module.principalEuler (N := A ⧸ (p i).asIdeal) t) ∧
      ∀ q : PrimeSpectrum A, Minimal (· ∈ Module.support A M) q →
        ({i | p i = q}.ncard : ℕ∞) = Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M) := by
  obtain ⟨s, p, _, _, _, heuler, _, hlocal⟩ :=
    Module.exists_prime_relSeries_principalEuler_sum_and_localLength t hM
  exact ⟨s, p, heuler, hlocal⟩

-- The closed residue-field contribution cancels for every scalar, not just regular ones.
example [IsLocalRing A] (t : A) :
    Module.principalEuler (N := A ⧸ (IsLocalRing.closedPoint A).asIdeal) t = 0 :=
  Module.principalEuler_quotient_closedPoint_eq_zero t

-- A field is genuinely zero-dimensional. At its zero scalar Euler length is zero,
-- whereas order of vanishing is one, so the closed contribution cannot use ord instead.
example {K : Type u} [Field K] :
    Module.supportDim K K = 0 ∧ Module.principalEuler (N := K) (0 : K) = 0 ∧
      Ring.ord K 0 = 1 := by
  refine ⟨?_, Module.principalEuler_zero_of_finite_length 0 (by simp), ?_⟩
  · rw [Module.supportDim_self_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  · simp [Ring.ord_zero]

-- Away from the scalar's zero locus, the prime-quotient endpoint agrees with ord.
example (t : A) (q : PrimeSpectrum A) (ht : t ∉ q.asIdeal) :
    Module.principalEuler (N := A ⧸ q.asIdeal) t =
      ((Ring.ord (A ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal t)).toNat : ℤ) :=
  Module.principalEuler_primeQuotient_eq_ord t q ht

section Associativity

variable [IsNoetherianRing A] [IsLocalRing A] [Module.Finite A M]

-- The support-dimension form needs no maximal-ideal membership assumption.
example (t : A) (hd : Module.supportDim A M ≤ 1)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    Module.principalEuler (N := M) t =
      ∑ᶠ q ∈ {q : PrimeSpectrum A | Minimal (· ∈ Module.support A M) q},
        ((Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) *
            Module.principalEuler (N := A ⧸ q.asIdeal) t :=
  Module.principalEuler_associativity_of_supportDim t hd hM

-- The final Euler endpoint derives dimension ≤ 1, including dimension zero; it does
-- not assume regularity, Cohen--Macaulayness, or equidimensionality.
example (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    Module.principalEuler (N := M) t =
      ∑ᶠ q ∈ {q : PrimeSpectrum A | Minimal (· ∈ Module.support A M) q},
        ((Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) *
            Module.principalEuler (N := A ⧸ q.asIdeal) t :=
  Module.principalEuler_associativity t ht hM

-- Only regularity on M is supplied, not a separate family of regularity assumptions
-- on the prime quotients. Coefficients remain lengths over the native localizations.
example (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A) (hr : IsSMulRegular M t)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    ((Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t))).toNat : ℤ) =
      ∑ᶠ q ∈ {q : PrimeSpectrum A | Minimal (· ∈ Module.support A M) q},
        ((Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) *
            ((Module.length A ((A ⧸ q.asIdeal) ⧸
              LinearMap.range (LinearMap.lsmul A (A ⧸ q.asIdeal) t))).toNat : ℤ) :=
  Module.principalCokernel_associativity t ht hr hM

end Associativity
