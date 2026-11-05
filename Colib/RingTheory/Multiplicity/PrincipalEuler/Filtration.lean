/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.RingTheory.Multiplicity.PrincipalEuler.Additivity
public import Colib.RingTheory.Multiplicity.PrincipalEuler.Support
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import StacksFrontier.RingTheory.Length.Additivity

/-!
# Principal Euler sums and local lengths along native prime filtrations

The filtration is Mathlib's `RelSeries` for
`Submodule.IsQuotientEquivQuotientPrime`. Its actual subquotients are identified with
`A / pᵢ` by the supplied linear equivalences. No additional filtration structure is used.

Two conclusions are kept distinct:

* If the scalar homology of the terms and factors has finite length, principal Euler
  length is the sum of the Euler lengths of all the prime factors. Over a Noetherian
  ring with `M` finite, finite length of `M / tM` supplies those finiteness hypotheses.
* At a minimal point `q` of `Supp M`, the number of occurrences of `q` among the labels
  is the length of `M_q` over `A_q`. This is the pinned Stacks 00L7 theorem, applied to
  the same native filtration. It requires no Noetherian or finite-module hypothesis
  once the finite prime filtration has been supplied.

The second statement counts only minimal labels. The Euler sum still runs over every
step. No vanishing of nonminimal contributions, weighted minimal-prime Euler formula,
principal associativity formula, or motivic comparison is asserted here.

## Source provenance

The Euler filtration argument is adapted from
`Aglib/RingTheory/Multiplicity/PrincipalEuler/Filtration.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. That file credits
`R5Lab.RingTheory.LocalLength.PrincipalEulerFiltration` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`860f378ac24bc0033903038bcae32ff592ede183c1c0378541bfd5a3a092a1f6`.
The local-length conclusion is reused from Stacks 00L7, via
`Module.setOf_minimal_range_eq_setOf_minimal_support_and_ncard_eq_length`, in pinned
Stacks revision `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`.

-/

@[expose] public noncomputable section

namespace Module

universe u v

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]

/-- Euler additivity on two nested submodules, using their actual submodule quotient. -/
theorem principalEuler_add_of_submodule_le (t : A) (U V : Submodule A M) (hUV : U ≤ V)
    (hU : FinitePrincipal U t) (hV : FinitePrincipal V t)
    (hQ : FinitePrincipal (V ⧸ U.submoduleOf V) t) :
    principalEuler (N := V) t = principalEuler (N := U) t +
      principalEuler (N := V ⧸ U.submoduleOf V) t := by
  have hC : FinitePrincipal (U.submoduleOf V) t :=
    (finitePrincipal_congr (Submodule.submoduleOfEquivOfLe hUV) t).mpr hU
  have h := principalEuler_add_of_exact (U.submoduleOf V).subtype (U.submoduleOf V).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _) t hC hV hQ
  simpa only [principalEuler_congr (Submodule.submoduleOfEquivOfLe hUV) t] using h

section GivenFiltration

variable (s : RelSeries {UV : Submodule A M × Submodule A M |
    UV.1.IsQuotientEquivQuotientPrime UV.2})
variable (p : Fin s.length → PrimeSpectrum A)
variable (hquot : ∀ i : Fin s.length,
    Nonempty (((s i.succ) ⧸ (s i.castSucc).submoduleOf (s i.succ)) ≃ₗ[A] A ⧸ (p i).asIdeal))
variable (hhead : s.head = ⊥) (hlast : s.last = ⊤)

include hquot hhead hlast

/-- The principal Euler integer is the sum over the actual prime factors of a native
finite filtration. This statement needs neither a Noetherian ring nor a finite module:
the filtration and the finite scalar-homology hypotheses are supplied explicitly. -/
@[colib_tag "COL-0172"]
theorem principalEuler_eq_sum_of_prime_relSeries (t : A)
    (hF : ∀ i, FinitePrincipal (s i) t)
    (hP : ∀ i, FinitePrincipal (A ⧸ (p i).asIdeal) t) :
    principalEuler (N := M) t =
      ∑ i : Fin s.length, principalEuler (N := A ⧸ (p i).asIdeal) t := by
  classical
  have hzero : principalEuler (N := s 0) t = 0 := by
    change principalEuler (N := s.head) t = 0
    rw [hhead]
    apply principalEuler_zero_of_finite_length
    simp only [Module.length_eq_zero, ne_eq, ENat.zero_ne_top, not_false_eq_true]
  have hstep : ∀ i : Fin s.length,
      principalEuler (N := s i.succ) t = principalEuler (N := s i.castSucc) t +
        principalEuler (N := A ⧸ (p i).asIdeal) t := by
    intro i
    have hQ := (finitePrincipal_congr (hquot i).some t).mpr (hP i)
    have h := principalEuler_add_of_submodule_le t _ _ (s.step i).1
      (hF i.castSucc) (hF i.succ) hQ
    simpa only [principalEuler_congr (hquot i).some t] using h
  have hsum : (∑ i : Fin s.length, principalEuler (N := s i.succ) t) =
      (∑ i : Fin s.length, principalEuler (N := s i.castSucc) t) +
        ∑ i : Fin s.length, principalEuler (N := A ⧸ (p i).asIdeal) t := by
    calc
      _ = ∑ i : Fin s.length, (principalEuler (N := s i.castSucc) t +
          principalEuler (N := A ⧸ (p i).asIdeal) t) :=
        Finset.sum_congr rfl fun i _ => hstep i
      _ = _ := Finset.sum_add_distrib
  have htel := (Fin.sum_univ_succ
    (fun i : Fin (s.length + 1) => principalEuler (N := s i) t)).symm.trans
      (Fin.sum_univ_castSucc (fun i : Fin (s.length + 1) => principalEuler (N := s i) t))
  rw [hzero, zero_add, hsum] at htel
  have hend : principalEuler (N := s (Fin.last s.length)) t = principalEuler (N := M) t := by
    change principalEuler (N := s.last) t = _
    rw [hlast]
    exact principalEuler_congr (Submodule.topEquiv (R := A) (M := M)) t
  exact hend.symm.trans (add_left_cancel htel).symm

/-- Finite length of `M / tM` supplies all term and factor finiteness assumptions in the
Euler filtration sum over a Noetherian ring. -/
theorem principalEuler_eq_sum_of_prime_relSeries_of_finite_cokernel
    [IsNoetherianRing A] [Module.Finite A M] (t : A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    principalEuler (N := M) t =
      ∑ i : Fin s.length, principalEuler (N := A ⧸ (p i).asIdeal) t := by
  classical
  apply principalEuler_eq_sum_of_prime_relSeries s p hquot hhead hlast t
  · exact fun i => finitePrincipal_submodule_of_finite_cokernel t hM (s i)
  · intro i
    exact (finitePrincipal_congr (hquot i).some t).mp
      (finitePrincipal_subquotient_of_finite_cokernel t hM (s i.castSucc) (s i.succ))

/-- Stacks 00L7 on the native filtration: minimal prime labels are exactly the minimal
points of the support. -/
@[stacks 00L7 "native RelSeries specialization: minimal support points"]
theorem minimal_range_eq_minimal_support_of_prime_relSeries :
    {q | Minimal (· ∈ Set.range p) q} = {q | Minimal (· ∈ support A M) q} :=
  (Module.setOf_minimal_range_eq_setOf_minimal_support_and_ncard_eq_length
    s.toFun p (fun i => (s.step i).1) hquot hhead hlast).1

/-- Stacks 00L7 on the same native filtration: a minimal support point occurs as many
times as the length of the module localized at that point, over the localized ring. -/
@[colib_tag "COL-0172", stacks 00L7 "native RelSeries specialization: localized multiplicity"]
theorem ncard_eq_length_localizedModule_of_prime_relSeries (q : PrimeSpectrum A)
    (hq : Minimal (· ∈ support A M) q) :
    ({i | p i = q}.ncard : ℕ∞) =
      Module.length (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl M) :=
  (Module.setOf_minimal_range_eq_setOf_minimal_support_and_ncard_eq_length
    s.toFun p (fun i => (s.step i).1) hquot hhead hlast).2 q hq

/-- The occurrence count in a finite prime filtration proves that the local length at a
minimal support point is finite, without an additional Noetherian hypothesis. -/
theorem length_localizedModule_ne_top_of_prime_relSeries (q : PrimeSpectrum A)
    (hq : Minimal (· ∈ support A M) q) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) ≠ ⊤ := by
  rw [← ncard_eq_length_localizedModule_of_prime_relSeries s p hquot hhead hlast q hq]
  exact ENat.natCast_ne_top _

/-- The natural-number local length is the occurrence count at a minimal support point. -/
theorem length_localizedModule_toNat_eq_ncard_of_prime_relSeries (q : PrimeSpectrum A)
    (hq : Minimal (· ∈ support A M) q) :
    (Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M)).toNat = {i | p i = q}.ncard := by
  simpa only [ENat.toNat_natCast] using congrArg ENat.toNat
    (ncard_eq_length_localizedModule_of_prime_relSeries s p hquot hhead hlast q hq).symm

end GivenFiltration

/-- A Noetherian finite module with finite scalar cokernel admits a native prime filtration
that simultaneously computes the Euler sum and the local multiplicities of minimal support
points. The prime labels and quotient equivalences come from the same filtration. -/
@[colib_tag "COL-0172"]
theorem exists_prime_relSeries_principalEuler_sum_and_localLength
    [IsNoetherianRing A] [Module.Finite A M] (t : A)
    (hM : Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M t)) ≠ ⊤) :
    ∃ (s : RelSeries {UV : Submodule A M × Submodule A M |
        UV.1.IsQuotientEquivQuotientPrime UV.2}) (p : Fin s.length → PrimeSpectrum A),
      s.head = ⊥ ∧ s.last = ⊤ ∧
      (∀ i : Fin s.length,
        Nonempty (((s i.succ) ⧸ (s i.castSucc).submoduleOf (s i.succ)) ≃ₗ[A]
          A ⧸ (p i).asIdeal)) ∧
      principalEuler (N := M) t =
        (∑ i : Fin s.length, principalEuler (N := A ⧸ (p i).asIdeal) t) ∧
      {q | Minimal (· ∈ Set.range p) q} = {q | Minimal (· ∈ support A M) q} ∧
      ∀ q : PrimeSpectrum A, Minimal (· ∈ support A M) q →
        ({i | p i = q}.ncard : ℕ∞) = Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M) := by
  classical
  obtain ⟨s, hhead, hlast⟩ :=
    IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime A M
  choose p hquot using fun i : Fin s.length => (s.step i).2
  refine ⟨s, p, hhead, hlast, hquot, ?_, ?_, ?_⟩
  · exact principalEuler_eq_sum_of_prime_relSeries_of_finite_cokernel
      s p hquot hhead hlast t hM
  · exact minimal_range_eq_minimal_support_of_prime_relSeries s p hquot hhead hlast
  · exact ncard_eq_length_localizedModule_of_prime_relSeries s p hquot hhead hlast

end Module
