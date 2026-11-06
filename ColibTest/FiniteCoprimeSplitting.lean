/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.FiniteCoprimeSplitting
import Colib.FieldTheory.Polynomial.CoprimeDegree
import Mathlib.Algebra.Field.ZMod

/-!
# Simultaneous splitting and preservation of prime-degree irreducibility

One actual intermediate field of the literal product splitting field splits
the supplied finite family and preserves every monic irreducible polynomial
of the specified prime degree. The field is chosen before those polynomials.
The boundary tests retain repeated factors, empty families, positive
characteristic, and characteristic zero.
-/

noncomputable section

namespace ColibTest.FiniteCoprimeSplitting

open Polynomial IntermediateField

universe u

variable {k : Type u} [Field k]

/-- One chosen finite separable prime-to-`n` field splits the supplied small
polynomial family and preserves every literal prime-degree irreducible image.
The existential field precedes the universal polynomial quantifier. -/
theorem one_field_preserves_all_prime_degree_polynomials [PerfectField k]
    (n : ℕ) [Fact n.Prime] (s : Finset k[X])
    (hne : ∀ q ∈ s, q ≠ 0) (hsmall : ∀ q ∈ s, q.natDegree < n) :
    ∃ S : IntermediateField k (∏ q ∈ s, q).SplittingField,
      FiniteDimensional k S ∧ Algebra.IsSeparable k S ∧
      n.Coprime (Module.finrank k S) ∧
      (∀ q ∈ s, (q.map (algebraMap k S)).Splits) ∧
      ∀ (r : k[X]), r.Monic → Irreducible r → r.natDegree = n →
        Irreducible (r.map (algebraMap k S)) ∧ (r.map (algebraMap k S)).natDegree = n := by
  obtain ⟨S, hfinite, hcop, hsplit⟩ :=
    exists_coprime_splitting_field_of_finset n s hne hsmall
  let : FiniteDimensional k S := hfinite
  refine ⟨S, hfinite, inferInstance, hcop, hsplit, ?_⟩
  intro r hr hirr hdegree
  have hcopr : r.natDegree.Coprime (Module.finrank k S) := by
    simpa only [hdegree] using hcop
  refine ⟨hr.irreducible_map_of_natDegree_coprime hirr hcopr, ?_⟩
  simpa only [Polynomial.natDegree_map] using hdegree

/-- The complete chain applies to a specified polynomial without replacing
its coefficient image by a factor or changing the chosen splitting field. -/
theorem splitting_and_irreducibility_in_same_field [PerfectField k]
    (n : ℕ) [Fact n.Prime] (s : Finset k[X])
    (hne : ∀ q ∈ s, q ≠ 0) (hsmall : ∀ q ∈ s, q.natDegree < n)
    (r : k[X]) (hr : r.Monic) (hirr : Irreducible r) (hdegree : r.natDegree = n) :
    ∃ S : IntermediateField k (∏ q ∈ s, q).SplittingField,
      FiniteDimensional k S ∧ Algebra.IsSeparable k S ∧
      n.Coprime (Module.finrank k S) ∧
      (∀ q ∈ s, (q.map (algebraMap k S)).Splits) ∧
      Irreducible (r.map (algebraMap k S)) ∧ (r.map (algebraMap k S)).natDegree = n := by
  obtain ⟨S, hfinite, hseparable, hcop, hsplit, hpreserve⟩ :=
    one_field_preserves_all_prime_degree_polynomials n s hne hsmall
  exact ⟨S, hfinite, hseparable, hcop, hsplit, hpreserve r hr hirr hdegree⟩

/-- Repeated factors are allowed: the supplied polynomial itself need not
be separable. The exponent may also be zero. -/
theorem repeated_linear_factor [PerfectField k] (p d : ℕ) [Fact p.Prime]
    (a : k) (hd : d < p) :
    ∃ S : IntermediateField k (∏ q ∈ ({(X - C a) ^ d} : Finset k[X]), q).SplittingField,
      FiniteDimensional k S ∧ p.Coprime (Module.finrank k S) ∧
      (((X - C a) ^ d).map (algebraMap k S)).Splits := by
  classical
  obtain ⟨S, hfd, hcop, hsplit⟩ := exists_coprime_splitting_field_of_finset p
    ({(X - C a) ^ d} : Finset k[X])
    (by simpa only [Finset.mem_singleton, forall_eq] using pow_ne_zero d (X_sub_C_ne_zero a))
    (by simpa only [Finset.mem_singleton, forall_eq, natDegree_pow,
      natDegree_X_sub_C, Nat.mul_one] using hd)
  exact ⟨S, hfd, hcop, hsplit _ (Finset.mem_singleton_self _)⟩

/-- The empty finite family is allowed, with literal product one. -/
theorem empty_witnesses [PerfectField k] (p : ℕ) [Fact p.Prime] :
    ∃ S : IntermediateField k (∏ q ∈ (∅ : Finset k[X]), q).SplittingField,
      FiniteDimensional k S ∧ p.Coprime (Module.finrank k S) := by
  obtain ⟨S, hfd, hcop, _⟩ := exists_coprime_splitting_field_of_finset (k := k) p ∅
    (by simp) (by simp)
  exact ⟨S, hfd, hcop⟩

/-- Positive characteristic is included: over the perfect field with two
elements, every supplied nonzero polynomial of degree below three splits. -/
theorem characteristic_two (s : Finset (ZMod 2)[X]) (hne : ∀ q ∈ s, q ≠ 0)
    (hsmall : ∀ q ∈ s, q.natDegree < 3) :
    ∃ S : IntermediateField (ZMod 2) (∏ q ∈ s, q).SplittingField,
      FiniteDimensional (ZMod 2) S ∧ (3 : ℕ).Coprime (Module.finrank (ZMod 2) S) ∧
      ∀ q ∈ s, (q.map (algebraMap (ZMod 2) S)).Splits :=
  exists_coprime_splitting_field_of_finset 3 s hne hsmall

/-- Characteristic zero is one way to obtain the producer's perfectness
premise; it is not a requirement of the generic construction. -/
theorem characteristic_zero [CharZero k] (p : ℕ) [Fact p.Prime]
    (s : Finset k[X]) (hne : ∀ q ∈ s, q ≠ 0) (hsmall : ∀ q ∈ s, q.natDegree < p) :
    ∃ S : IntermediateField k (∏ q ∈ s, q).SplittingField,
      FiniteDimensional k S ∧ p.Coprime (Module.finrank k S) ∧
      ∀ q ∈ s, (q.map (algebraMap k S)).Splits :=
  exists_coprime_splitting_field_of_finset p s hne hsmall

end ColibTest.FiniteCoprimeSplitting
