/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Actual scalar-factor multiplicity in the native local ring

Native `multiplicity` extracts the largest power of a nonunit factor of a nonzero coefficient
image. The remaining polynomial is not divisible by that factor and is therefore a unit in the
existing localization at its principal prime ideal. For a monic irreducible, the exponent is
the count in the actual `normalizedFactors` multiset. No replacement valuation or factor model
is introduced, and no separability or characteristic assumption is imposed.

-/

@[expose] public noncomputable section

universe u v

namespace Polynomial

variable {k : Type u} [Field k] {K : Type v} [Field K]

/-- Extract the full native multiplicity from a nonzero coefficient image. -/
theorem exists_map_eq_pow_multiplicity_mul_and_not_dvd
    (φ : k →+* K) {p : k[X]} (hp : p ≠ 0) {q : K[X]} (hq : ¬IsUnit q) :
    ∃ r : K[X], p.map φ = q ^ multiplicity q (p.map φ) * r ∧ ¬q ∣ r := by
  have hpmap : p.map φ ≠ 0 := Polynomial.map_ne_zero hp
  exact (FiniteMultiplicity.of_not_isUnit hq hpmap).exists_eq_pow_mul_and_not_dvd

/-- At a native principal prime factor, the image is a unit times the full multiplicity
power of that factor. A factor occurring in the image has strictly positive multiplicity. -/
theorem exists_atPrime_unit_mul_pow_multiplicity_map
    (φ : k →+* K) {p : k[X]} (hp : p ≠ 0) {q : K[X]}
    [(Ideal.span ({q} : Set K[X])).IsPrime] (hq : ¬IsUnit q) (hqp : q ∣ p.map φ) :
    0 < multiplicity q (p.map φ) ∧
      ∃ u : (Localization.AtPrime (Ideal.span ({q} : Set K[X])))ˣ,
        algebraMap K[X] (Localization.AtPrime (Ideal.span ({q} : Set K[X]))) (p.map φ) =
          (u : Localization.AtPrime (Ideal.span ({q} : Set K[X]))) *
            (algebraMap K[X] (Localization.AtPrime (Ideal.span ({q} : Set K[X]))) q) ^
              multiplicity q (p.map φ) := by
  obtain ⟨r, hr, hqr⟩ := exists_map_eq_pow_multiplicity_mul_and_not_dvd φ hp hq
  have hru : IsUnit
      (algebraMap K[X] (Localization.AtPrime (Ideal.span ({q} : Set K[X]))) r) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime (Ideal.span ({q} : Set K[X]))) (Ideal.span {q}) r).2
    simpa only [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton] using hqr
  obtain ⟨u, hu⟩ := hru
  refine ⟨multiplicity_pos_of_dvd hqp
    (FiniteMultiplicity.of_not_isUnit hq (Polynomial.map_ne_zero hp)), u, ?_⟩
  calc
    algebraMap K[X] (Localization.AtPrime (Ideal.span ({q} : Set K[X]))) (p.map φ) =
        algebraMap K[X] (Localization.AtPrime (Ideal.span ({q} : Set K[X])))
          (q ^ multiplicity q (p.map φ) * r) :=
      congrArg (algebraMap K[X] (Localization.AtPrime (Ideal.span ({q} : Set K[X])))) hr
    _ = _ := by rw [map_mul, map_pow, ← hu, mul_comm]

/-- For a literal monic irreducible factor, the local exponent is its count in the actual
normalized-factor multiset. Monicity is used only to identify `normalize q` with `q`. -/
theorem multiplicity_map_eq_count_normalizedFactors [DecidableEq K]
    (φ : k →+* K) {p : k[X]} (hp : p ≠ 0) {q : K[X]} (hq : q.Monic)
    (hqirr : Irreducible q) :
    multiplicity q (p.map φ) =
      (UniqueFactorizationMonoid.normalizedFactors (p.map φ)).count q := by
  have hpmap : p.map φ ≠ 0 := Polynomial.map_ne_zero hp
  simpa only [hq.normalize_eq_self] using
    UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors hqirr hpmap

end Polynomial

end
