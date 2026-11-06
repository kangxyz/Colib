/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Polynomial.FactorMultiplicity

/-! Source-only consumers, including a repeated factor. No example has been elaborated. -/

noncomputable section

open Polynomial

universe u v

variable {k : Type u} [Field k] {K : Type v} [Field K]

example (φ : k →+* K) {p : k[X]} (hp : p ≠ 0) {q : K[X]} (hq : ¬IsUnit q) :
    ∃ r : K[X], p.map φ = q ^ multiplicity q (p.map φ) * r ∧ ¬q ∣ r :=
  Polynomial.exists_map_eq_pow_multiplicity_mul_and_not_dvd φ hp hq

example (φ : k →+* K) {p : k[X]} (hp : p ≠ 0) {q : K[X]}
    [(Ideal.span ({q} : Set K[X])).IsPrime] (hq : ¬IsUnit q) (hqp : q ∣ p.map φ) :
    0 < multiplicity q (p.map φ) ∧
      ∃ u : (Localization.AtPrime (Ideal.span ({q} : Set K[X])))ˣ,
        algebraMap K[X] (Localization.AtPrime (Ideal.span ({q} : Set K[X]))) (p.map φ) =
          (u : Localization.AtPrime (Ideal.span ({q} : Set K[X]))) *
            (algebraMap K[X] (Localization.AtPrime (Ideal.span ({q} : Set K[X]))) q) ^
              multiplicity q (p.map φ) :=
  Polynomial.exists_atPrime_unit_mul_pow_multiplicity_map φ hp hq hqp

example [DecidableEq K] (φ : k →+* K) {p : k[X]} (hp : p ≠ 0) {q : K[X]}
    (hq : q.Monic) (hqirr : Irreducible q) :
    multiplicity q (p.map φ) =
      (UniqueFactorizationMonoid.normalizedFactors (p.map φ)).count q :=
  Polynomial.multiplicity_map_eq_count_normalizedFactors φ hp hq hqirr

-- A genuinely repeated polynomial factor retains exponent two in the local equation.
example (q : k[X]) (hq : Irreducible q) [(Ideal.span ({q} : Set k[X])).IsPrime] :
    ∃ u : (Localization.AtPrime (Ideal.span ({q} : Set k[X])))ˣ,
      algebraMap k[X] (Localization.AtPrime (Ideal.span ({q} : Set k[X]))) (q ^ 2) =
        (u : Localization.AtPrime (Ideal.span ({q} : Set k[X]))) *
          (algebraMap k[X] (Localization.AtPrime (Ideal.span ({q} : Set k[X]))) q) ^ 2 := by
  have hdvd : q ∣ (q ^ 2).map (RingHom.id k) := ⟨q, by simp only [Polynomial.map_id, pow_two]⟩
  obtain ⟨_, u, hu⟩ := Polynomial.exists_atPrime_unit_mul_pow_multiplicity_map
    (RingHom.id k) (pow_ne_zero 2 hq.ne_zero) hq.not_isUnit hdvd
  refine ⟨u, ?_⟩
  simpa only [Polynomial.map_id, multiplicity_pow_self hq.ne_zero hq.not_isUnit] using hu

end
