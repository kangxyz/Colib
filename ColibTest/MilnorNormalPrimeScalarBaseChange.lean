/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeScalarBaseChange

/-!
Consumers of actual chosen-norm scalar-factor base change. The coefficient
extension is arbitrary and need not be finite or algebraic. All multiplicities and
actual quotient maps are retained. Branch equivalences and commuting squares are
explicit structural data, not norm-comparison hypotheses.
-/

noncomputable section

open Polynomial Module UniqueFactorizationMonoid
open Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u v

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

-- The degree-one comparison needs no perfectness, normality, or characteristic assumption.
example {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L]
    (p : MonicIrreducibleOfDegree k 1)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p})) (x : MilnorKRing L) :
    milnorKNormRing k L x = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) :=
  milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_degree_one p rfl f x

-- Factor normality itself is independent of prime degree and characteristic zero.
example (φ : k →+* K) {d e : ℕ} (p : MonicIrreducibleOfDegree k d)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ) :
    Normal K (K[X] ⧸ Ideal.span {poly q}) :=
  normal_quotient_of_dvd_map_of_normal φ p q hq

example [CharZero k] (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ) :
    e = 1 ∨ e = d :=
  degree_eq_one_or_eq_of_dvd_map_of_normal_prime φ p hp q hq

-- The only extra instance in this one-factor comparison is native finite dimension.
example [CharZero k] (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ)
    (x : MilnorKRing (K[X] ⧸ Ideal.span {poly q})) :
    letI : FiniteDimensional K (K[X] ⧸ Ideal.span {poly q}) :=
      (AdjoinRoot.powerBasis' (monic q)).finite
    milnorKNormRing K (K[X] ⧸ Ideal.span {poly q}) x = simpleMilnorNorm q x := by
  let : FiniteDimensional K (K[X] ⧸ Ideal.span {poly q}) :=
    (AdjoinRoot.powerBasis' (monic q)).finite
  exact milnorKNormRing_eq_simpleMilnorNorm_of_dvd_map_of_normal_prime φ p hp q hq x

-- The family index may have an independent universe. The theorem supplies every FD instance.
example [CharZero k] {ι : Type v} (φ : k →+* K) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i)) :
    letI : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
      (AdjoinRoot.powerBasis' (monic p)).finite
    letI : ∀ i, FiniteDimensional K (K[X] ⧸ Ideal.span {poly (q i)}) :=
      fun i => (AdjoinRoot.powerBasis' (monic (q i))).finite
    milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x) =
      ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
        milnorKNormRing K (K[X] ⧸ Ideal.span {poly (q i)})
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)) x) :=
  milnorKNormRing_map_eq_weighted_sum_of_factors_of_normal_prime
    φ p hp x S e q hinj hq hcover

-- Every homogeneous input is covered, including degree zero.
example [CharZero k] {ι : Type v} (φ : k →+* K) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (n : ℕ) (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) n)
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i)) :
    letI : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
      (AdjoinRoot.powerBasis' (monic p)).finite
    letI : ∀ i, FiniteDimensional K (K[X] ⧸ Ideal.span {poly (q i)}) :=
      fun i => (AdjoinRoot.powerBasis' (monic (q i))).finite
    milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p})
        (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) =
      ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
        milnorKNormRing K (K[X] ⧸ Ideal.span {poly (q i)})
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i))
            (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) :=
  milnorKNormRing_map_eq_weighted_sum_of_factors_of_normal_prime
    φ p hp (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) S e q hinj hq hcover

example [CharZero k] (φ : k →+* K) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly p).map φ)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    letI : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
      (AdjoinRoot.powerBasis' (monic p)).finite
    letI : ∀ i : S, FiniteDimensional K (K[X] ⧸ Ideal.span {poly i.1.2}) :=
      fun i => (AdjoinRoot.powerBasis' (monic i.1.2)).finite
    milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x) =
      ∑ i ∈ S.attach, (multiplicity (poly i.1.2) ((poly p).map φ) : ℤ) •
        milnorKNormRing K (K[X] ⧸ Ideal.span {poly i.1.2})
          (milnorKRingMap
            (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)) x) :=
  milnorKNormRing_map_eq_sum_coefficientFactors_of_normal_prime φ p hp S hS x

example [CharZero k] (φ : k →+* K) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})] :
    ∃ (S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e))
      (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly p).map φ),
      letI : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
        (AdjoinRoot.powerBasis' (monic p)).finite
      letI : ∀ i : S, FiniteDimensional K (K[X] ⧸ Ideal.span {poly i.1.2}) :=
        fun i => (AdjoinRoot.powerBasis' (monic i.1.2)).finite
      ∀ x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}),
        milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x) =
          ∑ i ∈ S.attach, (multiplicity (poly i.1.2) ((poly p).map φ) : ℤ) •
            milnorKNormRing K (K[X] ⧸ Ideal.span {poly i.1.2})
              (milnorKRingMap
                (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)) x) :=
  exists_finset_milnorKNormRing_map_eq_sum_coefficientFactors_of_normal_prime φ p hp

example [CharZero k] [DecidableEq K] (φ : k →+* K) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    letI : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
      (AdjoinRoot.powerBasis' (monic p)).finite
    milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x) =
      ∑ i ∈ (normalizedFactors ((poly p).map φ)).toFinset.attach,
        let hi := (Polynomial.mem_normalizedFactors_iff
          (Polynomial.map_ne_zero (f := φ) (ne_zero p))).mp (Multiset.mem_toFinset.mp i.2)
        let q : MonicIrreducibleOfDegree K i.1.natDegree := ⟨i.1, hi.2.1, hi.1, rfl⟩
        letI : FiniteDimensional K (K[X] ⧸ Ideal.span {poly q}) :=
          (AdjoinRoot.powerBasis' (monic q)).finite
        (multiplicity i.1 ((poly p).map φ) : ℤ) •
          milnorKNormRing K (K[X] ⧸ Ideal.span {poly q})
            (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hi.2.2) x) :=
  milnorKNormRing_map_eq_sum_normalizedFactors_of_normal_prime φ p hp x

-- Chosen norms on 1 retain the source degree and every weighted factor degree.
example [CharZero k] {ι : Type v} (φ : k →+* K) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i)) :
    (d : ℤ) • (1 : MilnorKRing K) =
      ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
        ((e i : ℤ) • (1 : MilnorKRing K)) := by
  let : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
    (AdjoinRoot.powerBasis' (monic p)).finite
  let : ∀ i, FiniteDimensional K (K[X] ⧸ Ideal.span {poly (q i)}) :=
    fun i => (AdjoinRoot.powerBasis' (monic (q i))).finite
  have h := milnorKNormRing_map_eq_weighted_sum_of_factors_of_normal_prime
    φ p hp 1 S e q hinj hq hcover
  have hpone : milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) 1 =
      (d : ℤ) • (1 : MilnorKRing k) := by
    have hn := milnorKNormRing_one (K := k) (L := k[X] ⧸ Ideal.span {poly p})
    simpa only [finrank_quotient_span_eq_natDegree, natDegree_eq] using hn
  have hqone (i : ι) : milnorKNormRing K (K[X] ⧸ Ideal.span {poly (q i)}) 1 =
      (e i : ℤ) • (1 : MilnorKRing K) := by
    have hn := milnorKNormRing_one (K := K) (L := K[X] ⧸ Ideal.span {poly (q i)})
    simpa only [finrank_quotient_span_eq_natDegree, natDegree_eq] using hn
  simpa only [map_one, hpone, hqone, map_zsmul] using h

-- Actual branch fields require actual quotient equivalences and commuting ring maps.
-- These hypotheses do not assert a norm equality or a tower law.
example [CharZero k] {ι : Type v} (φ : k →+* K)
    {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L] [Normal k L]
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p}))
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i))
    (M : ι → Type u) [∀ i, Field (M i)] [∀ i, Algebra K (M i)]
    [∀ i, FiniteDimensional K (M i)]
    (g : ∀ i, M i ≃ₐ[K] (K[X] ⧸ Ideal.span {poly (q i)}))
    (j : ∀ i, L →+* M i)
    (hsquare : ∀ i, (g i).toRingHom.comp (j i) =
      (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)).comp f.toRingHom)
    (x : MilnorKRing L) :
    milnorKRingMap φ (milnorKNormRing k L x) =
      ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
        milnorKNormRing K (M i) (milnorKRingMap (j i) x) :=
  milnorKNormRing_map_eq_weighted_sum_of_branch_equivs_of_normal_prime
    φ p hp f S e q hinj hq hcover M g j hsquare x

end
