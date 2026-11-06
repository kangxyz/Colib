/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.ScalarFactorBaseChange

/-!
Uncompiled consumers of unconditional native simple-norm scalar-factor base change.
The D/E/F dependencies and this G module are source-only. The degree-zero and repeated-factor
consumers retain the infinity sign and the full multiplicity respectively.
-/

noncomputable section

open Polynomial UniqueFactorizationMonoid Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u v

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K] {ι : Type v}

example (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i)) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
        simpleMilnorNorm (q i)
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)) x) :=
  simpleMilnorNorm_map_eq_weighted_sum_of_factors φ p x S e q hinj hq hcover

example (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly p).map φ)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      ∑ i ∈ S.attach, (multiplicity (poly i.1.2) ((poly p).map φ) : ℤ) •
        simpleMilnorNorm i.1.2
          (milnorKRingMap
            (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)) x) :=
  simpleMilnorNorm_map_eq_sum_coefficientFactors φ p S hS x

example (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d) :
    ∃ (S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e))
      (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly p).map φ),
      ∀ x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}),
        milnorKRingMap φ (simpleMilnorNorm p x) =
          ∑ i ∈ S.attach, (multiplicity (poly i.1.2) ((poly p).map φ) : ℤ) •
            simpleMilnorNorm i.1.2
              (milnorKRingMap
                (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)) x) :=
  exists_finset_simpleMilnorNorm_map_eq_sum_coefficientFactors φ p

example [DecidableEq K] (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      ∑ i ∈ (normalizedFactors ((poly p).map φ)).toFinset.attach,
        let hi := (Polynomial.mem_normalizedFactors_iff
          (Polynomial.map_ne_zero (f := φ) (ne_zero p))).mp (Multiset.mem_toFinset.mp i.2)
        let q : MonicIrreducibleOfDegree K i.1.natDegree := ⟨i.1, hi.2.1, hi.1, rfl⟩
        (multiplicity i.1 ((poly p).map φ) : ℤ) •
          simpleMilnorNorm q (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hi.2.2) x) :=
  simpleMilnorNorm_map_eq_sum_normalizedFactors φ p x

-- Degree zero keeps a positive degree on both sides: the norm's negative infinity sign
-- cancels the negative polynomial degree exactly once.
example (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i)) :
    (d : ℤ) • (1 : MilnorKRing K) =
      ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
        ((e i : ℤ) • (1 : MilnorKRing K)) := by
  simpa only [simpleMilnorNorm_one, map_zsmul, map_one] using
    simpleMilnorNorm_map_eq_weighted_sum_of_factors φ p 1 S e q hinj hq hcover

-- A single repeated factor has coefficient two, not one or two duplicate summands.
example (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hmap : (poly p).map φ = (poly q) ^ 2)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      (2 : ℤ) • simpleMilnorNorm q
        (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q)
          (by rw [hmap, pow_two]; exact dvd_mul_right _ _)) x) := by
  have hq : poly q ∣ (poly p).map φ := by
    rw [hmap, pow_two]
    exact dvd_mul_right _ _
  have hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ →
        ∃ i ∈ ({PUnit.unit} : Finset PUnit.{1}), poly r = poly q := by
    intro a r hr
    have hrq : poly r ∣ poly q := (irreducible r).prime.dvd_of_dvd_pow (hmap ▸ hr)
    refine ⟨PUnit.unit, Finset.mem_singleton_self _, ?_⟩
    exact Polynomial.eq_of_monic_of_associated (monic r) (monic q)
      ((irreducible r).associated_of_dvd (irreducible q) hrq)
  have hm : multiplicity (poly q) ((poly p).map φ) = 2 := by
    rw [hmap]
    exact multiplicity_pow_self (ne_zero q) (irreducible q).not_isUnit 2
  have h := simpleMilnorNorm_map_eq_weighted_sum_of_factors φ p x
    ({PUnit.unit} : Finset PUnit.{1}) (fun _ => e) (fun _ => q)
    (fun _ _ _ _ _ => Subsingleton.elim _ _) (fun _ => hq) hcover
  simpa only [Finset.sum_singleton, hm, Nat.cast_ofNat] using h

-- The whole-ring formula applies directly to every homogeneous input without a new norm.
example (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d) (n : ℕ)
    (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) n)
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i)) :
    milnorKRingMap φ
        (simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) =
      ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
        simpleMilnorNorm (q i)
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i))
            (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) :=
  simpleMilnorNorm_map_eq_weighted_sum_of_factors φ p x S e q hinj hq hcover

-- The coefficient is also the count in the literal normalized-factor multiset.
example [DecidableEq K] (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i)) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      ∑ i ∈ S, ((normalizedFactors ((poly p).map φ)).count (poly (q i)) : ℤ) •
        simpleMilnorNorm (q i)
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)) x) := by
  calc
    milnorKRingMap φ (simpleMilnorNorm p x) =
        ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
          simpleMilnorNorm (q i)
            (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)) x) :=
      simpleMilnorNorm_map_eq_weighted_sum_of_factors φ p x S e q hinj hq hcover
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.multiplicity_map_eq_count_normalizedFactors
        φ (ne_zero p) (monic (q i)) (irreducible (q i))]

end
