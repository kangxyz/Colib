/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Norm.ScalarFactorReduction
public import Colib.KTheory.MilnorK.Norm.PolynomialResidueSupport
public import Colib.KTheory.MilnorK.Norm.InfinityResidueMap

/-!
# Scalar-factor base change for the existing simple Milnor norm

The image of a native simple norm is the sum of the native norms at the actual coefficient
factors, weighted by their full polynomial multiplicities. A native single lift is chosen
inside the proof. Its finite residues, outside-support vanishing, and infinity naturality
are proved by the D, E, and F leaves rather than supplied as comparison hypotheses.

The arbitrary finite-family interface is followed by an exact native closed-point factor set
and by the actual `normalizedFactors.toFinset` formula. Repeated factors occur once in the
index set and retain their full multiplicity as the coefficient.

No norm, field, map, or factor model is introduced. The coefficient homomorphism is arbitrary;
there are no characteristic, separability, algebraicity, or finiteness assumptions. The fields
share the universe required by the native Milnor ring map. A finite-family index may have
an independent universe. The normalized-factor spelling additionally uses `DecidableEq K`.

This entire G leaf and its D/E/F dependencies are uncompiled source-only drafts. The statements
are unconditional scalar-factor comparisons, not claims of successful elaboration. They do
not establish presentation independence or an actual field-norm tower law.
-/

@[expose] public noncomputable section

open Polynomial UniqueFactorizationMonoid

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

/-- Base change of the native simple norm along any complete, distinct finite family of
actual coefficient factors. All residue and infinity comparisons are conclusions of the
supporting theorems, not additional hypotheses. -/
theorem simpleMilnorNorm_map_eq_weighted_sum_of_factors
    {ι : Type v} (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i)) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
        simpleMilnorNorm (q i)
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)) x) := by
  obtain ⟨y, hy⟩ := exists_isSingleResidueLift_ring' p x
  let Φ : RatFunc k →+* RatFunc K := RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
  have hresidue : ∀ i ∈ S,
      monicIrreducibleResidue (q i) (milnorKRingMap Φ y) =
        (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
          milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)) x := by
    intro i _
    exact monicIrreducibleResidue_mapRingHom_of_isSingleResidueLift φ p (q i) (hq i) x y hy
  have hsupport : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      (∀ i ∈ S, poly r ≠ poly (q i)) →
        monicIrreducibleResidue r (milnorKRingMap Φ y) = 0 := by
    intro a r hr
    exact monicIrreducibleResidue_mapRingHom_eq_zero_outside_coefficientFactors
      φ p x y hy S e q hcover a r hr
  have hinfinity : infinityResidueRing K (milnorKRingMap Φ y) =
      milnorKRingMap φ (infinityResidueRing k y) :=
    infinityResidueRing_mapRingHom φ y
  exact simpleMilnorNorm_map_eq_weighted_sum_of_lift_residues
    φ Φ p x y hy S e q hinj hq
    (fun i => multiplicity (poly (q i)) ((poly p).map φ)) hresidue hsupport hinfinity

/-- The scalar-factor formula on an exact finite set of native closed points. Membership
supplies every factor map, and sigma-point injectivity removes any separate distinctness premise. -/
theorem simpleMilnorNorm_map_eq_sum_coefficientFactors
    (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly p).map φ)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      ∑ i ∈ S.attach, (multiplicity (poly i.1.2) ((poly p).map φ) : ℤ) •
        simpleMilnorNorm i.1.2
          (milnorKRingMap
            (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)) x) := by
  have hinj : Set.InjOn (fun i : S => poly i.1.2) (S.attach : Set S) := by
    intro i _ j _ hij
    exact Subtype.ext (sigma_poly_injective hij)
  have hq : ∀ i : S, poly i.1.2 ∣ (poly p).map φ := fun i => (hS i.1).mp i.2
  have hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S.attach, poly r = poly i.1.2 := by
    intro a r hr
    let i : S := ⟨⟨a, r⟩, (hS ⟨a, r⟩).mpr hr⟩
    exact ⟨i, Finset.mem_attach S i, rfl⟩
  exact simpleMilnorNorm_map_eq_weighted_sum_of_factors
    φ p x S.attach (fun i => i.1.1) (fun i => i.1.2) hinj hq hcover

/-- An actual complete finite factor set exists and gives the native scalar-factor formula
for every input class. No finite-family or comparison data is assumed in this endpoint. -/
theorem exists_finset_simpleMilnorNorm_map_eq_sum_coefficientFactors
    (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d) :
    ∃ (S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e))
      (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly p).map φ),
      ∀ x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}),
        milnorKRingMap φ (simpleMilnorNorm p x) =
          ∑ i ∈ S.attach, (multiplicity (poly i.1.2) ((poly p).map φ) : ℤ) •
            simpleMilnorNorm i.1.2
              (milnorKRingMap
                (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)) x) := by
  obtain ⟨S, hS⟩ := exists_finset_mem_iff_dvd_map φ (poly p) (ne_zero p)
  exact ⟨S, hS, simpleMilnorNorm_map_eq_sum_coefficientFactors φ p S hS⟩

/-- Base change over the literal normalized factors of the coefficient image. The sum
uses distinct factors, while its integer coefficients retain all repeated multiplicities. -/
theorem simpleMilnorNorm_map_eq_sum_normalizedFactors [DecidableEq K]
    (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap φ (simpleMilnorNorm p x) =
      ∑ i ∈ (normalizedFactors ((poly p).map φ)).toFinset.attach,
        let hi := (Polynomial.mem_normalizedFactors_iff
          (Polynomial.map_ne_zero (f := φ) (ne_zero p))).mp (Multiset.mem_toFinset.mp i.2)
        let q : MonicIrreducibleOfDegree K i.1.natDegree := ⟨i.1, hi.2.1, hi.1, rfl⟩
        (multiplicity i.1 ((poly p).map φ) : ℤ) •
          simpleMilnorNorm q (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hi.2.2) x) := by
  let S := (normalizedFactors ((poly p).map φ)).toFinset
  have hmem (i : S) : Irreducible i.1 ∧ i.1.Monic ∧ i.1 ∣ (poly p).map φ :=
    (Polynomial.mem_normalizedFactors_iff
      (Polynomial.map_ne_zero (f := φ) (ne_zero p))).mp (Multiset.mem_toFinset.mp i.2)
  let q (i : S) : MonicIrreducibleOfDegree K i.1.natDegree :=
    ⟨i.1, (hmem i).2.1, (hmem i).1, rfl⟩
  have hinj : Set.InjOn (fun i : S => poly (q i)) (S.attach : Set S) := by
    intro i _ j _ hij
    exact Subtype.ext hij
  have hq : ∀ i : S, poly (q i) ∣ (poly p).map φ := fun i => (hmem i).2.2
  have hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S.attach, poly r = poly (q i) := by
    intro a r hr
    have hrS : poly r ∈ S := Multiset.mem_toFinset.mpr
      ((Polynomial.mem_normalizedFactors_iff
        (Polynomial.map_ne_zero (f := φ) (ne_zero p))).mpr ⟨irreducible r, monic r, hr⟩)
    let i : S := ⟨poly r, hrS⟩
    exact ⟨i, Finset.mem_attach S i, rfl⟩
  exact simpleMilnorNorm_map_eq_weighted_sum_of_factors
    φ p x S.attach (fun i => i.1.natDegree) q hinj hq hcover

end Stacks.Chow

end
