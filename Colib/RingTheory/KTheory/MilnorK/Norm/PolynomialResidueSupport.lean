/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.CoefficientFactorSupport
public import Colib.RingTheory.KTheory.MilnorK.Norm.PolynomialResidueMap

/-!
# Native single-lift support under coefficient extension

A native single-residue lift has no image residue outside the actual factors of its source
polynomial. At a point with nonzero contraction, the polynomial residue comparison applies.
At a point with zero contraction, all source rational functions extend to the target local
ring; the existing DVR theorem for a field mapping into its local ring kills the residue.

Only theorem-local uses of Mathlib's localization lift occur. No map or norm is defined.
The coefficient homomorphism is arbitrary; no algebraicity, finiteness, separability, or
characteristic assumption is imposed. Milnor ring maps require a common field universe.

Source-only draft. Neither this file nor its new polynomial-residue dependency has been
compiled. Infinity compatibility and the final simple-norm base-change formula remain separate.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
  isDiscreteValuationRing_localizationAtPrime_polynomial

variable {k K : Type u} [Field k] [Field K]

/-- A point with zero contraction has zero residue on every coefficient-extended class.
The hypothesis is the literal divisibility test for a zero contracted polynomial prime. -/
theorem monicIrreducibleResidue_mapRingHom_eq_zero_of_not_dvd
    (φ : k →+* K) {e : ℕ} (q : MonicIrreducibleOfDegree K e)
    (h : ∀ a : k[X], a ≠ 0 → ¬poly q ∣ a.map φ)
    (y : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue q
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) = 0 := by
  let Q : Ideal K[X] := Ideal.span {poly q}
  let A := Localization.AtPrime Q
  let g : k[X] →+* A := (algebraMap K[X] A).comp (Polynomial.mapRingHom φ)
  have hg : ∀ a : nonZeroDivisors k[X], IsUnit (g a) := by
    intro a
    change IsUnit (algebraMap K[X] A ((a : k[X]).map φ))
    apply (IsLocalization.AtPrime.isUnit_to_map_iff A Q ((a : k[X]).map φ)).2
    apply Ideal.mem_primeCompl_iff.mpr
    intro ha
    exact h a (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
      (Ideal.mem_span_singleton.mp ha)
  let j : RatFunc k →+* A := IsLocalization.lift hg
  have hj : RatFunc.mapRingHom (Polynomial.mapRingHom φ)
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ) =
      (algebraMap A (RatFunc K)).comp j := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply]
    rw [RatFunc.mapRingHom_algebraMap]
    change algebraMap K[X] (RatFunc K) ((Polynomial.mapRingHom φ) a) =
      algebraMap A (RatFunc K) (IsLocalization.lift hg (algebraMap k[X] (RatFunc k) a))
    rw [IsLocalization.lift_eq]
    exact IsScalarTower.algebraMap_apply K[X] A (RatFunc K) ((Polynomial.mapRingHom φ) a)
  rw [hj, monicIrreducibleResidue_apply,
    dvrMilnorShiftMap_milnorKRingMap_units, MilnorKShift.shift_ofMilnorK, map_zero]

/-- Every image residue of a native single-residue lift vanishes away from the actual
coefficient factors of its source polynomial, including points with zero contraction. -/
theorem monicIrreducibleResidue_mapRingHom_eq_zero_of_isSingleResidueLift
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (y : MilnorKRing (RatFunc k)) (hy : IsSingleResidueLift p x y)
    (hqp : ¬poly q ∣ (poly p).map φ) :
    monicIrreducibleResidue q
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) = 0 := by
  classical
  by_cases h : ∃ a : k[X], a ≠ 0 ∧ poly q ∣ a.map φ
  · obtain ⟨a, ha, hqa⟩ := h
    obtain ⟨b, r, hqr⟩ := exists_dvd_map_of_dvd_map φ q a ha hqa
    have hrp : poly r ≠ poly p := by
      intro heq
      exact hqp (heq ▸ hqr)
    rw [monicIrreducibleResidue_mapRingHom φ r q hqr y,
      hy.2 b r hrp, map_zero, smul_zero]
  · apply monicIrreducibleResidue_mapRingHom_eq_zero_of_not_dvd φ q _ y
    intro a ha hqa
    exact h ⟨a, ha, hqa⟩

/-- A native single lift has image support in exactly the finite set of actual coefficient
factors. The set is allowed to include factors whose particular residue class is zero. -/
theorem exists_finset_coefficientFactor_support_of_isSingleResidueLift
    (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (y : MilnorKRing (RatFunc k)) (hy : IsSingleResidueLift p x y) :
    ∃ S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e),
      (∀ q, q ∈ S ↔ poly q.2 ∣ (poly p).map φ) ∧
      ∀ q ∉ S, monicIrreducibleResidue q.2
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) = 0 := by
  obtain ⟨S, hS⟩ := exists_finset_mem_iff_dvd_map φ (poly p) (ne_zero p)
  refine ⟨S, hS, ?_⟩
  intro q hq
  exact monicIrreducibleResidue_mapRingHom_eq_zero_of_isSingleResidueLift
    φ p q.2 x y hy (fun h => hq ((hS q).mpr h))

/-- A supplied finite family covering all actual factors satisfies the precise support
premise of the existing scalar-factor reduction. Extra points cause no difficulty. -/
theorem monicIrreducibleResidue_mapRingHom_eq_zero_outside_coefficientFactors
    {ι : Type v} (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (y : MilnorKRing (RatFunc k)) (hy : IsSingleResidueLift p x y)
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i))
    (a : ℕ) (r : MonicIrreducibleOfDegree K a)
    (hr : ∀ i ∈ S, poly r ≠ poly (q i)) :
    monicIrreducibleResidue r
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) = 0 := by
  apply monicIrreducibleResidue_mapRingHom_eq_zero_of_isSingleResidueLift φ p r x y hy
  intro h
  obtain ⟨i, hi, heq⟩ := hcover a r h
  exact hr i hi heq

end Stacks.Chow

end
