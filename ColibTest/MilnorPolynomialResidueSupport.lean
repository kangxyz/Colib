/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.PolynomialResidueSupport

/-!
Source-only consumers of native single-lift image support. The coefficient map is arbitrary,
including an explicitly transcendental coefficient extension. None has been compiled.
-/

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u v

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

example (φ : k →+* K) {e : ℕ} (q : MonicIrreducibleOfDegree K e)
    (h : ∀ a : k[X], a ≠ 0 → ¬poly q ∣ a.map φ)
    (y : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue q
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) = 0 :=
  monicIrreducibleResidue_mapRingHom_eq_zero_of_not_dvd φ q h y

example (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (y : MilnorKRing (RatFunc k)) (hy : IsSingleResidueLift p x y)
    (hqp : ¬poly q ∣ (poly p).map φ) :
    monicIrreducibleResidue q
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) = 0 :=
  monicIrreducibleResidue_mapRingHom_eq_zero_of_isSingleResidueLift φ p q x y hy hqp

example (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (y : MilnorKRing (RatFunc k)) (hy : IsSingleResidueLift p x y) :
    ∃ S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e),
      (∀ q, q ∈ S ↔ poly q.2 ∣ (poly p).map φ) ∧
      ∀ q ∉ S, monicIrreducibleResidue q.2
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) = 0 :=
  exists_finset_coefficientFactor_support_of_isSingleResidueLift φ p x y hy

-- The index universe is independent of the common universe of the two Milnor fields.
example {ι : Type v} (φ : k →+* K) {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (y : MilnorKRing (RatFunc k)) (hy : IsSingleResidueLift p x y)
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i))
    (a : ℕ) (r : MonicIrreducibleOfDegree K a)
    (hr : ∀ i ∈ S, poly r ≠ poly (q i)) :
    monicIrreducibleResidue r
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) = 0 :=
  monicIrreducibleResidue_mapRingHom_eq_zero_outside_coefficientFactors
    φ p x y hy S e q hcover a r hr

-- The arbitrary-field theorem genuinely applies to the transcendental extension k(t)/k.
example {d e : ℕ} (p : MonicIrreducibleOfDegree k d)
    (q : MonicIrreducibleOfDegree (RatFunc k) e)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (y : MilnorKRing (RatFunc k)) (hy : IsSingleResidueLift p x y)
    (hqp : ¬poly q ∣ (poly p).map (algebraMap k (RatFunc k))) :
    monicIrreducibleResidue q
        (milnorKRingMap
          (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k (RatFunc k)))
            (Polynomial.nonZeroDivisors_le_comap_mapRingHom (algebraMap k (RatFunc k))))
          y) = 0 :=
  monicIrreducibleResidue_mapRingHom_eq_zero_of_isSingleResidueLift
    (algebraMap k (RatFunc k)) p q x y hy hqp

end
