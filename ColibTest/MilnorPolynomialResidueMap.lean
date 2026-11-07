/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.PolynomialResidueMap
import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.SimpleNorm

/-!
Source-only consumers of polynomial residue naturality. These do not establish image support,
infinity naturality, simple-norm base change, or tower independence. None has been elaborated.
-/

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u v

attribute [local instance] Ideal.Quotient.field

-- Only the field-level dictionary promises independent source and target universes.
example {k : Type u} [Field k] {K : Type v} [Field K] (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) :
    (quotientRingEquivResidueField (Ideal.span {poly q})).symm.toRingHom.comp
      (IsLocalRing.ResidueField.map
        (Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
          (Polynomial.mapRingHom φ)
          (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
            (irreducible p) (irreducible q).not_isUnit hqp).symm)) =
      (AdjoinRoot.map φ (poly p) (poly q) hqp).comp
        (quotientRingEquivResidueField (Ideal.span {poly p})).symm.toRingHom :=
  quotientRingEquivResidueField_symm_comp_residueField_map_eq_comp_symm φ p q hqp

variable {k K : Type u} [Field k] [Field K]

example (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) (y : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue q
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) =
      (multiplicity (poly q) ((poly p).map φ) : ℤ) •
        milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hqp)
          (monicIrreducibleResidue p y) :=
  monicIrreducibleResidue_mapRingHom φ p q hqp y

example (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) (n : ℕ) (y : MilnorKTheory (RatFunc k) (n + 1)) :
    monicIrreducibleResidue q
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))
          (y : MilnorKRing (RatFunc k))) =
      (multiplicity (poly q) ((poly p).map φ) : ℤ) •
        milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hqp)
          (monicIrreducibleResidue p (y : MilnorKRing (RatFunc k))) :=
  monicIrreducibleResidue_mapRingHom φ p q hqp y

example (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (y : MilnorKRing (RatFunc k)) (hy : IsSingleResidueLift p x y) :
    monicIrreducibleResidue q
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) =
      (multiplicity (poly q) ((poly p).map φ) : ℤ) •
        milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hqp) x :=
  monicIrreducibleResidue_mapRingHom_of_isSingleResidueLift φ p q hqp x y hy

-- A zero source residue vanishes at every specified factor lying above that source point.
example (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) (y : MilnorKRing (RatFunc k))
    (hy : monicIrreducibleResidue p y = 0) :
    monicIrreducibleResidue q
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) = 0 := by
  rw [monicIrreducibleResidue_mapRingHom φ p q hqp y, hy, map_zero, smul_zero]

-- The polynomial symbol has target residue equal to the full factor multiplicity.
example (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) :
    monicIrreducibleResidue q
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))
          (milnorKSymbol (RatFunc k) (polyUnit (ne_zero p)))) =
      (multiplicity (poly q) ((poly p).map φ) : ℤ) •
        (1 : MilnorKRing (K[X] ⧸ Ideal.span {poly q})) := by
  rw [monicIrreducibleResidue_mapRingHom φ p q hqp,
    (isSingleResidueLift_one p).1, map_one]

-- The same residue formula can use the count in the actual normalized-factor multiset.
example [DecidableEq K] (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) (y : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue q
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) =
      ((UniqueFactorizationMonoid.normalizedFactors ((poly p).map φ)).count (poly q) : ℤ) •
        milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hqp)
          (monicIrreducibleResidue p y) := by
  rw [← Polynomial.multiplicity_map_eq_count_normalizedFactors
    φ (ne_zero p) (monic q) (irreducible q)]
  exact monicIrreducibleResidue_mapRingHom φ p q hqp y

end
