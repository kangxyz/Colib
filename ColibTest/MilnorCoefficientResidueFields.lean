/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.CoefficientResidueFields

/-! Source-only actual-map consumers. These do not test an unproved Milnor base-change formula. -/

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u v

variable {k : Type u} [Field k] {K : Type v} [Field K]

example (φ : k →+* K) (P : Ideal k[X]) [P.IsPrime] (Q : Ideal K[X]) [Q.IsPrime]
    (hPQ : P = Q.comap (Polynomial.mapRingHom φ)) (x : Localization.AtPrime P) :
    RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
        (algebraMap (Localization.AtPrime P) (RatFunc k) x) =
      algebraMap (Localization.AtPrime Q) (RatFunc K)
        (Localization.localRingHom P Q (Polynomial.mapRingHom φ) hPQ x) :=
  ratFunc_mapRingHom_algebraMap_localizationAtPrime φ P Q hPQ x

example (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ)
    (x : k[X] ⧸ Ideal.span {poly p}) :
    (quotientRingEquivResidueField (Ideal.span {poly q})).symm
      (IsLocalRing.ResidueField.map
        (Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
          (Polynomial.mapRingHom φ)
          (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
            (irreducible p) (irreducible q).not_isUnit hqp).symm)
        (quotientRingEquivResidueField (Ideal.span {poly p}) x)) =
      AdjoinRoot.map φ (poly p) (poly q) hqp x :=
  RingHom.congr_fun (quotientRingEquivResidueField_symm_comp_residueField_map φ p q hqp) x

example (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) :
    0 < multiplicity (poly q) ((poly p).map φ) ∧
      ∃ u : (Localization.AtPrime (Ideal.span {poly q}))ˣ,
        Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
            (Polynomial.mapRingHom φ)
            (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
              (irreducible p) (irreducible q).not_isUnit hqp).symm
            (algebraMap k[X] (Localization.AtPrime (Ideal.span {poly p})) (poly p)) =
          (u : Localization.AtPrime (Ideal.span {poly q})) *
            (algebraMap K[X] (Localization.AtPrime (Ideal.span {poly q})) (poly q)) ^
              multiplicity (poly q) ((poly p).map φ) :=
  exists_localRingHom_unit_mul_pow_multiplicity φ p q hqp

end
