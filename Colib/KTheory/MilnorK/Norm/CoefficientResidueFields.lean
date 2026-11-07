/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.RatFunc.CoefficientMap
public import Colib.RingTheory.AdjoinRoot.Map
public import Colib.RingTheory.Polynomial.FactorContraction
public import Colib.RingTheory.Polynomial.FactorMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.PolyResidueRing

/-!
# Actual rational, local, and residue-field coefficient squares

The maps in these equations are the existing `RatFunc.mapRingHom`, `Localization.localRingHom`,
`IsLocalRing.ResidueField.map`, `quotientRingEquivResidueField`, and `AdjoinRoot.map`. The factor
case proves the required contracted ideal equality using irreducibility; it does not assume a
residue-field comparison. No norm, residue, rational-function map, or field model is defined.

These field-level equations do not yet establish Milnor residue naturality or simple-norm
base change.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree

variable {k : Type u} [Field k] {K : Type v} [Field K]

/-- Actual coefficient change of rational functions commutes with the native map of local
rings. The statement works at any pair of primes with the specified contraction. -/
theorem ratFunc_mapRingHom_comp_algebraMap_localizationAtPrime
    (φ : k →+* K) (P : Ideal k[X]) [P.IsPrime] (Q : Ideal K[X]) [Q.IsPrime]
    (hPQ : P = Q.comap (Polynomial.mapRingHom φ)) :
    (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)).comp
        (algebraMap (Localization.AtPrime P) (RatFunc k)) =
      (algebraMap (Localization.AtPrime Q) (RatFunc K)).comp
        (Localization.localRingHom P Q (Polynomial.mapRingHom φ) hPQ) := by
  apply IsLocalization.ringHom_ext P.primeCompl
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply k[X] (Localization.AtPrime P) (RatFunc k),
    Localization.localRingHom_to_map,
    ← IsScalarTower.algebraMap_apply K[X] (Localization.AtPrime Q) (RatFunc K)]
  exact RatFunc.mapRingHom_algebraMap (Polynomial.mapRingHom φ)
    (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ) r

/-- The same fraction square evaluated on a local element. This is the exact `hf` input of
the native ramified tame-symbol comparison, with actual maps rather than an unspecified lift. -/
theorem ratFunc_mapRingHom_algebraMap_localizationAtPrime
    (φ : k →+* K) (P : Ideal k[X]) [P.IsPrime] (Q : Ideal K[X]) [Q.IsPrime]
    (hPQ : P = Q.comap (Polynomial.mapRingHom φ)) (x : Localization.AtPrime P) :
    RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
        (algebraMap (Localization.AtPrime P) (RatFunc k) x) =
      algebraMap (Localization.AtPrime Q) (RatFunc K)
        (Localization.localRingHom P Q (Polynomial.mapRingHom φ) hPQ x) :=
  RingHom.congr_fun
    (ratFunc_mapRingHom_comp_algebraMap_localizationAtPrime φ P Q hPQ) x

/-- At an actual scalar factor, the map on native residue fields agrees with `AdjoinRoot.map`
under the existing polynomial-quotient identifications. No comparison premise is supplied. -/
theorem residueField_map_comp_quotientRingEquivResidueField
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) :
    (IsLocalRing.ResidueField.map
      (Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
        (Polynomial.mapRingHom φ)
        (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
          (irreducible p) (irreducible q).not_isUnit hqp).symm)).comp
        (quotientRingEquivResidueField (Ideal.span {poly p})).toRingHom =
      (quotientRingEquivResidueField (Ideal.span {poly q})).toRingHom.comp
        (AdjoinRoot.map φ (poly p) (poly q) hqp) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [← residue_algebraMap_eq_quotientRingEquivResidueField,
    IsLocalRing.ResidueField.map_residue, Localization.localRingHom_to_map]
  change residue (Localization.AtPrime (Ideal.span {poly q}))
      (algebraMap K[X] (Localization.AtPrime (Ideal.span {poly q})) (r.map φ)) =
    quotientRingEquivResidueField (Ideal.span {poly q})
      (AdjoinRoot.map φ (poly p) (poly q) hqp (AdjoinRoot.mk (poly p) r))
  rw [AdjoinRoot.map_mk]
  exact residue_algebraMap_eq_quotientRingEquivResidueField (Ideal.span {poly q}) (r.map φ)

/-- The residue-field dictionary in the direction needed for polynomial Milnor residues:
returning to the target polynomial quotient gives the literal coefficient-factor map. -/
theorem quotientRingEquivResidueField_symm_comp_residueField_map
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) :
    (quotientRingEquivResidueField (Ideal.span {poly q})).symm.toRingHom.comp
      ((IsLocalRing.ResidueField.map
        (Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
          (Polynomial.mapRingHom φ)
          (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
            (irreducible p) (irreducible q).not_isUnit hqp).symm)).comp
          (quotientRingEquivResidueField (Ideal.span {poly p})).toRingHom) =
      AdjoinRoot.map φ (poly p) (poly q) hqp := by
  rw [residueField_map_comp_quotientRingEquivResidueField φ p q hqp]
  apply RingHom.ext
  intro x
  exact (quotientRingEquivResidueField (Ideal.span {poly q})).symm_apply_apply _

/-- The native local coefficient map sends the source polynomial uniformizer to a unit
times the target polynomial uniformizer raised to its actual multiplicity. This supplies
the `hπmap` input of ramified residue naturality without choosing an arbitrary exponent. -/
theorem exists_localRingHom_unit_mul_pow_multiplicity
    (φ : k →+* K) {d e : ℕ}
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
              multiplicity (poly q) ((poly p).map φ) := by
  obtain ⟨hm, u, hu⟩ := Polynomial.exists_atPrime_unit_mul_pow_multiplicity_map
    φ (ne_zero p) (irreducible q).not_isUnit hqp
  refine ⟨hm, u, ?_⟩
  rw [Localization.localRingHom_to_map]
  exact hu

end Stacks.Chow

end
