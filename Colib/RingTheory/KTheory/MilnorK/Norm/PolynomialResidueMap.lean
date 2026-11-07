/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.CoefficientResidueFields
public import Colib.RingTheory.KTheory.MilnorK.Residue.RamifiedMap
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ResidueConstants

/-!
# Native polynomial residues under coefficient extension

At an actual monic irreducible factor of a coefficient image, polynomial Milnor residue
commutes with the existing coefficient-factor map, multiplied by the actual factor multiplicity.
The proof uses the compiled rational/local square, residue-field dictionary, and local
uniformizer equation, followed by the existing specified-uniformizer ramification theorem.
Ordered symbol products generate the native whole Milnor ring additively.

No map, norm, residue, or field model is defined. The Milnor statements use a common field
universe as required by native `milnorKRingMap`; the preliminary field dictionary allows
independent universes. No characteristic, separability, or finite-extension hypothesis occurs.

This does not prove image support at all other points, infinity naturality, a simple-norm
base-change formula, or norm tower independence.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
  isDiscreteValuationRing_localizationAtPrime_polynomial

/-- The existing residue-field dictionary with its input in the source residue field, rather
than the polynomial quotient. This is an equality of the actual native ring homomorphisms. -/
theorem quotientRingEquivResidueField_symm_comp_residueField_map_eq_comp_symm
    {k : Type u} [Field k] {K : Type v} [Field K] (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) :
    (quotientRingEquivResidueField (Ideal.span {poly q})).symm.toRingHom.comp
      (IsLocalRing.ResidueField.map
        (Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
          (Polynomial.mapRingHom φ)
          (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
            (irreducible p) (irreducible q).not_isUnit hqp).symm)) =
      (AdjoinRoot.map φ (poly p) (poly q) hqp).comp
        (quotientRingEquivResidueField (Ideal.span {poly p})).symm.toRingHom := by
  apply RingHom.ext
  intro x
  let eP := quotientRingEquivResidueField (Ideal.span {poly p})
  let eQ := quotientRingEquivResidueField (Ideal.span {poly q})
  let κ := IsLocalRing.ResidueField.map
    (Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
      (Polynomial.mapRingHom φ)
      (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
        (irreducible p) (irreducible q).not_isUnit hqp).symm)
  have h : eQ.symm (κ (eP (eP.symm x))) =
      AdjoinRoot.map φ (poly p) (poly q) hqp (eP.symm x) := RingHom.congr_fun
    (quotientRingEquivResidueField_symm_comp_residueField_map φ p q hqp)
    (eP.symm x)
  exact (congrArg (fun z => eQ.symm (κ z)) (eP.apply_symm_apply x)).symm.trans h

variable {k K : Type u} [Field k] [Field K]

/-- Applying native Milnor ring functoriality to the actual residue-field dictionary. -/
theorem milnorKRingMap_quotientRingEquivResidueField_symm_residueField_map
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ)
    (x : MilnorKRing (Ideal.span {poly p}).ResidueField) :
    milnorKRingMap (quotientRingEquivResidueField (Ideal.span {poly q})).symm.toRingHom
      (milnorKRingMap
        (IsLocalRing.ResidueField.map
          (Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
            (Polynomial.mapRingHom φ)
            (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
              (irreducible p) (irreducible q).not_isUnit hqp).symm)) x) =
      milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hqp)
        (milnorKRingMap
          (quotientRingEquivResidueField (Ideal.span {poly p})).symm.toRingHom x) := by
  let eP := (quotientRingEquivResidueField (Ideal.span {poly p})).symm.toRingHom
  let eQ := (quotientRingEquivResidueField (Ideal.span {poly q})).symm.toRingHom
  let κ := IsLocalRing.ResidueField.map
    (Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
      (Polynomial.mapRingHom φ)
      (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
        (irreducible p) (irreducible q).not_isUnit hqp).symm)
  let a : (k[X] ⧸ Ideal.span {poly p}) →+* (K[X] ⧸ Ideal.span {poly q}) :=
    AdjoinRoot.map φ (poly p) (poly q) hqp
  have hd : eQ.comp κ = a.comp eP :=
    quotientRingEquivResidueField_symm_comp_residueField_map_eq_comp_symm φ p q hqp
  calc
    milnorKRingMap eQ (milnorKRingMap κ x) = milnorKRingMap (eQ.comp κ) x :=
      milnorKRingMap_comp_apply κ eQ x
    _ = milnorKRingMap (a.comp eP) x :=
      congrArg
        (fun f : (Ideal.span {poly p}).ResidueField →+* (K[X] ⧸ Ideal.span {poly q}) =>
          milnorKRingMap f x) hd
    _ = milnorKRingMap a (milnorKRingMap eP x) :=
      (milnorKRingMap_comp_apply eP a x).symm

private theorem polynomialResidue_symbolProd_shift_map
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) (l : List (RatFunc k)ˣ) :
    MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc K)
        (irreducible_algebraMap_self (p := poly q))
        (milnorKSymbolProd (RatFunc K)
          (l.map (Units.map
            (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)).toMonoidHom)))) =
      (multiplicity (poly q) ((poly p).map φ) : ℤ) •
        milnorKRingMap
          (IsLocalRing.ResidueField.map
            (Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
              (Polynomial.mapRingHom φ)
              (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
                (irreducible p) (irreducible q).not_isUnit hqp).symm))
          (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
            (irreducible_algebraMap_self (p := poly p)) (milnorKSymbolProd (RatFunc k) l))) := by
  let P : Ideal k[X] := Ideal.span {poly p}
  let Q : Ideal K[X] := Ideal.span {poly q}
  let hPQ : P = Q.comap (Polynomial.mapRingHom φ) :=
    (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
      (irreducible p) (irreducible q).not_isUnit hqp).symm
  let j : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (Polynomial.mapRingHom φ) hPQ
  let Φ : RatFunc k →+* RatFunc K := RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
  have hf (r : Localization.AtPrime P) :
      Φ (algebraMap (Localization.AtPrime P) (RatFunc k) r) =
        algebraMap (Localization.AtPrime Q) (RatFunc K) (j r) :=
    ratFunc_mapRingHom_algebraMap_localizationAtPrime φ P Q hPQ r
  obtain ⟨_, a, ha⟩ := exists_localRingHom_unit_mul_pow_multiplicity φ p q hqp
  have hshift := (dvrMilnorShiftMap_symbolProd_map_ramified j Φ hf
    (irreducible_algebraMap_self (p := poly p))
    (irreducible_algebraMap_self (p := poly q)) a
    (multiplicity (poly q) ((poly p).map φ)) ha l).2
  rw [milnorKRingMapLift_eq] at hshift
  exact hshift

private theorem polynomialResidue_symbolProd_map_residueField
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) (l : List (RatFunc k)ˣ) :
    monicIrreducibleResidue q
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))
          (milnorKSymbolProd (RatFunc k) l)) =
      (multiplicity (poly q) ((poly p).map φ) : ℤ) •
        milnorKRingMap (quotientRingEquivResidueField (Ideal.span {poly q})).symm.toRingHom
          (milnorKRingMap
            (IsLocalRing.ResidueField.map
              (Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
                (Polynomial.mapRingHom φ)
                (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
                  (irreducible p) (irreducible q).not_isUnit hqp).symm))
            (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
              (irreducible_algebraMap_self (p := poly p))
              (milnorKSymbolProd (RatFunc k) l)))) := by
  let P : Ideal k[X] := Ideal.span {poly p}
  let Q : Ideal K[X] := Ideal.span {poly q}
  let j := Localization.localRingHom P Q (Polynomial.mapRingHom φ)
    (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
      (irreducible p) (irreducible q).not_isUnit hqp).symm
  let Φ : RatFunc k →+* RatFunc K := RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
  let β : MilnorKRing P.ResidueField :=
    MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
      (irreducible_algebraMap_self (p := poly p)) (milnorKSymbolProd (RatFunc k) l))
  let Rq : MilnorKRing Q.ResidueField →+* MilnorKRing (K[X] ⧸ Q) :=
    milnorKRingMap (quotientRingEquivResidueField Q).symm.toRingHom
  calc
    monicIrreducibleResidue q (milnorKRingMap Φ (milnorKSymbolProd (RatFunc k) l)) =
        Rq (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc K)
          (irreducible_algebraMap_self (p := poly q))
          (milnorKRingMap Φ (milnorKSymbolProd (RatFunc k) l)))) :=
      monicIrreducibleResidue_apply q _
    _ = Rq (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc K)
        (irreducible_algebraMap_self (p := poly q))
        (milnorKSymbolProd (RatFunc K) (l.map (Units.map Φ.toMonoidHom))))) :=
      congrArg (fun z : MilnorKRing (RatFunc K) =>
        Rq (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc K)
          (irreducible_algebraMap_self (p := poly q)) z)))
        (milnorKRingMap_milnorKSymbolProd Φ l)
    _ = Rq ((multiplicity (poly q) ((poly p).map φ) : ℤ) •
        milnorKRingMap (IsLocalRing.ResidueField.map j) β) :=
      congrArg Rq (polynomialResidue_symbolProd_shift_map φ p q hqp l)
    _ = (multiplicity (poly q) ((poly p).map φ) : ℤ) •
        Rq (milnorKRingMap (IsLocalRing.ResidueField.map j) β) := map_zsmul Rq _ _

/-- Polynomial residue naturality on ordered symbol products. The multiplier is the actual
polynomial multiplicity, not a supplied ramification index or an omitted repeated factor. -/
theorem monicIrreducibleResidue_mapRingHom_symbolProd
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) (l : List (RatFunc k)ˣ) :
    monicIrreducibleResidue q
        (milnorKRingMap
          (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
            (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))
          (milnorKSymbolProd (RatFunc k) l)) =
      (multiplicity (poly q) ((poly p).map φ) : ℤ) •
        milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hqp)
          (monicIrreducibleResidue p (milnorKSymbolProd (RatFunc k) l)) := by
  let Φ : RatFunc k →+* RatFunc K := RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
  let y : MilnorKRing (RatFunc k) := milnorKSymbolProd (RatFunc k) l
  let m : ℤ := multiplicity (poly q) ((poly p).map φ)
  let eP := (quotientRingEquivResidueField (Ideal.span {poly p})).symm.toRingHom
  let eQ := (quotientRingEquivResidueField (Ideal.span {poly q})).symm.toRingHom
  let κ := IsLocalRing.ResidueField.map
    (Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
      (Polynomial.mapRingHom φ)
      (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
        (irreducible p) (irreducible q).not_isUnit hqp).symm)
  let a : (k[X] ⧸ Ideal.span {poly p}) →+* (K[X] ⧸ Ideal.span {poly q}) :=
    AdjoinRoot.map φ (poly p) (poly q) hqp
  let A : MilnorKRing (k[X] ⧸ Ideal.span {poly p}) →+*
      MilnorKRing (K[X] ⧸ Ideal.span {poly q}) := milnorKRingMap a
  let β : MilnorKRing (Ideal.span {poly p}).ResidueField :=
    MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
      (irreducible_algebraMap_self (p := poly p)) y)
  have hs : monicIrreducibleResidue p y = milnorKRingMap eP β :=
    monicIrreducibleResidue_apply p y
  have hd : milnorKRingMap eQ (milnorKRingMap κ β) = A (milnorKRingMap eP β) :=
    milnorKRingMap_quotientRingEquivResidueField_symm_residueField_map φ p q hqp β
  have hd' : milnorKRingMap eQ (milnorKRingMap κ β) = A (monicIrreducibleResidue p y) :=
    hd.trans (congrArg A hs.symm)
  have hraw : monicIrreducibleResidue q (milnorKRingMap Φ y) =
      m • milnorKRingMap eQ (milnorKRingMap κ β) :=
    polynomialResidue_symbolProd_map_residueField φ p q hqp l
  have hresult : monicIrreducibleResidue q (milnorKRingMap Φ y) =
      m • A (monicIrreducibleResidue p y) :=
    hraw.trans (congrArg (fun z : MilnorKRing (K[X] ⧸ Ideal.span {poly q}) => m • z) hd')
  exact hresult

/-- Polynomial residue naturality for every class in the native whole Milnor ring. This is
the finite-place comparison at a specified scalar factor; no support or infinity claim is made. -/
theorem monicIrreducibleResidue_mapRingHom
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) (y : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue q
        (milnorKRingMap
          (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
            (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) =
      (multiplicity (poly q) ((poly p).map φ) : ℤ) •
        milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hqp)
          (monicIrreducibleResidue p y) := by
  let Φ : RatFunc k →+* RatFunc K := RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
  let lhs : MilnorKRing (RatFunc k) →+
      MilnorKRing (K[X] ⧸ Ideal.span {poly q}) :=
    (monicIrreducibleResidue q).comp (milnorKRingMap Φ).toAddMonoidHom
  let rhs : MilnorKRing (RatFunc k) →+
      MilnorKRing (K[X] ⧸ Ideal.span {poly q}) :=
    (multiplicity (poly q) ((poly p).map φ) : ℤ) •
      ((milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hqp)).toAddMonoidHom.comp
        (monicIrreducibleResidue p))
  have hgen (l : List (RatFunc k)ˣ) :
      milnorKSymbolProd (RatFunc k) l ∈ AddMonoidHom.eqLocus lhs rhs := by
    change monicIrreducibleResidue q (milnorKRingMap Φ (milnorKSymbolProd (RatFunc k) l)) =
      (multiplicity (poly q) ((poly p).map φ) : ℤ) •
        milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hqp)
          (monicIrreducibleResidue p (milnorKSymbolProd (RatFunc k) l))
    exact monicIrreducibleResidue_mapRingHom_symbolProd φ p q hqp l
  exact mem_of_forall_milnorKSymbolProd_mem (H := AddMonoidHom.eqLocus lhs rhs) hgen y

/-- The polynomial-residue restriction square as an equality of native additive maps. -/
theorem monicIrreducibleResidue_comp_milnorKRingMap_mapRingHom
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ) :
    (monicIrreducibleResidue q).comp
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))).toAddMonoidHom =
      (multiplicity (poly q) ((poly p).map φ) : ℤ) •
        ((milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hqp)).toAddMonoidHom.comp
          (monicIrreducibleResidue p)) := by
  apply AddMonoidHom.ext
  intro y
  exact monicIrreducibleResidue_mapRingHom φ p q hqp y

/-- At a factor of the source point, the image of a native single-residue lift has the exact
weighted residue needed by the conditional scalar-factor norm reduction. -/
theorem monicIrreducibleResidue_mapRingHom_of_isSingleResidueLift
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hqp : poly q ∣ (poly p).map φ)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (y : MilnorKRing (RatFunc k)) (hy : IsSingleResidueLift p x y) :
    monicIrreducibleResidue q
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) =
      (multiplicity (poly q) ((poly p).map φ) : ℤ) •
        milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hqp) x := by
  rw [monicIrreducibleResidue_mapRingHom φ p q hqp y, hy.1]

end Stacks.Chow

end
