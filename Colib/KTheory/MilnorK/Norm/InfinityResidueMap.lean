/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.ChartInversionMap
public import Colib.KTheory.MilnorK.Norm.OriginResidueFields
public import Colib.KTheory.MilnorK.Norm.PolynomialResidueMap

/-!
# Native infinity residue under actual coefficient extension

The actual rational coefficient map commutes with native infinity residue. At the origin,
the polynomial residue comparison is specialized to `X`, whose multiplicity is one. The
existing quotient/residue equivalence is canceled rather than replaced, and the existing
origin residue-field equivalence returns to the coefficient field. Native chart inversion
then carries this comparison to infinity, without an additional sign.

There are no characteristic, separability, finite-extension, or algebraicity hypotheses.
The Milnor statements retain the common field universe required by `milnorKRingMap`.
No map or norm model is defined, and no symbol-generation argument is duplicated.

The unconditional
simple-norm scalar-factor formula remains a separate composition step.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
  isDiscreteValuationRing_localizationAtPrime_polynomial

variable {k K : Type u} [Field k] [Field K]

/-- The native whole-ring origin shift commutes with the actual local coefficient map.
This is the existing polynomial-residue theorem at `X`, with multiplicity exactly one. -/
theorem dvrMilnorShiftMap_shift_mapRingHom_at_origin
    (φ : k →+* K) (y : MilnorKRing (RatFunc k)) :
    MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc K)
        (irreducible_algebraMap_X (k := K))
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y)) =
      milnorKRingMap
        (IsLocalRing.ResidueField.map
          (Localization.localRingHom (Ideal.span ({X} : Set k[X]))
            (Ideal.span ({X} : Set K[X])) (Polynomial.mapRingHom φ)
            (Polynomial.span_X_comap_mapRingHom φ).symm))
        (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
          (irreducible_algebraMap_X (k := k)) y)) := by
  let p : MonicIrreducibleOfDegree k 1 := ⟨X, monic_X, irreducible_X, natDegree_X⟩
  let q : MonicIrreducibleOfDegree K 1 := ⟨X, monic_X, irreducible_X, natDegree_X⟩
  have hqp : poly q ∣ (poly p).map φ := by
    simp only [p, q, poly, Polynomial.map_X, dvd_refl]
  have hm : multiplicity (poly q) ((poly p).map φ) = 1 := by
    simp only [p, q, poly, Polynomial.map_X, multiplicity_self]
  let Φ : RatFunc k →+* RatFunc K := RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
  let eP := quotientRingEquivResidueField (Ideal.span {poly p})
  let eQ := quotientRingEquivResidueField (Ideal.span {poly q})
  let κ := IsLocalRing.ResidueField.map
    (Localization.localRingHom (Ideal.span {poly p}) (Ideal.span {poly q})
      (Polynomial.mapRingHom φ)
      (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
        (irreducible p) (irreducible q).not_isUnit hqp).symm)
  let a : (k[X] ⧸ Ideal.span {poly p}) →+* (K[X] ⧸ Ideal.span {poly q}) :=
    AdjoinRoot.map φ (poly p) (poly q) hqp
  let A : MilnorKRing (k[X] ⧸ Ideal.span {poly p}) →+*
      MilnorKRing (K[X] ⧸ Ideal.span {poly q}) := milnorKRingMap a
  let Pmap : MilnorKRing (Ideal.span {poly p}).ResidueField →+*
      MilnorKRing (k[X] ⧸ Ideal.span {poly p}) := milnorKRingMap eP.symm.toRingHom
  let Qmap : MilnorKRing (Ideal.span {poly q}).ResidueField →+*
      MilnorKRing (K[X] ⧸ Ideal.span {poly q}) := milnorKRingMap eQ.symm.toRingHom
  let Qinv : MilnorKRing (K[X] ⧸ Ideal.span {poly q}) →+*
      MilnorKRing (Ideal.span {poly q}).ResidueField := milnorKRingMap eQ.toRingHom
  let βp : MilnorKRing (Ideal.span {poly p}).ResidueField :=
    MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
      (irreducible_algebraMap_self (p := poly p)) y)
  let βq : MilnorKRing (Ideal.span {poly q}).ResidueField :=
    MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc K)
      (irreducible_algebraMap_self (p := poly q)) (milnorKRingMap Φ y))
  have hp : monicIrreducibleResidue p y = Pmap βp := monicIrreducibleResidue_apply p y
  have hq : monicIrreducibleResidue q (milnorKRingMap Φ y) = Qmap βq :=
    monicIrreducibleResidue_apply q _
  have hweighted : monicIrreducibleResidue q (milnorKRingMap Φ y) =
      (multiplicity (poly q) ((poly p).map φ) : ℤ) • A (monicIrreducibleResidue p y) :=
    monicIrreducibleResidue_mapRingHom φ p q hqp y
  have hn : monicIrreducibleResidue q (milnorKRingMap Φ y) =
      A (monicIrreducibleResidue p y) := by
    simpa only [hm, Nat.cast_one, one_zsmul] using hweighted
  have hd : Qmap (milnorKRingMap κ βp) = A (Pmap βp) :=
    milnorKRingMap_quotientRingEquivResidueField_symm_residueField_map φ p q hqp βp
  have hproj : Qmap βq = Qmap (milnorKRingMap κ βp) :=
    hq.symm.trans (hn.trans ((congrArg A hp).trans hd.symm))
  have hcancel (z : MilnorKRing (Ideal.span {poly q}).ResidueField) :
      Qinv (Qmap z) = z :=
    (milnorKRingMap_comp_apply eQ.symm.toRingHom eQ.toRingHom z).trans
      ((congrArg
        (fun f : (Ideal.span {poly q}).ResidueField →+* (Ideal.span {poly q}).ResidueField =>
          milnorKRingMap f z)
        (RingEquiv.toRingHom_comp_symm_toRingHom eQ)).trans (milnorKRingMap_id_apply z))
  have hresult : βq = milnorKRingMap κ βp :=
    (hcancel βq).symm.trans ((congrArg Qinv hproj).trans (hcancel _))
  exact hresult

/-- Native infinity residue commutes with the literal rational coefficient map, on the
entire Milnor ring. The chart change introduces no extra sign in this naturality equation. -/
theorem infinityResidueRing_mapRingHom (φ : k →+* K) (y : MilnorKRing (RatFunc k)) :
    infinityResidueRing K
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) =
      milnorKRingMap φ (infinityResidueRing k y) := by
  let Φ : RatFunc k →+* RatFunc K := RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
  let τ : RatFunc k →+* RatFunc k :=
    (AlgebraicGeometry.projectiveLineChartInversion k).toRingHom
  calc
    infinityResidueRing K (milnorKRingMap Φ y) =
        milnorKRingMap (residueFieldAtOriginEquiv K).symm.toRingHom
          (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc K)
            (irreducible_algebraMap_X (k := K))
            (milnorKRingMap Φ (milnorKRingMap τ y)))) := by
      rw [infinityResidueRing_apply, milnorKRingMap_comp_apply,
        AlgebraicGeometry.projectiveLineChartInversion_comp_mapRingHom,
        ← milnorKRingMap_comp_apply]
      rfl
    _ = milnorKRingMap (residueFieldAtOriginEquiv K).symm.toRingHom
        (milnorKRingMap
          (IsLocalRing.ResidueField.map
            (Localization.localRingHom (Ideal.span ({X} : Set k[X]))
              (Ideal.span ({X} : Set K[X])) (Polynomial.mapRingHom φ)
              (Polynomial.span_X_comap_mapRingHom φ).symm))
          (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
            (irreducible_algebraMap_X (k := k)) (milnorKRingMap τ y)))) := by
      rw [dvrMilnorShiftMap_shift_mapRingHom_at_origin]
    _ = milnorKRingMap φ
        (milnorKRingMap (residueFieldAtOriginEquiv k).symm.toRingHom
          (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
            (irreducible_algebraMap_X (k := k)) (milnorKRingMap τ y)))) := by
      rw [milnorKRingMap_comp_apply,
        residueFieldAtOriginEquiv_symm_comp_residueField_map, ← milnorKRingMap_comp_apply]
    _ = milnorKRingMap φ (infinityResidueRing k y) := rfl

/-- The infinity-residue naturality square as equality of native additive maps. -/
theorem infinityResidueRing_comp_milnorKRingMap_mapRingHom (φ : k →+* K) :
    (infinityResidueRing K).comp
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))).toAddMonoidHom =
      (milnorKRingMap φ).toAddMonoidHom.comp (infinityResidueRing k) := by
  apply AddMonoidHom.ext
  intro y
  exact infinityResidueRing_mapRingHom φ y

/-- The same comparison in every homogeneous degree, using native `milnorKTransport`.
Both sides are the existing degree-lowering residue, with no changed convention. -/
theorem infinityResidue_milnorKTransport_mapRingHom (φ : k →+* K) (n : ℕ)
    (y : MilnorKTheory (RatFunc k) (n + 1)) :
    infinityResidue (k := K) n
        (milnorKTransport (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) (n + 1) y) =
      milnorKTransport φ n (infinityResidue (k := k) n y) := by
  apply Subtype.ext
  simpa only [coe_infinityResidue, milnorKTransport_coe] using
    infinityResidueRing_mapRingHom φ (y : MilnorKRing (RatFunc k))

end Stacks.Chow

end
