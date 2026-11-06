/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.PurelyInseparable.PrimeDegree
public import Colib.KTheory.MilnorK.Norm.NormalPrimeTrace
public import Colib.KTheory.MilnorK.Norm.PrimeInseparableTrace
public import Colib.RingTheory.DiscreteValuationRing.RamificationDegree
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Data.Fintype.EquivFin

/-!
# The actual residue trace of a prime Galois DVR extension

The integral automorphism is the native `galRestrict R F E S`, on the actual
finite local DVR `S`. Its residue automorphism is the native
`IsLocalRing.ResidueField.mapAlgEquiv'`. The quotient stabilizer surjectivity
theorem is used directly, with the native integral-closure action on `S`.

The sum remains indexed by `Gal(E/F)`, including when the residue extension is
purely inseparable. Its coefficient is the actual native ramification index.
The proof separates residue degree one from ramification index one, and in the
latter case separates separable and purely inseparable residue extensions.
There is no torsion cancellation and no assumed norm tower or trace identity.

-/

@[expose] public noncomputable section

open IsLocalRing Module
open scoped BigOperators Pointwise

universe u v

namespace Stacks.Chow

variable (R S : Type u) (F E : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E] [IsGalois F E]

omit [Module.IsTorsionFree R S] in
/-- Normality and surjectivity for the literal integral restriction and its native
residue map. No replacement integral-closure carrier or action is introduced. -/
theorem dvr_residueField_normal_and_galRestrict_surjective :
    Normal (ResidueField R) (ResidueField S) ∧
      Function.Surjective (fun σ : Gal(E/F) =>
        ResidueField.mapAlgEquiv' (galRestrict R F E S σ)) := by
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  let := IsIntegralClosure.MulSemiringAction R F E S
  let : SMulCommClass Gal(E/F) R S :=
    ⟨fun σ r s => by
      change (galRestrict R F E S σ) (r • s) = r • (galRestrict R F E S σ) s
      exact (galRestrict R F E S σ).toLinearEquiv.map_smul r s⟩
  let : Algebra.IsInvariant R S Gal(E/F) := Algebra.isInvariant_of_isGalois R F E S
  refine ⟨Ideal.Quotient.normal Gal(E/F) (maximalIdeal R) (maximalIdeal S), ?_⟩
  intro τ
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective
    Gal(E/F) (maximalIdeal R) (maximalIdeal S) τ
  refine ⟨σ.val, ?_⟩
  ext x
  obtain ⟨s, rfl⟩ := residue_surjective x
  exact DFunLike.congr_fun hσ (residue S s)

omit [IsDomain R] [IsDiscreteValuationRing R] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)] in
private theorem dvr_galRestrict_residue_sum_of_maps_eq_id
    (y : MilnorKRing (ResidueField S))
    (h : ∀ σ : Gal(E/F), ResidueField.map (galRestrict R F E S σ : S →+* S) =
      RingHom.id (ResidueField S)) :
    (∑ σ : Gal(E/F),
      milnorKRingMap (ResidueField.map (galRestrict R F E S σ : S →+* S)) y) =
        (finrank F E : ℤ) • y := by
  classical
  have hc : Fintype.card Gal(E/F) = finrank F E :=
    Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank F E)
  simp only [h, milnorKRingMap_id_apply, Finset.sum_const, Finset.card_univ, hc,
    natCast_zsmul]

/-- The residue trace over the original generic Galois group is the actual
ramification index times restriction of the native chosen residue norm. -/
theorem dvr_sum_residue_galRestrict_eq_ramification_smul_norm
    (hp : Nat.Prime (finrank F E)) (y : MilnorKRing (ResidueField S)) :
    (∑ σ : Gal(E/F),
      milnorKRingMap (ResidueField.map (galRestrict R F E S σ : S →+* S)) y) =
        (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
          milnorKRingMap (algebraMap (ResidueField R) (ResidueField S))
            (milnorKNormRing (ResidueField R) (ResidueField S) y) := by
  classical
  let : Module.Flat R S := inferInstance
  let : FaithfulSMul R S := inferInstance
  have hd : Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S *
      finrank (ResidueField R) (ResidueField S) = finrank F E := by
    have h := Stacks.DiscreteValuationRing.Ramification.ramificationIdx_mul_inertiaDeg_eq_finrank
      R S F E
    rw [Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal R)] at h
    exact h
  have hprime : Nat.Prime
      (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S *
        finrank (ResidueField R) (ResidueField S)) := hd.symm ▸ hp
  rcases Nat.prime_mul_iff.mp hprime with ⟨_heprime, hf⟩ | ⟨hfprime, he⟩
  · have hb : Function.Bijective (algebraMap (ResidueField R) (ResidueField S)) :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hf
    have hmaps : ∀ σ : Gal(E/F),
        ResidueField.map (galRestrict R F E S σ : S →+* S) =
          RingHom.id (ResidueField S) := by
      intro σ
      ext x
      obtain ⟨a, rfl⟩ := hb.2 x
      exact (ResidueField.mapAlgEquiv' (galRestrict R F E S σ)).commutes a
    have hn : milnorKRingMap (algebraMap (ResidueField R) (ResidueField S))
        (milnorKNormRing (ResidueField R) (ResidueField S) y) = y := by
      rw [milnorKNormRing_of_bijective hb]
      let g := RingEquiv.ofBijective (algebraMap (ResidueField R) (ResidueField S)) hb
      change milnorKRingMap (g : ResidueField R →+* ResidueField S)
        (milnorKRingMap (g.symm : ResidueField S →+* ResidueField R) y) = y
      rw [milnorKRingMap_comp_apply, RingEquiv.comp_symm, milnorKRingMap_id_apply]
    rw [dvr_galRestrict_residue_sum_of_maps_eq_id R S F E y hmaps, hn, ← hd, hf, mul_one]
  · by_cases hsep : Algebra.IsSeparable (ResidueField R) (ResidueField S)
    · let : Algebra.IsSeparable (ResidueField R) (ResidueField S) := hsep
      obtain ⟨hnormal, hsurj⟩ := dvr_residueField_normal_and_galRestrict_surjective R S F E
      let : Normal (ResidueField R) (ResidueField S) := hnormal
      let : IsGalois (ResidueField R) (ResidueField S) := ⟨⟩
      have hc : Fintype.card Gal(E/F) =
          Fintype.card Gal((ResidueField S)/(ResidueField R)) := by
        rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
          IsGalois.card_aut_eq_finrank F E,
          IsGalois.card_aut_eq_finrank (ResidueField R) (ResidueField S), ← hd, he, one_mul]
      have hbij : Function.Bijective (fun σ : Gal(E/F) =>
          ResidueField.mapAlgEquiv' (galRestrict R F E S σ)) :=
        (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hc⟩
      rw [he, Nat.cast_one, one_smul,
        milnorKNormRing_map_eq_sum_gal_of_normal_prime hfprime]
      exact Fintype.sum_bijective
        (fun σ : Gal(E/F) => ResidueField.mapAlgEquiv' (galRestrict R F E S σ)) hbij
        _ _ (fun _ => rfl)
    · let : IsPurelyInseparable (ResidueField R) (ResidueField S) :=
        isPurelyInseparable_of_finrank_prime_of_not_isSeparable hfprime hsep
      have hmaps : ∀ σ : Gal(E/F),
          ResidueField.map (galRestrict R F E S σ : S →+* S) =
            RingHom.id (ResidueField S) := by
        intro σ
        have h : (ResidueField.mapAlgEquiv' (galRestrict R F E S σ)).toAlgHom =
            AlgHom.id (ResidueField R) (ResidueField S) := Subsingleton.elim _ _
        exact congrArg AlgHom.toRingHom h
      rw [dvr_galRestrict_residue_sum_of_maps_eq_id R S F E y hmaps,
        milnorKRingMap_milnorKNormRing_of_isPurelyInseparable_of_prime hfprime,
        smul_smul, ← Nat.cast_mul, hd]

/-- Homogeneous form of the same trace identity, still indexed by `Gal(E/F)`. -/
theorem dvr_sum_residue_galRestrict_eq_ramification_smul_norm_homogeneous
    (hp : Nat.Prime (finrank F E)) (n : ℕ) (y : MilnorKTheory (ResidueField S) n) :
    (∑ σ : Gal(E/F),
      milnorKTheoryMap (ResidueField.map (galRestrict R F E S σ : S →+* S)) n y) =
        (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
          milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n
            (milnorKNorm (ResidueField R) (ResidueField S) n y) := by
  apply Subtype.ext
  change (milnorKGrading (ResidueField S) n).subtype (∑ σ : Gal(E/F),
      milnorKTheoryMap (ResidueField.map (galRestrict R F E S σ : S →+* S)) n y) =
    (milnorKGrading (ResidueField S) n).subtype
      ((Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n y))
  rw [map_sum, map_zsmul]
  simp_rw [milnorKTheoryMap_eq_transport]
  exact dvr_sum_residue_galRestrict_eq_ramification_smul_norm R S F E hp
    (y : MilnorKRing (ResidueField S))

end Stacks.Chow

end
