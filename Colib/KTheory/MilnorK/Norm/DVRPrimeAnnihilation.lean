/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Norm.DVRResidueTrace
public import Colib.KTheory.MilnorK.Residue.Automorphism

/-!
# Prime annihilation of the actual norm-residue error

For an actual finite torsion-free local DVR extension with prime Galois fraction-field
degree, the restriction of the norm-residue error is killed by the actual ramification
index. Applying the chosen residue norm gives annihilation by the full field degree.

The coefficient `e` is never cancelled. The proof retains the original Galois index in
the residue trace, including purely inseparable residue extensions. It uses the native
chosen norm, its projection formula, the canonical residue and the local identity
`[E : F] = e [k(S) : k(R)]`. No tower identity, perfectness, Henselianity, tameness,
power basis or torsion-freeness of a Milnor group is assumed.

This proves an annihilator, not the norm-residue square on all classes. A second,
coprime annihilator from actual auxiliary branches remains a separate obligation.

-/

@[expose] public noncomputable section

open IsLocalRing Module
open scoped BigOperators

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

/-- The actual ramification index annihilates the restriction of the norm-residue error.
There is no cancellation of the ramification factor. -/
theorem ramification_smul_restrict_norm_residue_difference_eq_zero
    (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
      milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n
        (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
          milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) = 0 := by
  classical
  let : FaithfulSMul R S := inferInstance
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hne : algebraMap R S π ≠ 0 := fun h =>
    hπ.ne_zero (FaithfulSMul.algebraMap_injective R S (by simpa using h))
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hρ
  have he : e = Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S := by
    have hv := Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_ramificationIdx
      R S π hπ
    rw [hu, IsDiscreteValuationRing.addVal_def' u hρ e] at hv
    exact_mod_cast hv
  have hu' : algebraMap R S π = (u : S) *
      ρ ^ Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S := by
    simpa only [he] using hu
  have hf : ∀ a : R, algebraMap F E (algebraMap R F a) =
      algebraMap S E (algebraMap R S a) := fun a =>
    (IsScalarTower.algebraMap_apply R F E a).symm.trans
      (IsScalarTower.algebraMap_apply R S E a)
  have hκ : ResidueField.map (algebraMap R S) =
      algebraMap (ResidueField R) (ResidueField S) := rfl
  have hr := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified (algebraMap R S) (algebraMap F E) hf
      hπ hρ u (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S) hu' n)
    (milnorKNorm F E (n + 1) x)
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, hκ] at hr
  have htrace := milnorKNorm_map_eq_sum_gal_of_normal_prime hp (n + 1) x
  have hres :
      (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n
          (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x)) =
      (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) := by
    calc
      _ = dvrMilnorTameSymbol' S E n
          (milnorKTheoryMap (algebraMap F E) (n + 1)
            (milnorKNorm F E (n + 1) x)) := hr.symm
      _ = dvrMilnorTameSymbol' S E n
          (∑ σ : Gal(E/F), milnorKTheoryMap σ.toRingHom (n + 1) x) :=
        congrArg (dvrMilnorTameSymbol' S E n) htrace
      _ = ∑ σ : Gal(E/F), dvrMilnorTameSymbol' S E n
          (milnorKTheoryMap σ.toRingHom (n + 1) x) := map_sum _ _ _
      _ = ∑ σ : Gal(E/F),
          milnorKTheoryMap (ResidueField.map (galRestrict R F E S σ : S →+* S)) n
            (dvrMilnorTameSymbol' S E n x) := by
        apply Finset.sum_congr rfl
        intro σ _
        exact DFunLike.congr_fun (dvrMilnorTameSymbol'_map_galRestrict R S F E σ n) x
      _ = _ := dvr_sum_residue_galRestrict_eq_ramification_smul_norm_homogeneous
        R S F E hp n (dvrMilnorTameSymbol' S E n x)
  rw [map_sub, smul_sub, hres, sub_self]

/-- Every norm-residue error is killed by the prime generic degree. This is only the
prime annihilator; equality still needs a coprime annihilator from actual branches. -/
theorem finrank_smul_norm_residue_difference_eq_zero
    (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    (finrank F E : ℤ) •
      (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
        milnorKNorm (ResidueField R) (ResidueField S) n
          (dvrMilnorTameSymbol' S E n x)) = 0 := by
  let δ : MilnorKTheory (ResidueField R) n :=
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x)
  have hweighted := ramification_smul_restrict_norm_residue_difference_eq_zero
    R S F E hp n x
  change (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
    milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n δ = 0 at hweighted
  have hring : (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
      milnorKRingMap (algebraMap (ResidueField R) (ResidueField S))
        (δ : MilnorKRing (ResidueField R)) = 0 := by
    have h := congrArg ((milnorKGrading (ResidueField S) n).subtype) hweighted
    simpa only [map_zsmul, map_zero, milnorKTheoryMap_eq_transport,
      AddMonoidHom.coe_toIntLinearMap, AddSubgroup.subtype_apply, milnorKTransport_coe] using h
  have hnorm := congrArg (milnorKNormRing (ResidueField R) (ResidueField S)) hring
  rw [map_zsmul, milnorKNormRing_milnorKRingMap, map_zero, smul_smul] at hnorm
  let : FaithfulSMul R S := inferInstance
  let : Module.Flat R S := inferInstance
  have hd : Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S *
      finrank (ResidueField R) (ResidueField S) = finrank F E := by
    have h := Stacks.DiscreteValuationRing.Ramification.ramificationIdx_mul_inertiaDeg_eq_finrank
      R S F E
    rw [Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal R)] at h
    exact h
  rw [← Nat.cast_mul, hd] at hnorm
  apply Subtype.ext
  exact hnorm

end Stacks.Chow

end
