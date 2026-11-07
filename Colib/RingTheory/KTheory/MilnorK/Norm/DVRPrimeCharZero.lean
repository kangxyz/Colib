/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.RingTheory.KTheory.MilnorK.Norm.AuxiliaryMixedBranchError
public import Colib.RingTheory.KTheory.MilnorK.Norm.BranchNormRetraction
public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPrimeAnnihilation
public import Colib.RingTheory.KTheory.MilnorK.FiniteMixedGeneration
public import Mathlib.Data.Int.GCD

/-!
# Prime Galois norm-residue compatibility in residue characteristic zero

For each original class, the existing finite mixed-generation theorem chooses one actual
prime-to-degree coefficient field. Its literal mapped-root algebra is a field. The native
tensor base-change equivalence retains the original-field map on every element. All actual
normalization branches of that coefficient field, and every iterated branch above them,
are used. The weighted branch error is retracted by the actual residue norm, and the sum of
the original-base weights is the coefficient-field degree. Thus this class's original error
has a second annihilator coprime to the published prime annihilator. Native integer gcd
cancellation gives equality, without cancelling either integer separately.

The hypotheses are an actual finite torsion-free local DVR extension, prime Galois
fraction-field degree, and characteristic zero of the actual base residue field. All rings
and fields share one universe. Neither Henselianity of the original rings, supplied branch
maps, mixed membership, uniformizers, residue power bases, nor a chosen-norm tower law is
assumed. The completion constructions supply their own Henselian branches.
-/

@[expose] public noncomputable section

open IsLocalRing Module Polynomial
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable (R S F E : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E] [IsGalois F E] [CharZero (ResidueField R)]

/-- Each original norm-residue error has an actual auxiliary-degree annihilator coprime
to the original prime degree. Every normalization branch contributes to that degree. -/
theorem exists_coprime_smul_norm_residue_difference_eq_zero_of_charZero
    (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    ∃ d : ℕ, (finrank F E).Coprime d ∧
      (d : ℤ) •
        (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
          milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) = 0 := by
  classical
  let : CharZero R := RingHom.charZero (residue R)
  let : CharZero F := IsFractionRing.charZero_of_isFractionRing R
  let pb := Field.powerBasisOfFiniteOfSeparable F E
  let p : F[X] := minpoly F pb.gen
  have hpmonic : p.Monic := minpoly.monic pb.isIntegral_gen
  let : Fact (Irreducible p) := ⟨minpoly.irreducible pb.isIntegral_gen⟩
  have hdegree : p.natDegree = finrank F E := pb.natDegree_minpoly.trans pb.finrank.symm
  have hroot : aeval (AdjoinRoot.root p) (minpoly F pb.gen) = 0 :=
    (AdjoinRoot.aeval_eq (f := p) p).trans (AdjoinRoot.mk_self (f := p))
  let g : AdjoinRoot p ≃ₐ[F] E :=
    AdjoinRoot.equiv' p pb hroot (minpoly.aeval F pb.gen)
  let y : MilnorKTheory (AdjoinRoot p) (n + 1) :=
    milnorKTheoryMap g.symm.toRingHom (n + 1) x
  obtain ⟨s, _hs, K, hfinite, hseparable, hcoprime, _hsplit, hq, hgen⟩ :=
    exists_finite_coprime_milnorK_mixed_expansion p hpmonic (hdegree.symm ▸ hp) n y
  let : FiniteDimensional F K := hfinite
  let : Algebra.IsSeparable F K := hseparable
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let : Fact (Irreducible (p.map (algebraMap F K))) := ⟨hq⟩
  dsimp only at hgen
  obtain ⟨c, hc⟩ := hgen
  let M := AdjoinRoot (p.map (algebraMap F K))
  let jroot : AdjoinRoot p →+* M :=
    AdjoinRoot.map (algebraMap F K) p (p.map (algebraMap F K)) dvd_rfl
  let j : E →+* M := jroot.comp g.symm.toRingHom
  let : Algebra E M := j.toAlgebra
  let : FiniteDimensional K M :=
    (AdjoinRoot.powerBasis' (hpmonic.map (algebraMap F K))).finite
  let : Algebra.IsSeparable K M := inferInstance
  let : Algebra R K := ((algebraMap F K).comp (algebraMap R F)).toAlgebra
  have : IsScalarTower R F K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R M := ((algebraMap K M).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K M := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra S M := (j.comp (algebraMap S E)).toAlgebra
  have : IsScalarTower S E M := IsScalarTower.of_algebraMap_eq' rfl
  have hcoefficient (a : F) :
      j (algebraMap F E a) = algebraMap K M (algebraMap F K a) := by
    change jroot (g.symm (algebraMap F E a)) = _
    rw [g.symm.commutes]
    exact AdjoinRoot.map_of (algebraMap F K) p (p.map (algebraMap F K)) dvd_rfl a
  have : IsScalarTower R S M := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap K M (algebraMap F K (algebraMap R F r)) =
      j (algebraMap S E (algebraMap R S r))
    rw [← IsScalarTower.algebraMap_apply R S E,
      IsScalarTower.algebraMap_apply R F E]
    exact (hcoefficient (algebraMap R F r)).symm
  let eta : K ⊗[F] E ≃ₐ[K] M :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) g.symm).trans
      (AdjoinRoot.baseChangeAlgEquiv F K p)
  have heta (e : E) : eta (1 ⊗ₜ[F] e) = algebraMap E M e :=
    AdjoinRoot.baseChangeAlgEquiv_presentation_one_tmul F K E p g e
  have hmap : milnorKTheoryMap (algebraMap E M) (n + 1) x =
      milnorKTheoryMap jroot (n + 1) y := by
    change milnorKTheoryMap (jroot.comp g.symm.toRingHom) (n + 1) x = _
    rw [milnorKTheoryMap_comp]
    rfl
  have hmixed : milnorKTheoryMap (algebraMap E M) (n + 1) x ∈
      milnorKMixedSpan (algebraMap K M) n := by
    change milnorKTheoryMap (algebraMap E M) (n + 1) x ∈ Submodule.span ℤ _
    exact Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨c, hc.trans hmap.symm⟩
  let : DecidableEq (Ideal (integralClosure R K)) := Classical.decEq _
  have hbranch :=
    ramification_smul_restrict_norm_residue_difference_eq_zero_of_auxiliary_mixed
      R S F E K M eta heta hp n x hmixed
  refine ⟨finrank F K, hdegree ▸ hcoprime, ?_⟩
  exact finrank_smul_eq_zero_of_integralClosure_branch_ramification_smul_restrict_eq_zero
    R F K n
    (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x))
    hbranch

/-- The actual chosen norm commutes with canonical DVR residues for every class in a
prime Galois extension with characteristic-zero base residue field. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_prime_galois_of_charZero
    (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  obtain ⟨d, hcoprime, hd⟩ :=
    exists_coprime_smul_norm_residue_difference_eq_zero_of_charZero R S F E hp n x
  have hell := finrank_smul_norm_residue_difference_eq_zero R S F E hp n x
  apply sub_eq_zero.mp
  have h := intGCD_nsmul_eq_zero.mpr ⟨hell, hd⟩
  simpa only [Int.gcd_natCast_natCast, hcoprime.gcd_eq_one, one_nsmul] using h

/-- Equality of the actual additive norm-residue composites in each homogeneous degree. -/
theorem dvrMilnorTameSymbol'_comp_milnorKNorm_of_prime_galois_of_charZero
    (hp : Nat.Prime (finrank F E)) (n : ℕ) :
    (dvrMilnorTameSymbol' R F n).comp (milnorKNorm F E (n + 1)) =
      (milnorKNorm (ResidueField R) (ResidueField S) n).comp
        (dvrMilnorTameSymbol' S E n) := by
  apply AddMonoidHom.ext
  intro x
  exact dvrMilnorTameSymbol'_milnorKNorm_of_prime_galois_of_charZero R S F E hp n x

end Stacks.Chow

attribute [colib_tag "COL-0289"]
  Stacks.Chow.exists_coprime_smul_norm_residue_difference_eq_zero_of_charZero
  Stacks.Chow.dvrMilnorTameSymbol'_milnorKNorm_of_prime_galois_of_charZero
  Stacks.Chow.dvrMilnorTameSymbol'_comp_milnorKNorm_of_prime_galois_of_charZero

attribute [colib_ref "axiom_stacks"
  "StacksFrontier/AlgebraicGeometry/Chow/MilnorNorm/FieldNorm.lean"
  "ingredient" "The actual chosen norm and its full-degree norm-restriction projection formula"]
  Stacks.Chow.exists_coprime_smul_norm_residue_difference_eq_zero_of_charZero
  Stacks.Chow.dvrMilnorTameSymbol'_milnorKNorm_of_prime_galois_of_charZero

attribute [colib_ref "axiom_stacks"
  "StacksFrontier/RingTheory/DiscreteValuationRing/FundamentalIdentity.lean"
  "ingredient" "The native ramification and residue degrees used in the branch-weight descent"]
  Stacks.Chow.exists_coprime_smul_norm_residue_difference_eq_zero_of_charZero

end
