/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Charpoly.ResidueBranchCountOne
public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeScalarBaseChange
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# The actual lower residue norm square in ramification one

The original residue extension is normal of prime degree in characteristic zero. The
actual tensor decomposition and integral root coordinates first force distinct, exhaustive
residue factors with relative residue degree one. Native AdjoinRoot-to-adjoin equivalences,
followed by the actual degree-one inclusions, provide the branch presentations. Their root
and coefficient equations prove the full ring-map square before using the chosen norm's
scalar-factor formula. Ramification tower arithmetic supplies the remaining common weight.

No norm square, factor bijection, field presentation, or norm tower law is assumed. The
original residue power basis, its integral lift, full generic tensor decomposition and
actual local scalar towers are retained as explicit geometric inputs. This is the second
case of the lower residue square, not construction of those geometric inputs and not the
independent coprime annihilator by itself.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module UniqueFactorizationMonoid
open scoped TensorProduct BigOperators

universe u v w

namespace Stacks.Chow

open MonicIrreducibleOfDegree
open DiscreteValuationRing.Ramification

attribute [local instance] Ideal.Quotient.field

variable (R S T : Type u) (F E L : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra R S] [Algebra F E]
  [Algebra R E] [Algebra S E] [IsScalarTower R F E] [IsScalarTower R S E]
  [IsIntegralClosure S R E] [FiniteDimensional F E]
  [Module.IsTorsionFree R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field L]
  [Algebra R T] [FaithfulSMul R T] [IsLocalHom (algebraMap R T)] [Algebra T L]
  [IsFractionRing T L] [Algebra F L] [Algebra R L]
  [IsScalarTower R T L] [IsScalarTower R F L]
  {ι : Type w} [Fintype ι] (D : ι → Type v) (U : ι → Type u)
  [∀ i, Field (D i)] [∀ i, CommRing (U i)] [∀ i, IsDomain (U i)]
  [∀ i, IsDiscreteValuationRing (U i)]
  [∀ i, Algebra L (D i)] [∀ i, Algebra T (U i)]
  [∀ i, Algebra T (D i)] [∀ i, Algebra (U i) (D i)]
  [∀ i, IsScalarTower T L (D i)] [∀ i, IsScalarTower T (U i) (D i)]
  [∀ i, IsIntegralClosure (U i) T (D i)] [∀ i, FiniteDimensional L (D i)]
  [∀ i, Module.IsTorsionFree T (U i)] [∀ i, Module.Finite T (U i)]
  [∀ i, IsLocalHom (algebraMap T (U i))]
  [∀ i, Algebra R (U i)] [∀ i, Algebra S (U i)]
  [∀ i, FaithfulSMul S (U i)]
  [∀ i, IsScalarTower R S (U i)] [∀ i, IsScalarTower R T (U i)]
  [∀ i, IsLocalHom (algebraMap S (U i))]
  [CharZero (ResidueField R)]
  [Normal (ResidueField R) (ResidueField S)]



set_option backward.isDefEq.respectTransparency.types false in
/-- The whole-ring lower weighted residue norm identity when the original ramification
exponent is one and the original residue extension has normal prime degree. -/
theorem sum_ramification_smul_residue_norm_map_of_ramification_eq_one
    (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i)) (b : S)
    (hc : ∀ i, algebraMap (U i) (D i) (algebraMap S (U i) b) =
      ε (1 ⊗ₜ[F] (algebraMap S E b)) i)
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (he : algebraMap R S π = (u : S) * ϖ ^ 1)
    (B : PowerBasis (ResidueField R) (ResidueField S)) (hB : B.gen = residue S b)
    {τ : T} (hτ : Irreducible τ) (ω : ∀ i, U i)
    (hω : ∀ i, Irreducible (ω i)) (v : ∀ i, (U i)ˣ) (d : ι → ℕ)
    (hd : ∀ i, algebraMap T (U i) τ = (v i : U i) * ω i ^ d i)
    (hprime : Nat.Prime (finrank (ResidueField R) (ResidueField S)))
    (y : MilnorKRing (ResidueField S)) :
    (∑ i, (ramificationIdx S (U i) : ℤ) •
      milnorKNormRing (ResidueField T) (ResidueField (U i))
        (milnorKRingMap (algebraMap (ResidueField S) (ResidueField (U i))) y)) =
      (ramificationIdx R T : ℤ) •
        milnorKRingMap (algebraMap (ResidueField R) (ResidueField T))
          (milnorKNormRing (ResidueField R) (ResidueField S) y) := by
  classical
  let : ∀ i, IsLocalHom (algebraMap R (U i)) := fun i => by
    rw [IsScalarTower.algebraMap_eq R S (U i)]
    infer_instance
  let : ∀ i, FaithfulSMul R (U i) := fun i => FaithfulSMul.trans R S (U i)
  let : CharZero (ResidueField T) := charZero_of_injective_algebraMap
    (algebraMap (ResidueField R) (ResidueField T)).injective
  obtain ⟨hdegree, hinj, hcover⟩ :=
    Algebra.residue_branches_of_ramification_eq_one R F S E T L D U ε b hc
      hπ hϖ u he B hB hτ ω hω v d hd
  let β := fun i => residue (U i) (algebraMap S (U i) b)
  let H := fun i => IntermediateField.adjoin (ResidueField T) {β i}
  let p : MonicIrreducibleOfDegree (ResidueField R)
      (minpoly (ResidueField R) (residue S b)).natDegree :=
    minpolyOfDegree (ResidueField R)
      (Algebra.IsIntegral.isIntegral (R := ResidueField R) (residue S b))
  let q := fun i => minpolyOfDegree (ResidueField T)
    (Algebra.IsIntegral.isIntegral (R := ResidueField T) (β i))
  have hpdegree : (minpoly (ResidueField R) (residue S b)).natDegree.Prime := by
    rw [← hB, B.natDegree_minpoly, ← B.finrank]
    exact hprime
  have hsourceRoot : aeval (AdjoinRoot.root (poly p))
      (minpoly (ResidueField R) B.gen) = 0 := by
    rw [hB]
    exact (AdjoinRoot.aeval_eq (f := poly p) (poly p)).trans
      (AdjoinRoot.mk_self (f := poly p))
  have hsourceEval : aeval B.gen (poly p) = 0 := by
    change aeval B.gen (minpoly (ResidueField R) (residue S b)) = 0
    rw [← hB]
    exact minpoly.aeval (ResidueField R) B.gen
  let e₀ : AdjoinRoot (poly p) ≃ₐ[ResidueField R] ResidueField S :=
    AdjoinRoot.equiv' (poly p) B hsourceRoot hsourceEval
  have he₀root : e₀ (AdjoinRoot.root (poly p)) = residue S b := by
    change AdjoinRoot.liftAlgHom (poly p) (Algebra.ofId _ _) B.gen hsourceEval
      (AdjoinRoot.root (poly p)) = residue S b
    rw [AdjoinRoot.liftAlgHom_root, hB]
  let eH (i : ι) : H i ≃ₐ[ResidueField T] ResidueField (U i) :=
    AlgEquiv.ofBijective (H i).val
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (hdegree i).2)
  let e (i : ι) : AdjoinRoot (poly (q i)) ≃ₐ[ResidueField T] ResidueField (U i) :=
    (IntermediateField.adjoinRootEquivAdjoin (ResidueField T)
      (Algebra.IsIntegral.isIntegral (R := ResidueField T) (β i))).trans (eH i)
  have heroot (i : ι) : e i (AdjoinRoot.root (poly (q i))) = β i := by
    change eH i (IntermediateField.adjoinRootEquivAdjoin (ResidueField T)
      (Algebra.IsIntegral.isIntegral (R := ResidueField T) (β i))
        (AdjoinRoot.root (minpoly (ResidueField T) (β i)))) = β i
    rw [IntermediateField.adjoinRootEquivAdjoin_apply_root]
    rfl
  let φ := algebraMap (ResidueField R) (ResidueField T)
  let j := fun i => algebraMap (ResidueField S) (ResidueField (U i))
  have hq (i : ι) : poly (q i) ∣ (poly p).map φ := by
    simpa only [q, p, poly, minpolyOfDegree, β, φ, ResidueField.algebraMap_residue] using
      minpoly.dvd_map_of_isScalarTower' (ResidueField R)
        (ResidueField T) (ResidueField (U i)) (residue S b)
  have hsquare (i : ι) : (e i).symm.toRingHom.comp (j i) =
      (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)).comp e₀.symm.toRingHom := by
    have haux : (j i).comp e₀.toRingHom =
        (e i).toRingHom.comp (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)) := by
      apply AdjoinRoot.ringHom_ext
      · apply RingHom.ext
        intro a
        change j i (e₀ (AdjoinRoot.of (poly p) a)) =
          e i (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i) (AdjoinRoot.of (poly p) a))
        rw [AdjoinRoot.map_of]
        change j i (e₀ (algebraMap (ResidueField R) (AdjoinRoot (poly p)) a)) =
          e i (algebraMap (ResidueField T) (AdjoinRoot (poly (q i))) (φ a))
        rw [e₀.commutes, (e i).commutes]
        exact (IsScalarTower.algebraMap_apply (ResidueField R) (ResidueField S)
          (ResidueField (U i)) a).symm.trans
          (IsScalarTower.algebraMap_apply (ResidueField R) (ResidueField T)
            (ResidueField (U i)) a)
      · change j i (e₀ (AdjoinRoot.root (poly p))) =
          e i (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i) (AdjoinRoot.root (poly p)))
        rw [he₀root, AdjoinRoot.map_root, heroot]
        rfl
    apply RingHom.ext
    intro a
    apply (e i).injective
    change e i ((e i).symm (j i a)) =
      e i (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i) (e₀.symm a))
    rw [(e i).apply_symm_apply]
    have h := RingHom.congr_fun haux (e₀.symm a)
    change j i (e₀ (e₀.symm a)) =
      e i (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i) (e₀.symm a)) at h
    simpa only [e₀.apply_symm_apply] using h
  have hsum := milnorKNormRing_map_eq_weighted_sum_of_branch_equivs_of_normal_prime
    φ p hpdegree e₀.symm Finset.univ
    (fun i => (minpoly (ResidueField T) (β i)).natDegree) q
    (fun i _ j _ hij => hinj hij) hq
    (fun a r hr => by
      obtain ⟨i, hi, _⟩ := hcover (poly r) (monic r) (irreducible r) hr
      exact ⟨i, Finset.mem_univ i, hi.symm⟩)
    (fun i => ResidueField (U i)) (fun i => (e i).symm) j hsquare y
  have hmultiplicity (i : ι) : multiplicity (poly (q i)) ((poly p).map φ) = 1 := by
    have hP : ((poly p).map φ).Monic := (monic p).map φ
    have hPsq : Squarefree ((poly p).map φ) := (irreducible p).separable.map.squarefree
    rw [multiplicity_eq_count_normalizedFactors (irreducible (q i)) hP.ne_zero,
      (monic (q i)).normalize_eq_self]
    exact Multiset.count_eq_one_of_mem
      ((squarefree_iff_nodup_normalizedFactors hP.ne_zero).mp hPsq)
      ((Polynomial.mem_normalizedFactors_iff hP.ne_zero).mpr
        ⟨irreducible (q i), monic (q i), hq i⟩)
  simp only [hmultiplicity, Nat.cast_one, one_zsmul] at hsum
  have hidxRS : ramificationIdx R S = 1 := by
    have h := addVal_algebraMap_eq_ramificationIdx R S π hπ
    rw [he, IsDiscreteValuationRing.addVal_def' u hϖ 1] at h
    exact_mod_cast h.symm
  have hidxTU (i : ι) : ramificationIdx T (U i) = 1 := by
    have h := addVal_algebraMap_eq_ramificationIdx T (U i) τ hτ
    rw [hd i, IsDiscreteValuationRing.addVal_def' (v i) (hω i) (d i),
      (hdegree i).1] at h
    exact_mod_cast h.symm
  have hidxSU (i : ι) : ramificationIdx S (U i) = ramificationIdx R T := by
    have hT := (IsDiscreteValuationRing.ramificationIdx_and_inertiaDeg_tower R T (U i)).1
    have hS := (IsDiscreteValuationRing.ramificationIdx_and_inertiaDeg_tower R S (U i)).1
    have h : ramificationIdx R T * ramificationIdx T (U i) =
        ramificationIdx R S * ramificationIdx S (U i) := by
      simpa only [ramificationIdx_def,
        Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal T)
          (IsDiscreteValuationRing.not_a_field R),
        Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal T) (maximalIdeal (U i))
          (IsDiscreteValuationRing.not_a_field T),
        Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal S)
          (IsDiscreteValuationRing.not_a_field R),
        Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal S) (maximalIdeal (U i))
          (IsDiscreteValuationRing.not_a_field S)] using hT.symm.trans hS
    simpa only [hidxRS, hidxTU i, mul_one, one_mul] using h.symm
  simp_rw [hidxSU]
  rw [← Finset.smul_sum]
  exact congrArg (fun z : MilnorKRing (ResidueField T) => (ramificationIdx R T : ℤ) • z)
    hsum.symm

/-- The same lower residue identity in every homogeneous degree, including degree zero. -/
theorem sum_ramification_smul_residue_norm_map_of_ramification_eq_one_homogeneous
    (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i)) (b : S)
    (hc : ∀ i, algebraMap (U i) (D i) (algebraMap S (U i) b) =
      ε (1 ⊗ₜ[F] (algebraMap S E b)) i)
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (he : algebraMap R S π = (u : S) * ϖ ^ 1)
    (B : PowerBasis (ResidueField R) (ResidueField S)) (hB : B.gen = residue S b)
    {τ : T} (hτ : Irreducible τ) (ω : ∀ i, U i)
    (hω : ∀ i, Irreducible (ω i)) (v : ∀ i, (U i)ˣ) (d : ι → ℕ)
    (hd : ∀ i, algebraMap T (U i) τ = (v i : U i) * ω i ^ d i)
    (hprime : Nat.Prime (finrank (ResidueField R) (ResidueField S)))
    (n : ℕ) (y : MilnorKTheory (ResidueField S) n) :
    (∑ i, (ramificationIdx S (U i) : ℤ) •
      milnorKNorm (ResidueField T) (ResidueField (U i)) n
        (milnorKTheoryMap (algebraMap (ResidueField S) (ResidueField (U i))) n y)) =
      (ramificationIdx R T : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n y) := by
  classical
  apply Subtype.ext
  change (milnorKGrading (ResidueField T) n).subtype
      (∑ i, (ramificationIdx S (U i) : ℤ) •
        milnorKNorm (ResidueField T) (ResidueField (U i)) n
          (milnorKTheoryMap (algebraMap (ResidueField S) (ResidueField (U i))) n y)) =
    (milnorKGrading (ResidueField T) n).subtype
      ((ramificationIdx R T : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n y))
  rw [map_sum]
  simp_rw [map_zsmul, milnorKTheoryMap_eq_transport]
  exact sum_ramification_smul_residue_norm_map_of_ramification_eq_one
    R S T F E L D U ε b hc hπ hϖ u he B hB hτ ω hω v d hd hprime
      (y : MilnorKRing (ResidueField S))

end Stacks.Chow

end
