/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Norm.SplitBaseChange
public import Colib.KTheory.MilnorK.Norm.PresentationBaseChange
public import Colib.KTheory.MilnorK.FiniteMixedGeneration
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.Data.Int.GCD

/-!
# Normal prime-degree presentation independence

All fields are in one universe. The base is perfect. The proof first compares
actual embedding sums over the normal root field, then uses a classwise finite
coprime mixed-generation field. Native degree projection for the chosen FieldNorm
and a local Bezout calculation remove the residual torsion.

No tower law, chosen-norm/simple-norm comparison, or detection model is used.
The hypotheses in the final endpoint are prime degree, normality, perfectness,
and an actual algebra equivalence between the two native polynomial quotients.

UNCOMPILED SOURCE DRAFT. No Lean/Lake command has been run on this file.
-/

@[expose] public noncomputable section

open Polynomial
open scoped BigOperators

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

/-- Actual equivalent presentations have equal restricted norms over a field
in which both defining polynomials split separably. -/
theorem simpleMilnorNorm_map_eq_of_splits
    [Algebra k K] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d)
    (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (hpsep : (poly p).Separable)
    (hqsep : (poly q).Separable)
    (hpsplit : ((poly p).map (algebraMap k K)).Splits)
    (hqsplit : ((poly q).map (algebraMap k K)).Splits)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap (algebraMap k K) (simpleMilnorNorm p x) =
      milnorKRingMap (algebraMap k K)
        (simpleMilnorNorm q (milnorKRingMap f.toRingHom x)) := by
  classical
  let : Fintype ((k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K) :=
    PowerBasis.AlgHom.fintype (B := K) (AdjoinRoot.powerBasis' (monic p))
  let : Fintype ((k[X] ⧸ Ideal.span {poly q}) →ₐ[k] K) :=
    PowerBasis.AlgHom.fintype (B := K) (AdjoinRoot.powerBasis' (monic q))
  rw [simpleMilnorNorm_map_eq_sum_algHom p hpsep hpsplit x,
    simpleMilnorNorm_map_eq_sum_algHom q hqsep hqsplit
      (milnorKRingMap f.toRingHom x)]
  symm
  refine Fintype.sum_equiv
    (AlgEquiv.arrowCongr f.symm (AlgEquiv.refl : K ≃ₐ[k] K)) _ _ ?_
  intro σ
  have hm : milnorKRingMap σ.toRingHom (milnorKRingMap f.toRingHom x) =
      milnorKRingMap (σ.toRingHom.comp f.toRingHom) x :=
    milnorKRingMap_comp_apply f.toRingHom σ.toRingHom x
  simp only [AlgEquiv.arrowCongr_apply, AlgEquiv.symm_symm,
    AlgEquiv.refl_toAlgHom, AlgHom.id_comp]
  exact hm

/-- Restriction to the actual normal root field identifies the two norms.
This conclusion is equality after restriction, not yet equality over the base. -/
theorem simpleMilnorNorm_map_eq_over_normal
    [PerfectField k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d)
    (q : MonicIrreducibleOfDegree k e)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p}))
        (simpleMilnorNorm p x) =
      milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p}))
        (simpleMilnorNorm q (milnorKRingMap f.toRingHom x)) := by
  classical
  let ap : k[X] ⧸ Ideal.span {poly p} := AdjoinRoot.root (poly p)
  let aq : k[X] ⧸ Ideal.span {poly q} := AdjoinRoot.root (poly q)
  have hap : aeval ap (poly p) = 0 :=
    (AdjoinRoot.aeval_eq (f := poly p) (poly p)).trans (AdjoinRoot.mk_self (f := poly p))
  have haq : aeval aq (poly q) = 0 :=
    (AdjoinRoot.aeval_eq (f := poly q) (poly q)).trans (AdjoinRoot.mk_self (f := poly q))
  have hpmin : minpoly k ap = poly p :=
    (minpoly.eq_of_irreducible_of_monic (irreducible p) hap (monic p)).symm
  have hqmin : minpoly k aq = poly q :=
    (minpoly.eq_of_irreducible_of_monic (irreducible q) haq (monic q)).symm
  have hqmin' : minpoly k (f.symm aq) = poly q :=
    (minpoly.algEquiv_eq f.symm aq).trans hqmin
  have hpsplit :
      ((poly p).map (algebraMap k (k[X] ⧸ Ideal.span {poly p}))).Splits := by
    have h := Normal.splits (inferInstance : Normal k (k[X] ⧸ Ideal.span {poly p})) ap
    rw [hpmin] at h
    exact h
  have hqsplit :
      ((poly q).map (algebraMap k (k[X] ⧸ Ideal.span {poly p}))).Splits := by
    have h := Normal.splits (inferInstance : Normal k (k[X] ⧸ Ideal.span {poly p})) (f.symm aq)
    rw [hqmin'] at h
    exact h
  exact simpleMilnorNorm_map_eq_of_splits p q f
    (PerfectField.separable_of_irreducible (irreducible p))
    (PerfectField.separable_of_irreducible (irreducible q)) hpsplit hqsplit x

private theorem restriction_zero_degree_zsmul [Algebra k K] [FiniteDimensional k K]
    (z : MilnorKRing k) (hz : milnorKRingMap (algebraMap k K) z = 0) :
    (Module.finrank k K : ℤ) • z = 0 := by
  have hproj : milnorKNormRing k K (milnorKRingMap (algebraMap k K) z) =
      (Module.finrank k K : ℤ) • z := milnorKNormRing_milnorKRingMap z
  have hz' : milnorKNormRing k K (milnorKRingMap (algebraMap k K) z) = 0 :=
    (congrArg (milnorKNormRing k K) hz).trans (map_zero (milnorKNormRing k K))
  exact hproj.symm.trans hz'

private theorem simpleMilnorNorm_difference_smul_of_mixed
    [Algebra k K] [FiniteDimensional k K] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (hpK : Irreducible ((poly p).map (algebraMap k K)))
    (hqK : Irreducible ((poly q).map (algebraMap k K)))
    (m : ℕ) (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1)) :
    let _ : Fact (Irreducible ((poly p).map (algebraMap k K))) := ⟨hpK⟩
    let j : (k[X] ⧸ Ideal.span {poly p}) →+*
        AdjoinRoot ((poly p).map (algebraMap k K)) :=
      AdjoinRoot.map (algebraMap k K) (poly p) ((poly p).map (algebraMap k K)) dvd_rfl
    milnorKTheoryMap j (m + 1) x ∈
        milnorKMixedSpan (algebraMap K (AdjoinRoot ((poly p).map (algebraMap k K)))) m →
      (Module.finrank k K : ℤ) •
        (simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) -
          simpleMilnorNorm q (milnorKRingMap f.toRingHom
            (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))) = 0 := by
  let : Fact (Irreducible ((poly p).map (algebraMap k K))) := ⟨hpK⟩
  let j : (k[X] ⧸ Ideal.span {poly p}) →+*
      AdjoinRoot ((poly p).map (algebraMap k K)) :=
    AdjoinRoot.map (algebraMap k K) (poly p) ((poly p).map (algebraMap k K)) dvd_rfl
  change milnorKTheoryMap j (m + 1) x ∈
      milnorKMixedSpan (algebraMap K (AdjoinRoot ((poly p).map (algebraMap k K)))) m → _
  intro hx
  have hm : milnorKTheoryMap j (m + 1) x = milnorKTransport j (m + 1) x :=
    congrArg (fun h : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1) →ₗ[ℤ]
      MilnorKTheory (AdjoinRoot ((poly p).map (algebraMap k K))) (m + 1) => h x)
      (milnorKTheoryMap_eq_transport j)
  have hx' : milnorKTransport j (m + 1) x ∈
      milnorKMixedSpan (algebraMap K (AdjoinRoot ((poly p).map (algebraMap k K)))) m :=
    hm ▸ hx
  have hK : milnorKRingMap (algebraMap k K)
      (simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) =
        milnorKRingMap (algebraMap k K) (simpleMilnorNorm q
          (milnorKRingMap f.toRingHom (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))) :=
    simpleMilnorNorm_map_eq_of_mapped_mem_mixedSpan
      (algebraMap k K) p q f hpK hqK m x hx'
  apply restriction_zero_degree_zsmul
  exact (map_sub (milnorKRingMap (algebraMap k K)) _ _).trans (sub_eq_zero.mpr hK)

private theorem simpleMilnorNorm_difference_exists_coprime_smul
    [PerfectField k] {ell : ℕ}
    (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (m : ℕ) (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1)) :
    ∃ d : ℕ, ell.Coprime d ∧
      (d : ℤ) • (simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) -
        simpleMilnorNorm q (milnorKRingMap f.toRingHom
          (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))) = 0 := by
  classical
  let : Fact (Irreducible (poly p)) := ⟨irreducible p⟩
  let i : (k[X] ⧸ Ideal.span {poly p}) →+* AdjoinRoot (poly p) := RingHom.id _
  let y : MilnorKTheory (AdjoinRoot (poly p)) (m + 1) := milnorKTheoryMap i (m + 1) x
  have hpprime : (poly p).natDegree.Prime := by
    simpa only [natDegree_eq p] using hprime
  obtain ⟨s, _hs, S, hfinite, _hsep, hcop, _hsplit, hpS, hgen⟩ :=
    exists_finite_coprime_milnorK_mixed_expansion (poly p) (monic p) hpprime m y
  let : FiniteDimensional k S := hfinite
  let : Fact (Irreducible ((poly p).map (algebraMap k S))) := ⟨hpS⟩
  dsimp only at hgen
  obtain ⟨c, hc⟩ := hgen
  have hcop' : ell.Coprime (Module.finrank k S) := by
    simpa only [natDegree_eq p] using hcop
  have hqS : Irreducible ((poly q).map (algebraMap k S)) :=
    (monic q).irreducible_map_of_natDegree_coprime (irreducible q)
      (by simpa only [natDegree_eq q] using hcop')
  let jp : (k[X] ⧸ Ideal.span {poly p}) →+* AdjoinRoot ((poly p).map (algebraMap k S)) :=
    AdjoinRoot.map (algebraMap k S) (poly p) ((poly p).map (algebraMap k S)) dvd_rfl
  let j : AdjoinRoot (poly p) →+* AdjoinRoot ((poly p).map (algebraMap k S)) :=
    AdjoinRoot.map (algebraMap k S) (poly p) ((poly p).map (algebraMap k S)) dvd_rfl
  have hji : j.comp i = jp := by
    apply RingHom.ext
    intro z
    rfl
  have hmap : milnorKTheoryMap jp (m + 1) x = milnorKTheoryMap j (m + 1) y := by
    have hcomp : milnorKTheoryMap (j.comp i) (m + 1) x =
        milnorKTheoryMap j (m + 1) (milnorKTheoryMap i (m + 1) x) :=
      congrArg (fun h : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1) →ₗ[ℤ]
        MilnorKTheory (AdjoinRoot ((poly p).map (algebraMap k S))) (m + 1) => h x)
        (milnorKTheoryMap_comp i j)
    have hid : milnorKTheoryMap (j.comp i) (m + 1) x = milnorKTheoryMap jp (m + 1) x :=
      congrArg (fun h : (k[X] ⧸ Ideal.span {poly p}) →+*
        AdjoinRoot ((poly p).map (algebraMap k S)) => milnorKTheoryMap h (m + 1) x) hji
    exact hid.symm.trans hcomp
  have hmem : milnorKTheoryMap jp (m + 1) x ∈
      milnorKMixedSpan (algebraMap S (AdjoinRoot ((poly p).map (algebraMap k S)))) m := by
    change milnorKTheoryMap jp (m + 1) x ∈ Submodule.span ℤ _
    exact Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨c, hc.trans hmap.symm⟩
  refine ⟨Module.finrank k S, hcop', ?_⟩
  exact simpleMilnorNorm_difference_smul_of_mixed (K := S) p q f hpS hqS m x hmem

/-- Presentation independence for every positive homogeneous class. The finite
coprime extension is chosen for this class, not once for the whole Milnor ring. -/
theorem simpleMilnorNorm_eq_map_algEquiv_of_normal_prime_homogeneous
    [PerfectField k] {ell : ℕ}
    (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (m : ℕ) (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1)) :
    simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) =
      simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) := by
  classical
  let δ : MilnorKRing k :=
    simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) -
      simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))
  let : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
    (AdjoinRoot.powerBasis' (monic p)).finite
  have hdim : Module.finrank k (k[X] ⧸ Ideal.span {poly p}) = ell := by
    rw [finrank_quotient_span_eq_natDegree, natDegree_eq p]
  have hE : milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p})) δ = 0 := by
    dsimp only [δ]
    rw [map_sub, simpleMilnorNorm_map_eq_over_normal p q f
      (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})), sub_self]
  have hell : (ell : ℤ) • δ = 0 := by
    have h := restriction_zero_degree_zsmul δ hE
    rw [hdim] at h
    exact h
  obtain ⟨d, hcop, hd⟩ :=
    simpleMilnorNorm_difference_exists_coprime_smul p q hprime f m x
  change (d : ℤ) • δ = 0 at hd
  have hbez : (1 : ℤ) = (ell : ℤ) * Nat.gcdA ell d +
      (d : ℤ) * Nat.gcdB ell d := by
    simpa only [hcop.gcd_eq_one, Nat.cast_one] using
      Nat.gcd_eq_gcd_ab ell d
  have hδ : δ = 0 := by
    calc
      δ = (1 : ℤ) • δ := (one_smul ℤ δ).symm
      _ = ((ell : ℤ) * Nat.gcdA ell d +
            (d : ℤ) * Nat.gcdB ell d) • δ :=
        congrArg (fun a : ℤ => a • δ) hbez
      _ = Nat.gcdA ell d • ((ell : ℤ) • δ) +
            Nat.gcdB ell d • ((d : ℤ) • δ) := by
        rw [add_smul, mul_comm (ell : ℤ) (Nat.gcdA ell d),
          mul_comm (d : ℤ) (Nat.gcdB ell d),
          mul_smul, mul_smul]
      _ = 0 := by rw [hell, hd, smul_zero, smul_zero, add_zero]
  exact sub_eq_zero.mp hδ

/-- Whole-ring presentation independence in normal prime degree over a perfect base. -/
theorem simpleMilnorNorm_eq_map_algEquiv_of_normal_prime
    [PerfectField k] {ell : ℕ}
    (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    simpleMilnorNorm p x =
      simpleMilnorNorm q (milnorKRingMap f.toRingHom x) := by
  let lhs : MilnorKRing (k[X] ⧸ Ideal.span {poly p}) →+ MilnorKRing k := simpleMilnorNorm p
  let rhs : MilnorKRing (k[X] ⧸ Ideal.span {poly p}) →+ MilnorKRing k :=
    (simpleMilnorNorm q).comp (milnorKRingMap f.toRingHom).toAddMonoidHom
  have hgen (l : List (k[X] ⧸ Ideal.span {poly p})ˣ) :
      milnorKSymbolProd (k[X] ⧸ Ideal.span {poly p}) l ∈ AddMonoidHom.eqLocus lhs rhs := by
    change simpleMilnorNorm p (milnorKSymbolProd (k[X] ⧸ Ideal.span {poly p}) l) =
      simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (milnorKSymbolProd (k[X] ⧸ Ideal.span {poly p}) l))
    cases l with
    | nil => simp only [milnorKSymbolProd_nil, map_one, simpleMilnorNorm_one]
    | cons a l =>
        exact simpleMilnorNorm_eq_map_algEquiv_of_normal_prime_homogeneous
          p q hprime f l.length
          ⟨milnorKSymbolProd (k[X] ⧸ Ideal.span {poly p}) (a :: l), by
            simpa only [List.length_cons] using
              milnorKSymbolProd_mem_milnorKGrading (a :: l)⟩
  exact mem_of_forall_milnorKSymbolProd_mem (H := AddMonoidHom.eqLocus lhs rhs) hgen x

/-- Normal prime-degree presentation independence as equality of the existing additive maps. -/
theorem simpleMilnorNorm_eq_comp_of_normal_prime
    [PerfectField k] {ell : ℕ}
    (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q})) :
    simpleMilnorNorm p =
      (simpleMilnorNorm q).comp (milnorKRingMap f.toRingHom).toAddMonoidHom := by
  ext x
  exact simpleMilnorNorm_eq_map_algEquiv_of_normal_prime p q hprime f x

end Stacks.Chow

end
