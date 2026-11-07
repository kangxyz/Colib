/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeChosenComparison
public import Colib.FieldTheory.Polynomial.PrimeNormal

/-!
# Scalar-factor base change for the actual chosen normal prime-degree norm

The scalar-factor formula for the existing simple norm is upgraded to the existing
`milnorKNormRing`. Normality and the degree alternative for each literal factor are
conclusions, not comparison assumptions. The degree-one case is proved from the
native projection formula and the actual inverse structure map. The prime case
uses the chosen-norm/presentation comparison in `NormalPrimeChosenComparison`.

The coefficient homomorphism is arbitrary. The source field has characteristic
zero, as required by the imported prime-normal factor-degree theorem. No finite
or algebraic coefficient extension is assumed. The fields share the universe
required by the native Milnor ring; the finite index type has its own universe.
Every multiplicity remains the actual polynomial multiplicity in the formula.

The last endpoint transports the formula to supplied actual branch fields using
actual algebra equivalences and literal commuting squares. These are structural
dictionary hypotheses. This file does not construct a tensor-product factorization,
identify local-factor lengths, connect all DVR/completion branches, or prove a
general tower law. No norm, field, map model, or comparison structure is introduced.
-/

@[expose] public noncomputable section

open Polynomial Module UniqueFactorizationMonoid

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K]

/-- In extension degree one, the chosen norm agrees with the simple norm in an
actual polynomial presentation. No normality or perfectness is needed. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_degree_one
    {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L]
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hd : d = 1)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p})) (x : MilnorKRing L) :
    milnorKNormRing k L x = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) := by
  subst d
  have hdim : finrank k L = 1 := by
    calc
      finrank k L = finrank k (k[X] ⧸ Ideal.span {poly p}) :=
        f.toLinearEquiv.finrank_eq
      _ = (poly p).natDegree := finrank_quotient_span_eq_natDegree
      _ = 1 := natDegree_eq p
  have hb : Function.Bijective (algebraMap k L) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdim
  let g : k ≃ₐ[k] L := AlgEquiv.ofBijective (Algebra.ofId k L) hb
  let r : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] k := f.symm.trans g.symm
  have hg : (algebraMap k L).comp g.symm.toRingHom = RingHom.id L := by
    apply RingHom.ext
    intro a
    exact g.apply_symm_apply a
  have hx : milnorKRingMap (algebraMap k L)
      (milnorKRingMap g.symm.toRingHom x) = x := by
    rw [milnorKRingMap_comp_apply, hg, milnorKRingMap_id_apply]
  have hcomp : r.toRingHom.comp f.toRingHom = g.symm.toRingHom := by
    apply RingHom.ext
    intro a
    change g.symm (f.symm (f a)) = g.symm a
    rw [f.symm_apply_apply]
  calc
    milnorKNormRing k L x = milnorKNormRing k L
        (milnorKRingMap (algebraMap k L) (milnorKRingMap g.symm.toRingHom x)) := by
      rw [hx]
    _ = milnorKRingMap g.symm.toRingHom x := by
      rw [milnorKNormRing_milnorKRingMap, hdim, Nat.cast_one, one_zsmul]
    _ = milnorKRingMap r.toRingHom (milnorKRingMap f.toRingHom x) := by
      rw [milnorKRingMap_comp_apply, hcomp]
    _ = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) :=
      (simpleMilnorNorm_eq_map_of_degree_one p r (milnorKRingMap f.toRingHom x)).symm

/-- A presentation whose degree is one or prime identifies the actual chosen norm.
Normality is used only in the prime case. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_one_or_normal_prime
    [PerfectField k] {L : Type u} [Field L] [Algebra k L]
    [FiniteDimensional k L] [Normal k L]
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hd : d = 1 ∨ d.Prime)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p})) (x : MilnorKRing L) :
    milnorKNormRing k L x = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) := by
  rcases hd with hone | hprime
  · exact milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_degree_one p hone f x
  · have hdim : finrank k L = d := by
      calc
        finrank k L = finrank k (k[X] ⧸ Ideal.span {poly p}) :=
          f.toLinearEquiv.finrank_eq
        _ = (poly p).natDegree := finrank_quotient_span_eq_natDegree
        _ = d := natDegree_eq p
    have hp : Nat.Prime (finrank k L) := by rwa [hdim]
    exact milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime hp p f x

/-- The native quotient form of the degree-one-or-prime comparison. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_one_or_normal_prime
    [PerfectField k] {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (hd : d = 1 ∨ d.Prime)
    [FiniteDimensional k (k[X] ⧸ Ideal.span {poly p})]
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x = simpleMilnorNorm p x := by
  have h := milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_one_or_normal_prime
    p hd (AlgEquiv.refl : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k]
      (k[X] ⧸ Ideal.span {poly p})) x
  change milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x =
    simpleMilnorNorm p (milnorKRingMap (RingHom.id _) x) at h
  simpa only [milnorKRingMap_id_apply] using h

/-- The actual quotient of every irreducible coefficient factor is normal.
This supporting statement is valid in arbitrary characteristic and degree. -/
theorem normal_quotient_of_dvd_map_of_normal
    (φ : k →+* K) {d e : ℕ} (p : MonicIrreducibleOfDegree k d)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ) :
    Normal K (K[X] ⧸ Ideal.span {poly q}) := by
  let : Algebra k K := φ.toAlgebra
  let : Fact (Irreducible (poly p)) := ⟨irreducible p⟩
  let : Fact (Irreducible (poly q)) := ⟨irreducible q⟩
  let ep : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] AdjoinRoot (poly p) :=
    { toRingEquiv := RingEquiv.refl _
      commutes' := fun _ => rfl }
  let eq : (K[X] ⧸ Ideal.span {poly q}) ≃ₐ[K] AdjoinRoot (poly q) :=
    { toRingEquiv := RingEquiv.refl _
      commutes' := fun _ => rfl }
  let : Normal k (AdjoinRoot (poly p)) := Normal.of_algEquiv ep
  let : IsSplittingField K (AdjoinRoot (poly q)) ((poly p).map φ) :=
    AdjoinRoot.isSplittingField_of_dvd_map (monic p) hq
  let : Normal K (AdjoinRoot (poly q)) :=
    Normal.of_isSplittingField ((poly p).map φ)
  exact Normal.of_algEquiv eq.symm

/-- Every literal native coefficient factor has degree one or the source prime.
Only the existing degree theorem forces the characteristic-zero restriction. -/
theorem degree_eq_one_or_eq_of_dvd_map_of_normal_prime
    [CharZero k] (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ) :
    e = 1 ∨ e = d := by
  let : Algebra k K := φ.toAlgebra
  let : Fact (Irreducible (poly p)) := ⟨irreducible p⟩
  let ep : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] AdjoinRoot (poly p) :=
    { toRingEquiv := RingEquiv.refl _
      commutes' := fun _ => rfl }
  let : Normal k (AdjoinRoot (poly p)) := Normal.of_algEquiv ep
  have hp' : (poly p).natDegree.Prime := by simpa only [natDegree_eq p] using hp
  simpa only [natDegree_eq p, natDegree_eq q] using
    Polynomial.natDegree_eq_one_or_eq_of_dvd_map_of_prime_normal
      (monic p) (irreducible p) hp' (irreducible q) hq

/-- On an actual coefficient factor, its chosen norm is its literal simple norm.
Normality and the permissible degree of the factor are proved internally. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_dvd_map_of_normal_prime
    [CharZero k] (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (q : MonicIrreducibleOfDegree K e) (hq : poly q ∣ (poly p).map φ)
    [FiniteDimensional K (K[X] ⧸ Ideal.span {poly q})]
    (x : MilnorKRing (K[X] ⧸ Ideal.span {poly q})) :
    milnorKNormRing K (K[X] ⧸ Ideal.span {poly q}) x = simpleMilnorNorm q x := by
  let : Algebra k K := φ.toAlgebra
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let : Normal K (K[X] ⧸ Ideal.span {poly q}) :=
    normal_quotient_of_dvd_map_of_normal φ p q hq
  have hdegree : e = 1 ∨ e.Prime := by
    rcases degree_eq_one_or_eq_of_dvd_map_of_normal_prime φ p hp q hq with h | h
    · exact Or.inl h
    · exact Or.inr (h.symm ▸ hp)
  exact milnorKNormRing_eq_simpleMilnorNorm_of_one_or_normal_prime q hdegree x

/-- Scalar-factor base change for the actual chosen norm of a normal prime-degree
native quotient. All factor norms are actual chosen norms, with every multiplicity.
The finite-dimensional instances are constructed, not assumed. -/
theorem milnorKNormRing_map_eq_weighted_sum_of_factors_of_normal_prime
    [CharZero k] {ι : Type v} (φ : k →+* K) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i)) :
    letI : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
      (AdjoinRoot.powerBasis' (monic p)).finite
    letI : ∀ i, FiniteDimensional K (K[X] ⧸ Ideal.span {poly (q i)}) :=
      fun i => (AdjoinRoot.powerBasis' (monic (q i))).finite
    milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x) =
      ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
        milnorKNormRing K (K[X] ⧸ Ideal.span {poly (q i)})
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)) x) := by
  let : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
    (AdjoinRoot.powerBasis' (monic p)).finite
  let : ∀ i, FiniteDimensional K (K[X] ⧸ Ideal.span {poly (q i)}) :=
    fun i => (AdjoinRoot.powerBasis' (monic (q i))).finite
  change milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x) = _
  rw [milnorKNormRing_eq_simpleMilnorNorm_of_normal_prime p hp x]
  calc
    milnorKRingMap φ (simpleMilnorNorm p x) =
        ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
          simpleMilnorNorm (q i)
            (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)) x) :=
      simpleMilnorNorm_map_eq_weighted_sum_of_factors φ p x S e q hinj hq hcover
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : MilnorKRing K =>
        (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) • z)
        (milnorKNormRing_eq_simpleMilnorNorm_of_dvd_map_of_normal_prime
          φ p hp (q i) (hq i) _).symm

/-- The chosen-norm formula on an exact finite set of native coefficient factors.
Membership supplies the actual quotient maps and distinctness is automatic. -/
theorem milnorKNormRing_map_eq_sum_coefficientFactors_of_normal_prime
    [CharZero k] (φ : k →+* K) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e))
    (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly p).map φ)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    letI : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
      (AdjoinRoot.powerBasis' (monic p)).finite
    letI : ∀ i : S, FiniteDimensional K (K[X] ⧸ Ideal.span {poly i.1.2}) :=
      fun i => (AdjoinRoot.powerBasis' (monic i.1.2)).finite
    milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x) =
      ∑ i ∈ S.attach, (multiplicity (poly i.1.2) ((poly p).map φ) : ℤ) •
        milnorKNormRing K (K[X] ⧸ Ideal.span {poly i.1.2})
          (milnorKRingMap
            (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)) x) := by
  have hinj : Set.InjOn (fun i : S => poly i.1.2) (S.attach : Set S) := by
    intro i _ j _ hij
    exact Subtype.ext (sigma_poly_injective hij)
  have hq : ∀ i : S, poly i.1.2 ∣ (poly p).map φ := fun i => (hS i.1).mp i.2
  have hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S.attach, poly r = poly i.1.2 := by
    intro a r hr
    let i : S := ⟨⟨a, r⟩, (hS ⟨a, r⟩).mpr hr⟩
    exact ⟨i, Finset.mem_attach S i, rfl⟩
  exact milnorKNormRing_map_eq_weighted_sum_of_factors_of_normal_prime
    φ p hp x S.attach (fun i => i.1.1) (fun i => i.1.2) hinj hq hcover

/-- An exact finite native coefficient-factor set exists for the chosen-norm formula.
Neither a factor enumeration nor a norm-comparison hypothesis is supplied. -/
theorem exists_finset_milnorKNormRing_map_eq_sum_coefficientFactors_of_normal_prime
    [CharZero k] (φ : k →+* K) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})] :
    ∃ (S : Finset (Σ e : ℕ, MonicIrreducibleOfDegree K e))
      (hS : ∀ q, q ∈ S ↔ poly q.2 ∣ (poly p).map φ),
      letI : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
        (AdjoinRoot.powerBasis' (monic p)).finite
      letI : ∀ i : S, FiniteDimensional K (K[X] ⧸ Ideal.span {poly i.1.2}) :=
        fun i => (AdjoinRoot.powerBasis' (monic i.1.2)).finite
      ∀ x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}),
        milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x) =
          ∑ i ∈ S.attach, (multiplicity (poly i.1.2) ((poly p).map φ) : ℤ) •
            milnorKNormRing K (K[X] ⧸ Ideal.span {poly i.1.2})
              (milnorKRingMap
                (AdjoinRoot.map φ (poly p) (poly i.1.2) ((hS i.1).mp i.2)) x) := by
  obtain ⟨S, hS⟩ := exists_finset_mem_iff_dvd_map φ (poly p) (ne_zero p)
  exact ⟨S, hS,
    milnorKNormRing_map_eq_sum_coefficientFactors_of_normal_prime φ p hp S hS⟩

/-- The literal normalized-factor formula for the actual chosen norm. Repeated
factors occur once, with their full polynomial multiplicity as coefficient. -/
theorem milnorKNormRing_map_eq_sum_normalizedFactors_of_normal_prime
    [CharZero k] [DecidableEq K] (φ : k →+* K) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    letI : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
      (AdjoinRoot.powerBasis' (monic p)).finite
    milnorKRingMap φ (milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x) =
      ∑ i ∈ (normalizedFactors ((poly p).map φ)).toFinset.attach,
        let hi := (Polynomial.mem_normalizedFactors_iff
          (Polynomial.map_ne_zero (f := φ) (ne_zero p))).mp (Multiset.mem_toFinset.mp i.2)
        let q : MonicIrreducibleOfDegree K i.1.natDegree := ⟨i.1, hi.2.1, hi.1, rfl⟩
        letI : FiniteDimensional K (K[X] ⧸ Ideal.span {poly q}) :=
          (AdjoinRoot.powerBasis' (monic q)).finite
        (multiplicity i.1 ((poly p).map φ) : ℤ) •
          milnorKNormRing K (K[X] ⧸ Ideal.span {poly q})
            (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly q) hi.2.2) x) := by
  let S := (normalizedFactors ((poly p).map φ)).toFinset
  have hmem (i : S) : Irreducible i.1 ∧ i.1.Monic ∧ i.1 ∣ (poly p).map φ :=
    (Polynomial.mem_normalizedFactors_iff
      (Polynomial.map_ne_zero (f := φ) (ne_zero p))).mp (Multiset.mem_toFinset.mp i.2)
  let q (i : S) : MonicIrreducibleOfDegree K i.1.natDegree :=
    ⟨i.1, (hmem i).2.1, (hmem i).1, rfl⟩
  have hinj : Set.InjOn (fun i : S => poly (q i)) (S.attach : Set S) := by
    intro i _ j _ hij
    exact Subtype.ext hij
  have hq : ∀ i : S, poly (q i) ∣ (poly p).map φ := fun i => (hmem i).2.2
  have hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S.attach, poly r = poly (q i) := by
    intro a r hr
    have hrS : poly r ∈ S := Multiset.mem_toFinset.mpr
      ((Polynomial.mem_normalizedFactors_iff
        (Polynomial.map_ne_zero (f := φ) (ne_zero p))).mpr ⟨irreducible r, monic r, hr⟩)
    let i : S := ⟨poly r, hrS⟩
    exact ⟨i, Finset.mem_attach S i, rfl⟩
  exact milnorKNormRing_map_eq_weighted_sum_of_factors_of_normal_prime
    φ p hp x S.attach (fun i => i.1.natDegree) q hinj hq hcover

/-- The scalar-factor formula transported to actual source and branch fields.
The given algebra equivalences and commuting squares are only structural
dictionary data; no branch norm equality or tower law is assumed. -/
theorem milnorKNormRing_map_eq_weighted_sum_of_branch_equivs_of_normal_prime
    [CharZero k] {ι : Type v} (φ : k →+* K)
    {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L] [Normal k L]
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p}))
    (S : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (S : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly p).map φ)
    (hcover : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      poly r ∣ (poly p).map φ → ∃ i ∈ S, poly r = poly (q i))
    (M : ι → Type u) [∀ i, Field (M i)] [∀ i, Algebra K (M i)]
    [∀ i, FiniteDimensional K (M i)]
    (g : ∀ i, M i ≃ₐ[K] (K[X] ⧸ Ideal.span {poly (q i)}))
    (j : ∀ i, L →+* M i)
    (hsquare : ∀ i, (g i).toRingHom.comp (j i) =
      (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)).comp f.toRingHom)
    (x : MilnorKRing L) :
    milnorKRingMap φ (milnorKNormRing k L x) =
      ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
        milnorKNormRing K (M i) (milnorKRingMap (j i) x) := by
  let : Algebra k K := φ.toAlgebra
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let : Normal k (k[X] ⧸ Ideal.span {poly p}) := Normal.of_algEquiv f
  have hdim : finrank k L = d := by
    calc
      finrank k L = finrank k (k[X] ⧸ Ideal.span {poly p}) :=
        f.toLinearEquiv.finrank_eq
      _ = (poly p).natDegree := finrank_quotient_span_eq_natDegree
      _ = d := natDegree_eq p
  have hpL : Nat.Prime (finrank k L) := by rwa [hdim]
  have hsource : milnorKNormRing k L x =
      simpleMilnorNorm p (milnorKRingMap f.toRingHom x) :=
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime hpL p f x
  have hbranch (i : ι) :
      milnorKNormRing K (M i) (milnorKRingMap (j i) x) =
        simpleMilnorNorm (q i)
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i))
            (milnorKRingMap f.toRingHom x)) := by
    let : Normal K (K[X] ⧸ Ideal.span {poly (q i)}) :=
      normal_quotient_of_dvd_map_of_normal φ p (q i) (hq i)
    let : Normal K (M i) := Normal.of_algEquiv (g i).symm
    have hdegree : e i = 1 ∨ (e i).Prime := by
      rcases degree_eq_one_or_eq_of_dvd_map_of_normal_prime
          φ p hp (q i) (hq i) with h | h
      · exact Or.inl h
      · exact Or.inr (h.symm ▸ hp)
    calc
      milnorKNormRing K (M i) (milnorKRingMap (j i) x) =
          simpleMilnorNorm (q i)
            (milnorKRingMap (g i).toRingHom (milnorKRingMap (j i) x)) :=
        milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_one_or_normal_prime
          (q i) hdegree (g i) (milnorKRingMap (j i) x)
      _ = _ := by
        let a : (k[X] ⧸ Ideal.span {poly p}) →+*
            (K[X] ⧸ Ideal.span {poly (q i)}) :=
          AdjoinRoot.map φ (poly p) (poly (q i)) (hq i)
        let s : L →+* (k[X] ⧸ Ideal.span {poly p}) := f.toRingHom
        let t : M i →+* (K[X] ⧸ Ideal.span {poly (q i)}) := (g i).toRingHom
        have hc : t.comp (j i) = a.comp s := hsquare i
        have hleft : milnorKRingMap t (milnorKRingMap (j i) x) =
            milnorKRingMap (t.comp (j i)) x :=
          milnorKRingMap_comp_apply (j i) t x
        have hmiddle : milnorKRingMap (t.comp (j i)) x =
            milnorKRingMap (a.comp s) x :=
          congrArg (fun h : L →+* (K[X] ⧸ Ideal.span {poly (q i)}) =>
            milnorKRingMap h x) hc
        have hright : milnorKRingMap a (milnorKRingMap s x) =
            milnorKRingMap (a.comp s) x :=
          milnorKRingMap_comp_apply s a x
        exact congrArg (simpleMilnorNorm (q i))
          (hleft.trans (hmiddle.trans hright.symm))
  calc
    milnorKRingMap φ (milnorKNormRing k L x) =
        milnorKRingMap φ (simpleMilnorNorm p (milnorKRingMap f.toRingHom x)) :=
      congrArg (milnorKRingMap φ) hsource
    _ = ∑ i ∈ S, (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) •
        simpleMilnorNorm (q i)
          (milnorKRingMap (AdjoinRoot.map φ (poly p) (poly (q i)) (hq i))
            (milnorKRingMap f.toRingHom x)) :=
      simpleMilnorNorm_map_eq_weighted_sum_of_factors
        φ p (milnorKRingMap f.toRingHom x) S e q hinj hq hcover
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : MilnorKRing K =>
        (multiplicity (poly (q i)) ((poly p).map φ) : ℤ) • z) (hbranch i).symm

end Stacks.Chow

end
