/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Split base change for the native simple Milnor norm

For a separable defining polynomial that splits after scalar extension, the native
scalar-factor formula is the sum over the actual algebra embeddings of its quotient
field. The factors are precisely `X - C (σ root)`. Their multiplicities are one,
and their degree-one norms are the native evaluation maps.

No finiteness hypothesis on the coefficient extension is required. The second
endpoint supplies the finite embedding type from the native quotient power basis.

-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- After a separable defining polynomial splits, scalar extension of its native
simple Milnor norm is the sum over the actual algebra embeddings of its quotient
field. The finite-type instance may be any instance on that embedding type. -/
theorem simpleMilnorNorm_map_eq_sum_algHom
    {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    [Fintype ((k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K)]
    (hsep : (poly p).Separable)
    (hsplit : ((poly p).map (algebraMap k K)).Splits)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap (algebraMap k K) (simpleMilnorNorm p x) =
      ∑ σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K,
        milnorKRingMap σ.toRingHom x := by
  classical
  let q (σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K) :
      MonicIrreducibleOfDegree K 1 :=
    ⟨X - C (σ (AdjoinRoot.root (poly p))),
      monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩
  have hq (σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K) :
      poly (q σ) ∣ (poly p).map (algebraMap k K) := by
    change X - C (σ (AdjoinRoot.root (poly p))) ∣
      (poly p).map (algebraMap k K)
    apply dvd_iff_isRoot.mpr
    have hroot : (poly p).eval₂ (algebraMap k K)
        (σ (AdjoinRoot.root (poly p))) = 0 :=
      AdjoinRoot.aeval_algHom_eq_zero (poly p) σ
    rw [IsRoot, eval_map]
    exact hroot
  have hinj : Function.Injective
      (fun σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K => poly (q σ)) := by
    intro σ τ h
    apply AdjoinRoot.algHom_ext
    have hzero := congrArg (fun f : K[X] => f.coeff 0) h
    simp only [q, poly, coeff_sub, coeff_X_zero, coeff_C_zero,
      zero_sub, neg_inj] at hzero
    exact hzero
  have hcover :
      ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
        poly r ∣ (poly p).map (algebraMap k K) →
          ∃ σ ∈ (Finset.univ :
            Finset ((k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K)),
            poly r = poly (q σ) := by
    intro a r hr
    have hrdegree : (poly r).natDegree = 1 :=
      (hsplit.of_dvd
        (Polynomial.map_ne_zero
          (f := algebraMap k K) (ne_zero p)) hr).natDegree_eq_one_of_irreducible
        (irreducible r)
    let b : K := -(poly r).coeff 0
    have hrshape : poly r = X - C b := by
      dsimp only [b]
      simpa only [map_neg, sub_neg_eq_add] using
        (monic r).eq_X_add_C hrdegree
    have hbdiv : X - C b ∣ (poly p).map (algebraMap k K) := by
      simpa only [hrshape] using hr
    have hb : (poly p).eval₂ (algebraMap k K) b = 0 := by
      simpa only [IsRoot, eval_map] using dvd_iff_isRoot.mp hbdiv
    let σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K :=
      AdjoinRoot.liftAlgHom (poly p) (Algebra.ofId k K) b hb
    have hσ : σ (AdjoinRoot.root (poly p)) = b := by
      dsimp only [σ]
      exact AdjoinRoot.liftAlgHom_root _ _ _ _
    refine ⟨σ, Finset.mem_univ _, ?_⟩
    change poly r = X - C (σ (AdjoinRoot.root (poly p)))
    rw [hσ]
    exact hrshape
  have hmult (σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K) :
      multiplicity (poly (q σ))
        ((poly p).map (algebraMap k K)) = 1 := by
    apply Nat.le_antisymm
    · apply multiplicity_le_of_emultiplicity_le
      exact emultiplicity_le_one_of_separable
        (irreducible (q σ)).not_isUnit hsep.map
    · exact Nat.succ_le_of_lt (multiplicity_pos_of_dvd (hq σ)
        (FiniteMultiplicity.of_not_isUnit (irreducible (q σ)).not_isUnit
          (Polynomial.map_ne_zero (ne_zero p))))
  let e (σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K) :
      (K[X] ⧸ Ideal.span {poly (q σ)}) ≃ₐ[K] K :=
    quotientSpanXSubCAlgEquiv (σ (AdjoinRoot.root (poly p)))
  have hcomp (σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K) :
      (e σ).toRingHom.comp
        (AdjoinRoot.map (algebraMap k K) (poly p) (poly (q σ)) (hq σ)) =
          σ.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro c
      change (e σ)
          (AdjoinRoot.map (algebraMap k K) (poly p) (poly (q σ)) (hq σ)
            (AdjoinRoot.of (poly p) c)) =
        σ (AdjoinRoot.of (poly p) c)
      rw [AdjoinRoot.map_of]
      change (e σ)
          (algebraMap K (K[X] ⧸ Ideal.span {poly (q σ)})
            ((algebraMap k K) c)) =
        σ (algebraMap k (k[X] ⧸ Ideal.span {poly p}) c)
      calc
        (e σ)
            (algebraMap K (K[X] ⧸ Ideal.span {poly (q σ)})
              ((algebraMap k K) c)) =
            (algebraMap k K) c := (e σ).commutes ((algebraMap k K) c)
        _ = σ (algebraMap k (k[X] ⧸ Ideal.span {poly p}) c) :=
          (σ.commutes c).symm
    · change (e σ)
          (AdjoinRoot.map (algebraMap k K) (poly p) (poly (q σ)) (hq σ)
            (AdjoinRoot.root (poly p))) =
        σ (AdjoinRoot.root (poly p))
      rw [AdjoinRoot.map_root]
      change quotientSpanXSubCAlgEquiv (σ (AdjoinRoot.root (poly p)))
          (Ideal.Quotient.mk _ (X : K[X])) =
        σ (AdjoinRoot.root (poly p))
      rw [quotientSpanXSubCAlgEquiv_mk, eval_X]
  have hfactor :
      milnorKRingMap (algebraMap k K) (simpleMilnorNorm p x) =
        ∑ σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K,
          (multiplicity (poly (q σ)) ((poly p).map (algebraMap k K)) : ℤ) •
            simpleMilnorNorm (q σ) (milnorKRingMap
              (AdjoinRoot.map (algebraMap k K) (poly p) (poly (q σ)) (hq σ)) x) :=
    simpleMilnorNorm_map_eq_weighted_sum_of_factors (algebraMap k K) p x
      Finset.univ (fun _ => 1) q (fun _ _ _ _ h => hinj h) hq hcover
  refine hfactor.trans ?_
  apply Finset.sum_congr rfl
  intro σ _
  rw [hmult σ, Nat.cast_one, one_zsmul]
  let j : (k[X] ⧸ Ideal.span {poly p}) →+* (K[X] ⧸ Ideal.span {poly (q σ)}) :=
    AdjoinRoot.map (algebraMap k K) (poly p) (poly (q σ)) (hq σ)
  let t : (K[X] ⧸ Ideal.span {poly (q σ)}) →+* K := (e σ).toRingHom
  have ht : t.comp j = σ.toRingHom := hcomp σ
  have hn : simpleMilnorNorm (q σ) (milnorKRingMap j x) =
      milnorKRingMap t (milnorKRingMap j x) :=
    simpleMilnorNorm_eq_map_of_degree_one (q σ) (e σ) (milnorKRingMap j x)
  have hm : milnorKRingMap t (milnorKRingMap j x) =
      milnorKRingMap (t.comp j) x := milnorKRingMap_comp_apply j t x
  have hc : milnorKRingMap (t.comp j) x = milnorKRingMap σ.toRingHom x :=
    congrArg (fun f : (k[X] ⧸ Ideal.span {poly p}) →+* K => milnorKRingMap f x) ht
  exact hn.trans (hm.trans hc)

/-- The split base-change formula with its finite embedding type constructed from
its native quotient power basis. The coefficient extension need not be finite. -/
theorem simpleMilnorNorm_map_eq_sum_algHom_of_separable_of_splits
    {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (hsep : (poly p).Separable)
    (hsplit : ((poly p).map (algebraMap k K)).Splits)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    letI : Fintype ((k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K) :=
      PowerBasis.AlgHom.fintype (B := K)
        (AdjoinRoot.powerBasis' (monic p))
    milnorKRingMap (algebraMap k K) (simpleMilnorNorm p x) =
      ∑ σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K,
        milnorKRingMap σ.toRingHom x := by
  let : Fintype ((k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K) :=
    PowerBasis.AlgHom.fintype (B := K)
      (AdjoinRoot.powerBasis' (monic p))
  exact simpleMilnorNorm_map_eq_sum_algHom p hsep hsplit x

end Stacks.Chow

end
